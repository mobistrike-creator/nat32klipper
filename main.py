#!/usr/bin/env python3
"""NAT32KLIPPER for Windows + Render — Virtual Klipper + Moonraker + Web UI"""

import hashlib, base64, json, struct, time, os, re, mimetypes, threading, socket
from pathlib import Path
from collections import deque
from http.server import HTTPServer, BaseHTTPRequestHandler
from socketserver import ThreadingMixIn
from urllib.parse import unquote_plus

# ─── Configuration ──────────────────────────────────────────────
PORT = int(os.environ.get("PORT", 7125))
GCODES_DIR = Path("gcodes")
GCODES_DIR.mkdir(exist_ok=True)
PRINTER_HOSTNAME = "win-virtual-klipper"
KLIPPER_VERSION = "v0.12.0-virtual"
MOONRAKER_VERSION = "v0.9.1-virtual"

# ─── WebSocket helpers ─────────────────────────────────────────
WS_MAGIC = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"

def ws_accept_key(key: str) -> str:
    return base64.b64encode(hashlib.sha1((key + WS_MAGIC).encode()).digest()).decode()

def ws_encode_frame(data: bytes, opcode: int = 0x01) -> bytes:
    frame = bytearray()
    frame.append(0x80 | opcode)
    if len(data) < 126:
        frame.append(len(data))
    elif len(data) < 65536:
        frame.append(126)
        frame.extend(struct.pack(">H", len(data)))
    else:
        frame.append(127)
        frame.extend(struct.pack(">Q", len(data)))
    frame.extend(data)
    return bytes(frame)

def ws_decode_frame(data: bytes):
    if len(data) < 2:
        return None, data
    b0, b1 = data[0], data[1]
    opcode = b0 & 0x0F
    masked = bool(b1 & 0x80)
    length = b1 & 0x7F
    offset = 2
    if length == 126:
        if len(data) < 4:
            return None, data
        length = struct.unpack(">H", data[2:4])[0]
        offset = 4
    elif length == 127:
        if len(data) < 10:
            return None, data
        length = struct.unpack(">Q", data[2:10])[0]
        offset = 10
    if masked:
        if len(data) < offset + 4:
            return None, data
        mask_key = data[offset:offset + 4]
        offset += 4
    if len(data) < offset + length:
        return None, data
    payload = bytearray(data[offset:offset + length])
    if masked:
        for i in range(len(payload)):
            payload[i] ^= mask_key[i & 3]
    remaining = data[offset + length:]
    return (opcode, bytes(payload)), remaining

# ─── Virtual MCU ────────────────────────────────────────────────
class VirtualMCU:
    def __init__(self):
        self.lock = threading.Lock()
        self.extruder_temp = 25.0
        self.extruder_target = 0.0
        self.bed_temp = 25.0
        self.bed_target = 0.0
        self.fan_speed = 0.0
        self.pos_x = self.pos_y = self.pos_z = self.pos_e = 0.0
        self.progress = 0.0
        self.print_duration = 0
        self.print_state = "standby"
        self.filename = ""
        self.message = ""
        self.klippy_ready = True
        self._is_relative = False
        self._print_start_ms = 0.0
        self._paused_accum = 0.0
        self._pause_start = 0.0
        self._last_sim = 0.0
        self._total_seconds = 120.0

    def execute_gcode(self, script: str):
        with self.lock:
            for line in script.strip().split("\n"):
                line = line.strip()
                if not line or line.startswith(";") or line.startswith("//"):
                    continue
                line = line.split(";")[0].strip()
                self._process_line(line)

    def _process_line(self, cmd: str):
        if cmd == "G28":
            self.pos_x = self.pos_y = self.pos_z = 0.0
            self.message = "Homed all axes"
        elif cmd.startswith("G28"):
            for p in cmd.split()[1:]:
                a = p.upper()
                if a == "X": self.pos_x = 0.0
                elif a == "Y": self.pos_y = 0.0
                elif a == "Z": self.pos_z = 0.0
            self.message = f"Homed {cmd.split()[1:]}"
        elif cmd == "G90": self._is_relative = False
        elif cmd == "G91": self._is_relative = True
        elif cmd.startswith("G0") or cmd.startswith("G1"): self._parse_move(cmd)
        elif cmd.startswith("M104"):
            m = re.search(r'S([\d.]+)', cmd)
            if m: self.extruder_target = float(m.group(1))
        elif cmd.startswith("M140"):
            m = re.search(r'S([\d.]+)', cmd)
            if m: self.bed_target = float(m.group(1))
        elif cmd.startswith("M106"):
            m = re.search(r'S([\d.]+)', cmd)
            self.fan_speed = min(1.0, (float(m.group(1)) if m else 255) / 255.0)
        elif cmd == "M107": self.fan_speed = 0.0
        elif cmd == "M84" or cmd == "M18": self.message = "Steppers disabled"
        elif cmd.startswith("M117"): self.message = cmd[4:].strip()
        elif cmd == "M112": self.emergency_stop()
        elif cmd.startswith("G92"): self._parse_g92(cmd)

    def _parse_move(self, cmd: str):
        x = y = z = e = None
        for match in re.finditer(r'([XYZEF])(-?[\d.]+)', cmd, re.IGNORECASE):
            axis, val = match.group(1).upper(), float(match.group(2))
            if axis == 'X': x = val
            elif axis == 'Y': y = val
            elif axis == 'Z': z = val
            elif axis == 'E': e = val
        if self._is_relative:
            if x is not None: self.pos_x += x
            if y is not None: self.pos_y += y
            if z is not None: self.pos_z += z
            if e is not None: self.pos_e += e
        else:
            if x is not None: self.pos_x = x
            if y is not None: self.pos_y = y
            if z is not None: self.pos_z = z
            if e is not None: self.pos_e = e

    def _parse_g92(self, cmd: str):
        for match in re.finditer(r'([XYZEF])(-?[\d.]+)', cmd, re.IGNORECASE):
            a, v = match.group(1).upper(), float(match.group(2))
            if a == 'X': self.pos_x = v
            elif a == 'Y': self.pos_y = v
            elif a == 'Z': self.pos_z = v
            elif a == 'E': self.pos_e = v

    def start_print(self, filename: str):
        with self.lock:
            self.filename = filename
            self.progress = 0.0
            self.print_duration = 0
            self.print_state = "printing"
            self._print_start_ms = time.time()
            self._paused_accum = 0.0

    def pause_print(self):
        with self.lock:
            if self.print_state == "printing":
                self.print_state = "paused"
                self._pause_start = time.time()

    def resume_print(self):
        with self.lock:
            if self.print_state == "paused":
                self.print_state = "printing"
                self._paused_accum += time.time() - self._pause_start
                self._print_start_ms = time.time() - self._paused_accum

    def cancel_print(self):
        with self.lock:
            self.print_state = "standby"
            self.progress = 0.0
            self.filename = ""

    def emergency_stop(self):
        with self.lock:
            self.print_state = "error"
            self.message = "EMERGENCY STOP"
            self.extruder_target = 0.0
            self.bed_target = 0.0
            self.klippy_ready = False

    def firmware_restart(self):
        with self.lock:
            self.__init__()

    def tick(self):
        with self.lock:
            now = time.time()
            dt = now - self._last_sim
            self._last_sim = now
            if dt > 1.0: dt = 0.1
            if self.extruder_target > 0:
                self.extruder_temp += (self.extruder_target - self.extruder_temp) * dt * 0.05
            else:
                self.extruder_temp += (25.0 - self.extruder_temp) * dt * 0.01
            if self.bed_target > 0:
                self.bed_temp += (self.bed_target - self.bed_temp) * dt * 0.03
            else:
                self.bed_temp += (25.0 - self.bed_temp) * dt * 0.005
            if self.print_state == "printing":
                elapsed = now - self._print_start_ms
                self.progress = min(1.0, elapsed / self._total_seconds)
                self.print_duration = int(elapsed)
                if self.progress >= 1.0:
                    self.print_state = "complete"
                    self.message = "Print complete"

    def get_status(self) -> dict:
        with self.lock:
            return {
                "extruder": {"temperature": round(self.extruder_temp, 1), "target": round(self.extruder_target, 1)},
                "heater_bed": {"temperature": round(self.bed_temp, 1), "target": round(self.bed_target, 1)},
                "fan": {"speed": round(self.fan_speed, 3)},
                "toolhead": {"position": [round(self.pos_x, 1), round(self.pos_y, 1), round(self.pos_z, 1)]},
                "print_stats": {"filename": self.filename, "print_duration": self.print_duration,
                                "state": self.print_state, "message": self.message},
                "virtual_sdcard": {"progress": round(self.progress, 4)},
                "display_status": {"message": self.message},
                "webhooks": {"state": "ready" if self.klippy_ready else "shutdown"},
            }

# ─── Command History ────────────────────────────────────────────
class CmdHistory:
    def __init__(self, maxlen=14):
        self._items = deque(maxlen=maxlen)
    def add(self, cmd: str): self._items.append((time.time(), cmd))
    def add_custom(self, source: str, detail: str):
        self._items.append((time.time(), f"[{source}] {detail.replace(chr(10),' ').replace(chr(13),' ')}"))
    def add_print_start(self, filename: str): self._items.append((time.time(), f"> PRINT START {filename}"))

cmd_history = CmdHistory()

# ─── MCU tick thread ────────────────────────────────────────────
mcu = VirtualMCU()

def mcu_tick_loop():
    while True:
        mcu.tick()
        time.sleep(0.1)

tick_thread = threading.Thread(target=mcu_tick_loop, daemon=True)
tick_thread.start()

# ─── Web UI HTML (embedded) ────────────────────────────────────
WEB_UI_HTML = r"""<!DOCTYPE html>
<html lang="ru">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Virtual Klipper</title>
<style>
:root{--bg:#0d1117;--panel:#161b22;--border:#30363d;--text:#e6edf3;--muted:#8b949e;--accent:#58a6ff;--hot:#f85149;--bed:#d29922;--ok:#3fb950}
*{box-sizing:border-box;margin:0;padding:0}
body{font-family:Segoe UI,system-ui,sans-serif;background:var(--bg);color:var(--text)}
header{display:flex;align-items:center;justify-content:space-between;padding:12px 20px;border-bottom:1px solid var(--border);background:var(--panel);flex-wrap:wrap;gap:8px}
header h1{font-size:1.1rem;font-weight:600}
.badge{padding:4px 10px;border-radius:999px;font-size:.75rem;background:#238636;color:#fff}
.badge.err{background:#da3633}.badge.warn{background:#d29922}
.header-actions{display:flex;gap:8px;align-items:center;flex-wrap:wrap}
button.estop{background:#da3633;border-color:#da3633;color:#fff;font-weight:700}
.layout{display:grid;grid-template-columns:200px 1fr;min-height:calc(100vh-49px)}
nav{border-right:1px solid var(--border);padding:16px 0;background:var(--panel)}
nav a{display:block;padding:10px 20px;color:var(--muted);text-decoration:none;border-left:3px solid transparent;cursor:pointer}
nav a.active,nav a:hover{color:var(--text);background:#21262d;border-color:var(--accent)}
main{padding:16px;overflow-y:auto}
.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(220px,1fr));gap:12px}
.card{background:var(--panel);border:1px solid var(--border);border-radius:8px;padding:14px}
.card h3{font-size:.75rem;color:var(--muted);text-transform:uppercase;letter-spacing:.05em;margin-bottom:6px}
.big{font-size:1.8rem;font-weight:700}
.row{display:flex;gap:6px;flex-wrap:wrap;margin-top:8px;align-items:center}
.row.nowrap{flex-wrap:nowrap}
button,.btn{background:#21262d;border:1px solid var(--border);color:var(--text);padding:7px 12px;border-radius:6px;cursor:pointer;font-size:.82rem;white-space:nowrap}
button:hover{filter:brightness(1.2)}button.primary{background:var(--accent);border-color:var(--accent);color:#0d1117;font-weight:600}button.danger{border-color:var(--hot);color:var(--hot)}button.sm{padding:4px 8px;font-size:.75rem}
input,textarea,select{background:#0d1117;border:1px solid var(--border);color:var(--text);padding:7px 10px;border-radius:6px;font-family:Consolas,monospace;font-size:.82rem}
textarea{width:100%;min-height:80px;resize:vertical}input[type=number]{width:70px}input[type=range]{width:100%}
.bar{height:6px;background:#21262d;border-radius:3px;overflow:hidden;margin-top:6px}
.bar>i{display:block;height:100%;background:var(--accent);width:0;transition:width .3s}
.hidden{display:none!important}
.files-wrap{display:flex;flex-wrap:wrap;gap:12px}
.file-card{background:var(--panel);border:1px solid var(--border);border-radius:8px;padding:12px;width:220px;display:flex;flex-direction:column;gap:6px}
.file-card .thumb{width:100%;height:120px;object-fit:cover;border-radius:4px;background:#21262d}
.file-card .fname{font-size:.85rem;word-break:break-all;flex:1}
.file-card .fsize{color:var(--muted);font-size:.75rem}
footer{padding:8px 20px;color:var(--muted);font-size:.75rem;border-top:1px solid var(--border)}
@media(max-width:768px){.layout{grid-template-columns:1fr}nav{display:flex;overflow:auto;border-right:none;border-bottom:1px solid var(--border)}nav a{white-space:nowrap;border-left:none;border-bottom:3px solid transparent}}
</style></head>
<body>
<header><h1>Virtual Klipper</h1><div class=header-actions><span class=badge id=state>connecting...</span><button class=estop onclick=estop()>E-Stop</button><button onclick=fwrestart()>FW Restart</button></div></header>
<div class=layout>
<nav><a class=active data-tab=dash>Dashboard</a><a data-tab=control>Control</a><a data-tab=files>Files</a><a data-tab=console>Console</a></nav>
<main>
<section id=tab-dash>
<div class=grid>
<div class=card><h3>Nozzle</h3><div class=big><span id=ext-t>--</span><small>&deg;C</small></div><div class=muted>Target: <span id=ext-s>--</span>&deg;C</div></div>
<div class=card><h3>Bed</h3><div class=big><span id=bed-t>--</span><small>&deg;C</small></div><div class=muted>Target: <span id=bed-s>--</span>&deg;C</div></div>
<div class=card><h3>Fan</h3><div class=big><span id=fan-s>--</span><small>%</small></div></div>
<div class=card><h3>Position</h3><div class=big style=font-size:1.1rem><span id=pos>X-- Y-- Z--</span></div><div class=muted id=msg>&mdash;</div></div>
<div class=card><h3>Print</h3><div id=fname style=font-size:.85rem>&mdash;</div><div class=bar><i id=prog></i></div><div class=muted style=margin-top:6px><span id=ptime>0:00</span> &middot; <span id=pstate>standby</span></div><div class=row><button onclick=pause()>Pause</button><button onclick=resume()>Resume</button><button class=danger onclick=cancel()>Cancel</button></div></div>
<div class=card><h3>System</h3><div style=display:flex;gap:12px><div style=flex:1><div style=color:var(--muted);font-size:.7rem>RAM</div><div style=font-size:1.2rem;font-weight:700><span id=mem-heap>--</span><small>KB</small></div></div><div style=flex:1><div style=color:var(--muted);font-size:.7rem>Storage</div><div style=font-size:1.2rem;font-weight:700><span id=mem-stor>--</span><small>KB</small></div></div></div><div class=bar><i id=mem-bar style=width:0></i></div></div></div></section>
<section id=tab-control class=hidden>
<div class=grid>
<div class=card><h3>Temperatures</h3><div class=row nowrap><span style=font-size:.82rem>Nozzle</span><input id=ext-in type=number value=200><button onclick="gcode('M104 S'+$('ext-in').value)">Set</button><button class=sm onclick="gcode('M104 S0')">Off</button></div><div class=row nowrap><span style=font-size:.82rem>Bed</span><input id=bed-in type=number value=60><button onclick="gcode('M140 S'+$('bed-in').value)">Set</button><button class=sm onclick="gcode('M140 S0')">Off</button></div></div>
<div class=card><h3>Home</h3><div class=row><button onclick="gcode('G28')">Home All</button><button onclick="gcode('G28 X')">X</button><button onclick="gcode('G28 Y')">Y</button><button onclick="gcode('G28 Z')">Z</button></div></div>
<div class=card><h3>Move (mm)</h3><div class=row><button onclick="move(10,0,0)">X+10</button><button onclick="move(-10,0,0)">X-10</button><button onclick="move(0,10,0)">Y+10</button><button onclick="move(0,-10,0)">Y-10</button></div><div class=row><button onclick="move(0,0,1)">Z+1</button><button onclick="move(0,0,-1)">Z-1</button><button onclick="move(0,0,5)">Z+5</button><button onclick="move(0,0,-5)">Z-5</button></div></div>
<div class=card><h3>Extruder</h3><div class=row><button onclick="extrude(5)">Extr+5</button><button onclick="extrude(1)">+1</button><button onclick="extrude(-1)">-1</button><button onclick="extrude(-5)">Retr-5</button></div><div class=row style=margin-top:4px><input id=extrude-mm type=number value=10 style=width:50px><span style=font-size:.75rem;color:var(--muted)>mm</span><button onclick="extrude(+$('extrude-mm').value)">Extrude</button><button onclick="extrude(-$('extrude-mm').value)">Retract</button></div></div>
<div class=card><h3>Fan</h3><div class=row nowrap><input id=fan-val type=range min=0 max=255 value=0 oninput="$('fan-pct').textContent=Math.round(this.value/255*100)+'%'"><span id=fan-pct style=width:40px;text-align:right>0%</span></div><div class=row><button onclick="gcode('M106 S'+$('fan-val').value)">Set</button><button onclick=gcode('M107')>Off</button><button onclick="gcode('M106 S255')">100%</button></div></div>
<div class=card><h3>Speed / Flow</h3><div class=row nowrap><span style=font-size:.82rem;width:50px>Speed</span><input type=range min=50 max=200 value=100 oninput="$('spd-v').textContent=this.value+'%'"><span id=spd-v style=width:40px;text-align:right>100%</span></div><div class=row nowrap style=margin-top:4px><span style=font-size:.82rem;width:50px>Flow</span><input type=range min=50 max=200 value=100 oninput="$('flw-v').textContent=this.value+'%'"><span id=flw-v style=width:40px;text-align:right>100%</span></div><div class=row><button onclick="gcode('M220 S'+$('spd-v').textContent.replace('%',''))">Speed</button><button onclick="gcode('M221 S'+$('flw-v').textContent.replace('%',''))">Flow</button><button onclick="gcode('M220 S100');gcode('M221 S100')">Reset</button></div></div>
<div class=card><h3>Tools</h3><div class=row><button onclick="gcode('M84')">Disable Steppers</button><button onclick="gcode('M18')">Disable All</button></div></div></div></section>
<section id=tab-files class=hidden>
<div class=card><h3>GCODE Files</h3>
<div id=upload-area style="border:2px dashed var(--border);border-radius:8px;padding:16px;text-align:center;margin-bottom:12px;cursor:pointer" onclick="$('file-input').click()"><p style=color:var(--muted)>Click to upload G-code file</p><input type=file id=file-input accept=.gcode,.gc style=display:none onchange="uploadFile(this)"></div>
<div id=files-list class=files-wrap></div></div></section>
<section id=tab-console class=hidden>
<div class=card><h3>G-Code Console</h3><textarea id=gcode-in placeholder="Enter G-code command..." style=margin-bottom:8px></textarea><div class=row><button class=primary onclick=sendGcode()>Send</button><button onclick="$('gcode-in').value=''">Clear</button></div></div></section>
</main></div>
<footer><span>Virtual Klipper &mdash; port 7125</span><span id=mem-info>--</span></footer>
<script>
function $(id){return document.getElementById(id)}
async function api(path,opts){const r=await fetch(path,opts);return r.json()}
function setBadge(t,c){const e=$('state');e.textContent=t;e.className='badge '+(c||'')}
async function gcode(c){if(!c||!c.trim())return;await api('/api/gcode',{method:'POST',body:JSON.stringify({script:c})});poll()}
function move(x,y,z){gcode('G91\\nG1 X'+x+' Y'+y+' Z'+z+' F3000\\nG90')}
function extrude(m){gcode('G91\\nG1 E'+m+' F300\\nG90')}
async function sendGcode(){await gcode($('gcode-in').value)}
async function estop(){await api('/api/estop',{method:'POST'});poll()}
async function fwrestart(){await api('/api/fwrestart',{method:'POST'});poll()}
async function pause(){await api('/api/print/pause',{method:'POST'});poll()}
async function resume(){await api('/api/print/resume',{method:'POST'});poll()}
async function cancel(){await api('/api/print/cancel',{method:'POST'});poll()}
async function poll(){try{const j=await api('/api/query');const s=j.status;const ps=s.print_stats.state||'standby';const wh=s.webhooks?s.webhooks.state:'ready';if(ps==='error'||wh==='shutdown')setBadge('error','err');else if(ps==='printing')setBadge('printing','');else if(ps==='paused')setBadge('paused','warn');else setBadge('ready','');$('ext-t').textContent=(s.extruder.temperature||0).toFixed(1);$('ext-s').textContent=(s.extruder.target||0).toFixed(0);$('bed-t').textContent=(s.heater_bed.temperature||0).toFixed(1);$('bed-s').textContent=(s.heater_bed.target||0).toFixed(0);$('fan-s').textContent=s.fan.speed!==undefined?Math.round(s.fan.speed*100):'--';const p=s.toolhead.position;$('pos').textContent='X'+(p[0]||0).toFixed(1)+' Y'+(p[1]||0).toFixed(1)+' Z'+(p[2]||0).toFixed(1);$('fname').textContent=s.print_stats.filename||'\u2014';$('pstate').textContent=s.print_stats.state;$('prog').style.width=((s.virtual_sdcard.progress||0)*100)+'%';$('msg').textContent=s.display_status.message||'';const sec=s.print_stats.print_duration||0;$('ptime').textContent=Math.floor(sec/60)+':'+String(sec%60).padStart(2,'0')}catch(e){setBadge('offline','warn')}}
async function loadFiles(){try{const r=await fetch('/api/files');const j=await r.json();const w=$('files-list');w.innerHTML='';for(const f of(j.result.files||[])){const c=document.createElement('div');c.className='file-card';c.innerHTML='<img class=thumb><div class=fname>'+f.filename+'</div><div class=fsize>'+(f.size/1024).toFixed(1)+' KB</div><div class=row><button class=primary onclick="startPrint(\''+f.filename+'\')">Print</button><button class="danger sm" onclick="deleteFile(\''+f.filename+'\')">Delete</button></div>';w.appendChild(c)}}catch(e){}}
async function startPrint(fn){await api('/api/print/start',{method:'POST',body:JSON.stringify({filename:fn})});poll()}
async function uploadFile(i){const f=i.files[0];if(!f)return;const fd=new FormData();fd.append('file',f);$('upload-area').style.borderColor='var(--ok)';await fetch('/upload',{method:'POST',body:fd});$('upload-area').style.borderColor='';i.value='';loadFiles()}
async function deleteFile(n){if(!confirm('Delete '+n+'?'))return;await fetch('/api/delete?filename='+encodeURIComponent(n));loadFiles()}
document.querySelectorAll('nav a').forEach(a=>a.onclick=e=>{document.querySelectorAll('nav a').forEach(x=>x.classList.remove('active'));a.classList.add('active');['dash','control','files','console'].forEach(t=>$('tab-'+t).classList.toggle('hidden',t!==a.dataset.tab));if(a.dataset.tab==='files')loadFiles()})
setInterval(poll,1000);poll()
async function loadMemInfo(){try{const r=await fetch('/api/system/info');const j=await r.json();const h=(j.free_heap/1024).toFixed(0);const s=(j.free_storage/1024).toFixed(0);const t=(j.total_storage/1024).toFixed(0);const u=((j.total_storage-j.free_storage)/j.total_storage*100).toFixed(0);$('mem-info').textContent='RAM '+h+'K Storage '+s+'K free';$('mem-heap').textContent=h;$('mem-stor').textContent=s;$('mem-total').textContent=t;$('mem-bar').style.width=u+'%'}catch(e){}}
setInterval(loadMemInfo,5000);loadMemInfo()
</script></body></html>"""

# ─── HTTP Handler ───────────────────────────────────────────────
class Handler(BaseHTTPRequestHandler):
    def do_GET(self):
        self._handle()
    def do_POST(self):
        self._handle()
    def do_OPTIONS(self):
        self.send_response(204)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.end_headers()

    def _handle(self):
        try:
            resp = self._route()
            if resp is None:
                self.send_response(404)
                self.send_header("Content-Type", "application/json")
                self.send_header("Access-Control-Allow-Origin", "*")
                self.end_headers()
                self.wfile.write(b'{"error":{"message":"Not found"}}')
            else:
                code, body, ctype = resp
                self.send_response(code)
                self.send_header("Content-Type", ctype)
                self.send_header("Access-Control-Allow-Origin", "*")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
        except Exception as e:
            self.send_response(500)
            self.send_header("Content-Type", "application/json")
            self.end_headers()
            self.wfile.write(json.dumps({"error": str(e)}).encode())

    def _route(self):
        m, p = self.command, self.path.split("?")[0]
        q = self.path.split("?")[1] if "?" in self.path else ""

        # Web UI
        if m == "GET" and p in ("/", "/index.html"):
            html = WEB_UI_HTML.encode()
            return (200, html, "text/html;charset=utf-8")

        # API endpoints
        if m == "GET" and p == "/api/query":
            return (200, json.dumps({"status": mcu.get_status(), "eventtime": round(time.time(), 3)}).encode(), "application/json")

        if m == "GET" and p == "/api/files":
            files = []
            for f in sorted(GCODES_DIR.iterdir()):
                if f.is_file() and f.suffix.lower() in (".gcode", ".gc"):
                    files.append({"filename": f.name, "size": f.stat().st_size})
            return (200, json.dumps({"result": {"files": files}}).encode(), "application/json")

        if m == "GET" and p == "/api/files/directory":
            path = self._get_query_param(q, "path", "gcodes")
            files = []
            for f in sorted(GCODES_DIR.iterdir()):
                if f.is_file() and f.suffix.lower() in (".gcode", ".gc"):
                    files.append({"filename": f.name, "size": f.stat().st_size, "modified": int(f.stat().st_mtime)})
            return (200, json.dumps({"result": {"dirs": [], "files": files}}).encode(), "application/json")

        if m == "GET" and p == "/api/files/metadata":
            fn = self._get_query_param(q, "filename")
            fpath = GCODES_DIR / fn
            size = fpath.stat().st_size if fpath.exists() else 0
            return (200, json.dumps({"result": {"size": size, "estimated_time": 3600}}).encode(), "application/json")

        if m == "GET" and p.startswith("/api/files/gcodes/"):
            rel = p[len("/api/files/gcodes/"):]
            fpath = GCODES_DIR / rel
            if not fpath.exists() or not fpath.is_file():
                return None
            data = fpath.read_bytes()
            return (200, data, mimetypes.guess_type(str(fpath))[0] or "application/octet-stream")

        if m == "GET" and p == "/api/thumbnail":
            fn = self._get_query_param(q, "filename")
            fpath = GCODES_DIR / fn
            if not fpath.exists():
                return (404, b"", "text/plain")
            b64 = self._extract_thumbnail(str(fpath), int(self._get_query_param(q, "size", "48")))
            return (200, b64.encode(), "text/plain")

        if m == "GET" and p == "/api/delete":
            fn = self._get_query_param(q, "filename")
            fpath = GCODES_DIR / fn
            ok = fpath.exists() and fpath.is_file()
            if ok: fpath.unlink()
            return (200, json.dumps({"ok": ok}).encode(), "application/json")

        if m == "GET" and p == "/api/system/info":
            free_stor = 0; total_stor = 0
            try:
                du = GCODES_DIR.stat()
                total_stor = du.st_size if hasattr(du, 'st_size') else 0
                free_stor = 0
            except: pass
            return (200, json.dumps({"free_heap": 0, "free_storage": free_stor, "total_storage": total_stor}).encode(), "application/json")

        if m == "POST" and p == "/api/gcode":
            body = self._body()
            try: script = json.loads(body).get("script", body)
            except: script = body
            if script and script.strip():
                cmd_history.add_custom("WEB", script.strip())
                mcu.execute_gcode(script.strip())
            return (200, json.dumps({"ok": True}).encode(), "application/json")

        if m == "POST" and p == "/api/print/start":
            try: body = json.loads(self._body())
            except: body = {}
            fn = body.get("filename", "")
            if fn: cmd_history.add_print_start(fn)
            mcu.start_print(fn)
            return (200, json.dumps({"ok": True}).encode(), "application/json")

        if m == "POST" and p == "/api/print/pause":
            cmd_history.add("> PAUSE"); mcu.pause_print()
            return (200, json.dumps({"ok": True}).encode(), "application/json")

        if m == "POST" and p == "/api/print/resume":
            cmd_history.add("> RESUME"); mcu.resume_print()
            return (200, json.dumps({"ok": True}).encode(), "application/json")

        if m == "POST" and p == "/api/print/cancel":
            cmd_history.add("> CANCEL"); mcu.cancel_print()
            return (200, json.dumps({"ok": True}).encode(), "application/json")

        if m == "POST" and p == "/api/home":
            cmd_history.add_custom("WEB", "G28"); mcu.execute_gcode("G28")
            return (200, json.dumps({"ok": True}).encode(), "application/json")

        if m == "POST" and p.startswith("/api/home/"):
            axis = p[-1].upper()
            if axis in "XYZ": mcu.execute_gcode(f"G28 {axis}")
            return (200, json.dumps({"ok": True}).encode(), "application/json")

        if m == "POST" and p == "/api/estop":
            cmd_history.add("> EMERGENCY STOP"); mcu.emergency_stop()
            return (200, json.dumps({"ok": True}).encode(), "application/json")

        if m == "POST" and p == "/api/fwrestart":
            cmd_history.add("> FIRMWARE RESTART"); mcu.firmware_restart()
            return (200, json.dumps({"ok": True}).encode(), "application/json")

        if m == "POST" and p == "/api/move":
            try: body = json.loads(self._body())
            except: body = {}
            x = body.get("x", 0); y = body.get("y", 0); z = body.get("z", 0); f = body.get("feedrate", 3000)
            script = f"G91\nG1 X{x} Y{y} Z{z} F{f}\nG90"
            cmd_history.add_custom("WEB", script); mcu.execute_gcode(script)
            return (200, json.dumps({"ok": True}).encode(), "application/json")

        if m == "POST" and p == "/upload":
            return self._handle_upload()

        # Moonraker REST
        if m == "GET" and p == "/server/info":
            return (200, json.dumps({"result": {"klippy_connected": True, "klippy_state": "ready",
                "components": ["database","file_manager","klippy_apis"], "failed_components": [],
                "registered_directories": ["gcodes","config"], "moonraker_version": MOONRAKER_VERSION,
                "api_version": [1,4,0], "api_version_string": "1.4.0"}}).encode(), "application/json")

        if m == "GET" and p == "/printer/info":
            return (200, json.dumps({"result": {"state": "ready", "state_message": mcu.message or "Printer is ready",
                "hostname": PRINTER_HOSTNAME, "klipper_path": "/virtual/klipper", "python_path": "/virtual/python",
                "process_id": 1, "software_version": KLIPPER_VERSION, "cpu_info": "Virtual Host"}}).encode(), "application/json")

        if m == "GET" and p == "/printer/objects/list":
            return (200, json.dumps({"result": ["extruder","heater_bed","fan","toolhead","print_stats","virtual_sdcard","display_status","webhooks"]}).encode(), "application/json")

        if m == "GET" and p == "/printer/objects/query":
            return (200, json.dumps({"result": {"status": mcu.get_status(), "eventtime": round(time.time(), 3)}}).encode(), "application/json")

        if m == "POST" and p == "/printer/gcode/script":
            try: body = json.loads(self._body())
            except: body = {}
            script = body.get("script", "")
            if script: cmd_history.add_custom("CYD", script); mcu.execute_gcode(script)
            return (200, json.dumps({"result": "ok"}).encode(), "application/json")

        if m == "POST" and p == "/printer/print/start":
            try: body = json.loads(self._body())
            except: body = {}
            fn = body.get("filename", "")
            if fn: cmd_history.add_print_start(fn)
            mcu.start_print(fn)
            return (200, json.dumps({"result": "ok"}).encode(), "application/json")

        if m == "POST" and p in ("/printer/print/pause",):
            cmd_history.add("> PAUSE"); mcu.pause_print()
            return (200, json.dumps({"result": "ok"}).encode(), "application/json")

        if m == "POST" and p in ("/printer/print/resume",):
            cmd_history.add("> RESUME"); mcu.resume_print()
            return (200, json.dumps({"result": "ok"}).encode(), "application/json")

        if m == "POST" and p in ("/printer/print/cancel",):
            cmd_history.add("> CANCEL"); mcu.cancel_print()
            return (200, json.dumps({"result": "ok"}).encode(), "application/json")

        if m == "POST" and p == "/printer/emergency_stop":
            cmd_history.add("> EMERGENCY STOP"); mcu.emergency_stop()
            return (200, json.dumps({"result": "ok"}).encode(), "application/json")

        if m == "POST" and p == "/printer/firmware_restart":
            cmd_history.add("> FIRMWARE RESTART"); mcu.firmware_restart()
            return (200, json.dumps({"result": "ok"}).encode(), "application/json")

        if m == "POST" and (p == "/server/jsonrpc" or p == "/api/jsonrpc"):
            return self._handle_jsonrpc()

        # WebSocket upgrade
        if self.headers.get("Upgrade", "").lower() == "websocket":
            return self._handle_ws_upgrade()

        return None

    def _handle_ws_upgrade(self):
        key = self.headers.get("Sec-WebSocket-Key", "")
        accept = ws_accept_key(key)
        self.send_response(101)
        self.send_header("Upgrade", "websocket")
        self.send_header("Connection", "Upgrade")
        self.send_header("Sec-WebSocket-Accept", accept)
        self.end_headers()
        # After upgrade, the rest of the connection is raw WebSocket frames
        # We need to handle this in the socket directly
        self._ws_loop()
        return None

    def _ws_loop(self):
        """Read WebSocket frames from the raw socket after upgrade."""
        sock = self.request
        sock.settimeout(120)
        buf = b""
        try:
            while True:
                try:
                    chunk = sock.recv(4096)
                except socket.timeout:
                    break
                except (ConnectionResetError, BrokenPipeError):
                    break
                if not chunk:
                    break
                buf += chunk
                while buf:
                    frame, buf = ws_decode_frame(buf)
                    if frame is None:
                        break
                    opcode, payload = frame
                    if opcode == 0x08:
                        try: sock.send(ws_encode_frame(b"", 0x08))
                        except: pass
                        return
                    elif opcode == 0x09:
                        try: sock.send(ws_encode_frame(payload, 0x0A))
                        except: pass
                    elif opcode == 0x01:
                        try:
                            msg = json.loads(payload.decode())
                            method = msg.get("method", "")
                            rid = msg.get("id", 0)
                            if method == "printer.objects.subscribe":
                                resp = json.dumps({"jsonrpc": "2.0", "id": rid,
                                    "result": {"status": mcu.get_status()}})
                                sock.send(ws_encode_frame(resp.encode()))
                        except json.JSONDecodeError:
                            pass
        except Exception:
            pass

    def _handle_upload(self):
        ct = self.headers.get("Content-Type", "")
        if "multipart/form-data" not in ct:
            return (400, json.dumps({"error": "Expected multipart/form-data"}).encode(), "application/json")
        boundary = ""
        for part in ct.split(";"):
            part = part.strip()
            if part.startswith("boundary="):
                boundary = part[9:].strip('"')
                break
        if not boundary:
            return (400, json.dumps({"error": "No boundary"}).encode(), "application/json")

        body = self._body().decode("latin-1")
        for part in body.split(f"--{boundary}"):
            if "Content-Disposition" not in part or "filename=" not in part:
                continue
            m = re.search(r'filename="([^"]*)"', part)
            if not m: continue
            filename = m.group(1)
            if not filename.lower().endswith((".gcode", ".gc")): continue
            bs = part.find("\r\n\r\n")
            file_data = part[bs + 4:]
            if file_data.endswith("\r\n"): file_data = file_data[:-2]
            (GCODES_DIR / filename).write_bytes(file_data.encode("latin-1"))
            return (200, json.dumps({"ok": True}).encode(), "application/json")
        return (400, json.dumps({"error": "No file found"}).encode(), "application/json")

    def _handle_jsonrpc(self):
        try: body = json.loads(self._body())
        except: return (200, json.dumps({"jsonrpc":"2.0","id":None,"error":{"code":-32700,"message":"Parse error"}}).encode(), "application/json")
        method = body.get("method", ""); rid = body.get("id", 0)
        def r(data): return (200, json.dumps({"jsonrpc":"2.0","id":rid,"result":data}).encode(), "application/json")
        if method == "server.info": return r({"klippy_connected":True,"klippy_state":"ready","moonraker_version":MOONRAKER_VERSION,"api_version":[1,4,0]})
        if method == "printer.info": return r({"state":"ready","state_message":mcu.message,"hostname":PRINTER_HOSTNAME,"software_version":KLIPPER_VERSION})
        if method in ("printer.objects.subscribe","printer.objects.query"): return r({"status": mcu.get_status()})
        if method in ("printer.gcode.script","machine.gcode.script"):
            script = body.get("params",{}).get("script","")
            if script: cmd_history.add_custom("CYD>",script); mcu.execute_gcode(script)
            return r("ok")
        if method in ("printer.print.start","machine.print.start"):
            fn = body.get("params",{}).get("filename","")
            if fn: cmd_history.add_print_start(fn)
            mcu.start_print(fn)
            return r("ok")
        if method in ("printer.print.pause","machine.print.pause"): cmd_history.add("> PAUSE"); mcu.pause_print(); return r("ok")
        if method in ("printer.print.resume","machine.print.resume"): cmd_history.add("> RESUME"); mcu.resume_print(); return r("ok")
        if method in ("printer.print.cancel","machine.print.cancel"): cmd_history.add("> CANCEL"); mcu.cancel_print(); return r("ok")
        if method in ("printer.emergency_stop","machine.emergency_stop"): cmd_history.add("> EMERGENCY STOP"); mcu.emergency_stop(); return r("ok")
        if method in ("printer.firmware_restart","machine.firmware_restart"): cmd_history.add("> FIRMWARE RESTART"); mcu.firmware_restart(); return r("ok")
        return (200, json.dumps({"jsonrpc":"2.0","id":rid,"error":{"code":-32601,"message":"Method not found"}}).encode(), "application/json")

    def _body(self):
        length = int(self.headers.get("Content-Length", 0))
        return self.rfile.read(length) if length > 0 else b""

    def _get_query_param(self, q: str, key: str, default=""):
        for part in q.split("&"):
            if "=" in part:
                k, v = part.split("=", 1)
                if k == key: return unquote_plus(v)
        return default

    def _extract_thumbnail(self, filepath: str, size: int) -> str:
        try:
            with open(filepath, "r", encoding="latin-1") as f:
                lines = [f.readline() for _ in range(500)]
            result = []; collecting = False
            for line in lines:
                line = line.strip()
                if line.startswith("; thumbnail begin"):
                    try: w = int(line.split("x")[0].split()[-1])
                    except: w = 0
                    collecting = (w == size)
                elif line.startswith("; thumbnail end"): collecting = False
                elif collecting and line.startswith("; "): result.append(line[2:])
            return "".join(result)
        except: return ""

    def log_message(self, format, *args):
        pass  # suppress default logging

class ThreadedServer(ThreadingMixIn, HTTPServer):
    allow_reuse_address = True
    daemon_threads = True

# ─── Main ───────────────────────────────────────────────────────
if __name__ == "__main__":
    print(f"\n{'='*50}")
    print(f"  Virtual Klipper")
    print(f"  Port: {PORT}")
    print(f"  Web UI: http://0.0.0.0:{PORT}")
    print(f"  G-codes: {GCODES_DIR.absolute()}")
    print(f"{'='*50}\n")

    server = ThreadedServer(("0.0.0.0", PORT), Handler)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n  Server stopped.")
        server.shutdown()
