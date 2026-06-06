#!/usr/bin/env python3
"""NAT32KLIPPER for Windows — Virtual Klipper + Moonraker + Web UI"""

import asyncio
import hashlib
import base64
import json
import struct
import time
import math
import os
import re
import mimetypes
from pathlib import Path
from collections import deque

# ─── Configuration ──────────────────────────────────────────────
HOST = "0.0.0.0"
PORT = int(os.environ.get("PORT", 7125))
GCODES_DIR = Path("gcodes")
GCODES_DIR.mkdir(exist_ok=True)
PRINTER_HOSTNAME = "win-virtual-klipper"
KLIPPER_VERSION = "v0.12.0-virtual"
MOONRAKER_VERSION = "v0.9.1-virtual"
STATUS_PUSH_MS = 0.5

# ─── WebSocket helpers ─────────────────────────────────────────
WS_MAGIC = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"

def ws_accept_key(key: str) -> str:
    return base64.b64encode(
        hashlib.sha1((key + WS_MAGIC).encode()).digest()
    ).decode()

def ws_encode_frame(data: bytes, opcode: int = 0x01) -> bytes:
    # opcode: 0x01=text, 0x08=close, 0x09=ping, 0x0A=pong
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

# ─── HTTP request/response ─────────────────────────────────────
class HttpRequest:
    def __init__(self, method: str, path: str, query: str, headers: dict, body: bytes):
        self.method = method
        self.path = path
        self.query = query
        self.headers = headers
        self.body = body

    @classmethod
    def parse(cls, raw: bytes):
        parts = raw.split(b"\r\n\r\n", 1)
        header_part = parts[0].decode("utf-8", errors="replace")
        body = parts[1] if len(parts) > 1 else b""

        lines = header_part.split("\r\n")
        first = lines[0].split(" ")
        method = first[0] if len(first) > 0 else "GET"
        full_path = first[1] if len(first) > 1 else "/"
        query = ""
        if "?" in full_path:
            full_path, query = full_path.split("?", 1)

        headers = {}
        for line in lines[1:]:
            if ":" in line:
                k, v = line.split(":", 1)
                headers[k.strip().lower()] = v.strip()

        # read full body if Content-Length
        cl = int(headers.get("content-length", 0))
        if cl > 0 and len(body) < cl:
            return None, raw  # need more data

        return cls(method, full_path, query, headers, body), b""

    def query_param(self, key: str, default="") -> str:
        for part in self.query.split("&"):
            if "=" in part:
                k, v = part.split("=", 1)
                if k == key:
                    from urllib.parse import unquote_plus
                    return unquote_plus(v)
        return default

def http_response(code: int, body: str = "", content_type: str = "application/json",
                  extra_headers: dict = None) -> bytes:
    status = {200: "OK", 204: "No Content", 400: "Bad Request",
              404: "Not Found", 500: "Internal Server Error", 101: "Switching Protocols"}
    msg = f"HTTP/1.1 {code} {status.get(code, 'Unknown')}\r\n"
    msg += f"Content-Type: {content_type}\r\n"
    msg += f"Content-Length: {len(body.encode())}\r\n"
    msg += "Access-Control-Allow-Origin: *\r\n"
    msg += "Access-Control-Allow-Methods: GET, POST, OPTIONS\r\n"
    msg += "Access-Control-Allow-Headers: Content-Type\r\n"
    msg += "Connection: close\r\n"
    if extra_headers:
        for k, v in extra_headers.items():
            msg += f"{k}: {v}\r\n"
    msg += "\r\n"
    return msg.encode() + (body.encode() if body else b"")

def http_ok(json_body: str) -> bytes:
    return http_response(200, json_body)

def http_404(msg: str = "Not found") -> bytes:
    return http_response(404, json.dumps({"error": {"message": msg}}))

# ─── Virtual MCU ────────────────────────────────────────────────
class VirtualMCU:
    def __init__(self):
        self.extruder_temp = 25.0
        self.extruder_target = 0.0
        self.bed_temp = 25.0
        self.bed_target = 0.0
        self.fan_speed = 0.0
        self.pos_x = 0.0
        self.pos_y = 0.0
        self.pos_z = 0.0
        self.pos_e = 0.0
        self.progress = 0.0
        self.print_duration = 0
        self.print_state = "standby"  # standby, printing, paused, complete, error
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
            parts = cmd.split()
            for p in parts[1:]:
                axis = p.upper()
                if axis == "X":
                    self.pos_x = 0.0
                elif axis == "Y":
                    self.pos_y = 0.0
                elif axis == "Z":
                    self.pos_z = 0.0
            self.message = f"Homed {' '.join(parts[1:])}"
        elif cmd == "G90":
            self._is_relative = False
        elif cmd == "G91":
            self._is_relative = True
        elif cmd.startswith("G0") or cmd.startswith("G1"):
            self._parse_move(cmd)
        elif cmd.startswith("M104"):
            m = re.search(r'S([\d.]+)', cmd)
            if m:
                self.extruder_target = float(m.group(1))
        elif cmd.startswith("M140"):
            m = re.search(r'S([\d.]+)', cmd)
            if m:
                self.bed_target = float(m.group(1))
        elif cmd.startswith("M106"):
            m = re.search(r'S([\d.]+)', cmd)
            self.fan_speed = min(1.0, (float(m.group(1)) if m else 255) / 255.0)
        elif cmd == "M107":
            self.fan_speed = 0.0
        elif cmd.startswith("M220"):
            m = re.search(r'S([\d.]+)', cmd)
            if m:
                pass  # Speed factor - tracking optional
        elif cmd.startswith("M221"):
            m = re.search(r'S([\d.]+)', cmd)
            if m:
                pass  # Flow factor - tracking optional
        elif cmd == "M84" or cmd == "M18":
            self.message = "Steppers disabled"
        elif cmd == "M80":
            self.message = "Power toggled"
        elif cmd.startswith("M117"):
            self.message = cmd[4:].strip()
        elif cmd == "M112":
            self.emergency_stop()
        elif cmd == "M1120":
            self.firmware_restart()
        elif cmd.startswith("G92"):
            self._parse_g92(cmd)

    def _parse_move(self, cmd: str):
        x = y = z = e = None
        f = None
        for match in re.finditer(r'([XYZEF])(-?[\d.]+)', cmd, re.IGNORECASE):
            axis, val = match.group(1).upper(), float(match.group(2))
            if axis == 'X':
                x = val
            elif axis == 'Y':
                y = val
            elif axis == 'Z':
                z = val
            elif axis == 'E':
                e = val
            elif axis == 'F':
                f = val
        if self._is_relative:
            if x is not None:
                self.pos_x += x
            if y is not None:
                self.pos_y += y
            if z is not None:
                self.pos_z += z
            if e is not None:
                self.pos_e += e
        else:
            if x is not None:
                self.pos_x = x
            if y is not None:
                self.pos_y = y
            if z is not None:
                self.pos_z = z
            if e is not None:
                self.pos_e = e

    def _parse_g92(self, cmd: str):
        for match in re.finditer(r'([XYZEF])(-?[\d.]+)', cmd, re.IGNORECASE):
            axis, val = match.group(1).upper(), float(match.group(2))
            if axis == 'X':
                self.pos_x = val
            elif axis == 'Y':
                self.pos_y = val
            elif axis == 'Z':
                self.pos_z = val
            elif axis == 'E':
                self.pos_e = val

    def start_print(self, filename: str):
        self.filename = filename
        self.progress = 0.0
        self.print_duration = 0
        self.print_state = "printing"
        self._print_start_ms = time.time()
        self._paused_accum = 0.0

    def pause_print(self):
        if self.print_state == "printing":
            self.print_state = "paused"
            self._pause_start = time.time()

    def resume_print(self):
        if self.print_state == "paused":
            self.print_state = "printing"
            self._paused_accum += time.time() - self._pause_start
            self._print_start_ms = time.time() - self._paused_accum

    def cancel_print(self):
        self.print_state = "standby"
        self.progress = 0.0
        self.filename = ""

    def emergency_stop(self):
        self.print_state = "error"
        self.message = "EMERGENCY STOP"
        self.extruder_target = 0.0
        self.bed_target = 0.0
        self.klippy_ready = False

    def firmware_restart(self):
        self.__init__()

    def tick(self):
        now = time.time()
        dt = now - self._last_sim
        self._last_sim = now
        if dt > 1.0:
            dt = 0.1

        # Thermal simulation
        if self.extruder_target > 0:
            self.extruder_temp += (self.extruder_target - self.extruder_temp) * dt * 0.05
        else:
            self.extruder_temp += (25.0 - self.extruder_temp) * dt * 0.01

        if self.bed_target > 0:
            self.bed_temp += (self.bed_target - self.bed_temp) * dt * 0.03
        else:
            self.bed_temp += (25.0 - self.bed_temp) * dt * 0.005

        # Print simulation
        if self.print_state == "printing":
            elapsed = now - self._print_start_ms
            self.progress = min(1.0, elapsed / self._total_seconds)
            self.print_duration = int(elapsed)
            if self.progress >= 1.0:
                self.print_state = "complete"
                self.message = "Print complete"

        # Recover from error after 5s
        if not self.klippy_ready and self.print_state == "error":
            if now - getattr(self, '_error_start', now) > 5:
                self.klippy_ready = True

    def get_status(self) -> dict:
        return {
            "extruder": {"temperature": round(self.extruder_temp, 1),
                         "target": round(self.extruder_target, 1)},
            "heater_bed": {"temperature": round(self.bed_temp, 1),
                           "target": round(self.bed_target, 1)},
            "fan": {"speed": round(self.fan_speed, 3)},
            "toolhead": {"position": [round(self.pos_x, 1),
                                      round(self.pos_y, 1),
                                      round(self.pos_z, 1)]},
            "print_stats": {"filename": self.filename,
                            "print_duration": self.print_duration,
                            "state": self.print_state,
                            "message": self.message},
            "virtual_sdcard": {"progress": round(self.progress, 4)},
            "display_status": {"message": self.message},
            "webhooks": {"state": "ready" if self.klippy_ready else "shutdown"},
        }

# ─── Command History ────────────────────────────────────────────
class CmdHistory:
    def __init__(self, maxlen=14):
        self._items = deque(maxlen=maxlen)

    def add(self, cmd: str):
        self._items.append((time.time(), cmd))

    def add_custom(self, source: str, detail: str):
        sanitized = detail.replace("\n", " ").replace("\r", " ")
        self._items.append((time.time(), f"[{source}] {sanitized}"))

    def add_print_start(self, filename: str):
        self._items.append((time.time(), f"> PRINT START {filename}"))

    def get_all(self) -> list:
        return list(self._items)

cmd_history = CmdHistory()

# ─── Moonraker Server ──────────────────────────────────────────
WEB_UI_HTML = None  # loaded from file or embedded

class MoonrakerServer:
    def __init__(self, mcu: VirtualMCU):
        self.mcu = mcu
        self._ws_clients: set[asyncio.Queue] = set()
        self._request_queue = asyncio.Queue()
        self._html = ""

    async def handle_client(self, reader: asyncio.StreamReader, writer: asyncio.StreamWriter):
        try:
            data = b""
            while True:
                chunk = await asyncio.wait_for(reader.read(65536), timeout=300)
                if not chunk:
                    break
                data += chunk
                # Try to parse HTTP request
                if b"\r\n\r\n" in data:
                    req, rest = HttpRequest.parse(data)
                    if req is None:
                        continue  # need more data
                    if req.method == "GET" and req.headers.get("upgrade", "").lower() == "websocket":
                        await self._handle_websocket(writer, req)
                    else:
                        await self._handle_http(writer, req)
                    data = rest
                    if not data:
                        break
        except asyncio.TimeoutError:
            pass
        except (ConnectionResetError, BrokenPipeError):
            pass
        except Exception as e:
            print(f"[!] Client error: {e}")
        finally:
            try:
                writer.close()
            except Exception:
                pass

    async def _handle_http(self, writer: asyncio.StreamWriter, req: HttpRequest):
        # Avoid CORS preflight
        if req.method == "OPTIONS":
            writer.write(http_response(204))
            await writer.drain()
            return

        try:
            resp = self._route(req)
            writer.write(resp)
            await writer.drain()
        except Exception as e:
            print(f"[!] Route error: {e}")
            writer.write(http_response(500, json.dumps({"error": str(e)})))
            await writer.drain()

    def _route(self, req: HttpRequest) -> bytes:
        m, p = req.method, req.path

        # ── Web UI ──
        if m == "GET" and p in ("/", "/index.html"):
            return http_response(200, self._get_html(), "text/html;charset=utf-8")

        # ── API endpoints ──
        if m == "GET" and p == "/api/query":
            return http_ok(json.dumps({"status": self.mcu.get_status(),
                                       "eventtime": round(time.time(), 3)}))

        if m == "GET" and p == "/api/system/info":
            free_stor = 0
            total_stor = 0
            mem_rss = 0
            try:
                import psutil
                mem = psutil.virtual_memory()
                free_stor = psutil.disk_usage(str(GCODES_DIR)).free
                total_stor = psutil.disk_usage(str(GCODES_DIR)).total
                mem_rss = int(psutil.Process().memory_info().rss / 1024)
            except Exception:
                pass
            return http_ok(json.dumps({
                "free_heap": mem_rss,
                "free_storage": free_stor,
                "total_storage": total_stor,
            }))

        if m == "GET" and p == "/api/files":
            files = []
            for f in sorted(GCODES_DIR.iterdir()):
                if f.is_file() and f.suffix.lower() in (".gcode", ".gc"):
                    files.append({"filename": f.name, "size": f.stat().st_size})
            return http_ok(json.dumps({"result": {"files": files}}))

        if m == "GET" and p == "/api/files/directory":
            path = req.query_param("path", "gcodes")
            files = []
            for f in sorted(GCODES_DIR.iterdir()):
                if f.is_file() and f.suffix.lower() in (".gcode", ".gc"):
                    files.append({"filename": f.name, "size": f.stat().st_size,
                                  "modified": int(f.stat().st_mtime)})
            return http_ok(json.dumps({"result": {"dirs": [], "files": files}}))

        if m == "GET" and p.startswith("/api/files/gcodes/"):
            rel = p[len("/api/files/gcodes/"):]
            fpath = GCODES_DIR / rel
            if not fpath.exists() or not fpath.is_file():
                return http_404("File not found")
            data = fpath.read_bytes()
            ct, _ = mimetypes.guess_type(str(fpath))
            return http_response(200, data.decode("latin-1"),
                                 ct or "application/octet-stream")

        if m == "GET" and p == "/api/files/metadata":
            fn = req.query_param("filename")
            fpath = GCODES_DIR / fn
            size = fpath.stat().st_size if fpath.exists() else 0
            return http_ok(json.dumps({"result": {"size": size, "estimated_time": 3600}}))

        if m == "GET" and p == "/api/thumbnail":
            fn = req.query_param("filename")
            size = int(req.query_param("size", "48"))
            fpath = GCODES_DIR / fn
            if not fpath.exists():
                return http_response(404, "", "text/plain")
            b64 = self._extract_thumbnail(str(fpath), size)
            return http_response(200, b64, "text/plain")

        if m == "GET" and p == "/api/delete":
            fn = req.query_param("filename")
            fpath = GCODES_DIR / fn
            ok = fpath.exists() and fpath.is_file()
            if ok:
                fpath.unlink()
            return http_ok(json.dumps({"ok": ok}))

        if m == "POST" and p == "/api/gcode":
            try:
                body = req.body.decode() if req.body else "{}"
                data = json.loads(body)
                script = data.get("script", body)
            except json.JSONDecodeError:
                script = body
            if script and script.strip():
                cmd_history.add_custom("WEB", script.strip())
                self.mcu.execute_gcode(script.strip())
            return http_ok(json.dumps({"ok": True}))

        if m == "POST" and p == "/api/print/start":
            try:
                body = json.loads(req.body.decode() if req.body else "{}")
            except json.JSONDecodeError:
                body = {}
            fn = body.get("filename", "")
            if fn:
                cmd_history.add_print_start(fn)
            self.mcu.start_print(fn)
            return http_ok(json.dumps({"ok": True}))

        if m == "POST" and p in ("/api/print/pause",):
            cmd_history.add("> PAUSE")
            self.mcu.pause_print()
            return http_ok(json.dumps({"ok": True}))

        if m == "POST" and p in ("/api/print/resume",):
            cmd_history.add("> RESUME")
            self.mcu.resume_print()
            return http_ok(json.dumps({"ok": True}))

        if m == "POST" and p in ("/api/print/cancel",):
            cmd_history.add("> CANCEL")
            self.mcu.cancel_print()
            return http_ok(json.dumps({"ok": True}))

        if m == "POST" and p == "/api/home":
            cmd_history.add_custom("WEB", "G28")
            self.mcu.execute_gcode("G28")
            return http_ok(json.dumps({"ok": True}))

        if m == "POST" and p.startswith("/api/home/"):
            axis = p[-1].upper()
            if axis in "XYZ":
                self.mcu.execute_gcode(f"G28 {axis}")
                cmd_history.add_custom("WEB", f"G28 {axis}")
            return http_ok(json.dumps({"ok": True}))

        if m == "POST" and p == "/api/estop":
            cmd_history.add("> EMERGENCY STOP")
            self.mcu.emergency_stop()
            return http_ok(json.dumps({"ok": True}))

        if m == "POST" and p == "/api/fwrestart":
            cmd_history.add("> FIRMWARE RESTART")
            self.mcu.firmware_restart()
            return http_ok(json.dumps({"ok": True}))

        if m == "POST" and p == "/api/move":
            try:
                body = json.loads(req.body.decode() if req.body else "{}")
            except json.JSONDecodeError:
                body = {}
            x = body.get("x", 0)
            y = body.get("y", 0)
            z = body.get("z", 0)
            f = body.get("feedrate", 3000)
            script = f"G91\nG1 X{x} Y{y} Z{z} F{f}\nG90"
            cmd_history.add_custom("WEB", script)
            self.mcu.execute_gcode(script)
            return http_ok(json.dumps({"ok": True}))

        # ── Moonraker REST endpoints ──
        if m == "GET" and p == "/server/info":
            return http_ok(json.dumps({
                "result": {
                    "klippy_connected": True,
                    "klippy_state": "ready",
                    "components": ["database", "file_manager", "klippy_apis"],
                    "failed_components": [],
                    "registered_directories": ["gcodes", "config"],
                    "moonraker_version": MOONRAKER_VERSION,
                    "api_version": [1, 4, 0],
                    "api_version_string": "1.4.0", }}))

        if m == "GET" and p == "/printer/info":
            return http_ok(json.dumps({
                "result": {
                    "state": "ready",
                    "state_message": self.mcu.message or "Printer is ready",
                    "hostname": PRINTER_HOSTNAME,
                    "klipper_path": "/virtual/klipper",
                    "python_path": "/virtual/python",
                    "process_id": 1,
                    "software_version": KLIPPER_VERSION,
                    "cpu_info": "Windows Virtual Host", }}))

        if m == "GET" and p == "/printer/objects/list":
            return http_ok(json.dumps({
                "result": ["extruder", "heater_bed", "fan", "toolhead",
                           "print_stats", "virtual_sdcard", "display_status", "webhooks"]}))

        if m == "GET" and p == "/printer/objects/query":
            return http_ok(json.dumps({
                "result": {"status": self.mcu.get_status(),
                           "eventtime": round(time.time(), 3)}}))

        if m == "POST" and p == "/printer/gcode/script":
            try:
                body = json.loads(req.body.decode() if req.body else "{}")
            except json.JSONDecodeError:
                body = {}
            script = body.get("script", "")
            if script:
                cmd_history.add_custom("CYD", script)
                self.mcu.execute_gcode(script)
            return http_ok(json.dumps({"result": "ok"}))

        if m == "POST" and p == "/printer/print/start":
            try:
                body = json.loads(req.body.decode() if req.body else "{}")
            except json.JSONDecodeError:
                body = {}
            fn = body.get("filename", "")
            if fn:
                cmd_history.add_print_start(fn)
            self.mcu.start_print(fn)
            return http_ok(json.dumps({"result": "ok"}))

        if m == "POST" and p == "/printer/print/pause":
            cmd_history.add("> PAUSE")
            self.mcu.pause_print()
            return http_ok(json.dumps({"result": "ok"}))

        if m == "POST" and p == "/printer/print/resume":
            cmd_history.add("> RESUME")
            self.mcu.resume_print()
            return http_ok(json.dumps({"result": "ok"}))

        if m == "POST" and p == "/printer/print/cancel":
            cmd_history.add("> CANCEL")
            self.mcu.cancel_print()
            return http_ok(json.dumps({"result": "ok"}))

        if m == "POST" and p == "/printer/emergency_stop":
            cmd_history.add("> EMERGENCY STOP")
            self.mcu.emergency_stop()
            return http_ok(json.dumps({"result": "ok"}))

        if m == "POST" and p == "/printer/firmware_restart":
            cmd_history.add("> FIRMWARE RESTART")
            self.mcu.firmware_restart()
            return http_ok(json.dumps({"result": "ok"}))

        if m == "POST" and (p == "/server/jsonrpc" or p == "/api/jsonrpc"):
            return self._handle_jsonrpc(req)

        return http_404()

    def _handle_jsonrpc(self, req: HttpRequest) -> bytes:
        try:
            body = json.loads(req.body.decode() if req.body else "{}")
        except json.JSONDecodeError:
            return http_ok(json.dumps({"jsonrpc": "2.0", "id": None,
                                       "error": {"code": -32700, "message": "Parse error"}}))
        method = body.get("method", "")
        rid = body.get("id", 0)

        def result(data):
            return http_ok(json.dumps({"jsonrpc": "2.0", "id": rid, "result": data}))

        if method == "server.info":
            return result({"klippy_connected": True, "klippy_state": "ready",
                           "moonraker_version": MOONRAKER_VERSION, "api_version": [1, 4, 0]})
        if method == "printer.info":
            return result({"state": "ready", "state_message": self.mcu.message,
                           "hostname": PRINTER_HOSTNAME, "software_version": KLIPPER_VERSION})
        if method in ("printer.objects.subscribe", "printer.objects.query"):
            return result({"status": self.mcu.get_status()})
        if method in ("printer.gcode.script", "machine.gcode.script"):
            script = body.get("params", {}).get("script", "")
            if script:
                cmd_history.add_custom("CYD>", script)
                self.mcu.execute_gcode(script)
            return result("ok")
        if method in ("printer.print.start", "machine.print.start"):
            fn = body.get("params", {}).get("filename", "")
            if fn:
                cmd_history.add_print_start(fn)
            self.mcu.start_print(fn)
            return result("ok")
        if method in ("printer.print.pause", "machine.print.pause"):
            cmd_history.add("> PAUSE")
            self.mcu.pause_print()
            return result("ok")
        if method in ("printer.print.resume", "machine.print.resume"):
            cmd_history.add("> RESUME")
            self.mcu.resume_print()
            return result("ok")
        if method in ("printer.print.cancel", "machine.print.cancel"):
            cmd_history.add("> CANCEL")
            self.mcu.cancel_print()
            return result("ok")
        if method in ("printer.emergency_stop", "machine.emergency_stop"):
            cmd_history.add("> EMERGENCY STOP")
            self.mcu.emergency_stop()
            return result("ok")
        if method in ("printer.firmware_restart", "machine.firmware_restart"):
            cmd_history.add("> FIRMWARE RESTART")
            self.mcu.firmware_restart()
            return result("ok")

        return http_ok(json.dumps({"jsonrpc": "2.0", "id": rid,
                                   "error": {"code": -32601,
                                             "message": "Method not found"}}))

    async def _handle_websocket(self, writer: asyncio.StreamWriter, req: HttpRequest):
        key = req.headers.get("sec-websocket-key", "")
        accept = ws_accept_key(key)
        resp = ("HTTP/1.1 101 Switching Protocols\r\n"
                "Upgrade: websocket\r\n"
                "Connection: Upgrade\r\n"
                f"Sec-WebSocket-Accept: {accept}\r\n\r\n")
        writer.write(resp.encode())
        await writer.drain()

        queue = asyncio.Queue()
        self._ws_clients.add(queue)
        try:
            reader = asyncio.StreamReader()
            # We'll use the writer's underlying transport
            buf = b""
            while True:
                try:
                    chunk = await asyncio.wait_for(writer._transport._read_ready(), timeout=120)
                except asyncio.TimeoutError:
                    break
                except Exception:
                    break
                # Actually we can't read like this with StreamWriter
                # The WebSocket reading needs raw socket access
                # Let's use a different approach
                break
        finally:
            self._ws_clients.discard(queue)

    async def _push_status(self):
        while True:
            await asyncio.sleep(STATUS_PUSH_MS)
            status = json.dumps({
                "jsonrpc": "2.0",
                "method": "notify_status_update",
                "params": [self.mcu.get_status(), round(time.time(), 3)]
            })
            frame = ws_encode_frame(status.encode())
            dead = set()
            for q in self._ws_clients:
                try:
                    await q.put(frame)
                except Exception:
                    dead.add(q)
            self._ws_clients -= dead

    def set_html(self, html: str):
        self._html = html

    def _get_html(self) -> str:
        return self._html

    def _extract_thumbnail(self, filepath: str, size: int) -> str:
        try:
            with open(filepath, "r", encoding="latin-1") as f:
                lines = []
                for _ in range(500):
                    line = f.readline()
                    if not line:
                        break
                    lines.append(line)
            # Simple thumbnail extraction from gcode comments
            result = []
            collecting = False
            for line in lines:
                line = line.strip()
                if line.startswith("; thumbnail begin"):
                    w_str = line.split("x")[0].split()[-1]
                    try:
                        w = int(w_str)
                    except ValueError:
                        w = 0
                    collecting = (w == size)
                elif line.startswith("; thumbnail end"):
                    collecting = False
                elif collecting and line.startswith("; "):
                    result.append(line[2:])
            return "".join(result)
        except Exception:
            return ""


# ─── Upload handler ────────────────────────────────────────────
def handle_upload(req: HttpRequest) -> bytes:
    """Handle multipart file upload from the web UI."""
    ct = req.headers.get("content-type", "")
    if "multipart/form-data" not in ct:
        return http_response(400, json.dumps({"error": "Expected multipart/form-data"}))

    boundary = ""
    for part in ct.split(";"):
        part = part.strip()
        if part.startswith("boundary="):
            boundary = part[9:].strip('"')
            break
    if not boundary:
        return http_response(400, json.dumps({"error": "No boundary"}))

    body_str = req.body.decode("latin-1")
    parts = body_str.split(f"--{boundary}")
    for part in parts:
        if "Content-Disposition" not in part:
            continue
        if "filename=" not in part:
            continue
        # Extract filename
        m = re.search(r'filename="([^"]*)"', part)
        if not m:
            continue
        filename = m.group(1)
        if not filename.lower().endswith((".gcode", ".gc")):
            continue

        # Extract body after headers
        body_start = part.find("\r\n\r\n")
        file_data = part[body_start + 4:]
        if file_data.endswith("\r\n"):
            file_data = file_data[:-2]

        (GCODES_DIR / filename).write_bytes(file_data.encode("latin-1"))
        return http_ok(json.dumps({"ok": True}))

    return http_response(400, json.dumps({"error": "No file found"}))


# ─── Web UI HTML (embedded) ────────────────────────────────────
def get_web_ui_html() -> str:
    return r"""<!DOCTYPE html>
<html lang="ru">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Virtual Klipper (Windows)</title>
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
.layout{display:grid;grid-template-columns:200px 1fr}
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
footer{padding:8px 20px;color:var(--muted);font-size:.75rem;border-top:1px solid var(--border);position:fixed;bottom:0;width:100%;background:var(--panel)}
@media(max-width:768px){.layout{grid-template-columns:1fr}nav{display:flex;overflow:auto;border-right:none;border-bottom:1px solid var(--border)}nav a{white-space:nowrap;border-left:none;border-bottom:3px solid transparent};main{padding-bottom:60px}}
</style>
</head>
<body>
<header>
  <h1>Virtual Klipper · Windows</h1>
  <div class="header-actions">
    <span class="badge" id="state">connecting...</span>
    <button class="estop" onclick="estop()">E-Stop</button>
    <button onclick="fwrestart()">FW Restart</button>
  </div>
</header>
<div class="layout">
<nav>
  <a class="active" data-tab="dash">Dashboard</a>
  <a data-tab="control">Control</a>
  <a data-tab="files">Files</a>
  <a data-tab="console">Console</a>
</nav>
<main>
<section id="tab-dash">
  <div class="grid">
    <div class="card"><h3>Nozzle</h3><div class="big"><span id="ext-t">--</span><small>&deg;C</small></div><div class="muted">Target: <span id="ext-s">--</span>&deg;C</div></div>
    <div class="card"><h3>Bed</h3><div class="big"><span id="bed-t">--</span><small>&deg;C</small></div><div class="muted">Target: <span id="bed-s">--</span>&deg;C</div></div>
    <div class="card"><h3>Fan</h3><div class="big"><span id="fan-s">--</span><small>%</small></div></div>
    <div class="card"><h3>Position</h3><div class="big" style="font-size:1.1rem"><span id="pos">X-- Y-- Z--</span></div><div class="muted" id="msg">&mdash;</div></div>
    <div class="card"><h3>Print</h3><div id="fname" style="font-size:.85rem">&mdash;</div><div class="bar"><i id="prog"></i></div><div class="muted" style="margin-top:6px"><span id="ptime">0:00</span> &middot; <span id="pstate">standby</span></div>
      <div class="row"><button onclick="pause()">Pause</button><button onclick="resume()">Resume</button><button class="danger" onclick="cancel()">Cancel</button></div></div>
    <div class="card"><h3>System</h3>
      <div style="display:flex;gap:12px"><div style="flex:1"><div style="color:var(--muted);font-size:.7rem">RAM</div><div style="font-size:1.2rem;font-weight:700"><span id="mem-heap">--</span><small>KB</small></div></div><div style="flex:1"><div style="color:var(--muted);font-size:.7rem">Storage</div><div style="font-size:1.2rem;font-weight:700"><span id="mem-stor">--</span><small>KB</small></div></div></div>
      <div class="bar"><i id="mem-bar" style="width:0"></i></div></div>
  </div>
</section>
<section id="tab-control" class="hidden">
  <div class="grid">
    <div class="card"><h3>Temperatures</h3>
      <div class="row nowrap"><span style="font-size:.82rem">Nozzle</span><input id="ext-in" type="number" value="200"><button onclick="gcode('M104 S'+extIn())">Set</button><button class="sm" onclick="gcode('M104 S0')">Off</button></div>
      <div class="row nowrap"><span style="font-size:.82rem">Bed</span><input id="bed-in" type="number" value="60"><button onclick="gcode('M140 S'+bedIn())">Set</button><button class="sm" onclick="gcode('M140 S0')">Off</button></div>
    </div>
    <div class="card"><h3>Home</h3>
      <div class="row"><button onclick="gcode('G28')">Home All</button><button onclick="gcode('G28 X')">X</button><button onclick="gcode('G28 Y')">Y</button><button onclick="gcode('G28 Z')">Z</button></div>
    </div>
    <div class="card"><h3>Move (mm)</h3>
      <div class="row"><button onclick="move(10,0,0)">X+10</button><button onclick="move(-10,0,0)">X-10</button><button onclick="move(0,10,0)">Y+10</button><button onclick="move(0,-10,0)">Y-10</button></div>
      <div class="row"><button onclick="move(0,0,1)">Z+1</button><button onclick="move(0,0,-1)">Z-1</button><button onclick="move(0,0,5)">Z+5</button><button onclick="move(0,0,-5)">Z-5</button></div>
    </div>
    <div class="card"><h3>Extruder</h3>
      <div class="row"><button onclick="extrude(5)">Extr+5</button><button onclick="extrude(1)">+1</button><button onclick="extrude(-1)">-1</button><button onclick="extrude(-5)">Retr-5</button></div>
      <div class="row" style="margin-top:4px"><input id="extrude-mm" type="number" value="10" style="width:50px"><span style="font-size:.75rem;color:var(--muted)">mm</span><button onclick="extrude(+$('extrude-mm').value)">Extrude</button><button onclick="extrude(-$('extrude-mm').value)">Retract</button></div>
    </div>
    <div class="card"><h3>Fan</h3>
      <div class="row nowrap"><input id="fan-val" type="range" min="0" max="255" value="0" oninput="$('fan-pct').textContent=Math.round(this.value/255*100)+'%'"><span id="fan-pct" style="width:40px;text-align:right">0%</span></div>
      <div class="row"><button onclick="gcode('M106 S'+$('fan-val').value)">Set</button><button onclick="gcode('M107')">Off</button><button onclick="gcode('M106 S255')">100%</button></div>
    </div>
    <div class="card"><h3>Speed / Flow</h3>
      <div class="row nowrap"><span style="font-size:.82rem;width:50px">Speed</span><input type="range" min="50" max="200" value="100" oninput="$('spd-v').textContent=this.value+'%'"><span id="spd-v" style="width:40px;text-align:right">100%</span></div>
      <div class="row nowrap" style="margin-top:4px"><span style="font-size:.82rem;width:50px">Flow</span><input type="range" min="50" max="200" value="100" oninput="$('flw-v').textContent=this.value+'%'"><span id="flw-v" style="width:40px;text-align:right">100%</span></div>
      <div class="row"><button onclick="gcode('M220 S'+$('spd-v').textContent.replace('%',''))">Speed</button><button onclick="gcode('M221 S'+$('flw-v').textContent.replace('%',''))">Flow</button><button onclick="gcode('M220 S100');gcode('M221 S100')">Reset</button></div>
    </div>
    <div class="card"><h3>Tools</h3>
      <div class="row"><button onclick="gcode('M84')">Disable Steppers</button><button onclick="gcode('M18')">Disable All</button></div>
    </div>
  </div>
</section>
<section id="tab-files" class="hidden">
  <div class="card"><h3>GCODE Files</h3>
    <div id="upload-area" style="border:2px dashed var(--border);border-radius:8px;padding:16px;text-align:center;margin-bottom:12px;cursor:pointer" onclick="$('file-input').click()">
      <p style="color:var(--muted)">Click to upload G-code file</p>
      <input type="file" id="file-input" accept=".gcode,.gc" style="display:none" onchange="uploadFile(this)">
    </div>
    <div id="files-list" class="files-wrap"></div>
  </div>
</section>
<section id="tab-console" class="hidden">
  <div class="card"><h3>G-Code Console</h3>
    <textarea id="gcode-in" placeholder="Enter G-code command..." style="margin-bottom:8px"></textarea>
    <div class="row"><button class="primary" onclick="sendGcode()">Send</button><button onclick="$('gcode-in').value=''">Clear</button></div>
  </div>
</section>
</main></div>
<footer><span>Virtual Klipper for Windows &mdash; port 7125</span><span id="mem-info">--</span></footer>
<script>
function $(id){return document.getElementById(id)}
function extIn(){return $('ext-in').value}
function bedIn(){return $('bed-in').value}
async function api(path,opts){const r=await fetch(path,opts);return r.json();}
function setBadge(text,cls){const el=$('state');el.textContent=text;el.className='badge '+(cls||'');}
async function gcode(cmd){if(!cmd||!cmd.trim())return;await api('/api/gcode',{method:'POST',body:JSON.stringify({script:cmd})});poll();}
function move(dx,dy,dz){gcode(`G91\nG1 X${dx} Y${dy} Z${dz} F3000\nG90`);}
function extrude(mm){gcode(`G91\nG1 E${mm} F300\nG90`);}
async function sendGcode(){await gcode($('gcode-in').value);}
async function estop(){await api('/api/estop',{method:'POST'});poll();}
async function fwrestart(){await api('/api/fwrestart',{method:'POST'});poll();}
async function pause(){await api('/api/print/pause',{method:'POST'});poll();}
async function resume(){await api('/api/print/resume',{method:'POST'});poll();}
async function cancel(){await api('/api/print/cancel',{method:'POST'});poll();}
async function poll(){try{const j=await api('/api/query');const s=j.status;const ps=s.print_stats.state||'standby';const wh=s.webhooks?s.webhooks.state:'ready';if(ps==='error'||wh==='shutdown')setBadge('error','err');else if(ps==='printing')setBadge('printing','');else if(ps==='paused')setBadge('paused','warn');else setBadge('ready','');$('ext-t').textContent=(s.extruder.temperature||0).toFixed(1);$('ext-s').textContent=(s.extruder.target||0).toFixed(0);$('bed-t').textContent=(s.heater_bed.temperature||0).toFixed(1);$('bed-s').textContent=(s.heater_bed.target||0).toFixed(0);$('fan-s').textContent=s.fan.speed!==undefined?Math.round(s.fan.speed*100):'--';const p=s.toolhead.position;$('pos').textContent='X'+(p[0]||0).toFixed(1)+' Y'+(p[1]||0).toFixed(1)+' Z'+(p[2]||0).toFixed(1);$('fname').textContent=s.print_stats.filename||'\u2014';$('pstate').textContent=s.print_stats.state;$('prog').style.width=((s.virtual_sdcard.progress||0)*100)+'%';$('msg').textContent=s.display_status.message||'';const sec=s.print_stats.print_duration||0;$('ptime').textContent=Math.floor(sec/60)+':'+String(sec%60).padStart(2,'0');}catch(e){setBadge('offline','warn')}}
async function loadFiles(){try{const r=await fetch('/api/files');const j=await r.json();const wrap=$('files-list');wrap.innerHTML='';for(const f of(j.result.files||[])){const card=document.createElement('div');card.className='file-card';const img=document.createElement('img');img.className='thumb';card.appendChild(img);const name=document.createElement('div');name.className='fname';name.textContent=f.filename;card.appendChild(name);const sz=document.createElement('div');sz.className='fsize';sz.textContent=(f.size/1024).toFixed(1)+' KB';card.appendChild(sz);const btnRow=document.createElement('div');btnRow.className='row';const printBtn=document.createElement('button');printBtn.className='primary';printBtn.textContent='Print';printBtn.onclick=e=>{e.stopPropagation();startPrint(f.filename)};btnRow.appendChild(printBtn);const delBtn=document.createElement('button');delBtn.className='danger sm';delBtn.textContent='Delete';delBtn.onclick=e=>{e.stopPropagation();deleteFile(f.filename)};btnRow.appendChild(delBtn);card.appendChild(btnRow);wrap.appendChild(card);}}catch(e){}}
async function startPrint(fn){await api('/api/print/start',{method:'POST',body:JSON.stringify({filename:fn})});poll();}
async function uploadFile(input){const file=input.files[0];if(!file)return;const fd=new FormData();fd.append('file',file);const area=$('upload-area');area.style.borderColor='var(--ok)';await fetch('/upload',{method:'POST',body:fd});area.style.borderColor='';input.value='';loadFiles();}
async function deleteFile(name){if(!confirm('Delete '+name+'?'))return;await fetch('/api/delete?filename='+encodeURIComponent(name));loadFiles();}
document.querySelectorAll('nav a').forEach(a=>a.onclick=e=>{document.querySelectorAll('nav a').forEach(x=>x.classList.remove('active'));a.classList.add('active');['dash','control','files','console'].forEach(t=>$('tab-'+t).classList.toggle('hidden',t!==a.dataset.tab));if(a.dataset.tab==='files')loadFiles()});
setInterval(poll,1000);poll();
async function loadMemInfo(){try{const r=await fetch('/api/system/info');const j=await r.json();const h=(j.free_heap/1024).toFixed(0);const s=(j.free_storage/1024).toFixed(0);const t=(j.total_storage/1024).toFixed(0);const u=((j.total_storage-j.free_storage)/j.total_storage*100).toFixed(0);$('mem-info').textContent='RAM '+h+'K \u00b7 Storage '+s+'K free';$('mem-heap').textContent=h;$('mem-stor').textContent=s;$('mem-total').textContent=t;$('mem-bar').style.width=u+'%';}catch(e){}}
setInterval(loadMemInfo,5000);loadMemInfo();
</script>
</body>
</html>"""


# ─── Main ───────────────────────────────────────────────────────
async def main():
    print(f"\n{'='*50}")
    print(f"  Virtual Klipper for Windows")
    print(f"  Port: {PORT}")
    print(f"  Web UI: http://localhost:{PORT}")
    print(f"  Moonraker API: ws://localhost:{PORT}")
    print(f"  G-codes: {GCODES_DIR.absolute()}")
    print(f"{'='*50}\n")

    mcu = VirtualMCU()
    server = MoonrakerServer(mcu)
    server.set_html(get_web_ui_html())

    # Start status push task
    push_task = asyncio.create_task(server._push_status())

    async def client_connected(reader, writer):
        try:
            # Read the first chunk
            data = await asyncio.wait_for(reader.read(65536), timeout=30)
            if not data:
                writer.close()
                return

            raw = data
            # Keep reading until we have a complete HTTP request
            while True:
                req, rest = HttpRequest.parse(raw)
                if req is not None:
                    break  # full request parsed
                # Need more data
                chunk = await asyncio.wait_for(reader.read(4096), timeout=30)
                if not chunk:
                    break
                raw += chunk
                if len(raw) > 65536:
                    writer.close()
                    return

            if req is None:
                writer.close()
                return

            # Save rest for potential WebSocket
            raw_rest = rest

            # Handle WebSocket upgrade
            if req.headers.get("upgrade", "").lower() == "websocket":
                key = req.headers.get("sec-websocket-key", "")
                accept = ws_accept_key(key)
                resp = ("HTTP/1.1 101 Switching Protocols\r\n"
                        "Upgrade: websocket\r\n"
                        "Connection: Upgrade\r\n"
                        f"Sec-WebSocket-Accept: {accept}\r\n\r\n")
                writer.write(resp.encode())
                await writer.drain()

                # Handle WebSocket frames
                buf = raw_rest
                try:
                    while True:
                        chunk = await asyncio.wait_for(reader.read(4096), timeout=120)
                        if not chunk:
                            break
                        buf += chunk
                        while buf:
                            frame, buf = ws_decode_frame(buf)
                            if frame is None:
                                break
                            opcode, payload = frame
                            if opcode == 0x08:
                                writer.write(ws_encode_frame(b"", 0x08))
                                await writer.drain()
                                return
                            elif opcode == 0x09:
                                writer.write(ws_encode_frame(payload, 0x0A))
                                await writer.drain()
                            elif opcode == 0x01:
                                try:
                                    msg = json.loads(payload.decode())
                                    method = msg.get("method", "")
                                    rid = msg.get("id", 0)
                                    if method == "printer.objects.subscribe":
                                        resp_msg = json.dumps({
                                            "jsonrpc": "2.0", "id": rid,
                                            "result": {"status": mcu.get_status()}})
                                        writer.write(ws_encode_frame(resp_msg.encode()))
                                        await writer.drain()
                                except json.JSONDecodeError:
                                    pass
                except (asyncio.TimeoutError, ConnectionResetError, BrokenPipeError):
                    pass
                writer.close()
                return

            # Handle file upload
            if req.method == "POST" and req.path == "/upload":
                resp = handle_upload(req)
                writer.write(resp)
                await writer.drain()
                writer.close()
                return

            # Regular HTTP request - use the server router
            resp = server._route(req)
            writer.write(resp)
            await writer.drain()
        except (asyncio.TimeoutError, ConnectionResetError, BrokenPipeError, OSError):
            pass
        except Exception as e:
            print(f"[!] Client error: {e}")
        finally:
            try:
                writer.close()
            except Exception:
                pass

    server_instance = await asyncio.start_server(client_connected, HOST, PORT)

    async with server_instance:
        print(f"  Server running on http://{HOST}:{PORT}")
        print(f"  Press Ctrl+C to stop\n")
        await server_instance.serve_forever()


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        print("\n  Server stopped.")
