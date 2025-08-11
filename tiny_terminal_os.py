#!/usr/bin/env python3
"""
Tiny Terminal OS (T.T.OS)
------------------------
A playful, single-file, terminal-based "operating system" simulation with:
  • Custom virtual filesystem (TinyFS) persisted to a single image file
  • Simulated boot loader with menu (normal / safe / single-user)
  • Simulated kernel with a toy scheduler, processes, and syscalls
  • Interactive shell with common commands (ls, cd, cat, echo, ps, kill, cp, mv, rm, mkdir, rmdir, pwd, whoami, uptime, help, reboot, shutdown, edit, touch, time, env, export, mount, umount, fsck, format)

Run:
  python tiny_terminal_os.py            # boots with default disk image tinyfs.img
  python tiny_terminal_os.py --image mydisk.img

This is meant for learning and fun, not security-critical or production use.
"""
import argparse
import base64
import datetime as dt
import json
import os
import queue
import readline  # noqa: F401 (improves CLI UX on most systems)
import shlex
import signal
import sys
import threading
import time
from dataclasses import dataclass, field
from typing import Any, Dict, Generator, List, Optional, Tuple
import socket
import urllib.request
import urllib.parse
import tarfile
import io
import lzma  # ensure xz support is available for tarfile
import re
import tokenize
try:
    import curses  # full-screen TUI for kat
except Exception:
    curses = None
# -------------------- .deb Installer (toy) --------------------
class DebPackage:
    """
    Minimal .deb package reader/installer for TinyFS.
    Limitations:
      - Maintainer scripts (preinst/postinst/etc.) are ignored
      - No dependency resolution; just extracts data.tar.* into the FS
      - Symlinks are written as '<name>.symlink' text markers
    """
    def __init__(self, name: str, version: str, arch: str, description: str, data_name: str, data_bytes: bytes):
        self.name = name
        self.version = version
        self.arch = arch
        self.description = description
        self.data_name = data_name
        self.data_bytes = data_bytes

    @staticmethod
    def _parse_ar(blob: bytes) -> Dict[str, bytes]:
        # ar archive format: global header then file entries with 60-byte headers
        if not blob.startswith(b"!<arch>\n"):
            raise RuntimeError("not a .deb (ar) file")
        i = 8
        members: Dict[str, bytes] = {}
        n = len(blob)
        while i + 60 <= n:
            hdr = blob[i:i+60]; i += 60
            name = hdr[0:16].decode('utf-8', 'replace').strip()
            size_str = hdr[48:58].decode('utf-8', 'replace').strip() or '0'
            magic = hdr[58:60]
            try:
                size = int(size_str)
            except ValueError:
                size = 0
            if name.endswith('/'):
                name = name[:-1]
            data = blob[i:i+size]
            i += size
            if i % 2 == 1:
                i += 1  # ar entries are 2-byte aligned
            if magic != b"`\n":
                break
            members[name] = data
        return members

    @staticmethod
    def _parse_control(text: str) -> Dict[str, str]:
        fields: Dict[str, str] = {}
        cur: Optional[str] = None
        for line in text.splitlines():
            if not line.strip():
                cur = None
                continue
            if line.startswith((' ', '\t')) and cur:
                fields[cur] = fields.get(cur, '') + '\n' + line.strip()
            elif ':' in line:
                k, v = line.split(':', 1)
                fields[k.strip()] = v.strip()
                cur = k.strip()
        return fields

    @classmethod
    def load(cls, fs: 'TinyFS', path: str) -> 'DebPackage':
        blob = fs.read_file(path)
        members = cls._parse_ar(blob)
        # find control and data tar members
        control_name = None
        for cand in ("control.tar.xz", "control.tar.gz", "control.tar.bz2", "control.tar"):
            if cand in members:
                control_name = cand
                break
        data_name = None
        for cand in ("data.tar.xz", "data.tar.gz", "data.tar.bz2", "data.tar"):
            if cand in members:
                data_name = cand
                break
        if not data_name:
            raise RuntimeError(".deb missing data.tar.*")
        # read control fields
        name = "unknown"; version = ""; arch = ""; desc = ""
        if control_name:
            mode = 'r:*'
            if control_name.endswith('.xz'): mode = 'r:xz'
            elif control_name.endswith('.gz'): mode = 'r:gz'
            elif control_name.endswith('.bz2'): mode = 'r:bz2'
            tf = tarfile.open(fileobj=io.BytesIO(members[control_name]), mode=mode)
            try:
                control_member = None
                for m in tf.getmembers():
                    try:
                        base = os.path.basename(m.name)
                    except Exception:
                        base = m.name
                    if base == 'control' and m.isfile():
                        control_member = m
                        break
                if control_member is not None:
                    fobj = tf.extractfile(control_member)
                    if fobj is not None:
                        fields = cls._parse_control(fobj.read().decode('utf-8', 'ignore'))
                        name = fields.get('Package', name)
                        version = fields.get('Version', version)
                        arch = fields.get('Architecture', arch)
                        desc = fields.get('Description', desc)
                # If not found, silently continue; some packages may omit it (rare).
            finally:
                tf.close()
        return cls(name, version, arch, desc, data_name, members[data_name])

    @staticmethod
    def _safe_join(dest: str, member_name: str) -> str:
        # normalize tar member names and join under dest safely
        p = os.path.normpath('/' + member_name).lstrip('/')
        final = os.path.normpath(os.path.join(dest or '/', p))
        if not final.startswith('/'):
            final = '/' + final
        return final

    def extract_to_fs(self, fs: 'TinyFS', dest: str = "/") -> Dict[str, Any]:
        files = 0; dirs = 0; links = 0; paths: List[str] = []
        mode = 'r:*'
        if self.data_name.endswith('.xz'): mode = 'r:xz'
        elif self.data_name.endswith('.gz'): mode = 'r:gz'
        elif self.data_name.endswith('.bz2'): mode = 'r:bz2'
        with tarfile.open(fileobj=io.BytesIO(self.data_bytes), mode=mode) as tf:
            for m in tf.getmembers():
                target = self._safe_join(dest, m.name)
                if m.isdir():
                    try:
                        fs.mkdir(target)
                    except Exception:
                        # may already exist; ensure parents via private mkdirs
                        try:
                            fs._mkdirs(target)
                        except Exception:
                            pass
                    dirs += 1
                    paths.append(target + '/')
                elif m.isreg():
                    f = tf.extractfile(m)
                    data = f.read() if f else b''
                    fs.write_file(target, data, create_parents=True)
                    files += 1
                    paths.append(target)
                elif m.issym() or m.islnk():
                    # TinyFS has no symlinks; write a marker file
                    marker = (f"SYMLINK -> {m.linkname}\n").encode('utf-8')
                    fs.write_file(target + '.symlink', marker, create_parents=True)
                    links += 1
                    paths.append(target + '.symlink')
                else:
                    # skip devices/fifos
                    continue
        return {"files": files, "dirs": dirs, "links": links, "paths": paths}

# -------------------- Utilities --------------------
ISO = "%Y-%m-%dT%H:%M:%S"

def now_iso() -> str:
    # Use timezone-aware UTC (Python 3.12+: datetime.UTC; fallback for older versions)
    try:
        return dt.datetime.now(dt.UTC).strftime(ISO)
    except AttributeError:
        return dt.datetime.now(dt.timezone.utc).strftime(ISO)

class Colors:
    RESET = "\033[0m"
    DIM = "\033[2m"
    BOLD = "\033[1m"
    GREEN = "\033[32m"
    CYAN = "\033[36m"
    YELLOW = "\033[33m"
    RED = "\033[31m"
    MAGENTA = "\033[35m"

# -------------------- TinyFS: custom virtual filesystem --------------------
class TinyFS:
    """
    Very simple FS persisted to a single image file.

    File format:
      [0:4]    magic bytes: TFS1
      [4: ]    utf-8 JSON document of the filesystem state:
                {
                  "next_inode": int,
                  "inodes": {
                    str(inode_id): {
                      "type": "file"|"dir",
                      "name": str,
                      "parent": Optional[int],
                      "children": {name: inode_id}  # for dirs
                      "data": base64str              # for files
                      "ctime": iso,
                      "mtime": iso
                    }, ...
                  },
                  "root": 1
                }
    This is intentionally simple and educational (not efficient).
    """

    MAGIC = b"TFS1"

    def __init__(self, image_path: str, read_only: bool = False):
        self.image_path = image_path
        self.read_only = read_only
        self.mounted = False
        self.fs: Dict[str, Any] = {}
        self.cwd_inode = 1  # root by default once mounted
        self.lock = threading.RLock()

    # ---------- Low-level helpers ----------
    def _new_inode(self, type_: str, name: str, parent: Optional[int]) -> int:
        inode = self.fs["next_inode"]
        self.fs["next_inode"] += 1
        self.fs["inodes"][str(inode)] = {
            "type": type_,
            "name": name,
            "parent": parent,
            "children": {} if type_ == "dir" else None,
            "data": "" if type_ == "file" else None,
            "ctime": now_iso(),
            "mtime": now_iso(),
        }
        if parent is not None:
            p = self.fs["inodes"][str(parent)]
            if p["type"] != "dir":
                raise RuntimeError("parent not dir")
        return inode

    def _inode(self, inode_id: int) -> Dict[str, Any]:
        return self.fs["inodes"][str(inode_id)]

    def _resolve(self, path: str) -> int:
        if not path:
            return self.cwd_inode
        if path.startswith("/"):
            cur = self.fs["root"]
            parts = [p for p in path.split("/") if p]
        else:
            cur = self.cwd_inode
            parts = [p for p in path.split("/") if p]
        for part in parts:
            if part == ".":
                continue
            if part == "..":
                cur = self._inode(cur)["parent"] or self.fs["root"]
                continue
            node = self._inode(cur)
            if node["type"] != "dir":
                raise FileNotFoundError(f"Not a directory: {part}")
            children = node["children"]
            if part not in children:
                raise FileNotFoundError(path)
            cur = children[part]
        return cur

    def _ensure_writable(self):
        if self.read_only:
            raise PermissionError("filesystem is read-only (safe mode)")

    # ---------- Public API ----------
    def format(self):
        with self.lock:
            self.fs = {
                "next_inode": 1,
                "inodes": {},
                "root": 1,
            }
            root = self._new_inode("dir", name="/", parent=None)
            assert root == 1
            # seed a /boot and /etc and /home
            boot = self._new_inode("dir", name="boot", parent=root)
            self.fs["inodes"]["1"]["children"]["boot"] = boot
            etc = self._new_inode("dir", name="etc", parent=root)
            self.fs["inodes"]["1"]["children"]["etc"] = etc
            home = self._new_inode("dir", name="home", parent=root)
            self.fs["inodes"]["1"]["children"]["home"] = home
            user = self._new_inode("dir", name="guest", parent=home)
            self.fs["inodes"][str(home)]["children"]["guest"] = user

            # add /bin and /usr/bin
            bin_dir = self._new_inode("dir", name="bin", parent=root)
            self.fs["inodes"]["1"]["children"]["bin"] = bin_dir
            usr_dir = self._new_inode("dir", name="usr", parent=root)
            self.fs["inodes"]["1"]["children"]["usr"] = usr_dir
            usr_bin = self._new_inode("dir", name="bin", parent=usr_dir)
            self.fs["inodes"][str(usr_dir)]["children"]["bin"] = usr_bin

            # demo programs
            self.write_file("/bin/hello", (
                "#!ttsh\n"
                "echo Hello from /bin/hello\n"
            ).encode("utf-8"), create_parents=True)

            # default boot rc script (run on boot if present)
            self.write_file("/boot/rc.ttsh", (
                "#!ttsh\n"
                "echo [rc] system booting...\n"
            ).encode("utf-8"), create_parents=True)

            # default boot.cfg
            self.write_file("/boot/boot.cfg", (
                "# Tiny Terminal OS boot config\n"
                "DEFAULT=normal\n"
                "TIMEOUT=2\n"
                "KERNEL_ARGS=quiet loglevel=1\n"
            ).encode("utf-8"))

            # MOTD
            self.write_file("/etc/motd", (
                "Welcome to Tiny Terminal OS!\n"
                "Type 'help' to see available commands.\n"
            ).encode("utf-8"))

            # default apt sources
            try:
                sources = {
                    "repos": [
                        {"name": "local", "index": "/var/cache/ttos/repo/index.json"}
                    ]
                }
                self.write_file(
                    "/etc/apt/sources.json",
                    (json.dumps(sources, indent=2) + "\n").encode("utf-8"),
                    create_parents=True,
                )
            except Exception:
                pass

            # ensure default repo and apt cache directories + empty index
            try:
                self._mkdirs("/var/cache/ttos/repo")
                self._mkdirs("/var/cache/ttos/apt/sources")
                self._mkdirs("/var/cache/ttos/apt/archives")
                if not self.exists("/var/cache/ttos/repo/index.json"):
                    self.write_file("/var/cache/ttos/repo/index.json", b"{\"packages\": {}}\n", create_parents=True)
            except Exception:
                pass

            self.save()

    def save(self):
        with self.lock:
            if not self.mounted:
                return
            if self.read_only:
                return
            data = json.dumps(self.fs).encode("utf-8")
            blob = self.MAGIC + data
            with open(self.image_path, "wb") as f:
                f.write(blob)

    def mount(self, create_if_missing: bool = True):
        with self.lock:
            if not os.path.exists(self.image_path):
                if not create_if_missing:
                    raise FileNotFoundError(self.image_path)
                self.mounted = True
                print(Colors.DIM + "[fs] creating new image at " + os.path.abspath(self.image_path) + Colors.RESET)
                self.format()
            else:
                with open(self.image_path, "rb") as f:
                    blob = f.read()
                if not blob.startswith(self.MAGIC):
                    raise RuntimeError("Invalid filesystem image")
                js = blob[len(self.MAGIC):]
                self.fs = json.loads(js.decode("utf-8"))
                self.mounted = True

    def umount(self):
        with self.lock:
            self.save()
            self.mounted = False

    def ls(self, path: str) -> List[Tuple[str, str]]:
        inode = self._resolve(path)
        node = self._inode(inode)
        if node["type"] != "dir":
            raise NotADirectoryError(path)
        out = []
        for name, child_id in sorted(node["children"].items()):
            child = self._inode(child_id)
            out.append((name, child["type"]))
        return out

    def mkdir(self, path: str):
        self._ensure_writable()
        parent_path, name = os.path.split(path.rstrip("/"))
        if not name:
            raise FileExistsError("missing name")
        parent = self._resolve(parent_path or "/")
        pnode = self._inode(parent)
        if pnode["type"] != "dir":
            raise NotADirectoryError(parent_path)
        if name in pnode["children"]:
            raise FileExistsError(path)
        inode = self._new_inode("dir", name, parent)
        pnode["children"][name] = inode
        pnode["mtime"] = now_iso()
        self.save()

    def rmdir(self, path: str):
        self._ensure_writable()
        inode = self._resolve(path)
        node = self._inode(inode)
        if node["type"] != "dir":
            raise NotADirectoryError(path)
        if node["children"]:
            raise OSError("directory not empty")
        parent = node["parent"]
        if parent is None:
            raise OSError("cannot remove root")
        pnode = self._inode(parent)
        del pnode["children"][node["name"]]
        del self.fs["inodes"][str(inode)]
        pnode["mtime"] = now_iso()
        self.save()

    def read_file(self, path: str) -> bytes:
        inode = self._resolve(path)
        node = self._inode(inode)
        if node["type"] != "file":
            raise IsADirectoryError(path)
        return base64.b64decode(node["data"].encode("ascii")) if node["data"] else b""

    def exists(self, path: str) -> bool:
        try:
            self._resolve(path)
            return True
        except Exception:
            return False

    def is_dir(self, path: str) -> bool:
        try:
            inode = self._resolve(path)
            return self._inode(inode)["type"] == "dir"
        except Exception:
            return False

    def is_file(self, path: str) -> bool:
        try:
            inode = self._resolve(path)
            return self._inode(inode)["type"] == "file"
        except Exception:
            return False

    def write_file(self, path: str, data: bytes, create_parents: bool = False):
        self._ensure_writable()
        parent_path, name = os.path.split(path)
        parent_path = parent_path or "/"
        try:
            parent = self._resolve(parent_path)
        except FileNotFoundError:
            if create_parents:
                self._mkdirs(parent_path)
                parent = self._resolve(parent_path)
            else:
                raise
        pnode = self._inode(parent)
        if pnode["type"] != "dir":
            raise NotADirectoryError(parent_path)
        if name in pnode["children"]:
            inode = pnode["children"][name]
            node = self._inode(inode)
            if node["type"] != "file":
                raise IsADirectoryError(path)
        else:
            inode = self._new_inode("file", name, parent)
            pnode["children"][name] = inode
        node = self._inode(inode)
        node["data"] = base64.b64encode(data).decode("ascii")
        node["mtime"] = now_iso()
        pnode["mtime"] = now_iso()
        self.save()

    def _mkdirs(self, path: str):
        parts = [p for p in path.split("/") if p]
        cur = self.fs["root"]
        for part in parts:
            node = self._inode(cur)
            if part not in node["children"]:
                inode = self._new_inode("dir", part, cur)
                node["children"][part] = inode
                node["mtime"] = now_iso()
            cur = node["children"][part]

    def rm(self, path: str):
        self._ensure_writable()
        inode = self._resolve(path)
        node = self._inode(inode)
        if node["type"] != "file":
            raise IsADirectoryError(path)
        parent = node["parent"]
        pnode = self._inode(parent)
        del pnode["children"][node["name"]]
        del self.fs["inodes"][str(inode)]
        pnode["mtime"] = now_iso()
        self.save()

    def mv(self, src: str, dst: str):
        self._ensure_writable()
        sinode = self._resolve(src)
        s = self._inode(sinode)
        dparent_path, dname = os.path.split(dst.rstrip("/"))
        dparent = self._resolve(dparent_path or "/")
        dparent_node = self._inode(dparent)
        if dparent_node["type"] != "dir":
            raise NotADirectoryError(dparent_path)
        # disallow overwrite of non-empty dir
        if dname in dparent_node["children"]:
            raise FileExistsError(dst)
        # detach from old parent
        parent = s["parent"]
        self._inode(parent)["children"].pop(s["name"], None)
        # attach
        s["name"] = dname
        s["parent"] = dparent
        dparent_node["children"][dname] = sinode
        s["mtime"] = now_iso()
        dparent_node["mtime"] = now_iso()
        self.save()

    def cp(self, src: str, dst: str):
        self._ensure_writable()
        sinode = self._resolve(src)
        s = self._inode(sinode)
        if s["type"] == "dir":
            raise IsADirectoryError("cp does not support directories")
        data = base64.b64decode(s["data"]) if s["data"] else b""
        self.write_file(dst, data, create_parents=False)

    def cd(self, path: str):
        inode = self._resolve(path)
        node = self._inode(inode)
        if node["type"] != "dir":
            raise NotADirectoryError(path)
        self.cwd_inode = inode

    def pwd(self) -> str:
        # reconstruct from inode by walking to root
        cur = self.cwd_inode
        parts = []
        while True:
            node = self._inode(cur)
            if node["parent"] is None:
                break
            parts.append(node["name"])
            cur = node["parent"]
        return "/" + "/".join(reversed(parts))

    def fsck(self) -> List[str]:
        errs = []
        try:
            assert self.fs["root"] == 1
        except AssertionError:
            errs.append("root inode must be 1")
        # simple invariants
        for k, v in self.fs["inodes"].items():
            if v["type"] not in ("file", "dir"):
                errs.append(f"inode {k} invalid type")
            if v["type"] == "dir":
                if not isinstance(v.get("children"), dict):
                    errs.append(f"inode {k} dir children invalid")
            else:
                if not isinstance(v.get("data"), (str, type(None))):
                    errs.append(f"inode {k} file data invalid")
        return errs

 # -------------------- Network --------------------
class NetIf:
    def __init__(self):
        self.up: bool = False
        self.dns = ["system"]
        self.http_timeout: float = 10.0

    def ensure_up(self):
        if not self.up:
            raise RuntimeError("network is down (use 'net up')")

    def bring_up(self):
        self.up = True

    def bring_down(self):
        self.up = False

    def resolve(self, host: str) -> str:
        self.ensure_up()
        info = socket.getaddrinfo(host, None, proto=socket.IPPROTO_TCP)
        return info[0][4][0]

    def tcp_ping_stats(self, host: str, port: int = 443, count: int = 4, timeout: float = 2.0) -> Dict[str, Any]:
        self.ensure_up()
        rtts: List[Optional[float]] = []
        recv = 0
        for _ in range(count):
            s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            s.settimeout(timeout)
            t0 = time.perf_counter()
            try:
                s.connect((host, int(port)))
                rtt = (time.perf_counter() - t0) * 1000.0
                rtts.append(rtt)
                recv += 1
            except Exception:
                rtts.append(None)
            finally:
                try:
                    s.close()
                except Exception:
                    pass
        vals = [v for v in rtts if v is not None]
        stats: Dict[str, Any] = {
            "sent": count,
            "recv": recv,
            "loss": float((count - recv) * 100.0 / max(1, count)),
            "rtts": rtts,
        }
        if vals:
            stats.update({
                "min": min(vals),
                "avg": sum(vals) / len(vals),
                "max": max(vals),
            })
        return stats

    def http_get(self, url: str) -> Tuple[bytes, int, str]:
        self.ensure_up()
        req = urllib.request.Request(url, headers={"User-Agent": "TTOS/1.0"})
        with urllib.request.urlopen(req, timeout=self.http_timeout) as resp:
            data = resp.read()
            ct = resp.headers.get("Content-Type", "")
            status = getattr(resp, "status", 200)
            return data, status, ct

# -------------------- Kernel & Processes --------------------
@dataclass
class Process:
    pid: int
    name: str
    target: Generator
    state: str = "ready"  # ready | running | sleeping | stopped | zombie
    wake_at: float = 0.0
    exit_code: Optional[int] = None

class Kernel:
    def __init__(self, fs: TinyFS, args: Dict[str, str]):
        self.fs = fs
        self.args = args
        self.pid_ctr = 100
        self.procs: Dict[int, Process] = {}
        self.runq: queue.Queue[int] = queue.Queue()
        self.start_time = time.time()
        self.env: Dict[str, str] = {"USER": "guest", "SHELL": "/bin/ttsh", "PATH": "/bin:/usr/bin"}
        self.lock = threading.RLock()
        self._tick_thread: Optional[threading.Thread] = None
        self._running = False
        self.net = NetIf()

    # ---- process management ----
    def spawn(self, name: str, target: Generator) -> int:
        with self.lock:
            self.pid_ctr += 1
            pid = self.pid_ctr
            proc = Process(pid, name, target)
            self.procs[pid] = proc
            self.runq.put(pid)
            return pid

    def kill(self, pid: int, code: int = 0):
        with self.lock:
            if pid in self.procs:
                self.procs[pid].state = "stopped"
                self.procs[pid].exit_code = code

    def ps(self) -> List[Tuple[int, str, str]]:
        with self.lock:
            out = []
            for p in sorted(self.procs.values(), key=lambda x: x.pid):
                out.append((p.pid, p.name, p.state))
            return out

    def uptime(self) -> float:
        return time.time() - self.start_time

    # ---- scheduler ----
    def _tick(self):
        # very tiny round-robin with sleep handling
        while self._running:
            try:
                pid = self.runq.get(timeout=0.1)
            except queue.Empty:
                time.sleep(0.02)
                continue
            with self.lock:
                p = self.procs.get(pid)
                if not p or p.state in ("stopped", "zombie"):
                    continue
                if p.state == "sleeping":
                    if time.time() < p.wake_at:
                        # not ready yet, requeue and yield CPU
                        self.runq.put(pid)
                        time.sleep(0.01)
                        continue
                    else:
                        p.state = "ready"
                p.state = "running"
            # run one "timeslice"
            try:
                req = next(p.target)
                # cooperative contract: yield seconds to sleep or None
                if isinstance(req, (int, float)) and req > 0:
                    with self.lock:
                        p.state = "sleeping"
                        p.wake_at = time.time() + float(req)
                else:
                    with self.lock:
                        p.state = "ready"
                        self.runq.put(pid)
            except StopIteration:
                with self.lock:
                    p.state = "zombie"
                    p.exit_code = 0
            except Exception:
                with self.lock:
                    p.state = "zombie"
                    p.exit_code = 1
            time.sleep(0.001)

    def start(self):
        self._running = True
        self._tick_thread = threading.Thread(target=self._tick, name="scheduler", daemon=True)
        self._tick_thread.start()

    def stop(self):
        self._running = False
        if self._tick_thread and self._tick_thread.is_alive():
            self._tick_thread.join(timeout=0.5)

    # ---- syscalls (toy) ----
    def sys_sleep(self, secs: float):
        # used by generator-based processes
        yield max(0.0, secs)

    def sys_write_file(self, path: str, data: bytes):
        self.fs.write_file(path, data)

    def sys_read_file(self, path: str) -> bytes:
        return self.fs.read_file(path)

    # ---- network API ----
    def net_up(self):
        self.net.bring_up()

    def net_down(self):
        self.net.bring_down()

    def net_status(self) -> Dict[str, Any]:
        return {"up": self.net.up, "dns": self.net.dns, "timeout": self.net.http_timeout}

    def net_resolve(self, host: str) -> str:
        return self.net.resolve(host)

    def net_http_get(self, url: str) -> Tuple[bytes, int, str]:
        return self.net.http_get(url)

    def net_tcp_ping(self, host: str, port: int = 443, count: int = 4, timeout: float = 2.0) -> Dict[str, Any]:
        return self.net.tcp_ping_stats(host, port, count, timeout)

    def net_info(self) -> Dict[str, Any]:
        info: Dict[str, Any] = {
            "up": self.net.up,
            "dns": self.net.dns,
            "timeout": self.net.http_timeout,
            "hostname": "",
            "fqdn": "",
            "local_ipv4": [],
            "local_ipv6": [],
            "primary_ipv4": None,
            "primary_ipv6": None,
            "external_ipv4": None,
            "external_ipv6": None,
        }
        # basic host names
        try:
            info["hostname"] = socket.gethostname()
            info["fqdn"] = socket.getfqdn()
        except Exception:
            pass
        # gather local IPs via getaddrinfo(hostname)
        v4 = set(); v6 = set()
        try:
            for af, _stype, _proto, _canon, sa in socket.getaddrinfo(info["hostname"] or None, None):
                try:
                    ip = sa[0]
                except Exception:
                    continue
                if ":" in ip:
                    if ip != "::1":
                        v6.add(ip)
                else:
                    if ip != "127.0.0.1":
                        v4.add(ip)
        except Exception:
            pass
        info["local_ipv4"] = sorted(v4)
        info["local_ipv6"] = sorted(v6)
        # detect primary outbound IPv4/IPv6 via UDP connect trick (no packets actually sent)
        try:
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            s.connect(("8.8.8.8", 80))
            info["primary_ipv4"] = s.getsockname()[0]
            s.close()
        except Exception:
            pass
        try:
            s6 = socket.socket(socket.AF_INET6, socket.SOCK_DGRAM)
            s6.connect(("2001:4860:4860::8888", 80))
            info["primary_ipv6"] = s6.getsockname()[0]
            s6.close()
        except Exception:
            pass
        # external IPs (best effort) if network is up
        if self.net.up:
            try:
                data, status, _ = self.net.http_get("https://api.ipify.org?format=text")
                if status == 200:
                    info["external_ipv4"] = data.decode("utf-8", "ignore").strip()
            except Exception:
                pass
            try:
                data, status, _ = self.net.http_get("https://api64.ipify.org?format=text")
                if status == 200:
                    info["external_ipv6"] = data.decode("utf-8", "ignore").strip()
            except Exception:
                pass
        return info

# -------------------- Boot Loader --------------------
class BootLoader:
    def __init__(self, fs: TinyFS):
        self.fs = fs

    def _read_boot_cfg(self) -> Dict[str, str]:
        cfg = {"DEFAULT": "normal", "TIMEOUT": "2", "KERNEL_ARGS": "quiet"}
        try:
            content = self.fs.read_file("/boot/boot.cfg").decode("utf-8", "ignore")
            for line in content.splitlines():
                line = line.strip()
                if not line or line.startswith("#"):
                    continue
                if "=" in line:
                    k, v = line.split("=", 1)
                    cfg[k.strip().upper()] = v.strip()
        except Exception:
            pass
        return cfg

    def boot(self, mode: Optional[str] = None) -> Tuple['Kernel', str]:
        # Show boot menu / banner
        print(Colors.CYAN + "\nTINY TERMINAL OS BOOTLOADER" + Colors.RESET)
        print(Colors.DIM + "(c) 2025 Vertolini\n" + Colors.RESET)
        cfg = self._read_boot_cfg()
        default = (mode or cfg.get("DEFAULT", "normal")).lower()
        timeout = int(cfg.get("TIMEOUT", "2"))
        kernel_args = cfg.get("KERNEL_ARGS", "")

        options = [
            ("normal", "Standard boot (RW)"),
            ("safe", "Safe mode (RO FS, minimal services)"),
            ("single", "Single-user shell (RW)")
        ]
        print("Boot options:")
        for i, (key, desc) in enumerate(options, 1):
            sel = "(default)" if key == default else ""
            print(f"  {i}. {key:<6} - {desc} {sel}")
        # countdown
        for t in range(timeout, 0, -1):
            sys.stdout.write(f"Booting {default} in {t}...\r")
            sys.stdout.flush()
            time.sleep(1)
        print("\n")

        read_only = (default == "safe")
        if default not in {"normal", "safe", "single"}:
            default = "normal"

        # mount FS
        try:
            self.fs.mount(create_if_missing=True)
        except Exception as e:
            print(Colors.RED + f"FS mount failed: {e}" + Colors.RESET)
            print("Formatting a fresh filesystem image...")
            self.fs.format()
            self.fs.mount(create_if_missing=True)
        print(Colors.DIM + f"[boot] disk image: {os.path.abspath(self.fs.image_path)}" + Colors.RESET)

        # show banner / motd
        try:
            motd = self.fs.read_file("/etc/motd").decode()
            print(Colors.GREEN + motd + Colors.RESET)
        except Exception:
            pass

        # build kernel
        args = {a.split("=",1)[0]: a.split("=",1)[1] if "=" in a else "1" for a in kernel_args.split()}
        self.fs.read_only = read_only
        kernel = Kernel(self.fs, args)
        print(Colors.DIM + f"[boot] FS={'ro' if read_only else 'rw'} args={args}" + Colors.RESET)
        return kernel, default

# -------------------- Shell --------------------
class Shell:
    def __init__(self, kernel: Kernel):
        self.k = kernel
        self.fs = kernel.fs
        self.builtins = {
            "help": self.cmd_help,
            "ls": self.cmd_ls,
            "cd": self.cmd_cd,
            "pwd": self.cmd_pwd,
            "cat": self.cmd_cat,
            "echo": self.cmd_echo,
            "touch": self.cmd_touch,
            "rm": self.cmd_rm,
            "mkdir": self.cmd_mkdir,
            "rmdir": self.cmd_rmdir,
            "mv": self.cmd_mv,
            "cp": self.cmd_cp,
            "ps": self.cmd_ps,
            "kill": self.cmd_kill,
            "uptime": self.cmd_uptime,
            "whoami": self.cmd_whoami,
            "time": self.cmd_time,
            "clear": self.cmd_clear,
            "reboot": self.cmd_reboot,
            "shutdown": self.cmd_shutdown,
            "exit": self.cmd_exit,
            "quit": self.cmd_exit,
            "edit": self.cmd_edit,
            "kat": self.cmd_kat,
            "mount": self.cmd_mount,
            "umount": self.cmd_umount,
            "fsck": self.cmd_fsck,
            "format": self.cmd_format,
            "env": self.cmd_env,
            "export": self.cmd_export,
            "run": self.cmd_run,
            "about": self.cmd_about,
            "which": self.cmd_which,
            "source": self.cmd_source,
            "net": self.cmd_net,
            "ping": self.cmd_ping,
            "httpget": self.cmd_httpget,
            "dload": self.cmd_dload,
            "debinfo": self.cmd_debinfo,
            "debextract": self.cmd_debextract,
            "dpkg": self.cmd_dpkg,
            "apt": self.cmd_apt,
        }

    # ----- builtins -----
    def cmd_help(self, *args):
        print("Built-ins:")
        print("  help, ls, cd, pwd, cat, echo, touch, rm, mkdir, rmdir, mv, cp")
        print("  ps, kill, run, uptime, whoami, time, env, export, clear")
        print("  mount, umount, fsck, format, edit, kat, reboot, shutdown, exit, quit, about")
        print("Examples:")
        print("  echo 'hello' > /home/guest/hello.txt")
        print("  run cpu 3   # start CPU task for 3s in background")
        print("Network:")
        print("  net up | net down | net status")
        print("  net info  # show local/primary/external IPs")
        print("  ping example.com [port] [count]")
        print("  httpget https://example.com [/home/guest/out]")
        print("  dload URL [DEST]")
        print("Packages (.deb):")
        print("  debinfo /path/pkg.deb")
        print("  debextract /path/pkg.deb [DEST=/]")
        print("  dpkg -i /path/pkg.deb   # install (extracts data.tar.*)")
        print("APT:")
        print("  apt update")
        print("  apt search <query>")
        print("  apt install <name> [name...]")
        print("  apt remove <name>")
        print("  apt list --installed")
    # ----- apt helpers -----
    def _ensure_dir(self, path: str):
        try:
            if not self.fs.exists(path):
                self.fs.mkdir(path)
        except Exception:
            try:
                self.fs._mkdirs(path)
            except Exception:
                pass

    def _apt_cache_dir(self) -> str:
        base = "/var/cache/ttos/apt"
        self._ensure_dir("/var/cache/ttos")
        self._ensure_dir(base)
        self._ensure_dir(base + "/sources")
        self._ensure_dir(base + "/archives")
        return base

    def _apt_load_sources(self) -> Dict[str, Any]:
        try:
            data = self.fs.read_file("/etc/apt/sources.json").decode("utf-8", "ignore")
            obj = json.loads(data)
            if isinstance(obj, dict) and "repos" in obj:
                return obj
        except Exception:
            pass
        return {"repos": [{"name": "local", "index": "/var/cache/ttos/repo/index.json"}]}

    def _apt_parse_depends_expr(self, expr: Any) -> List[List[str]]:
        # Accept list-of-strings or a single string, convert to list of alt-groups
        if isinstance(expr, list):
            groups: List[List[str]] = []
            for item in expr:
                if isinstance(item, list):
                    groups.append([str(x).strip() for x in item if str(x).strip()])
                else:
                    # treat as a comma-separated or "a | b" string
                    groups.extend(self._apt_parse_depends_expr(str(item)))
            return groups
        s = str(expr or "").strip()
        if not s:
            return []
        groups: List[List[str]] = []
        for grp in s.split(","):
            alts = []
            for alt in grp.split("|"):
                name = alt.strip()
                name = re.sub(r"\(.*?\)", "", name).strip()
                name = re.sub(r"\[.*?\]", "", name).strip()
                name = name.split()[0] if name else ""
                if name:
                    alts.append(name)
            if alts:
                groups.append(alts)
        return groups

    def _apt_build_index_from_dir(self, repo_dir: str) -> Dict[str, Any]:
        idx: Dict[str, Any] = {"packages": {}}
        try:
            for fname, typ in self.fs.ls(repo_dir):
                if typ != "file" or not fname.endswith(".deb"):
                    continue
                p = f"{repo_dir}/{fname}"
                try:
                    blob = self.fs.read_file(p)
                    members = DebPackage._parse_ar(blob)
                    # locate control
                    control_name = None
                    for cand in ("control.tar.xz", "control.tar.gz", "control.tar.bz2", "control.tar"):
                        if cand in members:
                            control_name = cand
                            break
                    name = None; version = ""; desc = ""; arch = ""
                    deps: List[List[str]] = []
                    if control_name:
                        mode = 'r:*'
                        if control_name.endswith('.xz'): mode = 'r:xz'
                        elif control_name.endswith('.gz'): mode = 'r:gz'
                        elif control_name.endswith('.bz2'): mode = 'r:bz2'
                        tf = tarfile.open(fileobj=io.BytesIO(members[control_name]), mode=mode)
                        try:
                            control_member = None
                            for m in tf.getmembers():
                                try:
                                    base = os.path.basename(m.name)
                                except Exception:
                                    base = m.name
                                if base == 'control' and m.isfile():
                                    control_member = m
                                    break
                            if control_member is not None:
                                fobj = tf.extractfile(control_member)
                                if fobj is not None:
                                    fields = DebPackage._parse_control(fobj.read().decode('utf-8', 'ignore'))
                                    name = fields.get('Package')
                                    version = fields.get('Version', '')
                                    arch = fields.get('Architecture', '')
                                    desc = fields.get('Description', '')
                                    deps = self._apt_parse_depends_expr(fields.get('Depends', ''))
                        finally:
                            tf.close()
                    if name:
                        idx["packages"][name] = {
                            "version": version,
                            "path": p,
                            "depends": deps,
                            "arch": arch,
                            "desc": (desc.splitlines()[0] if desc else ""),
                        }
                except Exception:
                    continue
        except Exception:
            pass
        return idx

    def _apt_merge_index(self, acc: Dict[str, Any], add: Dict[str, Any]) -> Dict[str, Any]:
        if not acc:
            acc = {"packages": {}}
        if not add:
            return acc
        pkgs = add.get("packages") or {}
        for name, meta in pkgs.items():
            # Later repos override earlier ones
            acc.setdefault("packages", {})[name] = meta
        return acc

    def _apt_load_cached_index(self) -> Dict[str, Any]:
        try:
            cache = self._apt_cache_dir() + "/index.json"
            data = self.fs.read_file(cache).decode("utf-8", "ignore")
            obj = json.loads(data)
            if isinstance(obj, dict):
                return obj
        except Exception:
            pass
        return {"packages": {}}

    def _apt_list_installed(self) -> Dict[str, str]:
        res: Dict[str, str] = {}
        base = "/var/lib/ttos/dpkg"
        try:
            for name, typ in self.fs.ls(base):
                if typ != "dir":
                    continue
                ver = ""
                try:
                    txt = self.fs.read_file(f"{base}/{name}/manifest.txt").decode("utf-8", "ignore")
                    for line in txt.splitlines():
                        if line.startswith("Version:"):
                            ver = line.split(":", 1)[1].strip()
                            break
                except Exception:
                    pass
                if not ver:
                    try:
                        st = self.fs.read_file(f"{base}/{name}/status").decode("utf-8", "ignore")
                        if "installed" in st:
                            ver = st.strip().split()[-1]
                    except Exception:
                        pass
                res[name] = ver
        except Exception:
            pass
        return res

    def _apt_download_to_archives(self, name: str, meta: Dict[str, Any]) -> Optional[str]:
        archives = self._apt_cache_dir() + "/archives"
        ver = meta.get("version", "")
        fname = f"{name}_{ver}.deb" if ver else f"{name}.deb"
        dest = f"{archives}/{fname}"
        # If already present, reuse
        try:
            if self.fs.exists(dest) and self.fs.is_file(dest):
                return dest
        except Exception:
            pass
        # Source can be path or url
        if meta.get("path"):
            try:
                blob = self.fs.read_file(meta["path"])
                self.fs.write_file(dest, blob, create_parents=True)
                return dest
            except Exception as e:
                print(f"apt: cannot copy {meta['path']}: {e}")
                return None
        url = meta.get("url")
        if url:
            try:
                data, status, ctype = self.k.net_http_get(url)
                self.fs.write_file(dest, data, create_parents=True)
                return dest
            except Exception as e:
                print(f"apt: download failed for {name}: {e}")
                return None
        print(f"apt: no source (url/path) for {name}")
        return None

    def cmd_apt(self, *args):
        if not args:
            print("apt: commands: update | search <q> | install <name...> | remove <name> | list --installed")
            return
        sub = args[0]
        if sub == "update":
            sources = self._apt_load_sources().get("repos", [])
            cache_dir = self._apt_cache_dir()
            merged: Dict[str, Any] = {"packages": {}}
            for src in sources:
                name = src.get("name") or "src"
                index = src.get("index")
                dirpath = src.get("dir")
                idx_obj: Dict[str, Any] = {}
                if dirpath and self.fs.exists(dirpath):
                    idx_obj = self._apt_build_index_from_dir(dirpath)
                elif index:
                    if isinstance(index, str) and (index.startswith("http://") or index.startswith("https://")):
                        try:
                            data, status, _ = self.k.net_http_get(index)
                            idx_obj = json.loads(data.decode("utf-8", "ignore"))
                        except Exception as e:
                            print(f"apt: failed to fetch {index}: {e}")
                            continue
                    else:
                        try:
                            data = self.fs.read_file(index).decode("utf-8", "ignore")
                            idx_obj = json.loads(data)
                        except Exception as e:
                            # if it's a directory, attempt to build
                            try:
                                if self.fs.exists(index) and self.fs.is_dir(index):
                                    idx_obj = self._apt_build_index_from_dir(index)
                                else:
                                    # try parent directory of the index path
                                    parent = os.path.dirname(index) or "/"
                                    if self.fs.exists(parent) and self.fs.is_dir(parent):
                                        idx_obj = self._apt_build_index_from_dir(parent)
                                    else:
                                        # initialize empty repo index on first run
                                        try:
                                            self.fs.write_file(index, b"{\"packages\": {}}\n", create_parents=True)
                                            idx_obj = {"packages": {}}
                                        except Exception:
                                            idx_obj = None
                            except Exception:
                                idx_obj = None
                            if not idx_obj:
                                print(f"apt: cannot read index {index}: {e}")
                                continue
                merged = self._apt_merge_index(merged, idx_obj)
                # save per-source cache
                try:
                    self.fs.write_file(f"{cache_dir}/sources/{name}.json", (json.dumps(idx_obj, indent=2)+"\n").encode("utf-8"), create_parents=True)
                except Exception:
                    pass
            # save merged index
            self.fs.write_file(f"{cache_dir}/index.json", (json.dumps(merged, indent=2)+"\n").encode("utf-8"), create_parents=True)
            print(f"apt: package lists updated, {len(merged.get('packages', {}))} packages available")
            return
        elif sub == "search":
            if len(args) < 2:
                print("apt search: query")
                return
            q = args[1].lower()
            idx = self._apt_load_cached_index().get("packages", {})
            for name, meta in sorted(idx.items()):
                desc = meta.get("desc", "")
                if q in name.lower() or (desc and q in desc.lower()):
                    ver = meta.get("version", "")
                    print(f"{name} {ver} - {desc}")
            return
        elif sub == "list":
            if len(args) >= 2 and args[1] == "--installed":
                inst = self._apt_list_installed()
                for n, v in sorted(inst.items()):
                    print(f"{n}\t{v}")
                return
            print("apt list: only --installed supported")
            return
        elif sub == "install":
            if len(args) < 2:
                print("apt install: package name(s) required")
                return
            idx = self._apt_load_cached_index().get("packages", {})
            if not idx:
                print("apt: no package index; run 'apt update' first")
                return
            installed = self._apt_list_installed()
            # dependency resolution (DFS)
            order: List[str] = []
            visiting: Dict[str, int] = {}

            def visit(name: str) -> bool:
                if name in installed:
                    return True
                state = visiting.get(name, 0)
                if state == 1:
                    print(f"apt: dependency cycle at {name}")
                    return False
                if state == 2:
                    return True
                meta = idx.get(name)
                if not meta:
                    print(f"apt: unknown package '{name}' (not in index)")
                    return False
                visiting[name] = 1
                deps = meta.get("depends") or []
                # normalize depends into groups
                dep_groups: List[List[str]] = []
                for d in deps:
                    dep_groups.extend(self._apt_parse_depends_expr(d) if not isinstance(d, list) else [d])
                for group in dep_groups:
                    # satisfied by any alternative
                    if any(g in installed for g in group):
                        continue
                    # pick the first alternative that exists in index
                    choice = None
                    for cand in group:
                        if cand in idx:
                            choice = cand
                            break
                    if not choice:
                        print(f"apt: cannot satisfy dependency group {group} for {name}")
                        return False
                    if not visit(choice):
                        return False
                visiting[name] = 2
                order.append(name)
                return True

            for req in args[1:]:
                if not visit(req):
                    return
            # download & install in order
            for name in order:
                if name in installed:
                    continue
                meta = idx.get(name, {})
                deb_path = self._apt_download_to_archives(name, meta)
                if not deb_path:
                    print(f"apt: cannot get package {name}")
                    return
                # call dpkg to install
                self.cmd_dpkg("-i", deb_path)
            print("apt: install complete")
            return
        elif sub == "remove":
            if len(args) < 2:
                print("apt remove: package name required")
                return
            name = args[1]
            base = f"/var/lib/ttos/dpkg/{name}"
            try:
                txt = self.fs.read_file(base + "/manifest.txt").decode("utf-8", "ignore")
                paths = [p for p in txt.splitlines() if p and not p.startswith("Package:") and not p.startswith("Version:") and not p.startswith("Architecture:") and not p.startswith("Installed-Files:")]
            except Exception as e:
                print(f"apt: {name} not installed ({e})")
                return
            removed = 0
            for p in paths:
                if p.endswith('/'):
                    continue
                try:
                    self.fs.rm(p)
                    removed += 1
                except Exception:
                    pass
            # mark removed
            try:
                self.fs.write_file(base + "/status", b"ok removed\n", create_parents=True)
            except Exception:
                pass
            print(f"apt: removed {name} (files deleted: {removed})")
            return
        else:
            print("apt: unknown command")
            return

    def cmd_ls(self, *args):
        path = args[0] if args else "."
        try:
            for name, typ in self.fs.ls(path):
                marker = "/" if typ == "dir" else ""
                print(name + marker)
        except Exception as e:
            print(f"ls: {e}")

    def cmd_cd(self, *args):
        path = args[0] if args else "/"
        try:
            self.fs.cd(path)
        except Exception as e:
            print(f"cd: {e}")

    def cmd_pwd(self, *args):
        print(self.fs.pwd())

    def cmd_cat(self, *args):
        if not args:
            print("cat: missing operand")
            return
        try:
            data = self.fs.read_file(args[0])
            sys.stdout.write(data.decode("utf-8", "ignore"))
            if data and not str(data).endswith("\n"):
                print()
        except Exception as e:
            print(f"cat: {e}")

    def cmd_echo(self, *args):
        # support echo ... > file  and  >> append (not implemented, acts like >)
        if not args:
            print()
            return
        if ">" in args or ">>" in args:
            try:
                if ">>" in args:
                    op = ">>"
                else:
                    op = ">"
                idx = args.index(op)
                text = " ".join(args[:idx])
                path = args[idx+1]
                existing = b""
                if op == ">>":
                    try:
                        existing = self.fs.read_file(path)
                    except Exception:
                        existing = b""
                self.fs.write_file(path, existing + (text + "\n").encode("utf-8"))
            except Exception as e:
                print(f"echo: {e}")
        else:
            print(" ".join(args))

    def cmd_touch(self, *args):
        if not args:
            print("touch: missing file")
            return
        for p in args:
            try:
                try:
                    data = self.fs.read_file(p)
                except Exception:
                    data = b""
                self.fs.write_file(p, data)
            except Exception as e:
                print(f"touch: {p}: {e}")

    def cmd_rm(self, *args):
        if not args:
            print("rm: missing file")
            return
        for p in args:
            try:
                self.fs.rm(p)
            except Exception as e:
                print(f"rm: {p}: {e}")

    def cmd_mkdir(self, *args):
        if not args:
            print("mkdir: missing dir")
            return
        for p in args:
            try:
                self.fs.mkdir(p)
            except Exception as e:
                print(f"mkdir: {p}: {e}")

    def cmd_rmdir(self, *args):
        if not args:
            print("rmdir: missing dir")
            return
        for p in args:
            try:
                self.fs.rmdir(p)
            except Exception as e:
                print(f"rmdir: {p}: {e}")

    def cmd_mv(self, *args):
        if len(args) != 2:
            print("mv: src dst")
            return
        try:
            self.fs.mv(args[0], args[1])
        except Exception as e:
            print(f"mv: {e}")

    def cmd_cp(self, *args):
        if len(args) != 2:
            print("cp: src dst")
            return
        try:
            self.fs.cp(args[0], args[1])
        except Exception as e:
            print(f"cp: {e}")

    def cmd_ps(self, *args):
        for pid, name, state in self.k.ps():
            print(f"{pid:5d}  {name:<16} {state}")

    def cmd_kill(self, *args):
        if not args:
            print("kill: pid")
            return
        try:
            self.k.kill(int(args[0]))
        except Exception as e:
            print(f"kill: {e}")

    def cmd_uptime(self, *args):
        secs = int(self.k.uptime())
        print(f"up {secs}s")

    def cmd_whoami(self, *args):
        print(self.k.env.get("USER", "guest"))

    def cmd_time(self, *args):
        print(now_iso() + "Z")

    def cmd_clear(self, *args):
        os.system("clear" if os.name != "nt" else "cls")

    def cmd_reboot(self, *args):
        raise SystemExit("REBOOT")

    def cmd_shutdown(self, *args):
        raise SystemExit("SHUTDOWN")

    def cmd_exit(self, *args):
        raise SystemExit("EXIT")

    def cmd_edit(self, *args):
        if not args:
            print("edit: file")
            return
        path = args[0]
        try:
            try:
                content = self.fs.read_file(path).decode("utf-8")
            except Exception:
                content = ""
            print(Colors.DIM + "-- simple line editor. end with a single '.' on a line --" + Colors.RESET)
            print(Colors.DIM + "Current content (shown above). Start typing below:" + Colors.RESET)
            for line in content.splitlines():
                print(line)
            lines = []
            while True:
                s = input(Colors.MAGENTA + "~ " + Colors.RESET)
                if s == ".":
                    break
                lines.append(s)
            data = ("\n".join(lines) + "\n") if lines else ""
            self.fs.write_file(path, data.encode("utf-8"))
        except Exception as e:
            print(f"edit: {e}")

    def cmd_kat(self, *args):
        """kat — nano-style TUI editor (curses). Fallback to line mode.
        Usage:
          kat [FILE]           # open FILE in full-screen editor
          kat --line [FILE]    # force classic line editor
        Keys (TUI): ^X Exit  ^O WriteOut  ^G Help  ^W WhereIs  ^K Cut line  ^U Uncut
        """
        # flag parsing: allow --line to force non-curses mode
        use_line = False
        path = None
        if args and args[0] == "--line":
            use_line = True
            path = args[1] if len(args) > 1 else None
        else:
            path = args[0] if args else None

        if not use_line and curses is not None:
            try:
                self._kat_curses_editor(path)
                return
            except Exception as e:
                print(f"kat: curses UI failed ({e}); falling back to line editor")
        # fallback / explicit line mode
        self._kat_line_editor(path)

    def _kat_line_editor(self, path: Optional[str]):
        """Classic tiny line editor kept for compatibility."""
        # load file (if any)
        buf: List[str] = []
        dirty = False
        if path:
            try:
                data = self.fs.read_file(path).decode("utf-8", "ignore")
                buf = data.splitlines()
            except Exception:
                buf = []
        cur = len(buf) if buf else 0  # current line index (1-based logically)

        def _status():
            base = os.path.basename(path) if path else "(new)"
            return f"kat:{base} [{cur}/{len(buf)}]{' *' if dirty else ''}"

        def _print_range(a: int, b: int):
            nonlocal cur
            a = max(1, a); b = min(len(buf), b)
            if a > b or not buf:
                print(Colors.DIM + "(empty)" + Colors.RESET)
                return
            for i in range(a, b+1):
                print(f"{i:4d}| {buf[i-1]}")
            cur = b

        def _write(to_path: Optional[str]) -> bool:
            nonlocal path, dirty
            dest = to_path or path
            if not dest:
                print("kat: :w requires a filename the first time (e.g., :w my.txt)")
                return False
            try:
                data = ("\n".join(buf) + ("\n" if buf else "")).encode("utf-8")
                self.fs.write_file(dest, data, create_parents=True)
                path = dest
                dirty = False
                print(f"wrote {len(buf)} line(s) -> {dest}")
                return True
            except Exception as e:
                print(f"kat: write failed: {e}")
                return False

        print(Colors.DIM + "-- kat: tiny line editor. Type :help for commands --" + Colors.RESET)
        if buf:
            _print_range(1, min(len(buf), 20))

        while True:
            try:
                prompt = Colors.MAGENTA + _status() + Colors.RESET + " $ "
                line = input(prompt)
            except EOFError:
                print()
                break
            except KeyboardInterrupt:
                print("^C")
                continue
            if line is None:
                continue
            s = line.strip()
            if not s:
                continue

            # insert/append modes
            if s == 'i':
                print(Colors.DIM + "-- INSERT mode (end with a single '.' on its own line) --" + Colors.RESET)
                while True:
                    t = input("| ")
                    if t == ".":
                        break
                    # insert AFTER current line position
                    if cur <= 0:
                        buf.insert(0, t)
                        cur = 1
                    else:
                        buf.insert(cur, t)
                        cur += 1
                    dirty = True
                continue
            if s == 'a':
                print(Colors.DIM + "-- APPEND mode (end with a single '.' on its own line) --" + Colors.RESET)
                while True:
                    t = input("| ")
                    if t == ".":
                        break
                    buf.append(t)
                    cur = len(buf)
                    dirty = True
                continue

            # colon commands
            if s.startswith(":"):
                try:
                    parts = shlex.split(s[1:])
                except Exception:
                    print("kat: parse error")
                    continue
                if not parts:
                    continue
                cmd = parts[0]
                if cmd in ("help", "h"):
                    print(self._kat_line_editor.__doc__ or "")
                    print("Commands: i, a, :p [a [b]], :g N, :d [N], :w [FILE], :wq, :q, :q!, :help")
                    continue
                if cmd == 'p':
                    if len(parts) == 1:
                        if cur == 0:
                            _print_range(1, len(buf))
                        else:
                            _print_range(cur, cur)
                    elif len(parts) == 2:
                        a = int(parts[1])
                        _print_range(a, a)
                    else:
                        a = int(parts[1]); b = int(parts[2])
                        _print_range(a, b)
                    continue
                if cmd == 'g':
                    if len(parts) < 2:
                        print("kat: :g N")
                        continue
                    try:
                        n = int(parts[1])
                        if 1 <= n <= max(1, len(buf)):
                            cur = min(n, len(buf))
                        else:
                            print("kat: out of range")
                    except Exception:
                        print("kat: invalid number")
                    continue
                if cmd == 'd':
                    n = cur
                    if len(parts) >= 2:
                        try:
                            n = int(parts[1])
                        except Exception:
                            print("kat: :d [N]")
                            continue
                    if 1 <= n <= len(buf):
                        buf.pop(n-1)
                        dirty = True
                        cur = min(n, len(buf))
                    else:
                        print("kat: no such line")
                    continue
                if cmd == 'w':
                    to = parts[1] if len(parts) > 1 else None
                    _write(to)
                    continue
                if cmd == 'wq':
                    to = parts[1] if len(parts) > 1 else None
                    if _write(to):
                        return
                    continue
                if cmd == 'q':
                    if dirty:
                        print("kat: unsaved changes (use :w to save or :q! to discard)")
                        continue
                    return
                if cmd == 'q!':
                    return
                print("kat: unknown command (try :help)")
                continue

            # If it's plain text, treat as a one-line insert after current line
            if cur <= 0:
                buf.insert(0, s)
                cur = 1
            else:
                buf.insert(cur, s)
                cur += 1
            dirty = True

    def _kat_curses_editor(self, path: Optional[str]):
        """Nano-like full-screen editor using curses. Minimal but comfy.
        Keys: ^X Exit  ^O WriteOut  ^G Help  ^W Search  Arrows/Home/End/PGUP/PGDN  Backspace/Enter
        """
        # Load buffer
        try:
            data = self.fs.read_file(path).decode("utf-8", "ignore") if path else ""
        except Exception:
            data = ""
        lines: List[str] = data.splitlines()
        if lines == []:
            lines = [""]
        cy, cx = 0, 0      # cursor line/col
        top = 0            # first visible line
        dirty = False
        cut_buffer: List[str] = []  # for ^K/^U line cut/uncut

        def clamp():
            nonlocal cy, cx
            cy = max(0, min(cy, len(lines) - 1))
            cx = max(0, min(cx, len(lines[cy])))

        def status_line(name: str) -> str:
            star = "*" if dirty else ""
            base = name if name else "(new)"
            return f" {base}{star}  Ln {cy+1}, Col {cx+1} "

        def draw(stdscr):
            stdscr.clear()
            h, w = stdscr.getmaxyx()
            body_h = max(1, h - 2)
            # draw text area
            for i in range(body_h):
                li = top + i
                if li >= len(lines):
                    break
                s = lines[li]
                if len(s) > w - 1:
                    s = s[:w-1]
                try:
                    stdscr.addstr(i, 0, s)
                except Exception:
                    pass
            # status bar
            name = os.path.basename(path) if path else "(new)"
            bar = status_line(name)
            if len(bar) < w:
                bar = bar + " " * (w - len(bar))
            try:
                stdscr.addstr(h-2, 0, bar, curses.A_REVERSE)
            except Exception:
                pass
            # help bar
            helpmsg = "^G Help  ^O WriteOut  ^W WhereIs  ^K Cut  ^U Uncut  ^X Exit"
            if len(helpmsg) < w:
                helpmsg = helpmsg + " " * (w - len(helpmsg))
            try:
                stdscr.addstr(h-1, 0, helpmsg, curses.A_REVERSE)
            except Exception:
                pass
            # place cursor
            vy = cy - top
            if vy < 0:
                vy = 0
            elif vy >= body_h:
                vy = body_h - 1
            vx = min(cx, max(0, w - 1))
            try:
                stdscr.move(vy, vx)
            except Exception:
                pass
            stdscr.refresh()

        def prompt(stdscr, msg: str, default: str = "") -> Optional[str]:
            h, w = stdscr.getmaxyx()
            s = msg + default
            stdscr.move(h-2, 0)
            stdscr.clrtoeol()
            try:
                stdscr.addstr(h-2, 0, s, curses.A_REVERSE)
            except Exception:
                pass
            curses.curs_set(1)
            buf = list(default)
            while True:
                ch = stdscr.getch()
                if ch in (10, 13):  # Enter
                    return "".join(buf).strip()
                if ch in (27,):     # ESC
                    return None
                if ch in (curses.KEY_BACKSPACE, 127, 8):
                    if buf:
                        buf.pop()
                    # redraw line
                    stdscr.move(h-2, 0)
                    stdscr.clrtoeol()
                    try:
                        stdscr.addstr(h-2, 0, msg + "".join(buf), curses.A_REVERSE)
                    except Exception:
                        pass
                    continue
                if 32 <= ch <= 126:
                    buf.append(chr(ch))
                    stdscr.move(h-2, 0)
                    stdscr.clrtoeol()
                    try:
                        stdscr.addstr(h-2, 0, msg + "".join(buf), curses.A_REVERSE)
                    except Exception:
                        pass
            # unreachable

        def write_out(stdscr) -> bool:
            nonlocal path, dirty
            name = os.path.basename(path) if path else ""
            ask = f"Write file name: "
            dest = prompt(stdscr, ask, name)
            if dest is None:
                return False
            if not dest:
                return False
            try:
                payload = ("\n".join(lines) + "\n").encode("utf-8")
                self.fs.write_file(dest if dest.startswith("/") else os.path.join(self.fs.pwd(), dest), payload, create_parents=True)
                path = dest if dest.startswith("/") else os.path.join(self.fs.pwd(), dest)
                dirty = False
                return True
            except Exception as e:
                # show error in status
                h, w = stdscr.getmaxyx()
                msg = f"write failed: {e}"
                try:
                    stdscr.addstr(h-2, 0, (msg + " " * (w-len(msg)))[:w], curses.A_REVERSE)
                except Exception:
                    pass
                stdscr.getch()
                return False

        def find_next(stdscr) -> None:
            term = prompt(stdscr, "Search: ")
            if not term:
                return
            nonlocal cy, cx, top
            # search from current position forward
            li = cy
            col = cx + 1
            while li < len(lines):
                pos = lines[li].find(term, col if li == cy else 0)
                if pos != -1:
                    cy, cx = li, pos
                    # scroll into view
                    h, w = stdscr.getmaxyx()
                    body_h = max(1, h - 2)
                    if cy < top:
                        top = cy
                    elif cy >= top + body_h:
                        top = cy - body_h + 1
                    return
                li += 1
                col = 0

        def cut_line():
            nonlocal lines, cy, cx, cut_buffer, dirty
            if not lines:
                lines = [""]
                cy, cx = 0, 0
                return
            cut_buffer = [lines.pop(cy)]
            if not lines:
                lines = [""]
            if cy >= len(lines):
                cy = len(lines) - 1
            cx = min(cx, len(lines[cy]))
            dirty = True

        def uncut_line():
            nonlocal lines, cy, cx, cut_buffer, dirty
            if not cut_buffer:
                return
            lines.insert(cy, cut_buffer[0])
            dirty = True

        def main(stdscr):
            nonlocal cy, cx, top, dirty
            try:
                curses.curs_set(1)
            except Exception:
                pass
            stdscr.timeout(100)
            while True:
                # keep cursor sane
                clamp()
                # scroll if needed
                h, w = stdscr.getmaxyx()
                body_h = max(1, h - 2)
                if cy < top:
                    top = cy
                elif cy >= top + body_h:
                    top = cy - body_h + 1
                draw(stdscr)
                ch = stdscr.getch()
                if ch == -1:
                    continue
                # control keys
                if ch in (24,):  # ^X Exit
                    if dirty:
                        # confirm
                        h, w = stdscr.getmaxyx()
                        msg = "Save modified buffer? (Y)es/(N)o/(C)ancel"
                        try:
                            stdscr.addstr(h-2, 0, (msg + " " * (w-len(msg)))[:w], curses.A_REVERSE)
                        except Exception:
                            pass
                        c = stdscr.getch()
                        if c in (ord('y'), ord('Y')):
                            if write_out(stdscr):
                                return
                            else:
                                continue
                        elif c in (ord('n'), ord('N')):
                            return
                        else:
                            continue
                    return
                if ch in (15,):  # ^O WriteOut
                    write_out(stdscr)
                    continue
                if ch in (7,):   # ^G Help
                    h, w = stdscr.getmaxyx()
                    help_lines = [
                        "kat — nano-like keys:",
                        "  ^X Exit   ^O WriteOut   ^G Help   ^W WhereIs",
                        "  Arrows/Home/End, PgUp/PgDn, Enter, Backspace",
                        "  ^K Cut line   ^U Uncut",
                        "Press any key to continue...",
                    ]
                    stdscr.clear()
                    for i, hl in enumerate(help_lines):
                        try:
                            stdscr.addstr(i, 0, hl)
                        except Exception:
                            pass
                    stdscr.refresh()
                    stdscr.getch()
                    continue
                if ch in (23,):  # ^W WhereIs
                    find_next(stdscr)
                    continue
                if ch in (11,):  # ^K cut line
                    cut_line()
                    continue
                if ch in (21,):  # ^U uncut
                    uncut_line()
                    continue

                # navigation
                if ch in (curses.KEY_LEFT, 260):
                    if cx > 0:
                        cx -= 1
                    elif cy > 0:
                        cy -= 1
                        cx = len(lines[cy])
                    continue
                if ch in (curses.KEY_RIGHT, 261):
                    if cx < len(lines[cy]):
                        cx += 1
                    elif cy < len(lines) - 1:
                        cy += 1
                        cx = 0
                    continue
                if ch in (curses.KEY_UP, 259):
                    if cy > 0:
                        cy -= 1
                        cx = min(cx, len(lines[cy]))
                    continue
                if ch in (curses.KEY_DOWN, 258):
                    if cy < len(lines) - 1:
                        cy += 1
                        cx = min(cx, len(lines[cy]))
                    continue
                if ch in (curses.KEY_HOME, 262):
                    cx = 0
                    continue
                if ch in (curses.KEY_END, 360):
                    cx = len(lines[cy])
                    continue
                if ch in (curses.KEY_PPAGE, 339):  # PgUp
                    cy = max(0, cy - body_h)
                    continue
                if ch in (curses.KEY_NPAGE, 338):  # PgDn
                    cy = min(len(lines) - 1, cy + body_h)
                    continue
                if ch == curses.KEY_RESIZE:
                    continue

                # editing
                if ch in (curses.KEY_BACKSPACE, 127, 8):
                    if cx > 0:
                        s = lines[cy]
                        lines[cy] = s[:cx-1] + s[cx:]
                        cx -= 1
                        dirty = True
                    elif cy > 0:
                        prev_len = len(lines[cy-1])
                        lines[cy-1] += lines[cy]
                        lines.pop(cy)
                        cy -= 1
                        cx = prev_len
                        dirty = True
                    continue
                if ch in (10, 13):  # Enter
                    s = lines[cy]
                    left, right = s[:cx], s[cx:]
                    lines[cy] = left
                    lines.insert(cy+1, right)
                    cy += 1
                    cx = 0
                    dirty = True
                    continue
                # printable ASCII
                if 32 <= ch <= 126:
                    s = lines[cy]
                    lines[cy] = s[:cx] + chr(ch) + s[cx:]
                    cx += 1
                    dirty = True
                    continue
                # ignore others

        if curses is None:
            raise RuntimeError("curses not available")
        curses.wrapper(main)

    def cmd_mount(self, *args):
        if self.fs.mounted:
            print("already mounted")
            return
        try:
            self.fs.mount(create_if_missing=True)
            print("mounted", self.fs.image_path, "RO" if self.fs.read_only else "RW")
        except Exception as e:
            print(f"mount: {e}")

    def cmd_umount(self, *args):
        try:
            self.fs.umount()
            print("unmounted")
        except Exception as e:
            print(f"umount: {e}")

    def cmd_fsck(self, *args):
        errs = self.fs.fsck()
        if errs:
            print("FS ERRORS:")
            for e in errs:
                print("  -", e)
        else:
            print("FS clean")

    def cmd_format(self, *args):
        confirm = input("This will erase the disk image. Type 'YES' to continue: ")
        if confirm.strip() == "YES":
            self.fs.format()
            print("formatted")
        else:
            print("aborted")

    def cmd_env(self, *args):
        for k, v in sorted(self.k.env.items()):
            print(f"{k}={v}")

    def cmd_export(self, *args):
        # export KEY=VALUE
        if not args:
            print("export: KEY=VALUE ...")
            return
        for a in args:
            if "=" not in a:
                print(f"export: invalid: {a}")
                continue
            k, v = a.split("=", 1)
            self.k.env[k] = v

    # run background toy tasks
    def cmd_run(self, *args):
        if not args:
            print("run: task [args...]  (tasks: cpu <secs>, clock, io <file> <times>)")
            return
        task = args[0]
        if task == "cpu":
            secs = float(args[1]) if len(args) > 1 else 3.0
            def _cpu():
                end = time.time() + secs
                while time.time() < end:
                    # busy loop for demo; yield cooperatively
                    yield 0
                    # simulate slice work
                    _ = sum(i*i for i in range(200))
                return
            pid = self.k.spawn(f"cpu:{secs}s", _cpu())
            print(f"spawned pid {pid}")
        elif task == "clock":
            def _clock():
                while True:
                    print(Colors.DIM + f"[clock] {now_iso()}Z" + Colors.RESET)
                    # sleep 1s via cooperative yield
                    yield 1.0
            pid = self.k.spawn("clock", _clock())
            print(f"spawned pid {pid}")
        elif task == "io":
            if len(args) < 3:
                print("run io <file> <times>")
                return
            path = args[1]
            times = int(args[2])
            def _io():
                for i in range(times):
                    self.k.sys_write_file(path, f"line {i}\n".encode("utf-8"))
                    yield 0.2
                return
            pid = self.k.spawn("io", _io())
            print(f"spawned pid {pid}")
        else:
            print(f"unknown task: {task}")

    def cmd_about(self, *args):
        print("Tiny Terminal OS — a toy OS sim in one Python file. Not a real OS, just for fun and learning.")

    # ----- PATH execution & scripts -----
    def _which(self, cmd: str) -> Optional[str]:
        paths = self.k.env.get("PATH", "").split(":")
        for d in paths:
            if not d:
                continue
            try:
                inode = self.fs._resolve(d)
                node = self.fs._inode(inode)
                if node["type"] != "dir":
                    continue
                if cmd in node["children"]:
                    child = self.fs._inode(node["children"][cmd])
                    if child["type"] == "file":
                        return (d.rstrip("/") + "/" + cmd)
            except Exception:
                continue
        return None

    def _exec_file(self, path: str, args: List[str]):
        try:
            data = self.fs.read_file(path).decode("utf-8", "ignore")
        except Exception as e:
            print(f"exec: {e}")
            return
        if data.startswith("#!ttsh"):
            body = "\n".join(data.splitlines()[1:])
            self.run_script(body, args)
        else:
            # default behavior: print file contents
            sys.stdout.write(data)
            if data and not data.endswith("\n"):
                print()

    def run_script(self, content: str, args: List[str] | None = None):
        args = args or []
        for raw in content.splitlines():
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            # minimal $@ substitution
            line = line.replace("$@", " ".join(args))
            try:
                parts = shlex.split(line)
            except Exception:
                print("script: parse error")
                continue
            if not parts:
                continue
            cmd, *a = parts
            fn = self.builtins.get(cmd)
            if fn:
                try:
                    fn(*a)
                except SystemExit:
                    raise
                except Exception as e:
                    print(f"{cmd}: {e}")
            else:
                path = self._which(cmd)
                if path:
                    self._exec_file(path, a)
                else:
                    print(f"command not found: {cmd}")

    # utilities exposed as builtins
    def cmd_which(self, *args):
        if not args:
            print("which: command")
            return
        p = self._which(args[0])
        if p:
            print(p)
        else:
            print("")

    def cmd_source(self, *args):
        if not args:
            print("source: file")
            return
        try:
            data = self.fs.read_file(args[0]).decode("utf-8", "ignore")
            self.run_script(data, list(args[1:]))
        except Exception as e:
            print(f"source: {e}")

    def cmd_net(self, *args):
        sub = args[0] if args else "status"
        try:
            if sub == "up":
                self.k.net_up()
                print("net: up")
            elif sub == "down":
                self.k.net_down()
                print("net: down")
            elif sub == "status":
                s = self.k.net_status()
                print(f"net {'UP' if s['up'] else 'DOWN'} timeout={s['timeout']}s dns={','.join(map(str, s['dns']))}")
            elif sub == "info":
                s = self.k.net_info()
                print(f"host: {s.get('hostname','')} ({s.get('fqdn','')})")
                print(f"state: {'UP' if s['up'] else 'DOWN'}  timeout={s['timeout']}s")
                dns = s.get('dns') or []
                print("dns:", ",".join(map(str, dns)))
                if s.get('local_ipv4'):
                    print("local IPv4:", ", ".join(s['local_ipv4']))
                if s.get('local_ipv6'):
                    print("local IPv6:", ", ".join(s['local_ipv6']))
                if s.get('primary_ipv4'):
                    print("primary IPv4:", s['primary_ipv4'])
                if s.get('primary_ipv6'):
                    print("primary IPv6:", s['primary_ipv6'])
                if s.get('external_ipv4'):
                    print("external IPv4:", s['external_ipv4'])
                if s.get('external_ipv6'):
                    print("external IPv6:", s['external_ipv6'])
            elif sub == "resolve" and len(args) >= 2:
                print(self.k.net_resolve(args[1]))
            else:
                print("usage: net [up|down|status|info|resolve <host>]")
        except Exception as e:
            print(f"net: {e}")

    def cmd_ping(self, *args):
        if not args:
            print("ping: host [port] [count]")
            return
        host = args[0]
        port = int(args[1]) if len(args) > 1 else 443
        count = int(args[2]) if len(args) > 2 else 4
        try:
            stats = self.k.net_tcp_ping(host, port=port, count=count, timeout=2.0)
            for i, rtt in enumerate(stats.get('rtts', []), 1):
                if rtt is None:
                    print(f"tcp_ping seq={i} timeout")
                else:
                    print(f"tcp_ping seq={i} rtt={rtt:.1f} ms")
            print(f"--- {host} tcp/{port} ping statistics ---")
            print(f"{stats['sent']} packets transmitted, {stats['recv']} received, {stats['loss']:.0f}% packet loss")
            if 'avg' in stats:
                print(f"rtt min/avg/max = {stats['min']:.1f}/{stats['avg']:.1f}/{stats['max']:.1f} ms")
        except Exception as e:
            print(f"ping: {e}")

    def cmd_httpget(self, *args):
        if not args:
            print("httpget: URL [DEST]")
            return
        url = args[0]
        dest = args[1] if len(args) > 1 else None
        try:
            data, status, ctype = self.k.net_http_get(url)
            if dest:
                self.fs.write_file(dest, data, create_parents=True)
                print(f"Saved {len(data)} bytes to {dest} (status {status}, type {ctype})")
            else:
                is_text = (ctype.startswith("text/") or "json" in ctype) if ctype else True
                if is_text:
                    try:
                        sys.stdout.write(data.decode('utf-8'))
                    except Exception:
                        sys.stdout.write(data.decode('latin-1', 'ignore'))
                    if data and not data.endswith(b"\n"):
                        print()
                else:
                    print(f"[binary content {len(data)} bytes, type={ctype}]")
        except Exception as e:
            print(f"httpget: {e}")

    def cmd_dload(self, *args):
        if not args:
            print("dload: URL [DEST]")
            return
        url = args[0]
        dest = args[1] if len(args) > 1 else None
        try:
            data, status, ctype = self.k.net_http_get(url)
            if not dest:
                try:
                    parsed = urllib.parse.urlparse(url)
                    name = os.path.basename(parsed.path) or "index.html"
                    if not name.strip():
                        name = "download.bin"
                except Exception:
                    name = "download.bin"
                # save into current directory
                dest = os.path.join(self.fs.pwd(), name)
            self.fs.write_file(dest, data, create_parents=True)
            print(f"Downloaded {len(data)} bytes -> {dest} (status {status}, type {ctype})")
        except Exception as e:
            print(f"dload: {e}")

    def cmd_debinfo(self, *args):
        if not args:
            print("debinfo: FILE.deb")
            return
        try:
            pkg = DebPackage.load(self.fs, args[0])
            print(f"Package: {pkg.name}")
            print(f"Version: {pkg.version}")
            print(f"Architecture: {pkg.arch}")
            if pkg.description:
                print(f"Description: {pkg.description.splitlines()[0]}")
        except Exception as e:
            print(f"debinfo: {e}")

    def cmd_debextract(self, *args):
        if not args:
            print("debextract: FILE.deb [DEST=/]")
            return
        deb = args[0]
        dest = args[1] if len(args) > 1 else "/"
        try:
            pkg = DebPackage.load(self.fs, deb)
            stats = pkg.extract_to_fs(self.fs, dest)
            print(f"Extracted {stats['files']} files, {stats['dirs']} dirs, {stats['links']} links to {dest}")
        except Exception as e:
            print(f"debextract: {e}")

    def cmd_dpkg(self, *args):
        if not args or args[0] not in ("-i", "--install") or len(args) < 2:
            print("usage: dpkg -i FILE.deb")
            return
        deb = args[1]
        try:
            pkg = DebPackage.load(self.fs, deb)
            stats = pkg.extract_to_fs(self.fs, "/")
            # write a tiny status + manifest
            status_dir = f"/var/lib/ttos/dpkg/{pkg.name}"
            manifest = [
                f"Package: {pkg.name}",
                f"Version: {pkg.version}",
                f"Architecture: {pkg.arch}",
                f"Installed-Files: {len(stats['paths'])}",
                "",
            ] + stats['paths']
            self.fs.write_file(status_dir + "/manifest.txt", ("\n".join(manifest) + "\n").encode("utf-8"), create_parents=True)
            self.fs.write_file(status_dir + "/status", (f"ok installed {pkg.version}\n").encode("utf-8"), create_parents=True)
            print(f"Installed {pkg.name} {pkg.version}: {stats['files']} files, {stats['dirs']} dirs, {stats['links']} links")
        except Exception as e:
            print(f"dpkg: {e}")

    # ----- REPL -----
    def loop(self, single_user: bool = False):
        user = self.k.env.get("USER", "guest")
        try:
            while True:
                # advance scheduler lightly to keep background tasks alive
                time.sleep(0.01)
                prompt = Colors.BOLD + f"{user}@ttos" + Colors.RESET + ":" + self.fs.pwd() + "$ "
                try:
                    line = input(prompt)
                except EOFError:
                    print()
                    break
                if not line.strip():
                    continue
                try:
                    parts = shlex.split(line)
                except Exception:
                    print("parse error")
                    continue
                cmd, *args = parts
                fn = self.builtins.get(cmd)
                if fn:
                    try:
                        fn(*args)
                    except SystemExit as se:
                        raise
                    except Exception as e:
                        print(f"{cmd}: {e}")
                else:
                    path = self._which(cmd)
                    if path:
                        self._exec_file(path, args)
                    else:
                        print(f"command not found: {cmd}")
        except SystemExit as se:
            raise
        except KeyboardInterrupt:
            print("^C")

# -------------------- Main boot sequence --------------------

def main():
    parser = argparse.ArgumentParser(description="Tiny Terminal OS")
    parser.add_argument("--image", default="tinyfs.img", help="disk image path")
    parser.add_argument("--mode", choices=["normal", "safe", "single"], help="boot mode override")
    args = parser.parse_args()

    fs = TinyFS(args.image)
    boot = BootLoader(fs)
    kernel, mode = boot.boot(mode=args.mode)
    kernel.start()

    # spawn a demo clock task unless safe mode
    if mode != "safe":
        def _heartbeat():
            while True:
                yield 2.0
        kernel.spawn("heartbeat", _heartbeat())

    shell = Shell(kernel)
    # run optional boot rc script
    try:
        if mode != "safe" and fs.exists("/boot/rc.ttsh"):
            data = fs.read_file("/boot/rc.ttsh").decode("utf-8", "ignore")
            shell.run_script(data, [])
    except Exception:
        pass
    try:
        single = (mode == "single")
        shell.loop(single_user=single)
    except SystemExit as se:
        reason = str(se)
        print(Colors.YELLOW + f"System request: {reason}" + Colors.RESET)
    finally:
        print(Colors.DIM + "Saving filesystem and halting..." + Colors.RESET)
        try:
            fs.save()
        except Exception:
            pass
        kernel.stop()
        try:
            fs.umount()
        except Exception:
            pass
        print(Colors.GREEN + "Bye." + Colors.RESET)

if __name__ == "__main__":
    # Improve ctrl-c behavior on Windows
    try:
        signal.signal(signal.SIGINT, signal.SIG_DFL)
    except Exception:
        pass
    main()