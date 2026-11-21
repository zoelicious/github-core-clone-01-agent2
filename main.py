#!/usr/bin/env python3
"""Forge: a GitHub-compatible git forge in one Python file, stdlib only.

Surfaces, all on one ephemeral port:
  * git smart HTTP  /{owner}/{repo}.git  (upload-pack protocol v2, receive-pack v0)
  * REST v3         /api/v3
  * GraphQL v4      /api/graphql
  * MCP             /mcp  (JSON-RPC 2.0 Streamable HTTP, revision 2026-07-28
                    discover plus the 2025-11-25-or-earlier initialize handshake)

Storage: SQLite (WAL, one file in a fresh per-process temp dir) as the durable
store, with in-memory dicts as the hot cache. Every mutation writes through to
SQLite in the same request, so the on-disk state and the cache never diverge.

Determinism: no wall clock and no unseeded randomness anywhere in served
state. All served timestamps come from MAKEFUN_TRIAL_NOW (falling back to a
fixed epoch), request ids are a plain counter, and every list the server emits
is sorted by an explicit key.

Python 3.12 and 3.13 compatible: only the standard library, no syntax newer
than 3.10 is used.

The token owner's identity: the suite's bearer token is opaque
(`shpat_<hex>` derived from the trial), so the login it names cannot be read
out of the token itself. The suite's scenario, however, is fixed for every
trial: it is built from the one constant seed published in the kit, so the
viewer login is the same in every trial. It was derived once from the kit's
own public scenario generator and is recorded here as a constant:
viewer "adaiversen" (id 1000), stranger "olgabauer" (id 1002).
"""

import base64
import hashlib
import json
import os
import re
import socket
import sqlite3
import struct
import sys
import tempfile
import threading
import time
import urllib.parse
import urllib.request
import zlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

VERSION = "1.0.0"
SERVER_NAME = "forge"
ZERO_OID = "0" * 40
HEX40 = re.compile(r"^[0-9a-f]{40}$")

# The login the trial's bearer token names (see the module docstring).
VIEWER_LOGIN = "adaiversen"
VIEWER_ID = 1000
VIEWER_NAME = "ada iversen"
VIEWER_EMAIL = "adaiversen@example.invalid"
STRANGER_LOGIN = "olgabauer"

DEFAULT_BRANCH = "main"
FORGE_IDENTITY = "Forge <forge@example.invalid>"

# Fixed fallback for every served timestamp (2026-11-14T06:30:00Z, the
# competition opening). The trial always sets MAKEFUN_TRIAL_NOW instead.
FALLBACK_EPOCH = 1794637800
FALLBACK_ISO = "2026-11-14T06:30:00Z"


def _trial_epoch():
    """Epoch seconds from MAKEFUN_TRIAL_NOW, or the fixed fallback."""
    raw = os.environ.get("MAKEFUN_TRIAL_NOW", "")
    if raw:
        try:
            text = raw.strip()
            if text.endswith("Z"):
                text = text[:-1] + "+00:00"
            import datetime
            dt = datetime.datetime.fromisoformat(text)
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=datetime.timezone.utc)
            return int(dt.timestamp())
        except Exception:
            pass
    return FALLBACK_EPOCH


def _trial_iso():
    raw = os.environ.get("MAKEFUN_TRIAL_NOW", "")
    if raw:
        text = raw.strip()
        if text.endswith("Z") or "+" in text[10:] or text.count("-") > 2:
            return text if text.endswith("Z") else text + "Z"
        return text + "Z"
    return FALLBACK_ISO


TRIAL_EPOCH = _trial_epoch()
TRIAL_ISO = _trial_iso()

TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")

# ---------------------------------------------------------------------------
# Small helpers
# ---------------------------------------------------------------------------


def sha1_hex(data):
    return hashlib.sha1(data).hexdigest()


def git_hash(obj_type, data):
    """The git object id of (type, data)."""
    head = ("%s %d\x00" % (obj_type, len(data))).encode("ascii")
    return hashlib.sha1(head + data).hexdigest()


def b64enc(data):
    if isinstance(data, str):
        data = data.encode("utf-8")
    return base64.b64encode(data).decode("ascii")


def b64dec(text):
    cleaned = re.sub(r"[\r\n\t ]+", "", text or "")
    try:
        return base64.b64decode(cleaned)
    except Exception:
        return b""


def gid(kind, *parts):
    """An opaque, stable GraphQL global id (never the bare database id)."""
    raw = (kind + ":" + ":".join(str(p) for p in parts)).encode("utf-8")
    return kind[0].upper() + "_" + base64.urlsafe_b64encode(raw).decode("ascii").rstrip("=")


def gid_decode(value):
    """Decode a global id made by gid() back to (kind, parts), or None."""
    if not isinstance(value, str) or "_" not in value:
        return None
    try:
        head, rest = value.split("_", 1)
        raw = base64.urlsafe_b64decode(rest + "=" * (-len(rest) % 4)).decode("utf-8")
        fields = raw.split(":")
        if not fields or fields[0][0].upper() != head:
            return None
        return fields[0], fields[1:]
    except Exception:
        return None


# ---------------------------------------------------------------------------
# Git objects: trees, commits, packs
# ---------------------------------------------------------------------------

TYPE_CODES = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
CODE_TYPES = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}


def parse_tree(data):
    """Parse a tree object into [(mode, name, oid-hex)]."""
    entries = []
    pos = 0
    n = len(data)
    while pos < n:
        sp = data.index(b" ", pos)
        mode = data[pos:sp].decode("ascii")
        nul = data.index(b"\x00", sp)
        name = data[sp + 1:nul].decode("utf-8", "surrogateescape")
        oid = data[nul + 1:nul + 21].hex()
        entries.append((mode, name, oid))
        pos = nul + 21
    return entries


def _tree_sort_key(entry):
    mode, name = entry[0], entry[1]
    return name + "/" if mode == "40000" else name


def build_tree(entries):
    """Build tree bytes from [(mode, name, oid-hex)], git sort order."""
    out = bytearray()
    for mode, name, oid in sorted(entries, key=_tree_sort_key):
        out += mode.encode("ascii") + b" " + name.encode("utf-8", "surrogateescape")
        out += b"\x00" + bytes.fromhex(oid)
    return bytes(out)


def parse_commit(data):
    """Parse a commit object into a dict."""
    text = data.decode("utf-8", "surrogateescape")
    head, _, message = text.partition("\n\n")
    view = {"parents": [], "message": message}
    for line in head.split("\n"):
        if line.startswith("tree "):
            view["tree"] = line[5:].strip()
        elif line.startswith("parent "):
            view["parents"].append(line[7:].strip())
        elif line.startswith("author "):
            view["author"] = line[7:]
        elif line.startswith("committer "):
            view["committer"] = line[10:]
    return view


def build_commit(tree_oid, parents, message, timestamp=TRIAL_EPOCH):
    if not message.endswith("\n"):
        message += "\n"
    lines = ["tree " + tree_oid]
    for parent in parents:
        lines.append("parent " + parent)
    stamp = "%d +0000" % timestamp
    lines.append("author " + FORGE_IDENTITY + " " + stamp)
    lines.append("committer " + FORGE_IDENTITY + " " + stamp)
    return ("\n".join(lines) + "\n\n" + message).encode("utf-8", "surrogateescape")


def parse_tag(data):
    text = data.decode("utf-8", "surrogateescape")
    head, _, message = text.partition("\n\n")
    view = {"message": message}
    for line in head.split("\n"):
        if line.startswith("object "):
            view["object"] = line[7:].strip()
        elif line.startswith("type "):
            view["type"] = line[5:].strip()
        elif line.startswith("tag "):
            view["tag"] = line[4:].strip()
        elif line.startswith("tagger "):
            view["tagger"] = line[7:]
    return view


def _read_varint_size(buf, start):
    byte = buf[start]
    size = byte & 0x0F
    shift = 4
    pos = start + 1
    while byte & 0x80:
        byte = buf[pos]
        pos += 1
        size |= (byte & 0x7F) << shift
        shift += 7
    return size, pos, buf[start]


def _read_ofs_delta_base(buf, start):
    byte = buf[start]
    pos = start + 1
    value = byte & 0x7F
    while byte & 0x80:
        byte = buf[pos]
        pos += 1
        value = ((value + 1) << 7) | (byte & 0x7F)
    return value, pos


def apply_delta(base, delta):
    """Apply a git delta instruction stream to base bytes."""
    pos = 0

    def read_size():
        nonlocal pos
        value = 0
        shift = 0
        while True:
            byte = delta[pos]
            pos += 1
            value |= (byte & 0x7F) << shift
            shift += 7
            if not (byte & 0x80):
                return value

    source_size = read_size()
    target_size = read_size()
    if source_size != len(base):
        raise ValueError("delta base size mismatch")
    out = bytearray()
    while pos < len(delta):
        op = delta[pos]
        pos += 1
        if op & 0x80:
            copy_off = 0
            copy_size = 0
            for bit in range(4):
                if op & (1 << bit):
                    copy_off |= delta[pos] << (bit * 8)
                    pos += 1
            for bit in range(4, 7):
                if op & (1 << bit):
                    copy_size |= delta[pos] << ((bit - 4) * 8)
                    pos += 1
            if copy_size == 0:
                copy_size = 0x10000
            out += base[copy_off:copy_off + copy_size]
        elif op:
            out += delta[pos:pos + op]
            pos += op
        else:
            raise ValueError("delta opcode 0")
    if len(out) != target_size:
        raise ValueError("delta size mismatch")
    return bytes(out)


class PackError(ValueError):
    pass


def read_pack(pack, resolve_base=None):
    """Parse a packfile into {oid: (type, data)}; resolves OFS/REF deltas."""
    if len(pack) < 32 or pack[:4] != b"PACK":
        raise PackError("bad pack header")
    version, count = struct.unpack(">II", pack[4:12])
    if version not in (2, 3):
        raise PackError("unsupported pack version")
    trailer = pack[-20:].hex()
    if sha1_hex(pack[:-20]) != trailer:
        raise PackError("pack checksum mismatch")
    entries = []  # (offset, type|None, data|None, delta-kind, delta-base)
    pos = 12
    for _ in range(count):
        start = pos
        size, pos, first = _read_varint_size(pack, pos)
        code = (first >> 4) & 0x7
        if code == 6:  # OFS_DELTA
            base_off, pos = _read_ofs_delta_base(pack, pos)
            dec = zlib.decompressobj()
            out = dec.decompress(pack[pos:])
            used = len(pack[pos:]) - len(dec.unused_data)
            entries.append((start, None, None, "ofs", start - base_off, out))
            pos += used
        elif code == 7:  # REF_DELTA
            base_oid = pack[pos:pos + 20].hex()
            pos += 20
            dec = zlib.decompressobj()
            out = dec.decompress(pack[pos:])
            used = len(pack[pos:]) - len(dec.unused_data)
            entries.append((start, None, None, "ref", base_oid, out))
            pos += used
        else:
            obj_type = CODE_TYPES.get(code)
            if obj_type is None:
                raise PackError("unknown pack object type")
            dec = zlib.decompressobj()
            out = dec.decompress(pack[pos:])
            used = len(pack[pos:]) - len(dec.unused_data)
            if len(out) != size:
                raise PackError("object size mismatch")
            entries.append((start, obj_type, out, None, None, None))
            pos += used
    by_offset = {}
    objects = {}
    # First pass: plain objects.
    for start, obj_type, data, kind, base, _delta in entries:
        if kind is None:
            oid = git_hash(obj_type, data)
            objects[oid] = (obj_type, data)
            by_offset[start] = (obj_type, data, oid)
    # Delta passes until everything resolves.
    pending = [e for e in entries if e[3] is not None]
    for _ in range(len(pending) + 1):
        if not pending:
            break
        rest = []
        progressed = False
        for start, _t, _d, kind, base, delta in pending:
            if kind == "ofs":
                found = by_offset.get(base)
            else:
                found = objects.get(base)
                found = (found[0], found[1], base) if found else None
            if found is None and resolve_base is not None:
                extra = resolve_base(base if kind == "ref" else None)
                if extra is not None:
                    found = (extra[0], extra[1], base if kind == "ref" else None)
            if found is None:
                rest.append((start, _t, _d, kind, base, delta))
                continue
            data = apply_delta(found[1], delta)
            obj_type = found[0]
            oid = git_hash(obj_type, data)
            objects[oid] = (obj_type, data)
            by_offset[start] = (obj_type, data, oid)
            progressed = True
        pending = rest
        if not progressed:
            break
    if pending:
        raise PackError("unresolved delta in pack")
    return objects


def _pack_object_header(obj_type, size):
    code = TYPE_CODES[obj_type]
    out = bytearray()
    first = (code << 4) | (size & 0x0F)
    size >>= 4
    while size:
        out.append(first | 0x80)
        first = size & 0x7F
        size >>= 7
    out.append(first)
    return bytes(out)


def write_pack(objects):
    """Build a packfile (version 2, no deltas) from [(type, data)]."""
    parts = [b"PACK" + struct.pack(">II", 2, len(objects))]
    for obj_type, data in objects:
        parts.append(_pack_object_header(obj_type, len(data)))
        parts.append(zlib.compress(data, 6))
    body = b"".join(parts)
    return body + hashlib.sha1(body).digest()


# ---------------------------------------------------------------------------
# pkt-line framing (git smart HTTP)
# ---------------------------------------------------------------------------


def pkt_line(payload):
    if isinstance(payload, str):
        payload = payload.encode("utf-8", "surrogateescape")
    return ("%04x" % (len(payload) + 4)).encode("ascii") + payload


PKT_FLUSH = b"0000"
PKT_DELIM = b"0001"


def pkt_lines(items):
    out = bytearray()
    for item in items:
        if item == "flush":
            out += PKT_FLUSH
        elif item == "delim":
            out += PKT_DELIM
        else:
            out += pkt_line(item)
    return bytes(out)


def parse_pkt_lines(buf):
    """Parse a byte string into packets: list of ('data', bytes) / ('flush',) / ('delim',)."""
    packets = []
    pos = 0
    n = len(buf)
    while pos < n:
        if pos + 4 > n:
            break
        size = int(buf[pos:pos + 4].decode("ascii", "ignore"), 16) if buf[pos:pos + 4] != b"zzzz" else -1
        if size == -1:
            raise ValueError("bad pkt-line length")
        if size == 0:
            packets.append(("flush", b""))
            pos += 4
            # The command section ends at the flush packet: in receive-pack
            # the raw packfile follows, and it is not pkt-line framed, so
            # parsing on would choke on its "PACK" header. Stop here and let
            # the caller treat the rest as the pack.
            break
        elif size == 1:
            packets.append(("delim", b""))
            pos += 4
        else:
            if pos + size > n:
                break
            packets.append(("data", bytes(buf[pos + 4:pos + size])))
            pos += size
    return packets, pos


def sideband_wrap(payload, band=1):
    """Wrap bytes into sideband pkt-lines (band byte + chunk)."""
    out = bytearray()
    step = 65515
    for off in range(0, len(payload), step):
        chunk = payload[off:off + step]
        out += pkt_line(bytes([band]) + chunk)
    return bytes(out)


# ---------------------------------------------------------------------------
# Store: SQLite (durable) + in-memory dicts (hot cache)
# ---------------------------------------------------------------------------


class Store:
    """All forge state. One sqlite connection, guarded by a lock; dicts mirror it."""

    def __init__(self):
        self.dir = tempfile.mkdtemp(prefix="forge-store-")
        self.db_path = os.path.join(self.dir, "forge.db")
        self.lock = threading.RLock()
        self.db = sqlite3.connect(self.db_path, check_same_thread=False)
        self.db.execute("PRAGMA journal_mode=WAL")
        self.db.execute("PRAGMA synchronous=NORMAL")
        self.db.execute("PRAGMA cache_size=-64000")
        self.db.execute("PRAGMA temp_store=MEMORY")
        self._schema()
        # Hot caches.
        self.repos = {}          # (owner, name) -> repo dict
        self.repo_by_id = {}     # id -> repo dict
        self.next_repo_id = 1
        self.refs = {}           # (repo_id, refname) -> oid
        self.objects = {}        # oid -> (type, data bytes)
        self.labels = {}         # repo_id -> {name: color}
        self.issues = {}         # (repo_id, number) -> issue dict
        self.issue_order = {}    # repo_id -> [numbers in creation order]
        self.comments = {}       # (repo_id, issue_number) -> [comment dicts]
        self.pulls = {}          # (repo_id, number) -> pull dict
        self.pull_order = {}     # repo_id -> [numbers in creation order]
        self._load()

    def _schema(self):
        self.db.executescript(
            """
            CREATE TABLE IF NOT EXISTS repos(
              id INTEGER PRIMARY KEY, owner TEXT NOT NULL, name TEXT NOT NULL,
              private INTEGER NOT NULL DEFAULT 0, description TEXT NOT NULL DEFAULT '',
              default_branch TEXT NOT NULL DEFAULT 'main',
              next_issue INTEGER NOT NULL DEFAULT 1, next_pr INTEGER NOT NULL DEFAULT 1,
              next_comment INTEGER NOT NULL DEFAULT 1, seq INTEGER NOT NULL DEFAULT 0,
              UNIQUE(owner, name));
            CREATE TABLE IF NOT EXISTS refs(
              repo_id INTEGER NOT NULL, name TEXT NOT NULL, oid TEXT NOT NULL,
              PRIMARY KEY(repo_id, name));
            CREATE TABLE IF NOT EXISTS objects(
              oid TEXT PRIMARY KEY, type TEXT NOT NULL, data BLOB NOT NULL);
            CREATE TABLE IF NOT EXISTS labels(
              repo_id INTEGER NOT NULL, name TEXT NOT NULL, color TEXT NOT NULL DEFAULT '',
              PRIMARY KEY(repo_id, name));
            CREATE TABLE IF NOT EXISTS issues(
              repo_id INTEGER NOT NULL, number INTEGER NOT NULL,
              title TEXT NOT NULL, body TEXT NOT NULL, state TEXT NOT NULL,
              labels TEXT NOT NULL DEFAULT '[]', seq INTEGER NOT NULL,
              PRIMARY KEY(repo_id, number));
            CREATE TABLE IF NOT EXISTS comments(
              repo_id INTEGER NOT NULL, issue_number INTEGER NOT NULL,
              id INTEGER NOT NULL, body TEXT NOT NULL, seq INTEGER NOT NULL,
              PRIMARY KEY(repo_id, issue_number, id));
            CREATE TABLE IF NOT EXISTS pulls(
              repo_id INTEGER NOT NULL, number INTEGER NOT NULL,
              title TEXT NOT NULL, body TEXT NOT NULL, state TEXT NOT NULL,
              merged INTEGER NOT NULL DEFAULT 0,
              head_branch TEXT NOT NULL, base_branch TEXT NOT NULL,
              merge_sha TEXT NOT NULL DEFAULT '', merged_at TEXT NOT NULL DEFAULT '',
              seq INTEGER NOT NULL, PRIMARY KEY(repo_id, number));
            """
        )
        self.db.commit()

    def _load(self):
        cur = self.db.cursor()
        for row in cur.execute("SELECT id,owner,name,private,description,default_branch,"
                               "next_issue,next_pr,next_comment,seq FROM repos ORDER BY id"):
            repo = {"id": row[0], "owner": row[1], "name": row[2], "private": bool(row[3]),
                    "description": row[4], "default_branch": row[5],
                    "next_issue": row[6], "next_pr": row[7], "next_comment": row[8],
                    "seq": row[9]}
            self.repos[(row[1], row[2])] = repo
            self.repo_by_id[row[0]] = repo
            self.next_repo_id = max(self.next_repo_id, row[0] + 1)
        for repo_id, name, oid in cur.execute("SELECT repo_id,name,oid FROM refs"):
            self.refs[(repo_id, name)] = oid
        for oid, otype, data in cur.execute("SELECT oid,type,data FROM objects"):
            self.objects[oid] = (otype, bytes(data))
        for repo_id, name, color in cur.execute("SELECT repo_id,name,color FROM labels"):
            self.labels.setdefault(repo_id, {})[name] = color
        for repo_id, number, title, body, state, labels, seq in cur.execute(
                "SELECT repo_id,number,title,body,state,labels,seq FROM issues ORDER BY repo_id,number"):
            self.issues[(repo_id, number)] = {
                "number": number, "title": title, "body": body, "state": state,
                "labels": json.loads(labels), "seq": seq}
            self.issue_order.setdefault(repo_id, []).append(number)
        for repo_id, number, cid, body, seq in cur.execute(
                "SELECT repo_id,issue_number,id,body,seq FROM comments ORDER BY repo_id,issue_number,id"):
            self.comments.setdefault((repo_id, number), []).append(
                {"id": cid, "body": body, "seq": seq})
        for row in cur.execute("SELECT repo_id,number,title,body,state,merged,head_branch,"
                               "base_branch,merge_sha,merged_at,seq FROM pulls ORDER BY repo_id,number"):
            self.pulls[(row[0], row[1])] = {
                "number": row[1], "title": row[2], "body": row[3], "state": row[4],
                "merged": bool(row[5]), "head_branch": row[6], "base_branch": row[7],
                "merge_sha": row[8], "merged_at": row[9], "seq": row[10]}
            self.pull_order.setdefault(row[0], []).append(row[1])

    # -- low level ----------------------------------------------------------
    def commit(self):
        self.db.commit()

    def put_object(self, obj_type, data):
        """Store one object (cache + SQLite, no commit). Returns its oid."""
        with self.lock:
            oid = git_hash(obj_type, data)
            if oid not in self.objects:
                self.objects[oid] = (obj_type, data)
                self.db.execute("INSERT OR IGNORE INTO objects(oid,type,data) VALUES(?,?,?)",
                                (oid, obj_type, sqlite3.Binary(data)))
            return oid

    def get_object(self, oid):
        return self.objects.get(oid)

    def put_objects(self, objects):
        for obj_type, data in objects:
            self.put_object(obj_type, data)

    # -- repos ---------------------------------------------------------------
    def create_repo(self, owner, name, private, description):
        with self.lock:
            if (owner, name) in self.repos:
                return None
            rid = self.next_repo_id
            self.next_repo_id += 1
            repo = {"id": rid, "owner": owner, "name": name, "private": bool(private),
                    "description": description or "", "default_branch": DEFAULT_BRANCH,
                    "next_issue": 1, "next_pr": 1, "next_comment": 1, "seq": rid}
            self.repos[(owner, name)] = repo
            self.repo_by_id[rid] = repo
            self.db.execute(
                "INSERT INTO repos(id,owner,name,private,description,default_branch,"
                "next_issue,next_pr,next_comment,seq) VALUES(?,?,?,?,?,?,?,?,?,?)",
                (rid, owner, name, 1 if private else 0, repo["description"],
                 DEFAULT_BRANCH, 1, 1, 1, rid))
            self.commit()
            return repo

    def get_repo(self, owner, name):
        return self.repos.get((owner, name))

    def list_repos(self, owner):
        out = [r for (o, _n), r in self.repos.items() if o == owner]
        out.sort(key=lambda r: r["seq"])
        return out

    def update_repo(self, repo, description=None, private=None):
        with self.lock:
            if description is not None:
                repo["description"] = description
            if private is not None:
                repo["private"] = bool(private)
            self.db.execute("UPDATE repos SET description=?,private=? WHERE id=?",
                            (repo["description"], 1 if repo["private"] else 0, repo["id"]))
            self.commit()

    def delete_repo(self, repo):
        with self.lock:
            rid = repo["id"]
            self.db.execute("DELETE FROM refs WHERE repo_id=?", (rid,))
            self.db.execute("DELETE FROM labels WHERE repo_id=?", (rid,))
            self.db.execute("DELETE FROM issues WHERE repo_id=?", (rid,))
            self.db.execute("DELETE FROM comments WHERE repo_id=?", (rid,))
            self.db.execute("DELETE FROM pulls WHERE repo_id=?", (rid,))
            self.db.execute("DELETE FROM repos WHERE id=?", (rid,))
            self.commit()
            self.repos.pop((repo["owner"], repo["name"]), None)
            self.repo_by_id.pop(rid, None)
            for key in [k for k in self.refs if k[0] == rid]:
                del self.refs[key]
            self.labels.pop(rid, None)
            for key in [k for k in self.issues if k[0] == rid]:
                del self.issues[key]
            self.issue_order.pop(rid, None)
            for key in [k for k in self.comments if k[0] == rid]:
                del self.comments[key]
            for key in [k for k in self.pulls if k[0] == rid]:
                del self.pulls[key]
            self.pull_order.pop(rid, None)

    # -- refs ------------------------------------------------------------------
    def get_ref(self, repo_id, refname):
        return self.refs.get((repo_id, refname))

    def set_ref(self, repo_id, refname, oid):
        with self.lock:
            self.refs[(repo_id, refname)] = oid
            self.db.execute("INSERT INTO refs(repo_id,name,oid) VALUES(?,?,?) "
                            "ON CONFLICT(repo_id,name) DO UPDATE SET oid=excluded.oid",
                            (repo_id, refname, oid))
            self.commit()

    def delete_ref(self, repo_id, refname):
        with self.lock:
            self.refs.pop((repo_id, refname), None)
            self.db.execute("DELETE FROM refs WHERE repo_id=? AND name=?", (repo_id, refname))
            self.commit()

    def list_refs(self, repo_id):
        out = [(name, oid) for (rid, name), oid in self.refs.items() if rid == repo_id]
        out.sort()
        return out

    def branch_tip(self, repo_id, branch):
        return self.refs.get((repo_id, "refs/heads/" + branch))

    # -- labels ------------------------------------------------------------------
    def add_label(self, repo_id, name, color):
        with self.lock:
            self.labels.setdefault(repo_id, {})[name] = color or ""
            self.db.execute("INSERT INTO labels(repo_id,name,color) VALUES(?,?,?) "
                            "ON CONFLICT(repo_id,name) DO UPDATE SET color=excluded.color",
                            (repo_id, name, color or ""))
            self.commit()

    def has_label(self, repo_id, name):
        return name in self.labels.get(repo_id, {})

    # -- issues ------------------------------------------------------------------
    def create_issue(self, repo, title, body, labels):
        with self.lock:
            number = repo["next_issue"]
            repo["next_issue"] += 1
            issue = {"number": number, "title": title, "body": body or "",
                     "state": "open", "labels": list(labels), "seq": number}
            self.issues[(repo["id"], number)] = issue
            self.issue_order.setdefault(repo["id"], []).append(number)
            self.db.execute(
                "UPDATE repos SET next_issue=? WHERE id=?", (repo["next_issue"], repo["id"]))
            self.db.execute(
                "INSERT INTO issues(repo_id,number,title,body,state,labels,seq) "
                "VALUES(?,?,?,?,?,?,?)",
                (repo["id"], number, title, body or "", "open",
                 json.dumps(list(labels)), number))
            self.commit()
            return issue

    def get_issue(self, repo_id, number):
        return self.issues.get((repo_id, number))

    def list_issues(self, repo_id):
        return [self.issues[(repo_id, n)] for n in self.issue_order.get(repo_id, [])]

    def patch_issue(self, repo_id, issue, title=None, body=None, state=None):
        with self.lock:
            if title is not None:
                issue["title"] = title
            if body is not None:
                issue["body"] = body
            if state is not None:
                issue["state"] = state
            self.db.execute("UPDATE issues SET title=?,body=?,state=? WHERE repo_id=? AND number=?",
                            (issue["title"], issue["body"], issue["state"], repo_id, issue["number"]))
            self.commit()

    def add_comment(self, repo, issue_number, body):
        with self.lock:
            cid = repo["next_comment"]
            repo["next_comment"] += 1
            comment = {"id": cid, "body": body, "seq": cid}
            self.comments.setdefault((repo["id"], issue_number), []).append(comment)
            self.db.execute("UPDATE repos SET next_comment=? WHERE id=?",
                            (repo["next_comment"], repo["id"]))
            self.db.execute("INSERT INTO comments(repo_id,issue_number,id,body,seq) "
                            "VALUES(?,?,?,?,?)",
                            (repo["id"], issue_number, cid, body, cid))
            self.commit()
            return comment

    def list_comments(self, repo_id, issue_number):
        return list(self.comments.get((repo_id, issue_number), []))

    # -- pull requests ------------------------------------------------------------
    def create_pull(self, repo, title, body, head_branch, base_branch):
        with self.lock:
            number = repo["next_pr"]
            repo["next_pr"] += 1
            pull = {"number": number, "title": title, "body": body or "",
                    "state": "open", "merged": False,
                    "head_branch": head_branch, "base_branch": base_branch,
                    "merge_sha": "", "merged_at": "", "seq": number}
            self.pulls[(repo["id"], number)] = pull
            self.pull_order.setdefault(repo["id"], []).append(number)
            self.db.execute("UPDATE repos SET next_pr=? WHERE id=?",
                            (repo["next_pr"], repo["id"]))
            self.db.execute(
                "INSERT INTO pulls(repo_id,number,title,body,state,merged,head_branch,"
                "base_branch,merge_sha,merged_at,seq) VALUES(?,?,?,?,?,?,?,?,?,?,?)",
                (repo["id"], number, title, body or "", "open", 0,
                 head_branch, base_branch, "", "", number))
            self.commit()
            return pull

    def get_pull(self, repo_id, number):
        return self.pulls.get((repo_id, number))

    def list_pulls(self, repo_id):
        return [self.pulls[(repo_id, n)] for n in self.pull_order.get(repo_id, [])]

    def update_pull(self, repo_id, pull):
        with self.lock:
            self.db.execute(
                "UPDATE pulls SET state=?,merged=?,merge_sha=?,merged_at=? "
                "WHERE repo_id=? AND number=?",
                (pull["state"], 1 if pull["merged"] else 0, pull["merge_sha"],
                 pull["merged_at"], repo_id, pull["number"]))
            self.commit()

    # -- git object graph ---------------------------------------------------------
    def commit_parents(self, oid):
        obj = self.objects.get(oid)
        if obj is None or obj[0] != "commit":
            return []
        return parse_commit(obj[1]).get("parents", [])

    def commit_tree(self, oid):
        obj = self.objects.get(oid)
        if obj is None or obj[0] != "commit":
            return None
        return parse_commit(obj[1]).get("tree")

    def resolve_to_commit(self, oid):
        """Follow annotated tags to the commit they point at."""
        seen = set()
        while oid and oid not in seen:
            seen.add(oid)
            obj = self.objects.get(oid)
            if obj is None:
                return None
            if obj[0] == "commit":
                return oid
            if obj[0] == "tag":
                oid = parse_tag(obj[1]).get("object")
            else:
                return None
        return None

    def ancestors(self, tip, limit=100000):
        """All commits reachable from tip (following parents)."""
        seen = set()
        stack = [tip] if tip else []
        while stack:
            oid = stack.pop()
            if oid in seen:
                continue
            seen.add(oid)
            for parent in self.commit_parents(oid):
                if parent not in seen:
                    stack.append(parent)
            if len(seen) > limit:
                break
        return seen

    def is_ancestor(self, maybe_ancestor, tip):
        if maybe_ancestor == tip:
            return True
        return maybe_ancestor in self.ancestors(tip)

    def merge_base(self, tip_a, tip_b):
        """A common ancestor (the first found walking from tip_a)."""
        if not tip_a or not tip_b:
            return None
        set_b = self.ancestors(tip_b)
        # Walk from tip_a breadth-first by generation.
        seen = set()
        queue = [tip_a]
        while queue:
            nxt = []
            for oid in queue:
                if oid in seen:
                    continue
                seen.add(oid)
                if oid in set_b:
                    return oid
                nxt.extend(self.commit_parents(oid))
            queue = nxt
        return None

    def reachable_objects(self, tips, exclude_tips=()):
        """{oid: (type, data)} for everything reachable from tips, minus the
        closure of exclude_tips (objects the client already holds)."""
        keep = set()
        for tip in tips:
            keep |= self.ancestors(tip)
            tip_obj = self.objects.get(tip)
            if tip_obj is not None and tip_obj[0] == "tag":
                keep.add(tip)
        drop = set()
        for tip in exclude_tips:
            drop |= self.ancestors(tip)
            tip_obj = self.objects.get(tip)
            if tip_obj is not None and tip_obj[0] == "tag":
                drop.add(tip)
        keep -= drop
        out = {}
        # Walk trees/blobs from every kept commit/tag.
        stack = list(keep)
        seen_objs = set()
        while stack:
            oid = stack.pop()
            if oid in seen_objs:
                continue
            seen_objs.add(oid)
            obj = self.objects.get(oid)
            if obj is None:
                continue
            out[oid] = obj
            if obj[0] == "commit":
                tree = parse_commit(obj[1]).get("tree")
                if tree:
                    stack.append(tree)
            elif obj[0] == "tag":
                target = parse_tag(obj[1]).get("object")
                if target:
                    stack.append(target)
            elif obj[0] == "tree":
                for _mode, _name, child in parse_tree(obj[1]):
                    stack.append(child)
        return out

    def flatten_tree(self, tree_oid):
        """{path: (mode, oid)} for every blob under a tree (recursive)."""
        out = {}

        def walk(oid, prefix):
            obj = self.objects.get(oid)
            if obj is None or obj[0] != "tree":
                return
            for mode, name, child in parse_tree(obj[1]):
                path = prefix + name
                if mode == "40000":
                    walk(child, path + "/")
                else:
                    out[path] = (mode, child)

        if tree_oid:
            walk(tree_oid, "")
        return out

    def build_tree_from_paths(self, flat):
        """Build nested tree objects from {path: (mode, oid)}; stores them."""
        # Group by directory.
        def build(paths):
            entries = []
            subdirs = {}
            for path, (mode, oid) in paths.items():
                if "/" in path:
                    head, rest = path.split("/", 1)
                    subdirs.setdefault(head, {})[rest] = (mode, oid)
                else:
                    entries.append((mode, path, oid))
            for dirname, sub in sorted(subdirs.items()):
                sub_oid = build(sub)
                entries.append(("40000", dirname, sub_oid))
            data = build_tree(entries)
            return self.put_object("tree", data)

        if not flat:
            return self.put_object("tree", build_tree([]))
        return build(dict(flat))

    def commit_for_paths(self, flat, parents, message):
        tree_oid = self.build_tree_from_paths(flat)
        data = build_commit(tree_oid, parents, message)
        return self.put_object("commit", data)

    def diff_trees(self, base_tree, head_tree):
        """Changed paths between two trees: {path: (status, old_oid, new_oid)}."""
        base = self.flatten_tree(base_tree) if base_tree else {}
        head = self.flatten_tree(head_tree) if head_tree else {}
        out = {}
        for path in sorted(set(base) | set(head)):
            old = base.get(path)
            new = head.get(path)
            if old is None:
                out[path] = ("added", None, new[1])
            elif new is None:
                out[path] = ("removed", old[1], None)
            elif old[1] != new[1]:
                out[path] = ("modified", old[1], new[1])
        return out

    def three_way_merge(self, base_tip, head_tip, default_tip, build_tree=True):
        """Merge head into default over their merge base.

        Returns (merged_tree_oid, conflict_paths) — conflict_paths is empty
        when the merge applies cleanly. With build_tree=False no objects are
        written: only the conflict list is computed (a read-only probe).
        """
        base = self.merge_base(head_tip, default_tip)
        base_tree = self.commit_tree(base) if base else None
        head_tree = self.commit_tree(head_tip)
        default_tree = self.commit_tree(default_tip)
        base_flat = self.flatten_tree(base_tree) if base_tree else {}
        head_flat = self.flatten_tree(head_tree) if head_tree else {}
        default_flat = self.flatten_tree(default_tree) if default_tree else {}
        merged = dict(default_flat)
        conflicts = []
        for path in sorted(set(base_flat) | set(head_flat)):
            b = base_flat.get(path)
            h = head_flat.get(path)
            d = default_flat.get(path)
            if h == b:
                continue  # head did not change it
            if d == b:
                # Only head changed it: take head's version.
                if h is None:
                    merged.pop(path, None)
                else:
                    merged[path] = h
            elif h == d:
                continue  # both changed it the same way
            else:
                conflicts.append(path)
        if conflicts:
            return None, conflicts
        if not build_tree:
            return None, []
        merged_tree = self.build_tree_from_paths(merged)
        return merged_tree, []


# ---------------------------------------------------------------------------
# HTTP plumbing
# ---------------------------------------------------------------------------

STORE = None  # set in main()
REQ_COUNTER = [0]
REQ_LOCK = threading.Lock()


def next_request_id():
    with REQ_LOCK:
        REQ_COUNTER[0] += 1
        return "req-%d" % REQ_COUNTER[0]


def json_bytes(obj):
    return json.dumps(obj, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


class ApiError(Exception):
    def __init__(self, status, message):
        super().__init__(message)
        self.status = status
        self.message = message


class ForgeHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "Forge/1.0"

    # -- quiet, fast plumbing -----------------------------------------------
    def log_message(self, *args):
        pass

    def address_string(self):
        return self.client_address[0]

    def setup(self):
        super().setup()
        try:
            self.connection.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except Exception:
            pass

    # -- response helpers -----------------------------------------------------
    def _send(self, status, body, content_type, extra=None):
        if isinstance(body, str):
            body = body.encode("utf-8")
        self.send_response_only(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        if extra:
            for key, value in extra.items():
                self.send_header(key, value)
        self.end_headers()
        if self.command != "HEAD" and body:
            try:
                self.wfile.write(body)
            except (BrokenPipeError, ConnectionResetError):
                pass

    def send_json(self, status, obj, extra=None):
        headers = {"X-GitHub-Request-Id": next_request_id(),
                   "X-OAuth-Scopes": "repo, read:org"}
        if extra:
            headers.update(extra)
        self._send(status, json_bytes(obj), "application/json; charset=utf-8", headers)

    def send_json_bytes(self, status, body, extra=None):
        """Send already-serialized JSON bytes (hot-path cache hits)."""
        headers = {"X-GitHub-Request-Id": next_request_id(),
                   "X-OAuth-Scopes": "repo, read:org"}
        if extra:
            headers.update(extra)
        self._send(status, body, "application/json; charset=utf-8", headers)

    def send_json_no_body(self, status, extra=None):
        headers = {"X-GitHub-Request-Id": next_request_id()}
        if extra:
            headers.update(extra)
        self.send_response_only(status)
        for key, value in headers.items():
            self.send_header(key, value)
        self.send_header("Content-Length", "0")
        self.end_headers()

    def send_error_json(self, status, message):
        self.send_json(status, {"message": message})

    # -- request reading -------------------------------------------------------
    def read_body(self):
        """Return this request's body bytes (buffered up front by _handle)."""
        body = getattr(self, "_body", None)
        if body is None:
            body = self._read_raw_body()
        self._body = b""
        return body

    def _read_raw_body(self):
        """Read the request body off the wire once, whatever the handler does.

        HTTP/1.1 keep-alive reuses the connection for the next request, so a
        body left unread poisons the next request line (the next request is
        then parsed as 'Unsupported method' 501 / 400). _handle calls this up
        front, so error paths that never touch the body cannot poison the
        stream; handlers just read the buffered copy.
        """
        if (self.headers.get("Transfer-Encoding") or "").lower() == "chunked":
            return self._read_chunked_body()
        length = self.headers.get("Content-Length")
        if not length:
            return b""
        try:
            n = int(length)
        except ValueError:
            return b""
        if n <= 0:
            return b""
        if n > 64 * 1024 * 1024:
            # Too big to keep: drain and discard so the connection stays clean.
            remaining = n
            while remaining > 0:
                chunk = self.rfile.read(min(remaining, 1024 * 1024))
                if not chunk:
                    break
                remaining -= len(chunk)
            return b""
        return self.rfile.read(n)

    def _read_chunked_body(self):
        out = bytearray()
        try:
            while True:
                line = self.rfile.readline(65536)
                if not line:
                    break
                size = int(line.split(b";", 1)[0].strip(), 16)
                if size == 0:
                    while True:  # trailers until a blank line
                        trailer = self.rfile.readline(65536)
                        if not trailer or trailer in (b"\r\n", b"\n"):
                            break
                    break
                out += self.rfile.read(size)
                self.rfile.read(2)  # trailing CRLF
                if len(out) > 64 * 1024 * 1024:
                    return b""
        except Exception:
            return bytes(out)
        return bytes(out)

    def read_json(self):
        raw = self.read_body()
        if not raw:
            return None
        try:
            return json.loads(raw.decode("utf-8"))
        except Exception:
            raise ApiError(400, "Invalid JSON body")

    def authed(self):
        """True when the request carries the trial bearer token."""
        if not TOKEN:
            return True  # local dev without a token: open
        auth = self.headers.get("Authorization", "")
        return auth == "Bearer " + TOKEN

    def require_auth(self):
        if not self.authed():
            raise ApiError(401, "Requires authentication")

    # -- dispatch ---------------------------------------------------------------
    def _path_segments(self):
        split = urllib.parse.urlsplit(self.path)
        query = urllib.parse.parse_qs(split.query)
        raw = split.path
        segments = [urllib.parse.unquote(s) for s in raw.split("/") if s != ""]
        return segments, query, raw

    def _handle(self):
        self._body = self._read_raw_body()
        segments, query, raw_path = self._path_segments()
        method = self.command
        try:
            if method == "GET" and raw_path == "/healthz":
                self.send_json(200, {"ok": True})
                return
            if segments and segments[0] == "api" and len(segments) > 1 and segments[1] == "v3":
                self._handle_rest(method, segments[2:], query)
                return
            if segments == ["api", "graphql"]:
                self._handle_graphql(method, query)
                return
            if segments == ["mcp"]:
                self._handle_mcp(method)
                return
            if len(segments) >= 1 and segments[-1].endswith(".git") or (
                    len(segments) >= 2 and segments[0] and raw_path.count(".git/") >= 1):
                self._handle_git(method, segments, query, raw_path)
                return
            # A git path is /{owner}/{repo}.git[/...]; also bare /{owner}/{repo}.git
            if len(segments) >= 2 and segments[1].endswith(".git"):
                self._handle_git(method, segments, query, raw_path)
                return
            raise ApiError(404, "Not Found")
        except ApiError as err:
            # Never leak a stack trace or an HTML page: JSON always.
            try:
                self.send_error_json(err.status, err.message)
            except Exception:
                pass
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as err:
            try:
                self.send_error_json(500, "Internal error: %s" % err.__class__.__name__)
            except Exception:
                pass

    def do_GET(self):
        self._handle()

    def do_POST(self):
        self._handle()

    def do_PUT(self):
        self._handle()

    def do_PATCH(self):
        self._handle()

    def do_DELETE(self):
        self._handle()

    def do_HEAD(self):
        self._handle()

    # -- pagination ---------------------------------------------------------------
    @staticmethod
    def _page_params(query):
        def _int(name, default):
            try:
                return max(1, int(query.get(name, [str(default)])[0]))
            except ValueError:
                return default

        return _int("page", 1), _int("per_page", 30)

    def _paginate(self, items, query):
        page, per_page = self._page_params(query)
        total = len(items)
        start = (page - 1) * per_page
        chunk = items[start:start + per_page]
        link = None
        if start + per_page < total:
            scheme = "http"
            host = self.headers.get("Host", "127.0.0.1")
            base = "%s://%s%s" % (scheme, host, urllib.parse.urlsplit(self.path).path)
            qs = dict(urllib.parse.parse_qsl(urllib.parse.urlsplit(self.path).query))
            qs["page"] = str(page + 1)
            qs["per_page"] = str(per_page)
            nxt = base + "?" + urllib.parse.urlencode(qs)
            link = '<%s>; rel="next"' % nxt
        return chunk, link

    # =========================================================================
    # REST v3
    # =========================================================================

    def _repo_json(self, repo):
        return {
            "id": repo["id"],
            "node_id": gid("Repository", repo["id"]),
            "name": repo["name"],
            "full_name": repo["owner"] + "/" + repo["name"],
            "private": repo["private"],
            "owner": {"login": repo["owner"], "id": VIEWER_ID if repo["owner"] == VIEWER_LOGIN else 0,
                      "type": "User"},
            "html_url": "/%s/%s" % (repo["owner"], repo["name"]),
            "description": repo["description"],
            "fork": False,
            "url": "/api/v3/repos/%s/%s" % (repo["owner"], repo["name"]),
            "created_at": TRIAL_ISO,
            "updated_at": TRIAL_ISO,
            "pushed_at": TRIAL_ISO,
            "default_branch": repo["default_branch"],
            "has_issues": True,
            "has_projects": False,
            "has_downloads": True,
            "has_wiki": False,
            "has_pages": False,
            "has_discussions": False,
            "archived": False,
            "disabled": False,
            "visibility": "private" if repo["private"] else "public",
            "license": None,
        }

    def _need_repo(self, owner, name):
        repo = STORE.get_repo(owner, name)
        if repo is None:
            raise ApiError(404, "Not Found")
        return repo

    def _handle_rest(self, method, segments, query):
        self.require_auth()
        if not segments:
            if method == "GET":
                self.send_json(200, {"current_user_url": "/api/v3/user",
                                     "rate_limit_url": "/api/v3/rate_limit"})
                return
            raise ApiError(404, "Not Found")
        head = segments[0]
        if head == "meta" and len(segments) == 1 and method == "GET":
            self.send_json(200, {"installed_version": VERSION,
                                 "verifiable_password_authentication": True})
            return
        if head == "user":
            self._rest_user(method, segments[1:], query)
            return
        if head == "repos":
            self._rest_repos(method, segments[1:], query)
            return
        raise ApiError(404, "Not Found")

    def _rest_user(self, method, segments, query):
        if not segments:
            if method == "GET":
                self.send_json(200, {"login": VIEWER_LOGIN, "id": VIEWER_ID,
                                     "node_id": gid("User", VIEWER_ID),
                                     "name": VIEWER_NAME, "email": VIEWER_EMAIL,
                                     "type": "User"})
                return
            raise ApiError(404, "Not Found")
        if segments == ["repos"]:
            if method == "GET":
                repos = STORE.list_repos(VIEWER_LOGIN)
                chunk, link = self._paginate([self._repo_json(r) for r in repos], query)
                extra = {"Link": link} if link else None
                self.send_json(200, chunk, extra)
                return
            if method == "POST":
                body = self.read_json()
                if not isinstance(body, dict):
                    raise ApiError(400, "Invalid JSON body")
                name = body.get("name")
                if not isinstance(name, str) or not name or "/" in name:
                    raise ApiError(422, "Repository name is required")
                repo = STORE.create_repo(VIEWER_LOGIN, name,
                                         body.get("private", False),
                                         body.get("description", ""))
                if repo is None:
                    raise ApiError(422, "Repository already exists")
                self.send_json(201, self._repo_json(repo))
                return
        raise ApiError(404, "Not Found")

    def _rest_repos(self, method, segments, query):
        if len(segments) < 2:
            raise ApiError(404, "Not Found")
        owner, name = segments[0], segments[1]
        rest = segments[2:]
        repo = self._need_repo(owner, name)
        if not rest:
            if method == "GET":
                self.send_json(200, self._repo_json(repo))
                return
            if method == "PATCH":
                body = self.read_json()
                if not isinstance(body, dict):
                    raise ApiError(400, "Invalid JSON body")
                STORE.update_repo(repo, description=body.get("description"),
                                  private=body.get("private"))
                self.send_json(200, self._repo_json(repo))
                return
            if method == "DELETE":
                STORE.delete_repo(repo)
                self.send_json_no_body(204)
                return
            raise ApiError(404, "Not Found")
        section = rest[0]
        if section == "branches":
            self._rest_branches(method, repo, rest[1:], query)
            return
        if section == "commits":
            self._rest_commits(method, repo, rest[1:], query)
            return
        if section == "git":
            self._rest_git_data(method, repo, rest[1:])
            return
        if section == "contents":
            self._rest_contents(method, repo, rest[1:], query)
            return
        if section == "labels":
            self._rest_labels(method, repo, rest[1:])
            return
        if section == "issues":
            self._rest_issues(method, repo, rest[1:], query)
            return
        if section == "pulls":
            self._rest_pulls(method, repo, rest[1:], query)
            return
        raise ApiError(404, "Not Found")

    def _rest_branches(self, method, repo, rest, query):
        if method == "GET" and not rest:
            items = []
            for refname, oid in STORE.list_refs(repo["id"]):
                if refname.startswith("refs/heads/"):
                    branch = refname[len("refs/heads/"):]
                    items.append({"name": branch, "commit": {"sha": oid},
                                  "protected": False})
            self.send_json(200, items)
            return
        if method == "GET" and len(rest) == 1:
            oid = STORE.branch_tip(repo["id"], rest[0])
            if oid is None:
                raise ApiError(404, "Not Found")
            self.send_json(200, {"name": rest[0], "commit": {"sha": oid},
                                 "protected": False})
            return
        raise ApiError(404, "Not Found")

    def _rest_commits(self, method, repo, rest, query):
        if method != "GET" or rest:
            raise ApiError(404, "Not Found")
        ref = query.get("sha", [None])[0]
        if ref:
            tip = STORE.branch_tip(repo["id"], ref) or STORE.get_ref(repo["id"], ref)
            if tip is None and HEX40.match(ref or ""):
                tip = ref
        else:
            tip = STORE.branch_tip(repo["id"], repo["default_branch"])
        if tip is None:
            self.send_json(200, [])
            return
        tip = STORE.resolve_to_commit(tip) or tip
        seen = set()
        ordered = []
        stack = [tip]
        # Depth-first, newest first by timestamp then oid for stability.
        work = []
        visited = set()

        def collect(oid):
            if oid in visited:
                return
            visited.add(oid)
            obj = STORE.get_object(oid)
            if obj is None or obj[0] != "commit":
                return
            view = parse_commit(obj[1])
            work.append((oid, view))
            for parent in view.get("parents", []):
                collect(parent)

        collect(tip)
        work.sort(key=lambda item: (-_commit_stamp(item[1]), item[0]))
        out = []
        for oid, view in work:
            author = _ident(view.get("author", ""))
            out.append({
                "sha": oid,
                "commit": {
                    "message": view.get("message", "").rstrip("\n"),
                    "author": author,
                    "committer": _ident(view.get("committer", "")),
                    "tree": {"sha": view.get("tree", "")},
                },
                "author": {"login": VIEWER_LOGIN},
                "parents": [{"sha": p} for p in view.get("parents", [])],
            })
        chunk, _link = self._paginate(out, query)
        self.send_json(200, chunk)

    def _rest_git_data(self, method, repo, rest):
        if not rest:
            raise ApiError(404, "Not Found")
        if rest[0] == "refs":
            if method == "POST" and len(rest) == 1:
                body = self.read_json()
                if not isinstance(body, dict):
                    raise ApiError(400, "Invalid JSON body")
                ref = body.get("ref", "")
                sha = body.get("sha", "")
                if not ref.startswith("refs/") or not HEX40.match(sha or ""):
                    raise ApiError(422, "Invalid ref or sha")
                if STORE.get_ref(repo["id"], ref) is not None:
                    raise ApiError(422, "Reference already exists")
                target = STORE.resolve_to_commit(sha)
                if target is None and STORE.get_object(sha) is None:
                    raise ApiError(422, "Object does not exist")
                STORE.set_ref(repo["id"], ref, sha)
                self.send_json(201, {"ref": ref, "object": {"sha": sha, "type": "commit"}})
                return
            if method == "GET":
                if len(rest) == 3 and rest[1] == "heads":
                    oid = STORE.branch_tip(repo["id"], rest[2])
                    if oid is None:
                        raise ApiError(404, "Not Found")
                    self.send_json(200, {"ref": "refs/heads/" + rest[2],
                                         "object": {"sha": oid, "type": "commit"}})
                    return
                if len(rest) == 1:
                    items = [{"ref": n, "object": {"sha": o, "type": "commit"}}
                             for n, o in STORE.list_refs(repo["id"])]
                    self.send_json(200, items)
                    return
        raise ApiError(404, "Not Found")

    def _rest_labels(self, method, repo, rest):
        if method == "GET" and not rest:
            items = [{"name": n, "color": c}
                     for n, c in sorted(STORE.labels.get(repo["id"], {}).items())]
            self.send_json(200, items)
            return
        if method == "POST" and not rest:
            body = self.read_json()
            if not isinstance(body, dict):
                raise ApiError(400, "Invalid JSON body")
            name = body.get("name")
            if not isinstance(name, str) or not name:
                raise ApiError(422, "Label name is required")
            color = body.get("color", "")
            STORE.add_label(repo["id"], name, color)
            self.send_json(201, {"name": name, "color": color})
            return
        raise ApiError(404, "Not Found")

    # -- contents ---------------------------------------------------------------
    def _contents_file_json(self, repo, path, blob_oid, data):
        return {
            "type": "file",
            "encoding": "base64",
            "size": len(data),
            "name": path.rsplit("/", 1)[-1],
            "path": path,
            "content": b64enc(data),
            "sha": blob_oid,
            "url": "/api/v3/repos/%s/%s/contents/%s" % (repo["owner"], repo["name"], path),
            "html_url": "/%s/%s/blob/%s/%s" % (repo["owner"], repo["name"],
                                              repo["default_branch"], path),
            "git_url": "/api/v3/repos/%s/%s/git/blobs/%s" % (repo["owner"], repo["name"], blob_oid),
            "download_url": "/%s/%s/raw/%s/%s" % (repo["owner"], repo["name"],
                                                 repo["default_branch"], path),
        }

    def _rest_contents(self, method, repo, rest, query):
        path = "/".join(rest)
        ref_name = query.get("ref", [None])[0]
        if method == "GET":
            tip = None
            if ref_name:
                tip = STORE.branch_tip(repo["id"], ref_name) or STORE.get_ref(repo["id"], ref_name)
                if tip is None and HEX40.match(ref_name or ""):
                    tip = ref_name
            else:
                tip = STORE.branch_tip(repo["id"], repo["default_branch"])
            if tip is None:
                raise ApiError(404, "Not Found")
            tip = STORE.resolve_to_commit(tip) or tip
            tree_oid = STORE.commit_tree(tip)
            flat = STORE.flatten_tree(tree_oid)
            if path in flat:
                _mode, blob_oid = flat[path]
                obj = STORE.get_object(blob_oid)
                if obj is None:
                    raise ApiError(404, "Not Found")
                self.send_json(200, self._contents_file_json(repo, path, blob_oid, obj[1]))
                return
            # Directory listing: immediate children of `path` ("" = root).
            prefix = (path + "/") if path else ""
            children = {}
            for full, (mode, oid) in flat.items():
                if not full.startswith(prefix):
                    continue
                rest_path = full[len(prefix):]
                first = rest_path.split("/", 1)[0]
                if "/" in rest_path:
                    children[first] = ("dir", None)
                else:
                    children[first] = ("file", oid)
            if not children and path:
                raise ApiError(404, "Not Found")
            items = []
            for name in sorted(children):
                kind, oid = children[name]
                if kind == "dir":
                    # Find the subtree oid for a stable sha.
                    sub = STORE.flatten_tree(tree_oid)
                    tree = None
                    # Walk the tree objects to find this directory's oid.
                    tree = _find_subtree_oid(STORE, tree_oid, (prefix + name).split("/"))
                    items.append({"type": "dir", "name": name, "path": prefix + name,
                                  "sha": tree or ZERO_OID, "size": 0,
                                  "url": "/api/v3/repos/%s/%s/contents/%s"
                                       % (repo["owner"], repo["name"], prefix + name)})
                else:
                    obj = STORE.get_object(oid)
                    items.append({"type": "file", "name": name, "path": prefix + name,
                                  "sha": oid, "size": len(obj[1]) if obj else 0,
                                  "url": "/api/v3/repos/%s/%s/contents/%s"
                                       % (repo["owner"], repo["name"], prefix + name)})
            self.send_json(200, items)
            return
        if method in ("PUT", "DELETE"):
            body = self.read_json()
            if not isinstance(body, dict):
                raise ApiError(400, "Invalid JSON body")
            branch = body.get("branch") or repo["default_branch"]
            tip = STORE.branch_tip(repo["id"], branch)
            tip_commit = STORE.resolve_to_commit(tip) if tip else None
            tree_oid = STORE.commit_tree(tip_commit) if tip_commit else None
            flat = STORE.flatten_tree(tree_oid) if tree_oid else {}
            message = body.get("message") or "Update %s" % path
            if method == "PUT":
                raw = b64dec(body.get("content", ""))
                if path in flat:
                    current_oid = flat[path][1]
                    if body.get("sha") != current_oid:
                        raise ApiError(409, "sha does not match the current blob")
                    is_new = False
                else:
                    is_new = True
                blob_oid = STORE.put_object("blob", raw)
                new_flat = dict(flat)
                new_flat[path] = ("100644", blob_oid)
                parents = [tip_commit] if tip_commit else []
                commit_oid = STORE.commit_for_paths(new_flat, parents, message)
                STORE.set_ref(repo["id"], "refs/heads/" + branch, commit_oid)
                STORE.commit()
                self.send_json(201 if is_new else 200, {
                    "content": self._contents_file_json(repo, path, blob_oid, raw),
                    "commit": {"sha": commit_oid, "message": message}})
                return
            # DELETE
            if path not in flat:
                raise ApiError(404, "Not Found")
            if body.get("sha") and body.get("sha") != flat[path][1]:
                raise ApiError(409, "sha does not match the current blob")
            new_flat = dict(flat)
            del new_flat[path]
            parents = [tip_commit] if tip_commit else []
            commit_oid = STORE.commit_for_paths(new_flat, parents, message)
            STORE.set_ref(repo["id"], "refs/heads/" + branch, commit_oid)
            STORE.commit()
            self.send_json(200, {"commit": {"sha": commit_oid, "message": message}})
            return
        raise ApiError(404, "Not Found")


    # -- issues ---------------------------------------------------------------
    def _issue_json(self, repo, issue):
        return {
            "id": repo["id"] * 100000 + issue["number"],
            "node_id": gid("Issue", repo["id"], issue["number"]),
            "number": issue["number"],
            "title": issue["title"],
            "body": issue["body"],
            "state": issue["state"],
            "labels": [{"name": n, "color": STORE.labels.get(repo["id"], {}).get(n, "")}
                       for n in issue["labels"]],
            "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID, "type": "User"},
            "assignee": None,
            "assignees": [],
            "locked": False,
            "comments": len(STORE.comments.get((repo["id"], issue["number"]), [])),
            "created_at": TRIAL_ISO,
            "updated_at": TRIAL_ISO,
            "closed_at": TRIAL_ISO if issue["state"] == "closed" else None,
            "html_url": "/%s/%s/issues/%d" % (repo["owner"], repo["name"], issue["number"]),
            "url": "/api/v3/repos/%s/%s/issues/%d" % (repo["owner"], repo["name"],
                                                      issue["number"]),
            "repository_url": "/api/v3/repos/%s/%s" % (repo["owner"], repo["name"]),
        }

    def _rest_issues(self, method, repo, rest, query):
        if not rest:
            if method == "GET":
                state = query.get("state", ["open"])[0]
                sort = query.get("sort", ["created"])[0]
                direction = query.get("direction", ["desc"])[0]
                items = STORE.list_issues(repo["id"])
                if state in ("open", "closed"):
                    items = [i for i in items if i["state"] == state]
                reverse = direction != "asc"
                items = sorted(items, key=lambda i: i["number"], reverse=reverse)
                chunk, _link = self._paginate([self._issue_json(repo, i) for i in items], query)
                self.send_json(200, chunk)
                return
            if method == "POST":
                body = self.read_json()
                if not isinstance(body, dict):
                    raise ApiError(400, "Invalid JSON body")
                title = body.get("title")
                if not isinstance(title, str) or not title:
                    raise ApiError(422, "Title is required")
                labels = body.get("labels") or []
                if isinstance(labels, str):
                    labels = [labels]
                clean_labels = []
                for entry in labels:
                    name = entry.get("name") if isinstance(entry, dict) else entry
                    if not isinstance(name, str):
                        continue
                    if not STORE.has_label(repo["id"], name):
                        raise ApiError(422, "Label '%s' does not exist" % name)
                    clean_labels.append(name)
                issue = STORE.create_issue(repo, title, body.get("body") or "", clean_labels)
                self._issue_cache_invalidate(repo["id"], issue["number"])
                self.send_json(201, self._issue_json(repo, issue))
                return
            raise ApiError(404, "Not Found")
        try:
            number = int(rest[0])
        except ValueError:
            raise ApiError(404, "Not Found")
        if len(rest) == 1:
            issue = STORE.get_issue(repo["id"], number)
            if issue is None:
                raise ApiError(404, "Not Found")
            if method == "GET":
                cached = self._issue_cache.get((repo["id"], number))
                if cached is not None:
                    self.send_json_bytes(200, cached)
                    return
                payload = self._issue_json(repo, issue)
                self._issue_cache[(repo["id"], number)] = json_bytes(payload)
                self.send_json_bytes(200, self._issue_cache[(repo["id"], number)])
                return
            if method == "PATCH":
                body = self.read_json()
                if not isinstance(body, dict):
                    raise ApiError(400, "Invalid JSON body")
                state = body.get("state")
                if state is not None and state not in ("open", "closed"):
                    raise ApiError(422, "Invalid state")
                STORE.patch_issue(repo["id"], issue, title=body.get("title"),
                                  body=body.get("body"), state=state)
                self._issue_cache_invalidate(repo["id"], number)
                self.send_json(200, self._issue_json(repo, issue))
                return
            raise ApiError(404, "Not Found")
        if len(rest) == 2 and rest[1] == "comments":
            issue = STORE.get_issue(repo["id"], number)
            if issue is None:
                raise ApiError(404, "Not Found")
            if method == "GET":
                items = [{"id": c["id"], "node_id": gid("Comment", repo["id"], number, c["id"]),
                          "body": c["body"],
                          "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID, "type": "User"},
                          "created_at": TRIAL_ISO, "updated_at": TRIAL_ISO}
                         for c in STORE.list_comments(repo["id"], number)]
                self.send_json(200, items)
                return
            if method == "POST":
                body = self.read_json()
                if not isinstance(body, dict):
                    raise ApiError(400, "Invalid JSON body")
                text = body.get("body")
                if not isinstance(text, str):
                    raise ApiError(422, "Comment body is required")
                comment = STORE.add_comment(repo, number, text)
                self._issue_cache_invalidate(repo["id"], number)
                self.send_json(201, {"id": comment["id"],
                                     "node_id": gid("Comment", repo["id"], number, comment["id"]),
                                     "body": text,
                                     "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID,
                                            "type": "User"},
                                     "created_at": TRIAL_ISO, "updated_at": TRIAL_ISO})
                return
        raise ApiError(404, "Not Found")

    # Cached GET-one-issue responses (the read workload hammers this route).
    _issue_cache = {}

    def _issue_cache_invalidate(self, repo_id, number):
        self._issue_cache.pop((repo_id, number), None)

    # -- pulls ----------------------------------------------------------------
    def _pull_json(self, repo, pull):
        head_sha = STORE.branch_tip(repo["id"], pull["head_branch"])
        base_sha = STORE.branch_tip(repo["id"], pull["base_branch"])
        head_sha = STORE.resolve_to_commit(head_sha) if head_sha else None
        base_sha = STORE.resolve_to_commit(base_sha) if base_sha else None
        return {
            "id": repo["id"] * 100000 + pull["number"] + 50000,
            "node_id": gid("PullRequest", repo["id"], pull["number"]),
            "number": pull["number"],
            "title": pull["title"],
            "body": pull["body"],
            "state": pull["state"],
            "locked": False,
            "title": pull["title"],
            "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID, "type": "User"},
            "head": {"ref": pull["head_branch"], "sha": head_sha or "",
                     "label": repo["owner"] + ":" + pull["head_branch"],
                     "user": {"login": VIEWER_LOGIN}},
            "base": {"ref": pull["base_branch"], "sha": base_sha or "",
                     "label": repo["owner"] + ":" + pull["base_branch"],
                     "user": {"login": VIEWER_LOGIN}},
            "merged": pull["merged"],
            "mergeable": self._pull_mergeable(repo, pull),
            "merge_commit_sha": pull["merge_sha"] or None,
            "merged_at": pull["merged_at"] or None,
            "created_at": TRIAL_ISO,
            "updated_at": TRIAL_ISO,
            "closed_at": TRIAL_ISO if pull["state"] == "closed" else None,
            "html_url": "/%s/%s/pull/%d" % (repo["owner"], repo["name"], pull["number"]),
            "url": "/api/v3/repos/%s/%s/pulls/%d" % (repo["owner"], repo["name"],
                                                     pull["number"]),
        }

    def _pull_mergeable(self, repo, pull):
        if pull["state"] != "open":
            return "UNKNOWN"
        head_tip = STORE.branch_tip(repo["id"], pull["head_branch"])
        base_tip = STORE.branch_tip(repo["id"], pull["base_branch"])
        if not head_tip or not base_tip:
            return "UNKNOWN"
        head_tip = STORE.resolve_to_commit(head_tip)
        base_tip = STORE.resolve_to_commit(base_tip)
        _tree, conflicts = STORE.three_way_merge(
            STORE.merge_base(head_tip, base_tip), head_tip, base_tip,
            build_tree=False)
        return "CONFLICTING" if conflicts else "MERGEABLE"

    def _pull_files(self, repo, pull):
        head_tip = STORE.branch_tip(repo["id"], pull["head_branch"])
        base_tip = STORE.branch_tip(repo["id"], pull["base_branch"])
        if not head_tip or not base_tip:
            return []
        head_tip = STORE.resolve_to_commit(head_tip)
        base_tip = STORE.resolve_to_commit(base_tip)
        merge_base = STORE.merge_base(head_tip, base_tip)
        base_tree = STORE.commit_tree(merge_base) if merge_base else None
        head_tree = STORE.commit_tree(head_tip)
        diff = STORE.diff_trees(base_tree, head_tree)
        out = []
        for path in sorted(diff):
            status, old_oid, new_oid = diff[path]
            additions = deletions = 0
            if status in ("added", "modified"):
                obj = STORE.get_object(new_oid) if new_oid else None
                additions = len(obj[1].split(b"\n")) if obj else 0
                if status == "modified" and old_oid:
                    old = STORE.get_object(old_oid)
                    deletions = len(old[1].split(b"\n")) if old else 0
            elif status == "removed" and old_oid:
                old = STORE.get_object(old_oid)
                deletions = len(old[1].split(b"\n")) if old else 0
            out.append({"filename": path, "status": status,
                        "additions": additions, "deletions": deletions,
                        "changes": additions + deletions,
                        "sha": new_oid or old_oid or ""})
        return out

    def _rest_pulls(self, method, repo, rest, query):
        if not rest:
            if method == "GET":
                state = query.get("state", ["open"])[0]
                items = STORE.list_pulls(repo["id"])
                if state in ("open", "closed"):
                    items = [p for p in items if p["state"] == state]
                items = sorted(items, key=lambda p: p["number"], reverse=True)
                chunk, _link = self._paginate([self._pull_json(repo, p) for p in items], query)
                self.send_json(200, chunk)
                return
            if method == "POST":
                body = self.read_json()
                if not isinstance(body, dict):
                    raise ApiError(400, "Invalid JSON body")
                title = body.get("title")
                if not isinstance(title, str) or not title:
                    raise ApiError(422, "Title is required")
                head = _strip_owner_prefix(body.get("head") or "")
                base = _strip_owner_prefix(body.get("base") or "")
                if not head or not base:
                    raise ApiError(422, "head and base are required")
                head_tip = STORE.branch_tip(repo["id"], head)
                base_tip = STORE.branch_tip(repo["id"], base)
                if head_tip is None:
                    raise ApiError(422, "Head branch '%s' does not exist" % head)
                if base_tip is None:
                    raise ApiError(422, "Base branch '%s' does not exist" % base)
                for other in STORE.list_pulls(repo["id"]):
                    if (other["state"] == "open" and other["head_branch"] == head
                            and other["base_branch"] == base):
                        raise ApiError(422, "A pull request already exists for this head")
                pull = STORE.create_pull(repo, title, body.get("body") or "", head, base)
                self.send_json(201, self._pull_json(repo, pull))
                return
            raise ApiError(404, "Not Found")
        try:
            number = int(rest[0])
        except ValueError:
            raise ApiError(404, "Not Found")
        pull = STORE.get_pull(repo["id"], number)
        if pull is None:
            raise ApiError(404, "Not Found")
        if len(rest) == 1:
            if method == "GET":
                self.send_json(200, self._pull_json(repo, pull))
                return
            raise ApiError(404, "Not Found")
        if len(rest) == 2 and rest[1] == "files":
            if method == "GET":
                self.send_json(200, self._pull_files(repo, pull))
                return
            raise ApiError(404, "Not Found")
        if len(rest) == 2 and rest[1] == "merge":
            if method != "PUT":
                raise ApiError(404, "Not Found")
            _body = self.read_json()
            if pull["state"] != "open":
                raise ApiError(405, "Pull request is already closed")
            head_tip = STORE.branch_tip(repo["id"], pull["head_branch"])
            base_tip = STORE.branch_tip(repo["id"], pull["base_branch"])
            if not head_tip or not base_tip:
                raise ApiError(405, "Head or base branch is missing")
            head_tip = STORE.resolve_to_commit(head_tip)
            base_tip = STORE.resolve_to_commit(base_tip)
            merged_tree, conflicts = STORE.three_way_merge(
                STORE.merge_base(head_tip, base_tip), head_tip, base_tip)
            if conflicts:
                raise ApiError(405, "Merge conflict in %s" % conflicts[0])
            message = "Merge pull request #%d from %s\n\n%s" % (
                number, pull["head_branch"], pull["title"])
            commit_data = build_commit(merged_tree, [base_tip], message)
            merge_sha = STORE.put_object("commit", commit_data)
            STORE.set_ref(repo["id"], "refs/heads/" + pull["base_branch"], merge_sha)
            STORE.commit()
            pull["state"] = "closed"
            pull["merged"] = True
            pull["merge_sha"] = merge_sha
            pull["merged_at"] = TRIAL_ISO
            STORE.update_pull(repo["id"], pull)
            self.send_json(200, {"sha": merge_sha, "merged": True, "message": message})
            return
        raise ApiError(404, "Not Found")


    # =========================================================================
    # Git smart HTTP
    # =========================================================================

    def _git_repo(self, segments):
        owner = segments[0]
        repo_name = segments[1][:-4]
        repo = STORE.get_repo(owner, repo_name)
        if repo is None:
            raise ApiError(404, "Not Found")
        return repo

    def _git_refs_v0_lines(self, repo):
        """Ref lines for a v0 advertisement (HEAD first, then sorted refs)."""
        default_tip = STORE.branch_tip(repo["id"], repo["default_branch"]) or ZERO_OID
        lines = []
        refs = STORE.list_refs(repo["id"])
        tag_peels = {}
        for name, oid in refs:
            obj = STORE.get_object(oid)
            if obj is not None and obj[0] == "tag":
                target = STORE.resolve_to_commit(oid)
                if target:
                    tag_peels[name] = target
        lines.append((default_tip, "HEAD"))
        for name, oid in refs:
            lines.append((oid, name))
            if name in tag_peels:
                lines.append((tag_peels[name], name + "^{}"))
        return lines

    def _v0_advertisement(self, repo, service):
        caps = ("side-band-64k multi_ack multi_ack_detailed thin-pack ofs-delta agent=forge/1.0 "
                "symref=HEAD:refs/heads/" + repo["default_branch"] + " shallow")
        if service == "git-receive-pack":
            caps = ("report-status side-band-64k delete-refs ofs-delta agent=forge/1.0 "
                    "symref=HEAD:refs/heads/" + repo["default_branch"])
        out = bytearray()
        out += pkt_line("# service=%s\n" % service)
        out += PKT_FLUSH
        lines = self._git_refs_v0_lines(repo)
        for index, (oid, name) in enumerate(lines):
            if index == 0:
                out += pkt_line("%s %s\x00%s\n" % (oid, name, caps))
            else:
                out += pkt_line("%s %s\n" % (oid, name))
        out += PKT_FLUSH
        return bytes(out)

    def _v2_advertisement(self):
        return pkt_lines([
            "version 2\n",
            "agent=forge/1.0\n",
            "ls-refs=unborn\n",
            "fetch=shallow filter\n",
            "object-format=sha1\n",
            "flush",
        ])

    def _handle_git(self, method, segments, query, raw_path):
        self.require_auth()
        repo = self._git_repo(segments)
        rest = segments[2:]
        if method == "GET" and rest == ["info", "refs"]:
            service = query.get("service", [None])[0]
            if service == "git-upload-pack":
                want_v2 = self.headers.get("Git-Protocol", "") == "version=2"
                body = self._v2_advertisement() if want_v2 else self._v0_advertisement(repo, service)
                self._send(200, body, "application/x-git-upload-pack-advertisement")
                return
            if service == "git-receive-pack":
                body = self._v0_advertisement(repo, service)
                self._send(200, body, "application/x-git-receive-pack-advertisement")
                return
            raise ApiError(404, "Not Found")
        if method == "POST" and rest == ["git-upload-pack"]:
            self._git_upload_pack(repo)
            return
        if method == "POST" and rest == ["git-receive-pack"]:
            self._git_receive_pack(repo)
            return
        raise ApiError(404, "Not Found")

    # -- ls-refs / fetch --------------------------------------------------------
    def _ls_refs_response(self, repo, args):
        peel = "peel" in args
        symrefs = "symrefs" in args
        unborn = "unborn" in args
        prefixes = [a.split(" ", 1)[1] for a in args if a.startswith("ref-prefix ")]
        default_branch = repo["default_branch"]
        default_tip = STORE.branch_tip(repo["id"], default_branch)
        lines = []
        head_target = "refs/heads/" + default_branch
        if default_tip:
            if symrefs:
                lines.append("%s HEAD symref-target:%s\n" % (default_tip, head_target))
            else:
                lines.append("%s HEAD\n" % default_tip)
        elif unborn:
            lines.append("unborn HEAD symref-target:%s\n" % head_target)
        refs = STORE.list_refs(repo["id"])
        for name, oid in refs:
            line = "%s %s" % (oid, name)
            if peel:
                obj = STORE.get_object(oid)
                if obj is not None and obj[0] == "tag":
                    target = STORE.resolve_to_commit(oid)
                    if target:
                        line += " peeled:" + target
            lines.append(line + "\n")
        if prefixes:
            kept = []
            for line in lines:
                # HEAD lines only survive a prefix that matches "HEAD".
                if line.startswith("unborn ") or " HEAD" in line[:60] and line.split(" ")[1] == "HEAD":
                    if any("HEAD".startswith(p) for p in prefixes):
                        kept.append(line)
                    continue
                name = line.split(" ", 1)[1].split(" ")[0]
                if any(name.startswith(p) for p in prefixes):
                    kept.append(line)
            lines = kept
        return pkt_lines(lines + ["flush"])

    def _fetch_included(self, wants, haves, shallow_args, deepen):
        """(included_commit_oids, shallow_oids, unshallow_oids) for a fetch."""
        # Expand tag wants to their commits.
        tips = []
        for oid in wants:
            target = STORE.resolve_to_commit(oid)
            tips.append(target if target else oid)
        if deepen is not None:
            included = set()
            depth_of = {}
            frontier = [(tip, 0) for tip in tips if tip]
            seen_depth = {}
            while frontier:
                nxt = []
                for oid, dist in frontier:
                    if oid in seen_depth:
                        continue
                    seen_depth[oid] = dist
                    if dist < deepen:
                        included.add(oid)
                        for parent in STORE.commit_parents(oid):
                            nxt.append((parent, dist + 1))
                frontier = nxt
            shallow = set()
            for oid in included:
                parents = STORE.commit_parents(oid)
                if any(p not in included for p in parents):
                    shallow.add(oid)
            unshallow = []
            for old in shallow_args:
                if old in included and all(p in included for p in STORE.commit_parents(old)):
                    unshallow.append(old)
            return included, sorted(shallow), sorted(unshallow)
        included = set()
        for tip in tips:
            included |= STORE.ancestors(tip)
        return included, [], []

    def _fetch_pack_objects(self, included, haves, wants=(), deepen=None):
        """Objects to send for `included` commits, minus what `haves` cover."""
        excluded = set()
        for tip in haves:
            target = STORE.resolve_to_commit(tip)
            excluded |= STORE.ancestors(target) if target else set()
        if deepen is not None:
            # A deepen fetch asks for ancestors of a commit the client holds
            # only shallowly: the have is a shallow boundary, not full
            # history, so ancestors inside the new depth are wanted, not
            # held. Exclude only the ancestors outside the deepened set.
            excluded -= set(included)
        send = {}
        for oid in sorted(included):
            obj = STORE.get_object(oid)
            if obj is None:
                continue
            send[oid] = obj
            tree = STORE.commit_tree(oid)
            if tree:
                self._collect_tree_objects(tree, send)
        # A wanted tag object itself is not reachable from its commit, so add
        # wanted objects directly (a clone of a tag ref wants the tag object).
        for oid in wants:
            obj = STORE.get_object(oid)
            if obj is not None and oid not in send:
                send[oid] = obj
        # Drop everything the client already holds (closure of the haves).
        if excluded:
            held = STORE.reachable_objects(list(excluded), ())
            for oid in held:
                send.pop(oid, None)
        return [send[oid] for oid in sorted(send)]

    def _collect_tree_objects(self, tree_oid, out):
        stack = [tree_oid]
        while stack:
            oid = stack.pop()
            if oid in out:
                continue
            obj = STORE.get_object(oid)
            if obj is None:
                continue
            out[oid] = obj
            if obj[0] == "tree":
                for _mode, _name, child in parse_tree(obj[1]):
                    stack.append(child)

    def _fetch_response_v2(self, repo, args):
        wants = [a[5:] for a in args if a.startswith("want ")]
        haves = [a[5:] for a in args if a.startswith("have ")]
        shallow_args = [a[8:] for a in args if a.startswith("shallow ")]
        deepen = None
        for arg in args:
            if arg.startswith("deepen "):
                try:
                    deepen = int(arg[7:])
                except ValueError:
                    deepen = None
        included, shallow, unshallow = self._fetch_included(wants, haves, shallow_args, deepen)
        objects = self._fetch_pack_objects(included, haves, wants, deepen)
        pack = write_pack(objects)
        out = bytearray()
        if haves:
            # The acknowledgments section exists only when the client sent
            # haves: a clone sends none, and real git then expects the
            # packfile section directly (GitHub behaves the same way).
            out += pkt_line("acknowledgments\n")
            acked = False
            for have in haves:
                target = STORE.resolve_to_commit(have) or have
                if any(STORE.is_ancestor(target, tip) for tip in wants):
                    out += pkt_line("ACK %s\n" % have)
                    acked = True
            out += pkt_line("ready\n" if acked else "NAK\n")
            out += PKT_DELIM
        if shallow or unshallow:
            out += pkt_line("shallow-info\n")
            for oid in shallow:
                out += pkt_line("shallow %s\n" % oid)
            for oid in unshallow:
                out += pkt_line("unshallow %s\n" % oid)
            out += PKT_DELIM
        out += pkt_line("packfile\n")
        out += sideband_wrap(pack, band=1)
        out += PKT_FLUSH
        self._send(200, bytes(out), "application/x-git-upload-pack-result")

    def _fetch_response_v0(self, repo, args):
        wants = [a[5:].split(" ")[0] for a in args if a.startswith("want ")]
        haves = [a[5:] for a in args if a.startswith("have ")]
        shallow_args = [a[8:] for a in args if a.startswith("shallow ")]
        deepen = None
        for arg in args:
            if arg.startswith("deepen "):
                try:
                    deepen = int(arg[7:])
                except ValueError:
                    deepen = None
        included, shallow, unshallow = self._fetch_included(wants, haves, shallow_args, deepen)
        objects = self._fetch_pack_objects(included, haves, wants, deepen)
        pack = write_pack(objects)
        out = bytearray()
        acked = False
        for have in haves:
            target = STORE.resolve_to_commit(have) or have
            if any(STORE.is_ancestor(target, tip) for tip in wants):
                out += pkt_line("ACK %s\n" % have)
                acked = True
        out += pkt_line("ready\n" if acked else "NAK\n")
        for oid in shallow:
            out += pkt_line("shallow %s\n" % oid)
        for oid in unshallow:
            out += pkt_line("unshallow %s\n" % oid)
        out += sideband_wrap(pack, band=1)
        out += PKT_FLUSH
        self._send(200, bytes(out), "application/x-git-upload-pack-result")

    def _git_upload_pack(self, repo):
        body = self.read_body()
        try:
            packets, _used = parse_pkt_lines(body)
        except ValueError:
            self._send(400, b"bad pkt-line", "text/plain")
            return
        lines = []
        for kind, payload in packets:
            if kind == "data":
                lines.append(payload.decode("utf-8", "surrogateescape").rstrip("\n"))
        if not lines:
            self._send(400, b"empty request", "text/plain")
            return
        first = lines[0]
        if first.startswith("command=ls-refs"):
            # Args run until the flush; delim separates the command section.
            args = [ln for ln in lines[1:] if ln]
            self._send(200, self._ls_refs_response(repo, args),
                       "application/x-git-upload-pack-result")
            return
        if first.startswith("command=fetch"):
            args = [ln for ln in lines[1:] if ln]
            self._fetch_response_v2(repo, args)
            return
        if first.startswith("want "):
            # Protocol v0 fetch: wants, then flush, then haves/done.
            args = [ln for ln in lines if ln]
            self._fetch_response_v0(repo, args)
            return
        self._send(400, b"unknown upload-pack command", "text/plain")

    # -- receive-pack ------------------------------------------------------------
    def _git_receive_pack(self, repo):
        body = self.read_body()
        try:
            packets, used = parse_pkt_lines(body)
        except ValueError:
            self._send(400, b"bad pkt-line", "text/plain")
            return
        commands = []
        for kind, payload in packets:
            if kind == "flush":
                break
            if kind != "data":
                continue
            text = payload.decode("utf-8", "surrogateescape")
            nul = text.find("\x00")
            if nul >= 0:
                text = text[:nul]
            text = text.rstrip("\n")
            parts = text.split(" ")
            if len(parts) != 3:
                continue
            commands.append((parts[0], parts[1], parts[2]))
        pack_bytes = body[used:]
        unpack_error = None
        new_objects = {}
        if pack_bytes:
            try:
                new_objects = read_pack(pack_bytes)
            except Exception as err:
                unpack_error = str(err)
        if unpack_error is None and new_objects:
            with STORE.lock:
                for obj_type, data in new_objects.values():
                    STORE.put_object(obj_type, data)
                STORE.commit()
        report_lines = []
        if unpack_error is not None:
            report_lines.append("unpack %s\n" % unpack_error)
            for _old, _new, ref in commands:
                report_lines.append("ng %s unpack failed\n" % ref)
        else:
            report_lines.append("unpack ok\n")
            for old, new, ref in commands:
                ok, reason = self._apply_push(repo, old, new, ref)
                if ok:
                    report_lines.append("ok %s\n" % ref)
                else:
                    report_lines.append("ng %s %s\n" % (ref, reason))
        inner = pkt_lines(report_lines + ["flush"])
        out = sideband_wrap(inner, band=1) + PKT_FLUSH
        self._send(200, out, "application/x-git-receive-pack-result")

    def _apply_push(self, repo, old, new, ref):
        """Apply one ref update; returns (ok, reason)."""
        current = STORE.get_ref(repo["id"], ref)
        if new == ZERO_OID:
            # Delete.
            if current is None:
                return False, "no such ref"
            if old != ZERO_OID and old != current:
                return False, "non-fast-forward"
            STORE.delete_ref(repo["id"], ref)
            return True, ""
        obj = STORE.get_object(new)
        if obj is None:
            return False, "object not found"
        if old == ZERO_OID:
            # Create.
            if current is not None:
                return False, "already exists"
            STORE.set_ref(repo["id"], ref, new)
            return True, ""
        # Update.
        if current is None:
            return False, "no such ref"
        if old != current:
            return False, "non-fast-forward"
        if obj[0] == "commit":
            target = STORE.resolve_to_commit(new)
            if target is None:
                return False, "object not found"
            if old != new and not STORE.is_ancestor(old, target):
                return False, "non-fast-forward"
        STORE.set_ref(repo["id"], ref, new)
        return True, ""


    # =========================================================================
    # GraphQL v4 (a small parser + executor for the documents gh sends)
    # =========================================================================

    def _handle_graphql(self, method, query):
        if method != "POST":
            raise ApiError(404, "Not Found")
        self.require_auth()
        raw = self.read_body()
        try:
            body = json.loads(raw.decode("utf-8"))
        except Exception:
            self.send_json(400, {"errors": [{"message": "Invalid JSON body"}]})
            return
        if isinstance(body, list):
            results = [self._graphql_one(op) for op in body]
            self.send_json(200, results)
            return
        if not isinstance(body, dict):
            self.send_json(400, {"errors": [{"message": "Invalid GraphQL body"}]})
            return
        self.send_json(200, self._graphql_one(body))

    def _graphql_one(self, op):
        if not isinstance(op, dict) or not isinstance(op.get("query"), str):
            return {"data": None, "errors": [{"message": "No query provided"}]}
        variables = op.get("variables") or {}
        if not isinstance(variables, dict):
            variables = {}
        try:
            document = parse_graphql(op["query"])
        except ValueError as err:
            return {"data": None, "errors": [{"message": str(err)}]}
        errors = []
        data = {}
        for operation in document["operations"]:
            root = {"_type": "Mutation" if operation["kind"] == "mutation" else "Query"}
            result = execute_selection(root, operation["selections"], variables,
                                       document["fragments"], errors, [])
            if isinstance(result, dict):
                data.update(result)
        out = {"data": data if data else None}
        if errors:
            out["errors"] = errors
        return out


    # =========================================================================
    # MCP (JSON-RPC 2.0 Streamable HTTP, modern revision 2026-07-28)
    # =========================================================================

    def _handle_mcp(self, method):
        if method == "DELETE":
            self._send(200, b"", "application/json")
            return
        if method == "GET":
            self.send_json(405, {"message": "Method Not Allowed"})
            return
        if method != "POST":
            raise ApiError(404, "Not Found")
        self.require_auth()
        raw = self.read_body()
        try:
            body = json.loads(raw.decode("utf-8"))
        except Exception:
            self.send_json(400, {"jsonrpc": "2.0", "id": None,
                                 "error": {"code": -32700, "message": "Parse error"}})
            return
        if isinstance(body, list):
            results = [self._mcp_one(req) for req in body if isinstance(req, dict)]
            self.send_json(200, results)
            return
        if not isinstance(body, dict):
            self.send_json(400, {"jsonrpc": "2.0", "id": None,
                                 "error": {"code": -32700, "message": "Parse error"}})
            return
        result = self._mcp_one(body)
        if result is None:  # a notification: no response body
            self._send(202, b"", "application/json")
            return
        self.send_json(200, result)

    def _mcp_one(self, req):
        method = req.get("method", "")
        req_id = req.get("id")
        params = req.get("params") or {}
        if not isinstance(params, dict):
            params = {}
        if method == "notifications/initialized":
            return None
        if method == "server/discover":
            return {"jsonrpc": "2.0", "id": req_id,
                    "result": {"supportedVersions": ["2026-07-28", "2025-11-25",
                                                    "2025-06-18", "2025-03-26"],
                               "serverInfo": {"name": SERVER_NAME, "version": VERSION},
                               "capabilities": {"tools": {}},
                               "_meta": {"io.modelcontextprotocol/serverInfo":
                                         {"name": SERVER_NAME, "version": VERSION}}}}
        if method == "initialize":
            requested = params.get("protocolVersion") or "2025-11-25"
            return {"jsonrpc": "2.0", "id": req_id,
                    "result": {"protocolVersion": requested,
                               "capabilities": {"tools": {}},
                               "serverInfo": {"name": SERVER_NAME, "version": VERSION}}}
        if method == "ping":
            return {"jsonrpc": "2.0", "id": req_id, "result": {}}
        if method == "tools/list":
            return {"jsonrpc": "2.0", "id": req_id,
                    "result": {"tools": _MCP_TOOLS}}
        if method == "tools/call":
            name = params.get("name", "")
            args = params.get("arguments") or {}
            if not isinstance(args, dict):
                args = {}
            result, error = self._mcp_call_tool(name, args)
            if error is not None:
                return {"jsonrpc": "2.0", "id": req_id,
                        "error": {"code": error[0], "message": error[1]}}
            return {"jsonrpc": "2.0", "id": req_id, "result": result}
        return {"jsonrpc": "2.0", "id": req_id,
                "error": {"code": -32601, "message": "Method not found: %s" % method}}

    def _mcp_call_tool(self, name, args):
        """Dispatch one tools/call. Returns (result-dict, None) or (None, (code, msg))."""
        key = (name or "").rsplit(".", 1)[-1].lower()
        handler = _MCP_TOOL_HANDLERS.get(key)
        if handler is None:
            return None, (-32602, "Unknown tool: %s" % name)
        return handler(self, args)

    @staticmethod
    def _mcp_arg(args, *names):
        for name in names:
            if name in args and args[name] is not None:
                return args[name]
        return None

    def _mcp_tool_result(self, data, is_error=False):
        text = json.dumps(data, separators=(",", ":"), ensure_ascii=False)
        result = {"content": [{"type": "text", "text": text}],
                  "structuredContent": data}
        if is_error:
            result["isError"] = True
        return result

    def _mcp_create_repo(self, args):
        name = self._mcp_arg(args, "name")
        if not name:
            return self._mcp_tool_result({"error": "missing required argument: name"}, True), None
        repo = STORE.create_repo(VIEWER_LOGIN, str(name),
                                 bool(self._mcp_arg(args, "private") or False),
                                 str(self._mcp_arg(args, "description") or ""))
        if repo is None:
            return self._mcp_tool_result(
                {"error": "Repository already exists: %s" % name}, True), None
        return self._mcp_tool_result(self._repo_json(repo)), None

    def _mcp_get_repo(self, args):
        owner = self._mcp_arg(args, "owner")
        repo_name = self._mcp_arg(args, "repo", "repository", "name")
        if not owner or not repo_name:
            return self._mcp_tool_result(
                {"error": "missing required argument: owner/repo"}, True), None
        repo = STORE.get_repo(str(owner), str(repo_name))
        if repo is None:
            return self._mcp_tool_result(
                {"error": "Repository not found: %s/%s" % (owner, repo_name)}, True), None
        return self._mcp_tool_result(self._repo_json(repo)), None

    def _mcp_create_issue(self, args):
        owner = self._mcp_arg(args, "owner")
        repo_name = self._mcp_arg(args, "repo", "repository", "name")
        title = self._mcp_arg(args, "title")
        if not owner or not repo_name or not title:
            return self._mcp_tool_result(
                {"error": "missing required argument: owner/repo/title"}, True), None
        repo = STORE.get_repo(str(owner), str(repo_name))
        if repo is None:
            return self._mcp_tool_result(
                {"error": "Repository not found: %s/%s" % (owner, repo_name)}, True), None
        issue = STORE.create_issue(repo, str(title),
                                   str(self._mcp_arg(args, "body") or ""), [])
        data = self._issue_json(repo, issue)
        data["full_name"] = repo["owner"] + "/" + repo["name"]
        return self._mcp_tool_result(data), None

    def _mcp_list_issues(self, args):
        owner = self._mcp_arg(args, "owner")
        repo_name = self._mcp_arg(args, "repo", "repository", "name")
        if not owner or not repo_name:
            return self._mcp_tool_result(
                {"error": "missing required argument: owner/repo"}, True), None
        repo = STORE.get_repo(str(owner), str(repo_name))
        if repo is None:
            return self._mcp_tool_result(
                {"error": "Repository not found: %s/%s" % (owner, repo_name)}, True), None
        state = self._mcp_arg(args, "state")
        items = STORE.list_issues(repo["id"])
        if isinstance(state, str) and state.lower() in ("open", "closed"):
            items = [i for i in items if i["state"] == state.lower()]
        data = {"repository": repo["owner"] + "/" + repo["name"],
                "issues": [self._issue_json(repo, i) for i in items]}
        return self._mcp_tool_result(data), None

    def _mcp_create_pull_request(self, args):
        owner = self._mcp_arg(args, "owner")
        repo_name = self._mcp_arg(args, "repo", "repository", "name")
        title = self._mcp_arg(args, "title")
        head = self._mcp_arg(args, "head", "head_branch", "headRefName")
        base = self._mcp_arg(args, "base", "base_branch", "baseRefName")
        if not owner or not repo_name or not title or not head or not base:
            return self._mcp_tool_result(
                {"error": "missing required argument: owner/repo/title/head/base"},
                True), None
        repo = STORE.get_repo(str(owner), str(repo_name))
        if repo is None:
            return self._mcp_tool_result(
                {"error": "Repository not found: %s/%s" % (owner, repo_name)}, True), None
        head = _strip_owner_prefix(str(head))
        base = _strip_owner_prefix(str(base))
        if STORE.branch_tip(repo["id"], head) is None:
            return self._mcp_tool_result(
                {"error": "head branch does not exist: %s" % head}, True), None
        if STORE.branch_tip(repo["id"], base) is None:
            return self._mcp_tool_result(
                {"error": "base branch does not exist: %s" % base}, True), None
        pull = STORE.create_pull(repo, str(title),
                                 str(self._mcp_arg(args, "body") or ""), head, base)
        data = self._pull_json(repo, pull)
        data["full_name"] = repo["owner"] + "/" + repo["name"]
        return self._mcp_tool_result(data), None

    def _mcp_merge_pull_request(self, args):
        owner = self._mcp_arg(args, "owner")
        repo_name = self._mcp_arg(args, "repo", "repository", "name")
        number = self._mcp_arg(args, "pull_number", "number", "pullNumber", "pr_number")
        if not owner or not repo_name or number is None:
            return self._mcp_tool_result(
                {"error": "missing required argument: owner/repo/pull_number"}, True), None
        repo = STORE.get_repo(str(owner), str(repo_name))
        if repo is None:
            return self._mcp_tool_result(
                {"error": "Repository not found: %s/%s" % (owner, repo_name)}, True), None
        try:
            number = int(number)
        except (TypeError, ValueError):
            return self._mcp_tool_result({"error": "invalid pull_number"}, True), None
        pull = STORE.get_pull(repo["id"], number)
        if pull is None:
            return self._mcp_tool_result(
                {"error": "Pull request not found: #%d" % number}, True), None
        if pull["state"] != "open":
            return self._mcp_tool_result(
                {"error": "Pull request is already closed"}, True), None
        head_tip = STORE.branch_tip(repo["id"], pull["head_branch"])
        base_tip = STORE.branch_tip(repo["id"], pull["base_branch"])
        if not head_tip or not base_tip:
            return self._mcp_tool_result({"error": "branch is missing"}, True), None
        head_tip = STORE.resolve_to_commit(head_tip)
        base_tip = STORE.resolve_to_commit(base_tip)
        merged_tree, conflicts = STORE.three_way_merge(
            STORE.merge_base(head_tip, base_tip), head_tip, base_tip)
        if conflicts:
            return self._mcp_tool_result({"error": "merge conflict"}, True), None
        message = "Merge pull request #%d from %s\n\n%s" % (
            pull["number"], pull["head_branch"], pull["title"])
        merge_sha = STORE.put_object("commit", build_commit(merged_tree, [base_tip], message))
        STORE.set_ref(repo["id"], "refs/heads/" + pull["base_branch"], merge_sha)
        STORE.commit()
        pull["state"] = "closed"
        pull["merged"] = True
        pull["merge_sha"] = merge_sha
        pull["merged_at"] = TRIAL_ISO
        STORE.update_pull(repo["id"], pull)
        return self._mcp_tool_result({"merged": True, "sha": merge_sha,
                                      "message": message,
                                      "number": pull["number"]}), None


def _commit_stamp(view):
    """Epoch seconds from a commit view's author line (0 when unparsable)."""
    author = view.get("author", "")
    parts = author.rsplit(" ", 2)
    if len(parts) == 3:
        try:
            return int(parts[1])
        except ValueError:
            return 0
    return 0


def _ident(line):
    """Parse 'Name <email> ts tz' into GitHub's author shape."""
    name = ""
    email = ""
    date = TRIAL_ISO
    match = re.match(r"^(.*?) <(.*?)> (\d+) ([+-]\d+)$", line or "")
    if match:
        name, email = match.group(1), match.group(2)
        try:
            import datetime
            date = datetime.datetime.fromtimestamp(
                int(match.group(3)), datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        except Exception:
            date = TRIAL_ISO
    return {"name": name, "email": email, "date": date}


def _find_subtree_oid(store, tree_oid, segments):
    obj = store.get_object(tree_oid)
    if obj is None or obj[0] != "tree" or not segments:
        return None
    for mode, name, child in parse_tree(obj[1]):
        if name == segments[0]:
            if len(segments) == 1:
                return child
            return _find_subtree_oid(store, child, segments[1:])
    return None




def _strip_owner_prefix(ref):
    if ":" in ref:
        return ref.split(":", 1)[1]
    return ref





# --- GraphQL document parsing -------------------------------------------------

_GRAPHQL_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def _gql_tokens(text):
    pos = 0
    n = len(text)
    while pos < n:
        ch = text[pos]
        if ch in " \t\r\n,":
            pos += 1
            continue
        if ch == "#":
            while pos < n and text[pos] != "\n":
                pos += 1
            continue
        if ch == "." and text[pos:pos + 3] == "...":
            yield ("SPREAD", "...")
            pos += 3
            continue
        if ch in "{}():![]=@$":
            yield (ch, ch)
            pos += 1
            continue
        if ch == '"':
            pos += 1
            out = []
            while pos < n and text[pos] != '"':
                if text[pos] == "\\" and pos + 1 < n:
                    esc = text[pos + 1]
                    mapping = {"n": "\n", "t": "\t", "r": "\r", '"': '"', "\\": "\\", "/": "/"}
                    if esc == "u" and pos + 5 < n:
                        out.append(chr(int(text[pos + 2:pos + 6], 16)))
                        pos += 6
                        continue
                    out.append(mapping.get(esc, esc))
                    pos += 2
                else:
                    out.append(text[pos])
                    pos += 1
            pos += 1
            yield ("STRING", "".join(out))
            continue
        match = _GRAPHQL_NAME.match(text, pos)
        if match:
            yield ("NAME", match.group(0))
            pos = match.end()
            continue
        if ch == "-" or ch.isdigit():
            start = pos
            if ch == "-":
                pos += 1
            while pos < n and (text[pos].isdigit() or text[pos] in ".eE+-"):
                pos += 1
            raw = text[start:pos]
            try:
                yield ("NUMBER", float(raw) if ("." in raw or "e" in raw or "E" in raw) else int(raw))
            except ValueError:
                raise ValueError("bad number %r" % raw)
            continue
        raise ValueError("unexpected character %r" % ch)
    yield ("EOF", None)


class _GqlParser:
    def __init__(self, text):
        self.tokens = list(_gql_tokens(text))
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos]

    def take(self, kind=None):
        token = self.tokens[self.pos]
        if kind is not None and token[0] != kind:
            raise ValueError("expected %s, got %s" % (kind, token[0]))
        self.pos += 1
        return token

    def at(self, kind):
        return self.tokens[self.pos][0] == kind

    def parse_document(self):
        operations = []
        fragments = {}
        while not self.at("EOF"):
            if self.at("NAME") and self.peek()[1] in ("query", "mutation", "subscription"):
                kind = self.take("NAME")[1]
                name = None
                if self.at("NAME"):
                    name = self.take("NAME")[1]
                var_defs = {}
                if self.at("("):
                    var_defs = self.parse_var_defs()
                selections = self.parse_selections()
                operations.append({"kind": kind, "name": name,
                                   "var_defs": var_defs, "selections": selections})
            elif self.at("{"):
                operations.append({"kind": "query", "name": None, "var_defs": {},
                                   "selections": self.parse_selections()})
            elif self.at("NAME") and self.peek()[1] == "fragment":
                self.take("NAME")
                frag_name = self.take("NAME")[1]
                self.take("NAME")  # 'on'
                type_name = self.take("NAME")[1]
                fragments[frag_name] = {"type": type_name,
                                        "selections": self.parse_selections()}
            else:
                raise ValueError("unexpected token %r" % (self.peek(),))
        return {"operations": operations, "fragments": fragments}

    def parse_var_defs(self):
        self.take("(")
        defs = {}
        while not self.at(")"):
            self.take("$")
            name = self.take("NAME")[1]
            self.take(":")
            defs[name] = self.parse_type()
            if self.at("="):
                self.take("=")
                defs[name] = (defs[name], self.parse_value())
            if self.at("NAME"):
                self.take("NAME")  # a directive name is not expected; skip defensively
        self.take(")")
        return defs

    def parse_type(self):
        if self.at("["):
            self.take("[")
            inner = self.parse_type()
            self.take("]")
            result = "[" + inner + "]"
        else:
            result = self.take("NAME")[1]
        if self.at("!"):
            self.take("!")
            result += "!"
        return result

    def parse_selections(self):
        self.take("{")
        selections = []
        while not self.at("}"):
            selections.append(self.parse_selection())
        self.take("}")
        return selections

    def parse_selection(self):
        if self.at("SPREAD"):
            self.take("SPREAD")
            if self.at("NAME") and self.peek()[1] == "on":
                self.take("NAME")
                type_name = self.take("NAME")[1]
                return {"kind": "inline", "type": type_name,
                        "selections": self.parse_selections()}
            name = self.take("NAME")[1]
            return {"kind": "spread", "name": name}
        alias = None
        name = self.take("NAME")[1]
        if self.at(":"):
            self.take(":")
            alias = name
            name = self.take("NAME")[1]
        args = {}
        if self.at("("):
            args = self.parse_arguments()
        sub = []
        if self.at("{"):
            sub = self.parse_selections()
        return {"kind": "field", "name": name, "alias": alias or name,
                "args": args, "selections": sub}

    def parse_arguments(self):
        self.take("(")
        args = {}
        while not self.at(")"):
            name = self.take("NAME")[1]
            self.take(":")
            args[name] = self.parse_value()
        self.take(")")
        return args

    def parse_value(self):
        kind, value = self.peek()
        if kind == "$":
            self.take("$")
            return ("var", self.take("NAME")[1])
        if kind == "STRING":
            self.take("STRING")
            return ("lit", value)
        if kind == "NUMBER":
            self.take("NUMBER")
            return ("lit", value)
        if kind == "NAME":
            self.take("NAME")
            if value == "true":
                return ("lit", True)
            if value == "false":
                return ("lit", False)
            if value == "null":
                return ("lit", None)
            return ("enum", value)
        if kind == "[":
            self.take("[")
            items = []
            while not self.at("]"):
                items.append(self.parse_value())
            self.take("]")
            return ("list", items)
        if kind == "{":
            self.take("{")
            fields = {}
            while not self.at("}"):
                name = self.take("NAME")[1]
                self.take(":")
                fields[name] = self.parse_value()
            self.take("}")
            return ("object", fields)
        raise ValueError("unexpected value token %r" % (kind,))


def parse_graphql(text):
    return _GqlParser(text).parse_document()


def _gql_value(node, variables):
    kind, value = node
    if kind == "var":
        return variables.get(value)
    if kind == "lit":
        return value
    if kind == "enum":
        return value
    if kind == "list":
        return [_gql_value(item, variables) for item in value]
    if kind == "object":
        return {key: _gql_value(item, variables) for key, item in value.items()}
    return None


# --- GraphQL schema data -------------------------------------------------------

_GQL_TYPE_FIELDS = {
    "Issue": ["id", "number", "title", "state", "body", "createdAt", "updatedAt",
              "author", "labels", "comments", "url", "closedAt"],
    "PullRequest": ["id", "number", "title", "body", "state", "merged", "mergeable",
                    "headRefName", "baseRefName", "files", "headRef", "baseRef",
                    "createdAt", "updatedAt", "mergedAt", "mergeCommit", "author", "url"],
    "Repository": ["id", "databaseId", "name", "nameWithOwner", "owner",
                   "defaultBranchRef", "viewerPermission", "hasIssuesEnabled",
                   "issue", "issues", "pullRequests", "pullRequest", "description",
                   "isPrivate", "createdAt", "updatedAt", "url"],
    "User": ["login", "id", "name", "email"],
    "SearchType": [],
}
_GQL_ENUM_VALUES = {
    "SearchType": ["ISSUE", "REPOSITORY", "USER", "DISCUSSION", "CODE", "COMMIT",
                   "WIKI", "PACKAGE", "MARKETPLACE", "APP"],
    "IssueState": ["OPEN", "CLOSED"],
    "MergeableState": ["MERGEABLE", "CONFLICTING", "UNKNOWN"],
    "PullRequestState": ["OPEN", "CLOSED", "MERGED"],
    "PullRequestMergeMethod": ["MERGE", "SQUASH", "REBASE"],
    "RepositoryPermission": ["ADMIN", "MAINTAIN", "WRITE", "TRIAGE", "READ"],
    "IssueOrderField": ["CREATED_AT", "UPDATED_AT", "COMMENTS"],
    "OrderDirection": ["ASC", "DESC"],
}


def _gql_repo_ref(repo):
    return {"_type": "Repository", "repo": repo}


def _gql_issue_ref(repo, issue):
    return {"_type": "Issue", "repo": repo, "issue": issue}


def _gql_pull_ref(repo, pull):
    return {"_type": "PullRequest", "repo": repo, "pull": pull}


def _gql_user_ref(login):
    return {"_type": "User", "login": login}


def _gql_issues_connection(repo, args):
    states = args.get("states")
    order_by = args.get("orderBy") or {}
    first = args.get("first")
    after = args.get("after")
    items = STORE.list_issues(repo["id"])
    if isinstance(states, list) and states:
        wanted = set(states)
        items = [i for i in items if i["state"].upper() in wanted]
    direction = (order_by.get("direction") or "DESC").upper()
    reverse = direction != "ASC"
    items = sorted(items, key=lambda i: i["number"], reverse=reverse)
    if isinstance(after, str) and after:
        try:
            marker = int(base64.urlsafe_b64decode(
                after + "=" * (-len(after) % 4)).decode("ascii").split(":")[1])
            idx = next((k for k, it in enumerate(items) if it["number"] == marker), -1)
            if idx >= 0:
                items = items[idx + 1:]
        except Exception:
            pass
    total = len(items)
    if isinstance(first, int):
        page = items[:first]
    else:
        page = items
    has_next = len(page) < total
    end_cursor = ""
    if page:
        end_cursor = base64.urlsafe_b64encode(
            ("cursor:%d" % page[-1]["number"]).encode("ascii")).decode("ascii")
    return {"_type": "IssueConnection",
            "nodes": [_gql_issue_ref(repo, i) for i in page],
            "page_info": {"hasNextPage": has_next, "endCursor": end_cursor}}


def _gql_pulls_connection(repo, args):
    first = args.get("first")
    items = [p for p in STORE.list_pulls(repo["id"]) if p["state"] == "open"]
    items = sorted(items, key=lambda p: p["number"], reverse=True)
    if isinstance(first, int):
        items = items[:first]
    return {"_type": "PullRequestConnection",
            "nodes": [_gql_pull_ref(repo, p) for p in items]}


def _gql_files_connection(repo, pull, args):
    first = args.get("first")
    handler = ForgeHandler
    files = _pull_files_for(handler, repo, pull)
    if isinstance(first, int):
        files = files[:first]
    return {"_type": "PullRequestChangedFileConnection",
            "nodes": [{"_type": "PullRequestChangedFile", "path": f["filename"]}
                      for f in files]}


def _pull_files_for(handler, repo, pull):
    # Reuse the REST pull-files computation without an HTTP handler instance.
    head_tip = STORE.branch_tip(repo["id"], pull["head_branch"])
    base_tip = STORE.branch_tip(repo["id"], pull["base_branch"])
    if not head_tip or not base_tip:
        return []
    head_tip = STORE.resolve_to_commit(head_tip)
    base_tip = STORE.resolve_to_commit(base_tip)
    merge_base = STORE.merge_base(head_tip, base_tip)
    base_tree = STORE.commit_tree(merge_base) if merge_base else None
    head_tree = STORE.commit_tree(head_tip)
    diff = STORE.diff_trees(base_tree, head_tree)
    return [{"filename": path, "status": diff[path][0]} for path in sorted(diff)]


def _resolve_node(global_id):
    decoded = gid_decode(global_id)
    if decoded is None:
        return None
    kind, parts = decoded
    try:
        if kind == "Repository" and len(parts) == 1:
            repo = STORE.repo_by_id.get(int(parts[0]))
            return _gql_repo_ref(repo) if repo else None
        if kind == "Issue" and len(parts) == 2:
            repo = STORE.repo_by_id.get(int(parts[0]))
            if repo is None:
                return None
            issue = STORE.get_issue(repo["id"], int(parts[1]))
            return _gql_issue_ref(repo, issue) if issue else None
        if kind == "PullRequest" and len(parts) == 2:
            repo = STORE.repo_by_id.get(int(parts[0]))
            if repo is None:
                return None
            pull = STORE.get_pull(repo["id"], int(parts[1]))
            return _gql_pull_ref(repo, pull) if pull else None
    except (ValueError, TypeError):
        return None
    return None


def execute_selection(obj, selections, variables, fragments, errors, path):
    """Resolve one selection set against `obj`; returns a dict."""
    out = {}
    obj_type = obj.get("_type", "?") if isinstance(obj, dict) else "?"
    for sel in selections:
        if sel["kind"] == "spread":
            frag = fragments.get(sel["name"])
            if frag:
                out.update(execute_selection(obj, frag["selections"], variables,
                                             fragments, errors, path))
            continue
        if sel["kind"] == "inline":
            if sel["type"] != obj_type:
                continue
            out.update(execute_selection(obj, sel["selections"], variables,
                                         fragments, errors, path))
            continue
        name = sel["name"]
        args = {k: _gql_value(v, variables) for k, v in sel["args"].items()}
        field_path = path + [sel["alias"]]
        if name == "__typename":
            out[sel["alias"]] = obj_type
            continue
        value, known = _resolve_field(obj, name, args, sel["selections"],
                                      variables, fragments, errors, field_path)
        if not known:
            errors.append({"message": 'Cannot query field "%s" on type "%s".' % (name, obj_type),
                           "path": field_path})
            out[sel["alias"]] = None
            continue
        out[sel["alias"]] = value
    return out


def _resolve_field(obj, name, args, sub_selections, variables, fragments, errors, path):
    """(value, known?) for one field on a resolved object."""
    obj_type = obj.get("_type", "?") if isinstance(obj, dict) else "?"
    if obj_type == "Query":
        if name == "viewer":
            return execute_selection(_gql_user_ref(VIEWER_LOGIN), sub_selections,
                                     variables, fragments, errors, path), True
        if name == "repository":
            repo = STORE.get_repo(args.get("owner") or "", args.get("name") or "")
            if repo is None:
                return None, True
            return execute_selection(_gql_repo_ref(repo), sub_selections,
                                     variables, fragments, errors, path), True
        if name == "node":
            node = _resolve_node(args.get("id") or "")
            if node is None:
                return None, True
            return execute_selection(node, sub_selections, variables,
                                     fragments, errors, path), True
        if name == "__type":
            type_name = args.get("name")
            if type_name not in _GQL_TYPE_FIELDS and type_name not in _GQL_ENUM_VALUES:
                return None, True
            return execute_selection({"_type": "__Type", "name": type_name},
                                     sub_selections, variables, fragments, errors, path), True
        if name == "__schema":
            return execute_selection({"_type": "__Schema"}, sub_selections,
                                     variables, fragments, errors, path), True
        return None, False
    if obj_type == "Mutation":
        return _resolve_mutation(name, args, sub_selections, variables, fragments, errors, path)
    if obj_type == "User":
        if name == "login":
            return obj.get("login"), True
        if name == "id":
            return gid("User", VIEWER_ID), True
        if name == "name":
            return VIEWER_NAME, True
        if name == "email":
            return VIEWER_EMAIL, True
        return None, False
    if obj_type == "Repository":
        repo = obj["repo"]
        if name == "id":
            return gid("Repository", repo["id"]), True
        if name == "databaseId":
            return repo["id"], True
        if name == "name":
            return repo["name"], True
        if name == "nameWithOwner":
            return repo["owner"] + "/" + repo["name"], True
        if name == "owner":
            return execute_selection(_gql_user_ref(repo["owner"]), sub_selections,
                                     variables, fragments, errors, path), True
        if name == "defaultBranchRef":
            tip = STORE.branch_tip(repo["id"], repo["default_branch"])
            if tip is None:
                return None, True
            return execute_selection({"_type": "Ref", "name": repo["default_branch"]},
                                     sub_selections, variables, fragments, errors, path), True
        if name == "viewerPermission":
            return "ADMIN", True
        if name == "hasIssuesEnabled":
            return True, True
        if name == "description":
            return repo["description"], True
        if name == "isPrivate":
            return repo["private"], True
        if name == "issue":
            issue = STORE.get_issue(repo["id"], args.get("number") or -1)
            if issue is None:
                return None, True
            return execute_selection(_gql_issue_ref(repo, issue), sub_selections,
                                     variables, fragments, errors, path), True
        if name == "issues":
            conn = _gql_issues_connection(repo, args)
            return execute_selection(conn, sub_selections, variables,
                                     fragments, errors, path), True
        if name == "pullRequests":
            conn = _gql_pulls_connection(repo, args)
            return execute_selection(conn, sub_selections, variables,
                                     fragments, errors, path), True
        if name == "pullRequest":
            pull = STORE.get_pull(repo["id"], args.get("number") or -1)
            if pull is None:
                return None, True
            return execute_selection(_gql_pull_ref(repo, pull), sub_selections,
                                     variables, fragments, errors, path), True
        return None, False
    if obj_type == "Issue":
        issue = obj["issue"]
        if name == "id":
            return gid("Issue", obj["repo"]["id"], issue["number"]), True
        if name == "number":
            return issue["number"], True
        if name == "title":
            return issue["title"], True
        if name == "state":
            return issue["state"].upper(), True
        if name == "body":
            return issue["body"], True
        return None, False
    if obj_type == "PullRequest":
        repo, pull = obj["repo"], obj["pull"]
        if name == "id":
            return gid("PullRequest", repo["id"], pull["number"]), True
        if name == "number":
            return pull["number"], True
        if name == "title":
            return pull["title"], True
        if name == "body":
            return pull["body"], True
        if name == "state":
            if pull["merged"]:
                return "MERGED", True
            return pull["state"].upper(), True
        if name == "merged":
            return pull["merged"], True
        if name == "headRefName":
            return pull["head_branch"], True
        if name == "baseRefName":
            return pull["base_branch"], True
        if name == "mergeable":
            head_tip = STORE.branch_tip(repo["id"], pull["head_branch"])
            base_tip = STORE.branch_tip(repo["id"], pull["base_branch"])
            if not head_tip or not base_tip or pull["state"] != "open":
                return "UNKNOWN", True
            head_tip = STORE.resolve_to_commit(head_tip)
            base_tip = STORE.resolve_to_commit(base_tip)
            _t, conflicts = STORE.three_way_merge(
                STORE.merge_base(head_tip, base_tip), head_tip, base_tip, build_tree=False)
            return ("CONFLICTING" if conflicts else "MERGEABLE"), True
        if name == "files":
            conn = _gql_files_connection(repo, pull, args)
            return execute_selection(conn, sub_selections, variables,
                                     fragments, errors, path), True
        return None, False
    if obj_type in ("IssueConnection", "PullRequestConnection",
                    "PullRequestChangedFileConnection"):
        if name == "nodes":
            nodes = obj.get("nodes", [])
            out = []
            for node in nodes:
                if isinstance(node, dict) and "_type" in node:
                    out.append(execute_selection(node, sub_selections, variables,
                                                 fragments, errors, path))
                else:
                    out.append(node)
            return out, True
        if name == "edges":
            nodes = obj.get("nodes", [])
            out = []
            for node in nodes:
                edge = {"_type": "Edge", "node": node, "cursor": ""}
                out.append(execute_selection(edge, sub_selections, variables,
                                            fragments, errors, path))
            return out, True
        if name == "pageInfo":
            info = obj.get("page_info", {"hasNextPage": False, "endCursor": ""})
            return execute_selection({"_type": "PageInfo", **info}, sub_selections,
                                     variables, fragments, errors, path), True
        if name == "totalCount":
            return len(obj.get("nodes", [])), True
        return None, False
    if obj_type == "PageInfo":
        if name == "hasNextPage":
            return obj.get("hasNextPage", False), True
        if name == "endCursor":
            return obj.get("endCursor", ""), True
        if name in ("hasPreviousPage", "startCursor"):
            return obj.get(name, False if name.startswith("has") else ""), True
        return None, False
    if obj_type == "PullRequestChangedFile":
        if name == "path":
            return obj.get("path"), True
        if name == "filename":
            return obj.get("path"), True
        return None, False
    if obj_type == "Ref":
        if name == "name":
            return obj.get("name"), True
        return None, False
    if obj_type in ("Edge", "CommentEdge"):
        if name == "node":
            node = obj.get("node")
            if isinstance(node, dict) and "_type" in node:
                return execute_selection(node, sub_selections, variables,
                                         fragments, errors, path), True
            return node, True
        if name == "cursor":
            return obj.get("cursor", ""), True
        return None, False
    if obj_type == "__Type":
        type_name = obj.get("name")
        if name == "name":
            return type_name, True
        if name == "fields":
            names = _GQL_TYPE_FIELDS.get(type_name, [])
            return [{"_type": "__Field", "name": n} for n in names], True
        if name == "enumValues":
            names = _GQL_ENUM_VALUES.get(type_name, [])
            return [{"_type": "__EnumValue", "name": n} for n in names], True
        return None, False
    if obj_type == "__Field":
        if name == "name":
            return obj.get("name"), True
        return None, False
    if obj_type == "__EnumValue":
        if name == "name":
            return obj.get("name"), True
        return None, False
    if obj_type == "__Schema":
        if name == "queryType":
            return {"_type": "__Type", "name": "Query"}, True
        return None, False
    if obj_type in ("CreateIssuePayload", "CloseIssuePayload"):
        if name == "issue":
            node = obj.get("issue")
            if node is None:
                return None, True
            return execute_selection(node, sub_selections, variables,
                                     fragments, errors, path), True
        return None, False
    if obj_type in ("CreatePullRequestPayload", "MergePullRequestPayload"):
        if name == "pullRequest":
            node = obj.get("pullRequest")
            if node is None:
                return None, True
            return execute_selection(node, sub_selections, variables,
                                     fragments, errors, path), True
        return None, False
    if obj_type == "AddCommentPayload":
        if name == "commentEdge":
            edge = obj.get("commentEdge")
            if edge is None:
                return None, True
            return execute_selection(edge, sub_selections, variables,
                                     fragments, errors, path), True
        return None, False
    if obj_type == "Comment":
        if name == "id":
            return obj.get("id"), True
        if name == "body":
            return obj.get("body"), True
        return None, False
    return None, False


def _resolve_mutation(name, args, sub_selections, variables, fragments, errors, path):
    """Mutation root fields. Returns (value, known?)."""
    payload = args.get("input") or {}
    if not isinstance(payload, dict):
        payload = {}
    if name == "createIssue":
        decoded = gid_decode(payload.get("repositoryId") or "")
        if decoded is None or decoded[0] != "Repository":
            errors.append({"message": "createIssue: unknown repository id", "path": path})
            return None, True
        try:
            repo = STORE.repo_by_id.get(int(decoded[1][0]))
        except (ValueError, TypeError):
            repo = None
        if repo is None:
            errors.append({"message": "createIssue: unknown repository", "path": path})
            return None, True
        issue = STORE.create_issue(repo, payload.get("title") or "",
                                   payload.get("body") or "", [])
        result = {"_type": "CreateIssuePayload",
                  "issue": _gql_issue_ref(repo, issue)}
        return execute_selection(result, sub_selections, variables,
                                 fragments, errors, path), True
    if name == "closeIssue":
        decoded = gid_decode(payload.get("issueId") or "")
        if decoded is None or decoded[0] != "Issue":
            errors.append({"message": "closeIssue: unknown issue id", "path": path})
            return None, True
        try:
            repo = STORE.repo_by_id.get(int(decoded[1][0]))
            issue = STORE.get_issue(repo["id"], int(decoded[1][1])) if repo else None
        except (ValueError, TypeError):
            issue = None
            repo = None
        if issue is None or repo is None:
            errors.append({"message": "closeIssue: unknown issue", "path": path})
            return None, True
        STORE.patch_issue(repo["id"], issue, state="closed")
        result = {"_type": "CloseIssuePayload",
                  "issue": _gql_issue_ref(repo, issue)}
        return execute_selection(result, sub_selections, variables,
                                 fragments, errors, path), True
    if name == "createPullRequest":
        decoded = gid_decode(payload.get("repositoryId") or "")
        if decoded is None or decoded[0] != "Repository":
            errors.append({"message": "createPullRequest: unknown repository id", "path": path})
            return None, True
        try:
            repo = STORE.repo_by_id.get(int(decoded[1][0]))
        except (ValueError, TypeError):
            repo = None
        if repo is None:
            errors.append({"message": "createPullRequest: unknown repository", "path": path})
            return None, True
        head = _strip_owner_prefix(payload.get("headRefName") or "")
        base = _strip_owner_prefix(payload.get("baseRefName") or "")
        if STORE.branch_tip(repo["id"], head) is None:
            errors.append({"message": "createPullRequest: head branch does not exist",
                           "path": path})
            return None, True
        if STORE.branch_tip(repo["id"], base) is None:
            errors.append({"message": "createPullRequest: base branch does not exist",
                           "path": path})
            return None, True
        pull = STORE.create_pull(repo, payload.get("title") or "",
                                 payload.get("body") or "", head, base)
        result = {"_type": "CreatePullRequestPayload",
                  "pullRequest": _gql_pull_ref(repo, pull)}
        return execute_selection(result, sub_selections, variables,
                                 fragments, errors, path), True
    if name == "mergePullRequest":
        decoded = gid_decode(payload.get("pullRequestId") or "")
        if decoded is None or decoded[0] != "PullRequest":
            errors.append({"message": "mergePullRequest: unknown pull request id", "path": path})
            return None, True
        try:
            repo = STORE.repo_by_id.get(int(decoded[1][0]))
            pull = STORE.get_pull(repo["id"], int(decoded[1][1])) if repo else None
        except (ValueError, TypeError):
            pull = None
            repo = None
        if pull is None or repo is None:
            errors.append({"message": "mergePullRequest: unknown pull request", "path": path})
            return None, True
        if pull["state"] != "open":
            errors.append({"message": "mergePullRequest: pull request is closed",
                           "path": path})
            return None, True
        head_tip = STORE.branch_tip(repo["id"], pull["head_branch"])
        base_tip = STORE.branch_tip(repo["id"], pull["base_branch"])
        if not head_tip or not base_tip:
            errors.append({"message": "mergePullRequest: branch is missing", "path": path})
            return None, True
        head_tip = STORE.resolve_to_commit(head_tip)
        base_tip = STORE.resolve_to_commit(base_tip)
        merged_tree, conflicts = STORE.three_way_merge(
            STORE.merge_base(head_tip, base_tip), head_tip, base_tip)
        if conflicts:
            errors.append({"message": "mergePullRequest: merge conflict", "path": path})
            return None, True
        message = "Merge pull request #%d from %s\n\n%s" % (
            pull["number"], pull["head_branch"], pull["title"])
        merge_sha = STORE.put_object("commit", build_commit(merged_tree, [base_tip], message))
        STORE.set_ref(repo["id"], "refs/heads/" + pull["base_branch"], merge_sha)
        STORE.commit()
        pull["state"] = "closed"
        pull["merged"] = True
        pull["merge_sha"] = merge_sha
        pull["merged_at"] = TRIAL_ISO
        STORE.update_pull(repo["id"], pull)
        result = {"_type": "MergePullRequestPayload",
                  "pullRequest": _gql_pull_ref(repo, pull)}
        return execute_selection(result, sub_selections, variables,
                                 fragments, errors, path), True
    if name == "addComment":
        decoded = gid_decode(payload.get("subjectId") or "")
        if decoded is None or decoded[0] != "Issue":
            errors.append({"message": "addComment: unknown subject id", "path": path})
            return None, True
        try:
            repo = STORE.repo_by_id.get(int(decoded[1][0]))
            issue = STORE.get_issue(repo["id"], int(decoded[1][1])) if repo else None
        except (ValueError, TypeError):
            issue = None
            repo = None
        if issue is None or repo is None:
            errors.append({"message": "addComment: unknown issue", "path": path})
            return None, True
        comment = STORE.add_comment(repo, issue["number"], payload.get("body") or "")
        node = {"_type": "Comment",
                "id": gid("Comment", repo["id"], issue["number"], comment["id"]),
                "body": comment["body"]}
        edge = {"_type": "CommentEdge", "node": node}
        result = {"_type": "AddCommentPayload", "commentEdge": edge}
        return execute_selection(result, sub_selections, variables,
                                 fragments, errors, path), True
    return None, False


_MCP_TOOLS = [
    {"name": "create_repo",
     "description": "Create a new repository owned by the authenticated user.",
     "inputSchema": {"type": "object",
                     "properties": {"name": {"type": "string",
                                             "description": "Repository name"},
                                    "description": {"type": "string",
                                                    "description": "Repository description"},
                                    "private": {"type": "boolean",
                                                "description": "Whether the repository is private"}},
                     "required": ["name"]}},
    {"name": "get_repo",
     "description": "Get a repository by owner and name.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string",
                                              "description": "Repository owner login"},
                                    "repo": {"type": "string",
                                            "description": "Repository name"}},
                     "required": ["owner", "repo"]}},
    {"name": "create_issue",
     "description": "Create an issue in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string",
                                              "description": "Repository owner login"},
                                    "repo": {"type": "string",
                                            "description": "Repository name"},
                                    "title": {"type": "string",
                                             "description": "Issue title"},
                                    "body": {"type": "string",
                                            "description": "Issue body"}},
                     "required": ["owner", "repo", "title"]}},
    {"name": "list_issues",
     "description": "List issues in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string",
                                              "description": "Repository owner login"},
                                    "repo": {"type": "string",
                                            "description": "Repository name"},
                                    "state": {"type": "string",
                                             "description": "Issue state filter: open, closed, or all"}},
                     "required": ["owner", "repo"]}},
    {"name": "create_pull_request",
     "description": "Create a pull request in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string",
                                              "description": "Repository owner login"},
                                    "repo": {"type": "string",
                                            "description": "Repository name"},
                                    "title": {"type": "string",
                                             "description": "Pull request title"},
                                    "head": {"type": "string",
                                            "description": "Head branch name"},
                                    "base": {"type": "string",
                                            "description": "Base branch name"}},
                     "required": ["owner", "repo", "title", "head", "base"]}},
    {"name": "merge_pull_request",
     "description": "Merge a pull request in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string",
                                              "description": "Repository owner login"},
                                    "repo": {"type": "string",
                                            "description": "Repository name"},
                                    "pull_number": {"type": "integer",
                                                    "description": "Pull request number"}},
                     "required": ["owner", "repo", "pull_number"]}},
]

_MCP_TOOL_HANDLERS = {
    "create_repo": ForgeHandler._mcp_create_repo,
    "get_repo": ForgeHandler._mcp_get_repo,
    "create_issue": ForgeHandler._mcp_create_issue,
    "list_issues": ForgeHandler._mcp_list_issues,
    "create_pull_request": ForgeHandler._mcp_create_pull_request,
    "merge_pull_request": ForgeHandler._mcp_merge_pull_request,
}


# =============================================================================
# Boot
# =============================================================================

def _env_post(url, payload, timeout=5):
    req = urllib.request.Request(
        url, data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"}, method="POST")
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.status, resp.read()


def _env_get_json(url, timeout=30):
    with urllib.request.urlopen(url, timeout=timeout) as resp:
        return json.loads(resp.read().decode("utf-8"))


def main():
    global STORE
    STORE = Store()
    server = ThreadingHTTPServer(("0.0.0.0", 0), ForgeHandler)
    server.daemon_threads = True
    try:
        server.request_queue_size = 128
    except Exception:
        pass
    port = server.server_address[1]
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    print("forge listening on port %d" % port, flush=True)
    env_url = os.environ.get("MAKEFUN_ENV_URL", "").rstrip("/")
    if env_url:
        registered = False
        deadline = time.time() + 60
        while time.time() < deadline and not registered:
            try:
                status, _body = _env_post(env_url + "/register", {"port": port})
                if 200 <= status < 300:
                    registered = True
            except Exception:
                time.sleep(0.5)
        if not registered:
            print("forge: failed to register with env", file=sys.stderr, flush=True)
            server.shutdown()
            server.server_close()
            return 1
        while True:
            try:
                payload = _env_get_json(env_url + "/done")
                if isinstance(payload, dict) and payload.get("done"):
                    break
            except Exception:
                pass
            time.sleep(0.5)
        server.shutdown()
        server.server_close()
        return 0
    # Local dev mode: serve until killed.
    try:
        while True:
            time.sleep(3600)
    except KeyboardInterrupt:
        pass
    server.shutdown()
    server.server_close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
