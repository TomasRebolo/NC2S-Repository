import math
import tkinter as tk
from tkinter import simpledialog, messagebox, filedialog
from PIL import Image, ImageTk
#import #requests
import os
import socket
import ssl
import threading
import time
import struct
import re
from collections import deque
from queue import Queue, Empty
from cryptography import x509
from cryptography.hazmat.primitives import hashes, hmac, serialization
from cryptography.hazmat.primitives.asymmetric import dh, rsa, padding
from cryptography.hazmat.primitives.kdf.hkdf import HKDF
from cryptography.hazmat.primitives.serialization import Encoding, PublicFormat, load_pem_public_key, load_der_public_key
from cryptography.hazmat.backends import default_backend
from pymavlink import mavutil
import tkinter.ttk as ttk
import uuid
import sys
from collections import defaultdict
from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.x509 import load_der_x509_certificate
from cryptography.hazmat.primitives.asymmetric.ec import EllipticCurvePublicKey
import subprocess
from cryptography.x509 import load_der_x509_crl
import logging
import logging.handlers
import queue
import rasterio
import ctypes
from logging.handlers import QueueHandler, QueueListener
import glob
from datetime import datetime, timezone
from zoneinfo import ZoneInfo
import json
import signal
LOCAL_TZ = ZoneInfo("Europe/Lisbon")

from time_sync_utilis import (
    TIME_SYNC_READY_TOKEN,
    TimeSyncError,
    perform_time_sync,
    recv_exact,
)



# Parse and validate LOG_MODE (0=performance, 1=console, 2=console+file)
if len(sys.argv) != 2:
    print(f"Usage: {os.path.basename(sys.argv[0])} <LOG_MODE>")
    print("  LOG_MODE: 0 (performance), 1 (console only), 2 (console + file)")
    sys.exit(1)
LOG_MODE = sys.argv[1]
if LOG_MODE not in ('0', '1', '2'):
    print(f"Invalid LOG_MODE: {LOG_MODE}. Must be 0, 1 or 2.")
    sys.exit(1)
LOG_MODE = int(LOG_MODE)

# Configuration
#CERT_DIR = r"C:\Users\5066\Desktop\Rebolo\2CMD1\tese\cert1\cmd"
CERT_DIR = r"C:\Users\Admin\Desktop\tecnico\tese\tese\cert1\cmd"
CREDENTIAL_DIR = os.path.join(CERT_DIR, "credentials")
CRL_DIR = os.path.join(CERT_DIR, "crl")
CMD_CERT = os.path.join(CERT_DIR, "cmd.crt")
CMD_KEY = os.path.join(CERT_DIR, "cmd.key")
CA_CERT = os.path.join(CERT_DIR, "ca.crt")
POLICY_DIR = os.path.join(CERT_DIR, "mission_policy")
POLICY_FILE = os.path.join(POLICY_DIR, "mission_policy.json")  # Adjust path as needed
VALID_TYPES = [b'\x01', b'\x02', b'\x03', b'\x04', b'\x05', b'\x06', b'\x07', b'\x08', b'\x09', b'\x10', b'\x11', b'\x12', b'\x13', b'\x14', b'\x15', b'\x16', b'\x17']
MAX_SITLS = 10
SESSION_KEY_LENGTH = 32
SESSION_KEY_LIFETIME = 3*60
SESSION_RENEW_THRESHOLD = 3*30
CREDENTIAL_RENEW_THRESHOLD = 60
NETWORK_MAP_INTERVAL = 30  # Seconds for 0x06 and 0x10 message timeout
CRL_LIFETIME_SECONDS = 365 * 24 * 60 * 60  # 1 year

OPENSSL_PATH = r"C:\Program Files\OpenSSL-Win64\bin\openssl.exe"
#CA_CONF_PATH = r"C:\Users\5066\Desktop\Rebolo\2CMD1\tese\cert1\ca\ca.conf"
CA_CONF_PATH = r"C:\Users\Admin\Desktop\tecnico\tese\tese\cert1\ca\ca.conf"
CRL_CERT_DIR = os.path.join(CERT_DIR, "CRL_CERTIFICATES")
os.makedirs(CRL_CERT_DIR, exist_ok=True)

# Load PRcmd and PUcmd
with open(CMD_KEY, 'rb') as f:
    PRcmd = serialization.load_pem_private_key(f.read(), None, default_backend())
with open(CMD_CERT, 'rb') as f:
    cmd_cert = x509.load_pem_x509_certificate(f.read(), default_backend())
PUcmd = cmd_cert.public_key()
cmd_cn = cmd_cert.subject.get_attributes_for_oid(x509.NameOID.COMMON_NAME)[0].value
cmd_serial = cmd_cert.serial_number
print(f"[{cmd_cn}] Loaded command certificate: {CMD_CERT}, Serial: {cmd_serial}")


log_path = os.path.join(CERT_DIR, f"{cmd_cn}_log.txt")
os.makedirs(CERT_DIR, exist_ok=True)

# Create and clear the root logger
logger = logging.getLogger()
logger.setLevel(logging.DEBUG)
logger.handlers.clear()

# Common formatter
formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')

# --- Setup async logging ---
if LOG_MODE == 0:
    # Mode 0: completely silent—no handlers, no I/O
    pass

elif LOG_MODE in (1, 2):
    # Always use async logging via a queue
    log_queue = queue.Queue()
    queue_handler = QueueHandler(log_queue)
    logger.addHandler(queue_handler)

    # Prepare handlers for the listener
    listener_handlers = []

    # Console handler for both mode 1 and 2
    console = logging.StreamHandler(sys.stdout)
    console.setLevel(logging.INFO)
    console.setFormatter(formatter)
    listener_handlers.append(console)

    # File handler only in mode 2
    if LOG_MODE == 2:
        fileh = logging.FileHandler(log_path, mode='w', encoding='utf-8')
        fileh.setLevel(logging.DEBUG)
        fileh.setFormatter(formatter)
        listener_handlers.append(fileh)

    # Start the background listener
    listener = QueueListener(log_queue, *listener_handlers)
    listener.start()

    # Redirect print()/stderr to logger
    class StreamToLogger:
        def __init__(self, log_func):
            self.log_func = log_func
        def write(self, msg):
            for line in msg.rstrip().splitlines():
                self.log_func(line)
        def flush(self):
            pass

    sys.stdout = StreamToLogger(logger.info)
    sys.stderr = StreamToLogger(logger.error)





# Session management
global offset_per_node
offset_per_node = {}
global message_lenght_sent
message_lenght_sent = {}
global message_lenght_received
message_lenght_received = {}
global message_processing_time
message_processing_time = []
global connection_establishement_time
connection_establishement_time = {}
global number_gap_drop
number_gap_drop = 0
global gap_values_per_connection
gap_values_per_connection = {}
gap_values_lock = threading.Lock()
gcs_sessions = {}  # {(ip,port): {"session_key": key, "offset": offset, "gcs_cn": cn, "gcs_pu": gcs_pu, "hash": hash, "mtls_port": mtls_port}}
cmd2_sessions = {}  # {(ip,port): {"session_key": key, "offset": offset, "2cmd_cn": cn, "2cmd_pu": pu, "hash": hash, "mtls_port": mtls_port}}
pending_dh = {}  # addr → {"private_key": ..., "start_time": ..., "initiator": True}
global credentials
credentials = []
indirect_credentials = {}
clients_lock = threading.Lock()
sysid_to_gcs = {}  # {sysid: gcs_cn}
sysid_to_uxv_cn = {}  # {sysid: uxv_cn}
sysid_to_gcs_lock = threading.Lock()
client_timestamps = {}  # {cn: deque(maxlen=200)}
popup_counts = {}  # {cn: [timestamps]}
popup_queue = Queue()
running = True
crl = []  # List of credential hashes
crl_timestamp = 0
crl_lifetime = 0
crl_lock = threading.Lock()
network_map = defaultdict(list)  # cn → [uxv1, uxv2, ...]
gcs_connections = defaultdict(set)  # {'cmd': {gcs_cn}, '2cmd1': {gcs_cn}, ...}
network_lock = threading.Lock()
network_text = None
network_frame = None
global latest_crl
global latest_time 
latest_crl = None
latest_time = None

original_map_image = None
current_map_photo = None
current_map_width = 0
current_map_height = 0
lon1, lat1, lon2, lat2 = 0, 0, 0, 0
IMAGE_WIDTH, IMAGE_HEIGHT = 0, 0

# SITL tracking
sitls = {}
colors = ["red", "blue", "green", "yellow", "purple", "orange", "cyan", "magenta", "brown", "pink"]
color_index = 0
node_notebooks = {}  # {cn: ttk.Notebook}

cert_expirations = {}
cert_expirations_lock = threading.Lock()
RENEW_THRESHOLD_SEC = 120   # renew when ≤ 2 minutes to expiry
CERT_CHECK_EVERY_SEC = 10   # monitor cadence
DEFAULT_DAYS = "365"        # -days for CA
EXT_SECTION = "v3_req"      # extension section to use at signing
#try:
    #ctypes.windll.shcore.SetProcessDpiAwareness(1)  # 1 = SYSTEM_DPI_AWARE
#except Exception:
    #pass  # If not on Windows or the call fails, ignore it
# Tkinter root
root = tk.Tk()
root.withdraw()

global gcs_permissions, cmd2_permissions

serv_temp_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
server_address = ('172.18.6.212', 8080)


def is_valid_ipv4(ip):
    pattern = r'^(?:(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.){3}(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)$'
    return bool(re.match(pattern, ip))

def create_credential(cred_type, pu1, pu2, timestamp, lifetime, prcmd, capacity_string=None):
    global credentials
    if not isinstance(pu1, EllipticCurvePublicKey):
        raise ValueError("PU1 must be EC public key")
    if not isinstance(pu2, EllipticCurvePublicKey):
        raise ValueError("PU2 must be EC public key")
    
    type_byte = bytes([cred_type])
    pu1_der = pu1.public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo)
    pu2_der = pu2.public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo)
    len_pu1 = len(pu1_der).to_bytes(2, 'big')
    len_pu2 = len(pu2_der).to_bytes(2, 'big')
    
    payload = type_byte + len_pu1 + pu1_der + len_pu2 + pu2_der
    ts_bytes = int(timestamp * 1e6).to_bytes(8, 'big')
    lifetime_bytes = int(lifetime * 1e6).to_bytes(8, 'big')
    payload += ts_bytes + lifetime_bytes
    
    
    # Add capacity level for 0x02 and 0x03
    if cred_type in [0x01, 0x02, 0x03]:
        if not isinstance(capacity_string, str):
            raise ValueError("Capability string must be a string")
        capacity_bytes = capacity_string.encode('utf-8')
        if len(capacity_bytes) > 255:
            raise ValueError("Capability string too long")
        payload += len(capacity_bytes).to_bytes(1, 'big') + capacity_bytes
    
    signature = prcmd.sign(payload, ec.ECDSA(hashes.SHA256()))
    sig_len = len(signature).to_bytes(2, 'big')
    cred = payload + signature + sig_len
    cred_hash = hashes.Hash(hashes.SHA256())
    cred_hash.update(cred)
    hash_value = cred_hash.finalize()
    credentials.append({
                "type": cred_type,
                "pu1": load_der_public_key(pu1_der),
                "pu2": load_der_public_key(pu2_der),
                "timestamp": int(timestamp * 1e6),
                "lifetime": lifetime,
                "capacity_string": capacity_string,
                "raw": cred,
                "hash": hash_value
            })
    return cred, hash_value



def verify_credential(cred, pucmd, peer_pu=None, own_pu=None):
    try:
        sig_len = int.from_bytes(cred[-2:], 'big')  # last 2 bytes = sig_len
        signature = cred[-(2 + sig_len):-2]         # signature is before the 2 bytes
        payload = cred[:-(sig_len + 2)] 
        cred_body_len = len(cred) - sig_len - 2 # the rest is payload
        pucmd.verify(signature, payload, ec.ECDSA(hashes.SHA256()))
    except Exception as e:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] Credential signature verification failed: {e}")
        raise ValueError(f"Signature verification failed: {e}")
    type_byte = cred[0]
    offset = 1
    len_pu1 = int.from_bytes(cred[offset : offset + 2], "big")
    offset += 2
    pu1_der = cred[offset : offset + len_pu1]
    pu1 = load_der_public_key(pu1_der)
    offset += len_pu1
    len_pu2 = int.from_bytes(cred[offset : offset + 2], "big")
    offset += 2
    pu2_der = cred[offset : offset + len_pu2]
    pu2 = load_der_public_key(pu2_der)
    offset += len_pu2
    timestamp = int.from_bytes(cred[offset : offset + 8], "big") / 1e6
    lifetime = int.from_bytes(cred[offset + 8 : offset + 16], "big")/ 1e6

    offset += 16

    capacity_string = None
    if type_byte in [0x01 ,0x02, 0x03]:
        if offset >= cred_body_len:
            raise ValueError("Missing capability string in credential")
    str_len = cred[offset]
    offset += 1
    if offset + str_len > cred_body_len:
        raise ValueError("Invalid capability string length")
    capacity_string = cred[offset:offset + str_len].decode('utf-8')
    offset += str_len

    if LOG_MODE in (1, 2):
        logger.info(f"[{cmd_cn}] now:{time.time()} Timestamp={timestamp}, Lifetime={lifetime}, Capacity='{capacity_string}'")
    if time.time() >= timestamp + lifetime:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] Credential expired: Timestamp={timestamp}, Lifetime={lifetime}, Current={time.time()}")
        raise ValueError("Credential expired")

    cred_hash = hashes.Hash(hashes.SHA256())
    cred_hash.update(cred)
    final_hash = cred_hash.finalize()

    with crl_lock:
        if final_hash in crl:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Credential revoked (hash match).")
            raise ValueError("Credential is revoked")

    if peer_pu and pu1_der != peer_pu.public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo):
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] Peer public key mismatch: Expected={peer_pu.public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo).hex()[:20]}..., Got={pu1_der.hex()[:20]}...")
        raise ValueError("Peer public key mismatch")
    if own_pu and pu2_der != own_pu.public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo):
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] Own public key mismatch: Expected={own_pu.public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo).hex()[:20]}..., Got={pu2_der.hex()[:20]}...")
        raise ValueError("Own public key mismatch")

    return {
        "type": type_byte,
        "pu1": pu1,
        "pu2": pu2,
        "timestamp": timestamp,
        "lifetime": lifetime,
        "capacity_string": capacity_string,
        "raw": cred
    }
    
def _human_secs(s):
    s = int(s); sign = "-" if s < 0 else ""; s = abs(s)
    h, r = divmod(s, 3600); m, r = divmod(r, 60)
    return f"{sign}{h:02d}:{m:02d}:{r:02d}"

def _tte_seconds(dt_utc):
    return (dt_utc - datetime.now(timezone.utc)).total_seconds()

def _run_logged(cmd_args):
    """Run a subprocess; log pretty command; raise on failure."""
    pretty = " ".join([f'"{a}"' if (" " in a and not a.startswith("-")) else a for a in cmd_args])
    if LOG_MODE in (1, 2):
        logger.info(f"[{cmd_cn}] [CMD] {pretty}")
    subprocess.run(cmd_args, check=True)

BACKUP_KEEP_LAST = 0  # 0 = delete all backups after a successful renewal

def _purge_old_backups(cn: str, keep_last: int = BACKUP_KEEP_LAST):
    """Delete *.crt.bak / *.bak.crt for this CN to keep the folder tidy."""
    patterns = [
        os.path.join(CERT_DIR, f"{cn}_*.crt.bak"),
        os.path.join(CERT_DIR, f"{cn}_*.bak.crt"),
    ]
    files = []
    for pat in patterns:
        files.extend(glob.glob(pat))
    files.sort(key=lambda p: os.path.getmtime(p), reverse=True)  # newest first
    for f in files[keep_last:]:
        try:
            os.remove(f)
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] [CLEAN] Deleted backup: {f}")
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] [CLEAN-ERROR] {f}: {e}")
            
            
def _owning_gcs_for_uxv(uxv_cn: str) -> str | None:
    # network_map[gcs_cn] = [uxv_cn,...] ; network_map[2cmd_cn] = [gcs_cn,...]
    with network_lock:
        for gcs_cn, uxvs in network_map.items():
            if gcs_cn.lower().startswith("gcs") and uxv_cn in uxvs:
                return gcs_cn
    return None

def _choose_next_hop_for_gcs(target_gcs_cn: str):
    """Return ('gcs', addr, session) if direct; else ('2cmd', addr, session)."""
    
    # Prefer direct GCS sessions that are fresh (saw 0x06 recently)
    with clients_lock:
        for addr, sess in gcs_sessions.items():
            if sess.get("gcs_cn") == target_gcs_cn:
                return ("gcs", addr, sess)

        # Otherwise, find a 2CMD that advertises this GCS and is fresh (saw 0x10 recently)
        for addr, sess in cmd2_sessions.items():
            two_cmd_cn = sess.get("2cmd_cn")
            if (target_gcs_cn in gcs_connections.get(two_cmd_cn, set())):
                return ("2cmd", addr, sess)

    return (None, None, None)

def route_certificate_update_0x17(target_cn: str, cert_bytes: bytes) -> bool:
    """
    Send (0x17 | certificate_bytes | timestamp | HMAC) toward the node that owns target_cn.
    target_cn can be a GCS, 2CMD, or a UXV. Returns True if a hop was sent.
    """
    type_byte = b'\x17'
    timestamp_bytes = struct.pack('<Q', int(time.time() * 1e6))
    payload = cert_bytes

    with clients_lock:
        # 1) If it's a directly-connected peer (GCS or 2CMD), send to it.
        for addr, sess in gcs_sessions.items():
            if sess.get("gcs_cn") == target_cn:
                if verify_policy(type_byte, sess["capacity_string"], sess):
                    h = compute_hmac(type_byte, payload, timestamp_bytes, sess["session_key_sending"])
                    message = type_byte + payload + timestamp_bytes + h
                    udp_socket.sendto(message, addr)
                    message_lenght_sent.setdefault(target_cn, []).append((0x17, len(message)))
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] 0x17 to DIRECT GCS {target_cn} at {addr}")
                    return True

        for addr, sess in cmd2_sessions.items():
            if sess.get("2cmd_cn") == target_cn:
                if verify_policy(type_byte, sess["capacity_string"], sess):
                    h = compute_hmac(type_byte, payload, timestamp_bytes, sess["session_key_sending"])
                    message = type_byte + payload + timestamp_bytes + h
                    udp_socket.sendto(message, addr)
                    message_lenght_sent.setdefault(target_cn, []).append((0x17, len(message)))
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] 0x17 to DIRECT 2CMD {target_cn} at {addr}")
                    return True

    # 2) Not directly connected: if it's a GCS, route via 2CMD that advertises it
    if target_cn.lower().startswith("gcs"):
        hop_kind, addr, sess = _choose_next_hop_for_gcs(target_cn)
        if hop_kind:
            if verify_policy(type_byte, sess["capacity_string"], sess):
                h = compute_hmac(type_byte, payload, timestamp_bytes, sess["session_key_sending"])
                message = type_byte + payload + timestamp_bytes + h
                udp_socket.sendto(message, addr)
                message_lenght_sent.setdefault(target_cn, []).append((0x17, len(message)))
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] 0x17 to {hop_kind.upper()} for GCS {target_cn} via {addr}")
                return True
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] No route found to GCS {target_cn}")
        return False

    # 3) Otherwise assume it's a UXV: find its owning GCS and route as in (2)
    owning_gcs = _owning_gcs_for_uxv(target_cn)
    if owning_gcs:
        hop_kind, addr, sess = _choose_next_hop_for_gcs(owning_gcs)
        if hop_kind:
            if verify_policy(type_byte, sess["capacity_string"], sess):
                h = compute_hmac(type_byte, payload, timestamp_bytes, sess["session_key_sending"])
                message = type_byte + payload + timestamp_bytes + h
                udp_socket.sendto(message, addr)
                message_lenght_sent.setdefault(target_cn, []).append((0x17, len(message)))
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] 0x17 toward UXV {target_cn} via {hop_kind.upper()} {sess.get('2cmd_cn', sess.get('gcs_cn'))} (owner GCS={owning_gcs}, adr:{addr})")
                return True
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] Owning GCS {owning_gcs} found, but no fresh hop")
        return False

    if LOG_MODE in (1, 2):
        logger.info(f"[{cmd_cn}] No route for CN {target_cn} (not direct, no GCS owner)")
    return False




def renew_certificate(cn: str):
    """
    Renew a certificate for CN using the SAME key and CN.conf.
    Backs up current CN.crt → CN_<ts>.crt.bak, then overwrites CN.crt.
    Updates cert_expirations[cn] on success.
    """
    key_path  = os.path.join(CERT_DIR, f"{cn}.key")
    conf_path = os.path.join(CERT_DIR, f"{cn}.conf")
    csr_path  = os.path.join(CERT_DIR, f"{cn}.csr")
    crt_path  = os.path.join(CERT_DIR, f"{cn}.crt")

    if not os.path.exists(key_path):
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] [RENEW] Skip {cn}: missing key {key_path}")
        return
    if not os.path.exists(conf_path):
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] [RENEW] Skip {cn}: missing conf {conf_path}")
        return
    if not os.path.exists(CA_CONF_PATH):
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] [RENEW] Skip {cn}: missing CA conf {CA_CONF_PATH}")
        return

    # 0) Backup existing cert (rename to *.crt.bak so scanner ignores it)
    if os.path.exists(crt_path):
        ts = int(time.time())
        backup = os.path.join(CERT_DIR, f"{cn}_{ts}.crt.bak")
        try:
            os.replace(crt_path, backup)
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] [BACKUP] {cn}: {backup}")
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] [WARN] Could not backup {crt_path}: {e}")

    # 1) CSR (same key + conf)
    _run_logged([OPENSSL_PATH, "req", "-new",
                 "-key", key_path,
                 "-out", csr_path,
                 "-config", conf_path])

    # 2) CA signs CSR into fresh CRT (overwrites CN.crt)
    _run_logged([OPENSSL_PATH, "ca",
                 "-config", CA_CONF_PATH,
                 "-in", csr_path,
                 "-out", crt_path,
                 "-days", DEFAULT_DAYS,
                 "-extensions", EXT_SECTION,
                 "-extfile", conf_path,
                 "-batch"])

    # 3) Parse renewed cert and update the cache
    try:
        with open(crt_path, "rb") as f:
            cert = x509.load_pem_x509_certificate(f.read(), default_backend())
        new_expiry = cert.not_valid_after_utc
        with cert_expirations_lock:
            cert_expirations[cn] = new_expiry
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] [RENEWED] {cn} → {new_expiry.isoformat()} (UTC) | {new_expiry.astimezone(LOCAL_TZ).isoformat()} ({LOCAL_TZ.key})")
        _purge_old_backups(cn)
        cert_der = cert.public_bytes(encoding=serialization.Encoding.DER)
        sent = route_certificate_update_0x17(cn, cert_der)
        if not sent:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] 0x17: no route found for {cn}; will rely on pull/update on connect")
    except Exception as e:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] [ERROR] Renewed but failed to parse {cn}.crt: {e}")
        


def certificate_renewal_monitor():
    """Background thread: refresh expiries and renew when within threshold."""
    while running:
        try:

            with cert_expirations_lock:
                items = list(cert_expirations.items())

            for cn, expiry in items:
                secs = _tte_seconds(expiry)
                if secs <= 86400:  # log countdown if within 24h
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] [TTE] {cn}: {_human_secs(secs)} left | expires {expiry.isoformat()}")

                if secs <= RENEW_THRESHOLD_SEC:
                    if secs <= 0:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] [ALERT] {cn} expired {_human_secs(secs)} ago — renewing…")
                    else:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] [INFO] {cn} expiring in {_human_secs(secs)} (≤ {RENEW_THRESHOLD_SEC}s) — renewing…")
                    try:
                        renew_certificate(cn)
                    except subprocess.CalledProcessError as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] [OPENSSL-ERROR] Renewal for {cn} failed: {e}")
                    except Exception as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] [ERROR] Renewal for {cn} failed: {e}")

        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] [CERT-MON-ERROR] {e}")

        time.sleep(CERT_CHECK_EVERY_SEC)

def send_heartbeat():
    """Send periodic 0x12 heartbeat to all connected GCSs and 2CMDs."""
    while running:
        with clients_lock:
            for session_dict in [gcs_sessions, cmd2_sessions]:
                for addr, session in session_dict.items():
                    if verify_policy(b'\x12', session["capacity_string"], session):
                        type_byte = b'\x12'
                        payload = cmd_cn.encode('utf-8')
                        timestamp = int(time.time() * 1e6)
                        timestamp_bytes = struct.pack('<Q', timestamp)
                        hmac_value = compute_hmac(type_byte, payload, timestamp_bytes, session["session_key_sending"])
                        message = type_byte + payload + timestamp_bytes + hmac_value
                        udp_socket.sendto(message, addr)
                        message_lenght_sent.setdefault(session.get('gcs_cn', session.get('2cmd_cn', 'unknown')), []).append((0x12, len(message)))
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Sent 0x12 heartbeat to {session.get('gcs_cn', session.get('2cmd_cn'))} at {addr} on timestamp: {timestamp}")
        time.sleep(1)   
    
def initiate_dh_key_renewal(addr, session):
    if LOG_MODE in (1, 2):
        logger.info(f"[{cmd_cn}] Initiating DH key renewal with {session.get('2cmd_cn', session.get('gcs_cn', 'unknown'))} at {addr}")
    
    timestamp_bytes = struct.pack('<Q', int(time.time() * 1e6))
    hmac_value = compute_hmac(b'\x11', cmd_cn.encode('utf-8'), timestamp_bytes, session["session_key_sending"])
    msg = b'\x11' + cmd_cn.encode('utf-8') + timestamp_bytes + hmac_value
    udp_socket.sendto(msg, addr)
    message_lenght_sent.setdefault(session.get('gcs_cn', session.get('2cmd_cn', 'unknown')), []).append((0x11, len(msg)))
    message = f"{cmd_cn} initating key renewal with  {session.get('2cmd_cn', session.get('gcs_cn', 'unknown'))}, sent 0x11"
    serv_temp_sock.sendto(message.encode('utf-8'), server_address)
    pending_dh[addr] = {
        "start_time": time.time(),
        "initiator": True,
        "retry_count": pending_dh.get(addr, {}).get("retry_count", 0) + 1  # Increment retry count
    }
    if LOG_MODE in (1, 2):
        logger.info(f"[{cmd_cn}] Sent 0x11 to {session.get('2cmd_cn', session.get('gcs_cn', 'unknown'))} at {addr} on {pending_dh[addr]['start_time']} seconds")
    
def session_key_monitor():
    while running:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] Key monitor thread")
        now = time.time()
        with clients_lock:
            for session_dict in [cmd2_sessions, gcs_sessions]:
                for addr, session in list(session_dict.items()):
                    created = session.get("session_created_at", 0)
                    if now - created >= SESSION_KEY_LIFETIME - SESSION_RENEW_THRESHOLD:
                        if addr not in pending_dh:
                            initiate_dh_key_renewal(addr, session)
        time.sleep(10)
        
def cleanup_pending_dh():
    max_retries = 3  # Maximum number of retry attempts
    while running:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] Cleanup pending DH renewals")
        now = time.time()
        with clients_lock:
            for addr in list(pending_dh):
                if now - pending_dh[addr]["start_time"] > 10:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] {now - pending_dh[addr]['start_time']} seconds since last DH renewal with {addr}")
                    retry_count = pending_dh[addr]["retry_count"]
                    if retry_count < max_retries:
                        session = gcs_sessions.get(addr, cmd2_sessions.get(addr))
                        if session:
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{cmd_cn}] Retrying DH renewal with {session.get('2cmd_cn', session.get('gcs_cn', 'unknown'))} at {addr}, Attempt {retry_count}/{max_retries}")
                            initiate_dh_key_renewal(addr, session)
                        else:
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{cmd_cn}] No session found for {addr}, removing from pending_dh")
                            del pending_dh[addr]
                    else:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Exhausted retries ({max_retries}) for DH renewal with {addr}")
                        del pending_dh[addr]
                        
                        session_info = gcs_sessions.pop(addr, None)
                        if session_info:
                            gcs_cn = session_info["gcs_cn"]
                            popup_queue.put(("Key Renewal Failed", f"Failed to renew session key with {session.get('gcs_cn', 'unknown')} after {max_retries} attempts, removing session and retry connection."))
                            if gcs_cn in node_notebooks:
                                try:
                                    notebook = node_notebooks[gcs_cn]
                                    for widget in notebook_frame.winfo_children():
                                        if isinstance(widget, ttk.Label) and widget.winfo_name() == f"label_{gcs_cn}":
                                            widget.destroy()
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{cmd_cn}] Removed label for GCS {gcs_cn}")
                                            break
                                    notebook.pack_forget()
                                    notebook.destroy()
                                    del node_notebooks[gcs_cn]
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{cmd_cn}] Removed notebook for GCS {gcs_cn}")
                                except tk.TclError as e:
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{cmd_cn}] Error removing notebook for GCS {gcs_cn}: {e}")
                            popup_queue.put(("Timeout", f"GCS {gcs_cn} disconnected due to timeout", gcs_cn))
                            with network_lock:
                                gcs_connections[cmd_cn].discard(gcs_cn)
                                if gcs_cn in network_map:
                                    del network_map[gcs_cn]
                                root.after(0, update_network_view)
                            credentials = load_credentials(CREDENTIAL_DIR, PUcmd)
                            latest_cred = None
                            latest_ts = 0
                            with crl_lock:
                                for cred in credentials:
                                    if cred["type"] == 0x02 and cred["pu2"].public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo) == \
                                    session_info["gcs_pu"].public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo) and cred["timestamp"] > latest_ts and \
                                    cred["hash"] not in crl:
                                        latest_cred = cred
                                        latest_ts = cred["timestamp"]
                                if latest_cred:
                                    threading.Thread(target=establish_gcs_connection, args=(addr[0], session_info.get("mtls_port"), addr[1], latest_cred["raw"], session_info["hash"], session_info["cred_timestamp"], session_info["cred_lifetime"], gcs_cn, session_info["capacity_string"]), daemon=True).start()
                        else:
                            session_info = cmd2_sessions.pop(addr, None)
                            if session_info:
                                cmd2_cn = session_info["2cmd_cn"]
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd_cn}] 2CMD {cmd2_cn} at {addr} timed out (no 0x10 message)")
                                if cmd2_cn in node_notebooks:
                                    try:
                                        notebook = node_notebooks[cmd2_cn]
                                        for widget in notebook_frame.winfo_children():
                                            if isinstance(widget, ttk.Label) and widget.winfo_name() == f"label_{cmd2_cn}":
                                                widget.destroy()
                                                if LOG_MODE in (1, 2):
                                                    logger.info(f"[{cmd_cn}] Removed label for 2CMD {cmd2_cn}")
                                                break
                                        notebook.pack_forget()
                                        notebook.destroy()
                                        del node_notebooks[cmd2_cn]
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{cmd_cn}] Removed notebook for 2CMD {cmd2_cn}")
                                    except tk.TclError as e:
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{cmd_cn}] Error removing notebook for 2CMD {cmd2_cn}: {e}")
                                popup_queue.put(("Timeout", f"2CMD {cmd2_cn} disconnected due to timeout", cmd2_cn))
                                with network_lock:
                                    gcs_connections[cmd2_cn].clear()
                                    if cmd2_cn in network_map:
                                        del network_map[cmd2_cn]
                                    root.after(0, update_network_view)
                                credentials = load_credentials(CREDENTIAL_DIR, PUcmd)
                                latest_cred = None
                                latest_ts = 0
                                with crl_lock:
                                    for cred in credentials:
                                        if cred["type"] == 0x01 and cred["pu2"].public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo) == \
                                        session_info["2cmd_pu"].public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo) and cred["timestamp"] > latest_ts and \
                                        cred["hash"] not in crl:
                                            latest_cred = cred
                                            latest_ts = cred["timestamp"]
                                    if latest_cred:
                                        threading.Thread(target=establish_cmd2_connection, args=(addr[0], session_info.get("mtls_port"), addr[1], latest_cred["raw"], session_info["hash"], session_info["cred_timestamp"], session_info["cred_lifetime"], cmd2_cn, session_info["capacity_string"]), daemon=True).start()
                    
        time.sleep(5)


def credential_expiry_monitor():
    while running:
        now = time.time()
        with clients_lock:
            for session_dict in [cmd2_sessions, gcs_sessions]:
                for addr, session in list(session_dict.items()):
                    expiry_time = session["cred_timestamp"] + session["cred_lifetime"]
                    if now >= expiry_time - SESSION_RENEW_THRESHOLD:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Credential for {session.get('2cmd_cn', session.get('gcs_cn', 'unknown'))} at {addr} nearing expiration.")
                        if "gcs_cn" in session:
                            # Renew credential for GCS session
                            timestamp = time.time()
                            new_cred, new_hash = create_credential( 0x02 , PUcmd, session["gcs_pu"], timestamp, session["cred_lifetime"], PRcmd, session["capacity_string"])
                            session["cred_timestamp"] = timestamp
                            session["hash"] = new_hash
                            cred_len_bytes = len(new_cred).to_bytes(4, "big")
                            timestamp_bytes = struct.pack("<Q", int(timestamp * 1e6))
                            type_byte = b"\x13"  # Renewal message type for GCS sessions
                            payload = cred_len_bytes + new_cred
                            hmac_value = compute_hmac(type_byte, payload, timestamp_bytes, session["session_key_sending"])
                            data = type_byte + payload + timestamp_bytes + hmac_value
                            udp_socket.sendto(data, addr)
                            message_lenght_sent.setdefault(session['gcs_cn'], []).append((0x13, len(data)))
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{cmd_cn}] Sent credential renewal (0x13) to GCS {session['gcs_cn']} at {addr}")
                            
                            os.makedirs(CREDENTIAL_DIR, exist_ok=True)
                            filename = os.path.join(CREDENTIAL_DIR, f"{cmd_cn}_to_{session['gcs_cn']}_{int(timestamp*1e6)}.cred")
                            with open(filename, 'wb') as f:
                                f.write(new_cred)

                        elif "2cmd_cn" in session:
                            # Renew credential for cmd2 session
                            timestamp = time.time()
                            new_cred, new_hash = create_credential( 0x01 , PUcmd, session["2cmd_pu"], timestamp, session["cred_lifetime"], PRcmd, session["capacity_string"])
                            session["cred_timestamp"] = timestamp
                            session["hash"] = new_hash
                            cred_len_bytes = len(new_cred).to_bytes(4, "big")
                            timestamp_bytes = struct.pack("<Q", int(timestamp * 1e6))
                            type_byte = b"\x14"  # Renewal message type for cmd2 sessions
                            payload = cred_len_bytes + new_cred
                            hmac_value = compute_hmac(type_byte, payload, timestamp_bytes, session["session_key_sending"])
                            data = type_byte + payload + timestamp_bytes + hmac_value
                            udp_socket.sendto(data, addr)
                            message_lenght_sent.setdefault(session['2cmd_cn'], []).append((0x14, len(data)))
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{cmd_cn}] Sent credential renewal (0x14) to 2CMD {session['2cmd_cn']} at {addr}")
        
                            os.makedirs(CREDENTIAL_DIR, exist_ok=True)
                            filename = os.path.join(CREDENTIAL_DIR, f"{cmd_cn}_to_{session['2cmd_cn']}_{int(timestamp*1e6)}.cred")
                            with open(filename, 'wb') as f:
                                f.write(new_cred)

        time.sleep(10)

def indirect_credential_expiry_monitor():
    while running:
        now = time.time()
        expired_keys = []
        with clients_lock:
            for key, info in indirect_credentials.items():
                expiry_time = info["timestamp"] + info["lifetime"]
                if now >= expiry_time - SESSION_RENEW_THRESHOLD:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Credential {key} nearing expiration.")
                    expired_keys.append(key)
        
        for key in expired_keys:
            renew_indirect_credential(key)
        
        time.sleep(10)

def renew_indirect_credential(key):
    if len(key) == 3:
        node1, node2, node3 = key
    elif len(key) == 2:
        node1, node2 = key
        node3 = None  # or set to '' if more appropriate
    else:
        raise ValueError(f"Invalid key length in indirect_credentials: {key}")
    cred_info = indirect_credentials[key]

    # Load keys (must store the right PU info when first issuing)
    try:
        pu1 = cred_info["pu1"]
        pu2 = cred_info["pu2"]
        capacity = cred_info["capacity_string"]
        cred_type = cred_info["type"]
        cred_lifetime = cred_info["lifetime"]

        new_timestamp = time.time()
        new_cred, new_hash = create_credential(cred_type, pu1, pu2, new_timestamp, cred_lifetime, PRcmd, capacity)
        timestamp_bytes = struct.pack('<Q', int(new_timestamp * 1e6))
        # Store updated info
        indirect_credentials[key].update({
            "timestamp": new_timestamp,
            "cred_hash": new_hash,
        })

        if cred_type == 0x02:  # 2CMD → GCS
            with clients_lock:
                cmd2_addr = next((addr for addr, info in cmd2_sessions.items() if info["2cmd_cn"] == node1), None)
            if cmd2_addr is None:
                raise ValueError("Command 2 connection for node1 not found")
            session_key = cmd2_sessions[cmd2_addr]["session_key_sending"]
            type_byte = b'\x14'
            cred_len_bytes = len(new_cred).to_bytes(4, 'big')
            payload = cred_len_bytes + new_cred
            hmac_value = compute_hmac(type_byte, payload, timestamp_bytes, session_key )
            data = type_byte + payload + timestamp_bytes + hmac_value
            udp_socket.sendto(data, cmd2_addr)
            message_lenght_sent.setdefault(node1, []).append((0x14, len(data)))
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Sent 0x14 to 2CMD: {node1} at {cmd2_addr}: GCS={node2}, Timestamp={int(new_timestamp * 1e6)}")
            
            os.makedirs(CREDENTIAL_DIR, exist_ok=True)
            filename = os.path.join(CREDENTIAL_DIR, f"{node1}_to_{node2}_{int(new_timestamp*1e6)}.cred")
            with open(filename, 'wb') as f:
                f.write(new_cred)
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Stored credential to {filename}")
            
        elif cred_type == 0x03:  # GCS → UXV
            cmd2_cn = node1
            gcs_cn = node2
            uxv_cn = node3
            
            type_byte = b'\x13'
            cred_len_bytes = len(new_cred).to_bytes(4, 'big')
            payload = cred_len_bytes + new_cred

            with clients_lock:
                # CMD direct GCS sessions
                for addr, session in gcs_sessions.items():
                    if session["gcs_cn"] == gcs_cn:
                        session_key = session["session_key_sending"]
                        hmac_value = compute_hmac(type_byte, payload, timestamp_bytes, session_key)
                        data = type_byte + payload + timestamp_bytes + hmac_value
                        udp_socket.sendto(data, addr)
                        message_lenght_sent.setdefault(gcs_cn, []).append((0x13, len(data)))
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Sent 0x13 to GCS {gcs_cn} at {addr}: UXV={uxv_cn}, Timestamp={int(new_timestamp * 1e6)}")
                        
                        os.makedirs(CREDENTIAL_DIR, exist_ok=True)
                        filename = os.path.join(CREDENTIAL_DIR, f"{gcs_cn}_to_{uxv_cn}_{int(new_timestamp*1e6)}.cred")
                        with open(filename, 'wb') as f:
                            f.write(new_cred)
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Stored credential to {filename}")
                        
                # 2CMDs that list this GCS in their connections
                for addr, session in cmd2_sessions.items():
                    if cmd2_cn == session["2cmd_cn"]:
                        session_key = session["session_key_sending"]
                        type_byte_2cmd = b'\x14'
                        hmac_value = compute_hmac(type_byte_2cmd, payload, timestamp_bytes, session_key)
                        data = type_byte_2cmd + payload + timestamp_bytes + hmac_value
                        udp_socket.sendto(data, addr)
                        message_lenght_sent.setdefault(cmd2_cn, []).append((0x14, len(data)))
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Sent 0x14 to 2CMD {cmd2_cn} at {addr}: GCS={gcs_cn}, UXV={uxv_cn}, Timestamp={int(new_timestamp * 1e6)}")

                        os.makedirs(CREDENTIAL_DIR, exist_ok=True)
                        filename = os.path.join(CREDENTIAL_DIR, f"{gcs_cn}_to_{uxv_cn}_{int(new_timestamp*1e6)}.cred")
                        with open(filename, 'wb') as f:
                            f.write(new_cred)
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Stored credential to {filename}")

    except Exception as e:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] Failed to renew credential {key}: {e}")


def load_credentials(cred_dir, pucmd):
    global credentials 
    credentials = []
    if not os.path.exists(cred_dir):
        return credentials
    for filename in os.listdir(cred_dir):
        try:
            with open(os.path.join(cred_dir, filename), 'rb') as f:
                cred = f.read()
            cred_data = verify_credential(cred, pucmd)
            cred_hash = hashes.Hash(hashes.SHA256())
            cred_hash.update(cred)
            credentials.append({
                "type": cred_data["type"],
                "pu1": cred_data["pu1"],
                "pu2": cred_data["pu2"],
                "timestamp": cred_data["timestamp"],
                "lifetime": cred_data["lifetime"],
                "capacity_string": cred_data["capacity_string"],
                "raw": cred,
                "hash": cred_hash.finalize()
            })
        except ValueError as e:
            if "expired" in str(e).lower():
                messagebox.showwarning("Expired Credential", f"Credential {filename} is expired and will be ignored.")
            else:
                messagebox.showerror("Invalid Credential", f"Credential {filename} failed verification: {e}")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load credential {filename}: {e}")
    return credentials

def load_policies():
    try:
        with open(POLICY_FILE, 'r') as f:
            data = json.load(f)
        # Convert hex strings to bytes
        def convert(section):
            converted = {}
            for cap, value in section.items():
                if isinstance(value, list):
                    converted[cap] = [bytes.fromhex(h) for h in value]
                elif isinstance(value, dict):
                    inner = {}
                    for hex_code, names in value.items():
                        inner[bytes.fromhex(hex_code)] = None if names is None else list(names)
                    converted[cap] = inner
                else:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Unknown policy format for {cap}")
            return converted

        gcs_permissions = convert(data.get("gcs", {}))
        cmd2_permissions = convert(data.get("cmd2", {}))
        
        if not gcs_permissions or not cmd2_permissions:
            raise ValueError("Missing or empty policy sections in JSON")
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] Loaded policies from {POLICY_FILE}")
        return gcs_permissions, cmd2_permissions
    except FileNotFoundError:
        logger.error(f"[{cmd_cn}] Policy file not found: {POLICY_FILE}. Using default hardcoded policies.")
        
    except Exception as e:
        logger.error(f"[{cmd_cn}] Failed to load policies: {e}. Using defaults.")
        

def crl_lifetime_monitor():
    """Periodically refreshes and broadcasts the credential CRL."""
    global crl_timestamp, crl_lifetime
    while running:
        now = time.time()
        ts_bytes = None
        with crl_lock:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] CRL monitor thread - now: {now}, last update: {crl_timestamp}")
            if now - crl_lifetime >= 120:
                try:
                    crl_data, new_ts, lifetime = create_crl(crl, PRcmd)
                    crl_timestamp = new_ts
                    crl_lifetime = lifetime
                    for old_file in os.listdir(CRL_DIR):
                        if old_file.endswith('.crl'):
                            try:
                                os.remove(os.path.join(CRL_DIR, old_file))
                            except Exception as e:
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd_cn}] Failed to remove old CRL {old_file}: {e}")
                    os.makedirs(CRL_DIR, exist_ok=True)
                    crl_filename = os.path.join(CRL_DIR, f"crl_{int(crl_timestamp*1e6)}.crl")
                    with open(crl_filename, 'wb') as f:
                        f.write(crl_data)
                    ts_bytes = struct.pack('<Q', int(crl_timestamp * 1e6))
                except Exception as e:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Error creating periodic CRL: {e}")
        
                
                for addr, session_info in list(gcs_sessions.items()):
                    session_key = session_info["session_key_sending"]
                    type_byte = b'\x04'
                    hmac_value = compute_hmac(type_byte, crl_data, ts_bytes, session_key)
                    data = type_byte + crl_data + ts_bytes + hmac_value
                    udp_socket.sendto(data, addr)
                    message_lenght_sent.setdefault(session_info['gcs_cn'], []).append((0x04, len(data)))
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Sent periodic CRL to GCS {session_info['gcs_cn']} at {addr}")
                for addr, session_info in list(cmd2_sessions.items()):
                    session_key = session_info["session_key_sending"]
                    type_byte = b'\x04'
                    hmac_value = compute_hmac(type_byte, crl_data, ts_bytes, session_key)
                    data = type_byte + crl_data + ts_bytes + hmac_value
                    udp_socket.sendto(data, addr)
                    message_lenght_sent.setdefault(session_info['2cmd_cn'], []).append((0x04, len(data)))
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Sent periodic CRL to 2CMD {session_info['2cmd_cn']} at {addr}")
        
        
        try:
            cert_crl = load_latest_cert_crl(CRL_CERT_DIR)
            if cert_crl is not None and cert_crl.next_update_utc:
                seconds_left = cert_crl.next_update_utc.timestamp() - now
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] Certificate CRL next update in {seconds_left}s at {cert_crl.next_update_utc.isoformat()} (UTC)")
                if seconds_left <= 120:
                    old_serials = {entry.serial_number for entry in cert_crl}
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Certificate CRL expiring in {seconds_left}s, requesting refresh from CA")
                    timestamp = int(time.time() * 1e6)
                    crl_pem = os.path.join(CRL_CERT_DIR, f"ca_{timestamp}.crl.pem")
                    subprocess.run([OPENSSL_PATH, "ca", "-gencrl", "-config", CA_CONF_PATH, "-out", crl_pem], check=True)
                    crl_der = os.path.join(CRL_CERT_DIR, f"ca_{timestamp}.crl")
                    subprocess.run([OPENSSL_PATH, "crl", "-in", crl_pem, "-out", crl_der, "-outform", "DER"], check=True)
                    with open(crl_der, 'rb') as f:
                        crl_data = f.read()
                    new_crl = load_der_x509_crl(crl_data, default_backend())
                    new_serials = {entry.serial_number for entry in new_crl}
                    missing = old_serials - new_serials
                    if missing:
                        logger.warning(f"[{cmd_cn}] Missing revoked serials in refreshed CRL: {missing}")
                    else:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Refreshed CRL contains previous revoked serials: {old_serials}")
                    timestamp_bytes = struct.pack('<Q', int(time.time() * 1e6))
                    type_byte = b'\x16'
                    with clients_lock:
                        for session_dict in [gcs_sessions, cmd2_sessions]:
                            for addr, session in session_dict.items():
                                session_key = session["session_key_sending"]
                                hmac_value = compute_hmac(type_byte, crl_data, timestamp_bytes, session_key)
                                msg = type_byte + crl_data + timestamp_bytes + hmac_value
                                udp_socket.sendto(msg, addr)
                                message_lenght_sent.setdefault(session.get('gcs_cn', session.get('2cmd_cn', 'unknown')), []).append((0x16, len(msg)))
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd_cn}] Sent 0x16 (CRL for certificates) to {session.get('gcs_cn', session.get('2cmd_cn'))} at {addr}")
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Certificate CRL refresh error: {e}")            
                    
                    
                    
        time.sleep(30)


def create_crl(new_revoked_hashes, prcmd):
    global credentials, crl
    for h, expiration, filename in crl:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] CRL Entry: Hash in the begining: {h.hex()}, Expiration: {expiration}, Filename: {filename}")
    now = time.time() 
    valid_new = []
    for h, expiration, filename in new_revoked_hashes:
        for cred in credentials:
            if cred["hash"] == h:
                credentials.remove(cred)
                for old_file in os.listdir(CREDENTIAL_DIR):               
                    if old_file == filename:
                        try:
                            os.remove(os.path.join(CREDENTIAL_DIR, old_file))
                        except Exception as e:
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{cmd_cn}] Failed to remove old credential {old_file}: {e}")
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] Found revoked cred hash, expiration: {expiration}, now:{now}, filename: {filename}")
        if expiration >= now:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] removing expired cred hash from CRL: {h.hex()}")
            valid_new.append((h, expiration, filename))
    
    if LOG_MODE in (1, 2):
        logger.info(f"[{cmd_cn}] Valid new revoked hashes: {valid_new}")        
    crl.clear()
    for h, expiration, filename in crl:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] CRL Entry after filtering: Hash: {h.hex()}, Expiration: {expiration}, Filename: {filename}")
    crl.extend(valid_new)
    for h, expiration, filename in crl:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] CRL Entry after adding valid new: {h.hex()}, Expiration: {expiration}, Filename: {filename}")
    
    
    timestamp = time.time()
    lifetime = CRL_LIFETIME_SECONDS  
    lt_bytes = int(lifetime*1e6).to_bytes(8, 'big')
    ts_bytes = int(timestamp * 1e6).to_bytes(8, 'big')
    payload = ts_bytes + lt_bytes
    for h , expiration, filename in crl:
        payload += h
    
    signature = prcmd.sign(payload, ec.ECDSA(hashes.SHA256()))
    sig_len = len(signature).to_bytes(2, 'big')  # prefixo com tamanho da assinatura

    return payload + signature + sig_len, timestamp, timestamp+lifetime

def verify_crl(crl_data, pucmd):
    # Últimos 2 bytes = comprimento da assinatura
    sig_len = int.from_bytes(crl_data[-2:], 'big')
    signature = crl_data[-(2 + sig_len):-2]
    payload = crl_data[:-(2 + sig_len)]

    # Verifica assinatura EC
    pucmd.verify(signature, payload, ec.ECDSA(hashes.SHA256()))

    # Extrai timestamp
    timestamp = int.from_bytes(payload[:8], 'big') / 1e6
    lifetime = int.from_bytes(payload[8:16], 'big')
    if time.time() >= timestamp + lifetime:
        raise ValueError("CRL expired")
    # Extrai hashes revogados (32 bytes cada)
    revoked_hashes = [payload[i:i+32] for i in range(16, len(payload), 32)]
    return timestamp, revoked_hashes

def load_latest_cert_crl(crl_dir):
    global latest_crl, latest_time

    # Only consider files ending in .crl or .crl.der
    crl_files = [f for f in os.listdir(crl_dir) if f.endswith(".crl") or f.endswith(".crl.der")]
    if LOG_MODE in (1, 2):
        logger.info(f"[DEBUG] Found CRL files: {crl_files}")
    if not crl_files:
        return None

    for crl_file in crl_files:
        crl_path = os.path.join(crl_dir, crl_file)
        try:
            with open(crl_path, "rb") as f:
                crl_data = f.read()
                cert_crl = load_der_x509_crl(crl_data, default_backend())
                if LOG_MODE in (1, 2):
                    logger.info(f"crl: {cert_crl}")
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] before if latest_time: {latest_time}, crl.last_update_utc: {cert_crl.last_update_utc}, latest_crl: {latest_crl}")
                if latest_time is None or cert_crl.last_update_utc > latest_time:
                    latest_time = cert_crl.last_update_utc
                    latest_crl = cert_crl
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] after if latest_time: {latest_time}, crl.last_update: {cert_crl.last_update_utc}, latest_crl: {latest_crl}")
                if LOG_MODE in (1, 2):
                    logger.info(f"latest_crl: {latest_crl}")
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[WARN] Skipping invalid CRL '{crl_file}': {e}")
            continue

    return latest_crl
    


def scan_certificates():
    cert_map = {"uxv": [], "gcs": [], "cmd": [], "2cmd": []}
    try:
        ca_cert = x509.load_pem_x509_certificate(open(CA_CERT, 'rb').read(), default_backend())
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] Loaded CA certificate: {CA_CERT}")
    except Exception as e:
        messagebox.showerror("Error", f"Failed to load CA certificate: {e}")
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] Failed to load CA certificate: {e}")
        return cert_map
    
    revoked_serials = set()
    try:
        cert_crl = load_latest_cert_crl(CRL_CERT_DIR)
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] load_latest_cert_crl returned: {cert_crl}")
        if cert_crl is not None:
            revoked_serials = {entry.serial_number for entry in cert_crl}
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Loaded CRL with {revoked_serials}")
        else:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] No valid CRL found in {CRL_CERT_DIR}")
    except Exception as e:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] Failed to load certificate CRL: {e}")
        
    
    new_cache = {}
    files_found = False
    for cert_file in os.listdir(CERT_DIR):
        if cert_file.endswith('.crt') and cert_file != 'ca.crt':
            files_found = True
            cert_path = os.path.join(CERT_DIR, cert_file)
            try:
                cert = x509.load_pem_x509_certificate(open(cert_path, 'rb').read(), default_backend())
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] Loaded certificate: {cert_file}")
                ca_cert.public_key().verify(cert.signature,cert.tbs_certificate_bytes,ec.ECDSA(cert.signature_hash_algorithm))
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] Verified signature for {cert_file}")
                cn = cert.subject.get_attributes_for_oid(x509.NameOID.COMMON_NAME)[0].value
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] CN for {cert_file}: {cn}")
                pu = cert.public_key()
                cert_serial = cert.serial_number
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] Serial for {cert_file}: {cert_serial}")
                if not isinstance(pu, EllipticCurvePublicKey):
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Skipped {cert_file}: Not EC key")
                    continue
                if cert_serial in revoked_serials:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Skipped {cert_file}: Certificate is revoked")
                    continue

                

                now = datetime.now(timezone.utc)
                # cryptography>=41 provides *_utc properties; fall back if needed
                not_before = getattr(cert, "not_valid_before_utc", cert.not_valid_before.replace(tzinfo=timezone.utc))
                not_after  = getattr(cert, "not_valid_after_utc",  cert.not_valid_after.replace(tzinfo=timezone.utc))
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] Validity for {cert_file}: not_before={not_before.isoformat()}, not_after={not_after.isoformat()}, now={now.isoformat()}")
                if not (not_before <= now <= not_after):
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] {cn} cert rejected: outside validity window "
                                f"({not_before.isoformat()} .. {not_after.isoformat()}), now={now.isoformat()}")
                    continue
                
                if cn.startswith("sitl"):
                    cert_map["uxv"].append((cn, pu, cert_serial))
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Added UXV certificate: {cn}")
                elif cn.lower().startswith("gcs"):
                    cert_map["gcs"].append((cn, pu, cert_serial))
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Added GCS certificate: {cn}")
                elif cn.lower() == "cmd":
                    cert_map["cmd"].append((cn, pu, cert_serial))
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Added CMD certificate: {cn}")
                elif cn.lower().startswith("2cmd"):
                    cert_map["2cmd"].append((cn, pu, cert_serial))
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Added 2CMD certificate: {cn}")
                else:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Skipped {cert_file}: Unknown CN {cn}")
                    
                    
                expiry_utc = cert.not_valid_after_utc
                new_cache[cn] = expiry_utc
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] Cached expiry for {cn}: {expiry_utc}") 
            except Exception as e:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] Skipped {cert_file}: {e}")
                continue
            
            with cert_expirations_lock:
                cert_expirations.clear()
                cert_expirations.update(new_cache)
            
    
    if not files_found:
        messagebox.showerror("Error", f"No .crt files found in {CERT_DIR}")
    elif not cert_map["uxv"] or not cert_map["gcs"]:
        found_cns = [cn for cat in cert_map.values() for cn, pu, serial in cat]
        messagebox.showerror("Error", f"No valid UXV or GCS certificates found. Found CNs: {', '.join(found_cns) if found_cns else 'None'}")
    
    return cert_map

class NewConnectionDialog(tk.Toplevel):
    def __init__(self, parent):
        super().__init__(parent)
        self.title("New Connection")
        self.transient(parent)
        self.grab_set()
        self.cert_map = scan_certificates()
        self.node1_selected = None
        self.node1_gcs_menu = None
        
        tk.Label(self, text="Connection Type:").grid(row=0, column=0, padx=5, pady=5)
        self.type_var = tk.StringVar(value="0x01")
        tk.OptionMenu(self, self.type_var, "0x01", "0x02", "0x03").grid(row=0, column=1, padx=5, pady=5)
        
        self.node1_frame = tk.Frame(self)
        self.node1_frame.grid(row=1, column=0, columnspan=2, padx=5, pady=5)
        
        tk.Label(self.node1_frame, text="Node 1 (CN):").grid(row=0, column=0, padx=5, pady=5)
        self.node1_var = tk.StringVar()
        self.node1_menu = tk.OptionMenu(self.node1_frame, self.node1_var, "", command=self.update_node1_gcs_dropdown)
        self.node1_menu.grid(row=0, column=1, padx=5, pady=5)
        
        self.node1_gcs_var = tk.StringVar()
        self.node1_gcs_menu = tk.OptionMenu(self.node1_frame, self.node1_gcs_var, "")
        self.node1_gcs_menu.grid(row=0, column=2, padx=5, pady=5)
        
        tk.Label(self, text="Node 2 (CN):").grid(row=2, column=0, padx=5, pady=5)
        self.node2_var = tk.StringVar()
        self.node2_menu = tk.OptionMenu(self, self.node2_var, "", command=self.update_node2_dropdown)
        self.node2_menu.grid(row=2, column=1, padx=5, pady=5)
        
        tk.Label(self, text="Node IP (IPv4):").grid(row=3, column=0, padx=5, pady=5)
        self.ip_var = tk.StringVar()
        tk.Entry(self, textvariable=self.ip_var).grid(row=3, column=1, padx=5, pady=5)
        
        tk.Label(self, text="Node mTLS Port:").grid(row=4, column=0, padx=5, pady=5)
        self.mtls_port_var = tk.StringVar()
        tk.Entry(self, textvariable=self.mtls_port_var).grid(row=4, column=1, padx=5, pady=5)
        
        tk.Label(self, text="Node UDP Port:").grid(row=5, column=0, padx=5, pady=5)
        self.udp_port_var = tk.StringVar()
        tk.Entry(self, textvariable=self.udp_port_var).grid(row=5, column=1, padx=5, pady=5)
        
        tk.Label(self, text="Lifetime (seconds):").grid(row=6, column=0, padx=5, pady=5)
        self.lifetime_var = tk.StringVar(value="86400")
        tk.Entry(self, textvariable=self.lifetime_var).grid(row=6, column=1, padx=5, pady=5)
        
        # Place "Access Level" widgets in row 7
        self.access_level_label = tk.Label(self, text="Access Level:")
        self.access_level_label.grid(row=7, column=0, padx=5, pady=5)
        self.access_level_label.grid_remove()

        self.access_level_var = tk.StringVar(value="Access1")
        self.access_menu = tk.OptionMenu(self, self.access_level_var, "Access1", "Access2", "Access3")
        self.access_menu.grid(row=7, column=1, padx=5, pady=5)
        self.access_menu.grid_remove()
        
        # Place "SendWaypoint" checkbox in row 8
        self.send_waypoint_var = tk.BooleanVar(value=False)
        self.send_waypoint_check = tk.Checkbutton(self, text="SendWaypoint", variable=self.send_waypoint_var)
        self.send_waypoint_check.grid(row=8, column=0, columnspan=2, padx=5, pady=5)
        self.send_waypoint_check.grid_remove()
        
        # Place "Create" and "Cancel" buttons in row 9
        self.create_button = tk.Button(self, text="Create", command=self.create)
        self.create_button.grid(row=9, column=0, padx=5, pady=5)
        tk.Button(self, text="Cancel", command=self.destroy).grid(row=9, column=1, padx=5, pady=5)
        
        self.type_var.trace('w', self.update_dropdowns)
        self.update_dropdowns()

    def update_dropdowns(self, *args):
        cred_type = self.type_var.get()
        self.node1_menu['menu'].delete(0, 'end')
        self.node2_menu['menu'].delete(0, 'end')
        self.node1_gcs_menu['menu'].delete(0, 'end')
        
        if cred_type in ["0x01", "0x02", "0x03"]:
            self.access_level_label.grid()
            self.access_menu.grid()
            if cred_type in ["0x01", "0x02"]:
                self.send_waypoint_check.grid()
            else:
                self.send_waypoint_check.grid_remove()
        else:
            self.access_level_label.grid_remove()
            self.access_menu.grid_remove()
            self.send_waypoint_check.grid_remove()


        
        if cred_type == "0x03":
            self.node1_gcs_menu.grid(row=0, column=2, padx=5, pady=5)
            with clients_lock:
                node1_options = [cmd_cn] + [info["2cmd_cn"] for addr, info in cmd2_sessions.items()]
            node2_options = [cn for cn ,_ , _ in self.cert_map["uxv"]]
            for cn in node1_options:
                self.node1_menu['menu'].add_command(label=cn, command=lambda x=cn: self.node1_var.set(x))
            for cn in node2_options:
                self.node2_menu['menu'].add_command(label=cn, command=lambda x=cn: self.node2_var.set(x))
            self.node1_var.set(node1_options[0] if node1_options else "")
            self.node2_var.set(node2_options[0] if node2_options else "")
            self.update_node1_gcs_dropdown()
            self.update_node2_dropdown()
        else:
            self.node1_gcs_menu.grid_remove()
            if cred_type == "0x01":
                node1_options = [cn for cn, _, _ in self.cert_map["cmd"]]
                node2_options = [cn for cn, _, _ in self.cert_map["2cmd"]]
            else:  # 0x02
                node1_options = [cn for cn, _, _ in self.cert_map["cmd"]] + [info["2cmd_cn"] for addr, info in cmd2_sessions.items()]
                node2_options = [cn for cn, _, _ in self.cert_map["gcs"]]
            
            for cn in node1_options:
                self.node1_menu['menu'].add_command(label=cn, command=lambda x=cn: self.node1_var.set(x))
            for cn in node2_options:
                self.node2_menu['menu'].add_command(label=cn, command=lambda x=cn: self.node2_var.set(x))
            
            self.node1_var.set(node1_options[0] if node1_options else "")
            self.node2_var.set(node2_options[0] if node2_options else "")
        
            capacity_string = self.access_level_var.get()
            if cred_type in [0x01, 0x02] and self.send_waypoint_var.get():
                capacity_string += ",SendWaypoint"
            if cred_type not in [0x01, 0x02, 0x03]:
                capacity_string = ""
        
        self.create_button.config(state='normal' if node1_options and node2_options else 'disabled')

    def update_node1_gcs_dropdown(self):
        selected_intermediate = self.node1_var.get()
        if not selected_intermediate or selected_intermediate not in gcs_connections:
            return  # Exit if no valid intermediate node is selected

        gcs_list = sorted(gcs_connections[selected_intermediate])
        if not gcs_list:
            return  # Exit if no GCS nodes are available

        if self.node1_gcs_menu is None:
            # Initialize the GCS dropdown if it doesn't exist
            self.node1_gcs_var = tk.StringVar()
            self.node1_gcs_var.set(gcs_list[0])
            self.node1_gcs_menu = tk.OptionMenu(self.node1_frame, self.node1_gcs_var, *gcs_list)
            self.node1_gcs_menu.grid(row=0, column=2, padx=5, pady=5)
        else:
            # Update the existing dropdown
            menu = self.node1_gcs_menu['menu']
            menu.delete(0, 'end')
            for gcs in gcs_list:
                menu.add_command(label=gcs, command=tk._setit(self.node1_gcs_var, gcs))
            self.node1_gcs_var.set(gcs_list[0])


    def update_node2_dropdown(self, *args):
        cred_type = self.type_var.get()
        self.node1_selected = self.node1_var.get()
        self.node2_menu['menu'].delete(0, 'end')
        
        if cred_type == "0x03":
            node2_options = [cn for cn, _, _ in self.cert_map["uxv"]]
        elif cred_type == "0x02":
            node2_options = [cn for cn, _, _ in self.cert_map["gcs"]]
        else:  # 0x01
            node2_options = [cn for cn, _, _ in self.cert_map["2cmd"]]
        
        for cn in node2_options:
            self.node2_menu['menu'].add_command(label=cn, command=lambda x=cn: self.node2_var.set(x))
        
        self.node2_var.set(node2_options[0] if node2_options else "")
        self.create_button.config(state='normal' if self.node1_var.get() and (self.node1_gcs_var.get() or cred_type != "0x03") and self.node2_var.get() else 'disabled')

    def create(self):
        try:
            cred_type = int(self.type_var.get(), 16)
            node1_cn = self.node1_var.get()
            node2_cn = self.node2_var.get()
            ip = self.ip_var.get()
            mtls_port = self.mtls_port_var.get()
            udp_port = self.udp_port_var.get()
            lifetime = int(self.lifetime_var.get())
            capacity_string = self.access_level_var.get()
            if cred_type in [0x01, 0x02] and self.send_waypoint_var.get():
                capacity_string += ",SendWaypoint"
            if cred_type not in [0x01, 0x02, 0x03]:
                capacity_string = ""
            
            if not node1_cn or not node2_cn:
                messagebox.showerror("Error", "Invalid node selection")
                return
            if cred_type == 0x03 and not self.node1_gcs_var.get():
                messagebox.showerror("Error", "Invalid GCS selection for Node 1")
                return
            if not is_valid_ipv4(ip):
                messagebox.showerror("Error", "Invalid IPv4 address")
                return
            if not mtls_port.isdigit() or int(mtls_port) <= 0:
                messagebox.showerror("Error", "Invalid mTLS port")
                return
            if not udp_port.isdigit() or int(udp_port) <= 0:
                messagebox.showerror("Error", "Invalid UDP port")
                return
            if lifetime <= 0:
                messagebox.showerror("Error", "Invalid lifetime")
                return
            if cred_type in [0x01, 0x02, 0x03] and not capacity_string:
                messagebox.showerror("Error", "No access level selected")
                return
            
            if cred_type == 0x03:
                node1_pu = next(pu for cn, pu,_ in self.cert_map["gcs"] if cn == self.node1_gcs_var.get())
            else:
                node1_pu = next(pu for cn, pu,_ in self.cert_map["cmd"] + self.cert_map["2cmd"] if cn == node1_cn)
            node2_pu = next(pu for cn, pu,_ in (self.cert_map["2cmd"] if cred_type == 0x01 else self.cert_map["gcs"] if cred_type == 0x02 else self.cert_map["uxv"]) if cn == node2_cn)
            
            timestamp = time.time()
            cred, cred_hash = create_credential(cred_type, node1_pu, node2_pu, timestamp, lifetime, PRcmd, capacity_string)
            
            os.makedirs(CREDENTIAL_DIR, exist_ok=True)
            if cred_type == 0x01 or cred_type == 0x02:
                filename = os.path.join(CREDENTIAL_DIR, f"{node1_cn}_to_{node2_cn}_{int(timestamp*1e6)}.cred")
            else:  # 0x03
                filename = os.path.join(CREDENTIAL_DIR, f"{self.node1_gcs_var.get()}_to_{node2_cn}_{int(timestamp*1e6)}.cred")
            with open(filename, 'wb') as f:
                f.write(cred)
            
            if cred_type == 0x01:
                threading.Thread(target=establish_cmd2_connection, args=(ip, int(mtls_port), int(udp_port), cred, cred_hash, timestamp, lifetime, node2_cn, capacity_string), daemon=True).start()
            elif cred_type == 0x02:
                if node1_cn == cmd_cn:
                    threading.Thread(target=establish_gcs_connection, args=(ip, int(mtls_port), int(udp_port), cred, cred_hash, timestamp, lifetime, node2_cn, capacity_string), daemon=True).start()
                else:
                    with clients_lock:
                        cmd2_addr = next((addr for addr, info in cmd2_sessions.items() if info["2cmd_cn"] == node1_cn), None)
                        if not cmd2_addr:
                            messagebox.showerror("Error", f"Selected 2CMD {node1_cn} not connected")
                            return
                        session_key = cmd2_sessions[cmd2_addr]["session_key_sending"]
                        type_byte = b'\x09'
                        gcs_cn_bytes = node2_cn.encode('utf-8')
                        ip_bytes = ip.encode('ascii')
                        mtls_port_bytes = int(mtls_port).to_bytes(4, 'big')
                        udp_port_bytes = int(udp_port).to_bytes(4, 'big')
                        cred_len_bytes = len(cred).to_bytes(4, 'big')
                        payload = bytes([len(gcs_cn_bytes)]) + gcs_cn_bytes + bytes([len(ip_bytes)]) + ip_bytes + mtls_port_bytes + udp_port_bytes + cred_len_bytes + cred
                        timestamp_bytes = struct.pack('<Q', int(timestamp * 1e6))
                        hmac_value = compute_hmac(type_byte, payload, timestamp_bytes, session_key)
                        data = type_byte + payload + timestamp_bytes + hmac_value
                        udp_socket.sendto(data, cmd2_addr)
                        message_lenght_sent.setdefault(node1_cn, []).append((0x09, len(data)))
                        message = f"{cmd_cn} sent 0x09 to {node1_cn}"
                        serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Sent 0x09 to 2CMD {node1_cn} at {cmd2_addr}: GCS={node2_cn}, Timestamp={int(timestamp*1e6)}")
                        
                        
                        indirect_credentials[node1_cn, node2_cn, ] = {
                            "type": cred_type,
                            "pu1": node1_pu,
                            "pu2": node2_pu,
                            "timestamp": timestamp,
                            "lifetime": lifetime,
                            "capacity_string": capacity_string, 
                            "cred_hash": cred_hash
                        }
            else:  # 0x03
                with clients_lock:
                    if node1_cn == cmd_cn:
                        gcs_addr = next((addr for addr, info in gcs_sessions.items() if info["gcs_cn"] == self.node1_gcs_var.get()), None)
                        if not gcs_addr:
                            messagebox.showerror("Error", f"Selected GCS {self.node1_gcs_var.get()} not connected")
                            return
                        session_key = gcs_sessions[gcs_addr]["session_key_sending"]
                        type_byte = b'\x05'
                        uxv_cn_bytes = node2_cn.encode('utf-8')
                        ip_bytes = ip.encode('ascii')
                        mtls_port_bytes = int(mtls_port).to_bytes(4, 'big')
                        udp_port_bytes = int(udp_port).to_bytes(4, 'big')
                        cred_len_bytes = len(cred).to_bytes(4, 'big')
                        payload = bytes([len(uxv_cn_bytes)]) + uxv_cn_bytes + bytes([len(ip_bytes)]) + ip_bytes + mtls_port_bytes + udp_port_bytes + cred_len_bytes + cred
                        timestamp_bytes = struct.pack('<Q', int(timestamp * 1e6))
                        hmac_value = compute_hmac(type_byte, payload, timestamp_bytes, session_key)
                        data = type_byte + payload + timestamp_bytes + hmac_value
                        udp_socket.sendto(data, gcs_addr)
                        message_lenght_sent.setdefault(self.node1_gcs_var.get(), []).append((0x05, len(data)))
                        message = f"{cmd_cn} sent 0x05 to {self.node1_gcs_var.get()}"
                        serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Sent 0x05 to GCS {self.node1_gcs_var.get()} at {gcs_addr}: UXV={node2_cn}, Timestamp={int(timestamp*1e6)}")
                        
                        indirect_credentials[node1_cn, self.node1_gcs_var.get(),node2_cn ] = {
                            "type": cred_type,
                            "pu1": node1_pu,
                            "pu2": node2_pu,
                            "timestamp": timestamp,
                            "lifetime": lifetime,
                            "capacity_string": capacity_string,
                            "cred_hash": cred_hash
                        }
                    else:
                        cmd2_addr = next((addr for addr, info in cmd2_sessions.items() if info["2cmd_cn"] == node1_cn), None)
                        if not cmd2_addr:
                            messagebox.showerror("Error", f"Selected 2CMD {node1_cn} not connected")
                            return
                        session_key = cmd2_sessions[cmd2_addr]["session_key_sending"]
                        type_byte = b'\x08'
                        gcs_cn_bytes = self.node1_gcs_var.get().encode('utf-8')
                        uxv_cn_bytes = node2_cn.encode('utf-8')
                        ip_bytes = ip.encode('ascii')
                        mtls_port_bytes = int(mtls_port).to_bytes(4, 'big')
                        udp_port_bytes = int(udp_port).to_bytes(4, 'big')
                        cred_len_bytes = len(cred).to_bytes(4, 'big')
                        payload = bytes([len(gcs_cn_bytes)]) + gcs_cn_bytes + bytes([len(uxv_cn_bytes)]) + uxv_cn_bytes + bytes([len(ip_bytes)]) + ip_bytes + mtls_port_bytes + udp_port_bytes + cred_len_bytes + cred
                        timestamp_bytes = struct.pack('<Q', int(timestamp * 1e6))
                        hmac_value = compute_hmac(type_byte, payload, timestamp_bytes, session_key)
                        data = type_byte + payload + timestamp_bytes + hmac_value
                        udp_socket.sendto(data, cmd2_addr)
                        message_lenght_sent.setdefault(node1_cn, []).append((0x08, len(data)))
                        message = f"{cmd_cn} sent 0x08 to {node1_cn}"
                        serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Sent 0x08 to 2CMD {node1_cn} at {cmd2_addr}: GCS={self.node1_gcs_var.get()}, UXV={node2_cn}, Timestamp={int(timestamp*1e6)}")
                        
                        indirect_credentials[node1_cn, self.node1_gcs_var.get(), node2_cn ] = {
                            "type": cred_type,
                            "pu1": node1_pu,
                            "pu2": node2_pu,
                            "timestamp": timestamp,
                            "lifetime": lifetime,
                            "capacity_string": capacity_string, 
                            "cred_hash": cred_hash
                        }
            
            messagebox.showinfo("Success", f"Credential created: {filename}")
            self.destroy()
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Failed to create credential: {e}")
            messagebox.showerror("Error", f"Failed to create credential: {e}")



class ChangeCapacityDialog(tk.Toplevel):
    def __init__(self, parent):
        super().__init__(parent)
        self.title("Change Capacity")
        self.transient(parent)
        self.grab_set()
        self.cert_map = scan_certificates()
        self.node1_selected = None
        self.node1_gcs_menu = None
        
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] ChangeCapacityDialog initialized with cert_map: {self.cert_map}")
        
        tk.Label(self, text="Connection Type:").grid(row=0, column=0, padx=5, pady=5)
        self.type_var = tk.StringVar(value="0x01")
        tk.OptionMenu(self, self.type_var, "0x01", "0x02", "0x03").grid(row=0, column=1, padx=5, pady=5)
        
        self.node1_frame = tk.Frame(self)
        self.node1_frame.grid(row=1, column=0, columnspan=2, padx=5, pady=5)
        
        tk.Label(self.node1_frame, text="Node 1 (CN):").grid(row=0, column=0, padx=5, pady=5)
        self.node1_var = tk.StringVar()
        self.node1_menu = tk.OptionMenu(self.node1_frame, self.node1_var, "", command=self.update_node1_gcs_dropdown)
        self.node1_menu.grid(row=0, column=1, padx=5, pady=5)
        
        self.node1_gcs_var = tk.StringVar()
        self.node1_gcs_menu = tk.OptionMenu(self.node1_frame, self.node1_gcs_var, "", command=self.update_node2_dropdown)
        self.node1_gcs_menu.grid(row=0, column=2, padx=5, pady=5)
        
        tk.Label(self, text="Node 2 (CN):").grid(row=2, column=0, padx=5, pady=5)
        self.node2_var = tk.StringVar()
        self.node2_menu = tk.OptionMenu(self, self.node2_var, "")
        self.node2_menu.grid(row=2, column=1, padx=5, pady=5)
        
        tk.Label(self, text="Lifetime (seconds):").grid(row=6, column=0, padx=5, pady=5)
        self.lifetime_var = tk.StringVar(value="86400")
        tk.Entry(self, textvariable=self.lifetime_var).grid(row=6, column=1, padx=5, pady=5)
        
        # Place "Access Level" widgets in row 7
        self.access_level_label = tk.Label(self, text="Access Level:")
        self.access_level_label.grid(row=7, column=0, padx=5, pady=5)
        self.access_level_label.grid_remove()

        self.access_level_var = tk.StringVar(value="Access1")
        self.access_menu = tk.OptionMenu(self, self.access_level_var, "Access1", "Access2", "Access3")
        self.access_menu.grid(row=7, column=1, padx=5, pady=5)
        self.access_menu.grid_remove()
        
        # Place "SendWaypoint" checkbox in row 8
        self.send_waypoint_var = tk.BooleanVar(value=False)
        self.send_waypoint_check = tk.Checkbutton(self, text="SendWaypoint", variable=self.send_waypoint_var)
        self.send_waypoint_check.grid(row=8, column=0, columnspan=2, padx=5, pady=5)
        self.send_waypoint_check.grid_remove()
        
        # Place "Create" and "Cancel" buttons in row 9
        self.create_button = tk.Button(self, text="Create", command=self.create)
        self.create_button.grid(row=9, column=0, padx=5, pady=5)
        tk.Button(self, text="Cancel", command=self.destroy).grid(row=9, column=1, padx=5, pady=5)
        
        
        self.type_var.trace('w', self.update_dropdowns)
        self.update_dropdowns()

    def update_dropdowns(self, *args):
        cred_type = self.type_var.get()
        self.node1_menu['menu'].delete(0, 'end')
        self.node2_menu['menu'].delete(0, 'end')
        self.node1_gcs_menu['menu'].delete(0, 'end')
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] network_map: {network_map}")
        
        if cred_type in ["0x01", "0x02", "0x03"]:
            self.access_menu.grid(row=4, column=1, padx=5, pady=5)
            self.send_waypoint_check.grid(row=5, column=0, columnspan=2, padx=5, pady=5) if cred_type in ["0x01", "0x02"] else self.send_waypoint_check.grid_remove()
        else:
            self.access_menu.grid_remove()
            self.send_waypoint_check.grid_remove()
        
        with clients_lock:
            if cred_type == "0x03":
                self.node1_gcs_menu.grid(row=0, column=2, padx=5, pady=5)
                node1_options = [cmd_cn] + [info["2cmd_cn"] for addr, info in cmd2_sessions.items()]
                node2_options = []
                for cn in node1_options:
                    self.node1_menu['menu'].add_command(label=cn, command=lambda x=cn: self.node1_var.set(x))
                self.node1_var.set(node1_options[0] if node1_options else "")
                self.node2_var.set("")
                self.update_node1_gcs_dropdown()
                #self.update_node2_dropdown()
            else:
                self.node1_gcs_menu.grid_remove()
                if cred_type == "0x01":
                    node1_options = [cn for cn, _, _ in self.cert_map["cmd"]]
                    node2_options = [info["2cmd_cn"] for addr, info in cmd2_sessions.items()]
                else:  # 0x02
                    node1_options = [cmd_cn] + [info["2cmd_cn"] for addr, info in cmd2_sessions.items()]
                    node2_options = sorted(gcs_connections.get(cmd_cn, []))
                
                for cn in node1_options:
                    self.node1_menu['menu'].add_command(label=cn, command=lambda x=cn: self.node1_var.set(x))
                for cn in node2_options:
                    self.node2_menu['menu'].add_command(label=cn, command=lambda x=cn: self.node2_var.set(x))
                
                self.node1_var.set(node1_options[0] if node1_options else "")
                self.node2_var.set(node2_options[0] if node2_options else "")
            
            capacity_string = self.access_level_var.get()
            if cred_type in ["0x01", "0x02"] and self.send_waypoint_var.get():
                capacity_string += ",SendWaypoint"
            if cred_type not in ["0x01", "0x02", "0x03"]:
                capacity_string = ""
            
            self.create_button.config(state='normal' if node1_options and (self.node1_gcs_var.get() or cred_type != "0x03") and self.node2_var.get() else 'disabled')

    def update_node1_gcs_dropdown(self):
        selected_intermediate = self.node1_var.get()
        if not selected_intermediate or selected_intermediate not in gcs_connections:
            return  # Exit if no valid intermediate node is selected

        gcs_list = sorted(gcs_connections[selected_intermediate])
        if not gcs_list:
            return  # Exit if no GCS nodes are available

        if self.node1_gcs_menu is None:
            # Initialize the GCS dropdown if it doesn't exist
            self.node1_gcs_var = tk.StringVar()
            self.node1_gcs_var.set(gcs_list[0])
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Initializing GCS dropdown with: {gcs_list}")
            self.node1_gcs_menu = tk.OptionMenu(self.node1_frame, self.node1_gcs_var, *gcs_list)
            self.node1_gcs_menu.grid(row=0, column=2, padx=5, pady=5)
            self.node1_gcs_var.trace('w', self.update_node2_dropdown)
            
        else:
            # Update the existing dropdown
            menu = self.node1_gcs_menu['menu']
            menu.delete(0, 'end')
            for gcs in gcs_list:
                menu.add_command(label=gcs, command=tk._setit(self.node1_gcs_var, gcs))
            self.node1_gcs_var.set(gcs_list[0])
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Updated GCS dropdown with: {gcs_list}")
            self.node1_gcs_var.trace('w', self.update_node2_dropdown)


    def update_node2_dropdown(self, *args):
        try:
            cred_type = self.type_var.get()
            self.node1_selected = self.node1_var.get()
            self.node2_menu['menu'].delete(0, 'end')
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] update_node2_dropdown before clients_lock node1_selected={self.node1_selected}")
            if cred_type == "0x03":
                selected_gcs = self.node1_gcs_var.get()
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] update_node2_dropdown: selected_gcs={selected_gcs}, network_map={network_map}")
                node2_options = sorted(network_map.get(selected_gcs, []))
                
            elif cred_type == "0x02":
                node2_options = sorted(gcs_connections.get(self.node1_selected, []))
            else:  # 0x01
                node2_options = [info["2cmd_cn"] for addr, info in cmd2_sessions.items()]
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Node 2 options: {node2_options}")
            for cn in node2_options:
                self.node2_menu['menu'].add_command(label=cn, command=lambda x=cn: self.node2_var.set(x))
            
            self.node2_var.set(node2_options[0] if node2_options else "")
            self.create_button.config(state='normal' if self.node1_var.get() and (self.node1_gcs_var.get() or cred_type != "0x03") and self.node2_var.get() else 'disabled')
        except Exception as e:
            messagebox.showerror("Error", f"Failed to update Node 2 dropdown: {e}")
            self.node2_var.set("")
            
    def create(self):
        try:
            cred_type = int(self.type_var.get(), 16)
            node1_cn = self.node1_var.get()
            node2_cn = self.node2_var.get()
            lifetime = int(self.lifetime_var.get())
            capacity_string = self.access_level_var.get()
            if cred_type in [0x01, 0x02] and self.send_waypoint_var.get():
                capacity_string += ",SendWaypoint"
            if cred_type not in [0x01, 0x02, 0x03]:
                capacity_string = ""

            if not node1_cn or not node2_cn:
                messagebox.showerror("Error", "Invalid node selection")
                return
            if cred_type == 0x03 and not self.node1_gcs_var.get():
                messagebox.showerror("Error", "Invalid GCS selection for Node 1")
                return
            if lifetime <= 0:
                messagebox.showerror("Error", "Invalid lifetime")
                return
            if cred_type in [0x01, 0x02, 0x03] and not capacity_string:
                messagebox.showerror("Error", "No access level selected")
                return

            # Select public keys based on credential type
            if cred_type == 0x03:
                node1_pu = next(pu for cn, pu,_ in self.cert_map["gcs"] if cn == self.node1_gcs_var.get())
            else:
                node1_pu = next(pu for cn, pu,_ in self.cert_map["cmd"] + self.cert_map["2cmd"] if cn == node1_cn)
            node2_pu = next(pu for cn, pu,_ in (self.cert_map["2cmd"] if cred_type == 0x01 else self.cert_map["gcs"] if cred_type == 0x02 else self.cert_map["uxv"]) if cn == node2_cn)

            # Create new credential
            timestamp = time.time()
            cred, cred_hash = create_credential(cred_type, node1_pu, node2_pu, timestamp, lifetime, PRcmd, capacity_string)

            # Save credential to file
            os.makedirs(CREDENTIAL_DIR, exist_ok=True)
            if cred_type == 0x01 or cred_type == 0x02:
                filename = os.path.join(CREDENTIAL_DIR, f"{node1_cn}_to_{node2_cn}_{int(timestamp*1e6)}.cred")
            
            else:
                filename = os.path.join(CREDENTIAL_DIR, f"{self.node1_gcs_var.get()}_to_{node2_cn}_{int(timestamp*1e6)}.cred")
            with open(filename, 'wb') as f:
                f.write(cred)

            with clients_lock:
                timestamp_bytes = struct.pack('<Q', int(timestamp * 1e6))
                if cred_type == 0x01:
                    # Update cmd2_sessions with new credential details
                    cmd2_addr = next((addr for addr, info in cmd2_sessions.items() if info["2cmd_cn"] == node2_cn), None)
                    if not cmd2_addr:
                        messagebox.showerror("Error", f"Selected 2CMD {node2_cn} not connected")
                        return
                    cmd2_sessions[cmd2_addr].update({
                        "hash": cred_hash,
                        "cred_timestamp": timestamp,
                        "capacity_string": capacity_string,
                        "cred_lifetime": lifetime
                    })
                    # Create and send 0x14 message with empty GCS_CN and UXV_CN
                    type_byte = b'\x14'
                    cred_len_bytes = len(cred).to_bytes(4, 'big')
                    payload = cred_len_bytes + cred
                    hmac_value = compute_hmac(type_byte, payload, timestamp_bytes, cmd2_sessions[cmd2_addr]["session_key_sending"])
                    data = type_byte + payload + timestamp_bytes + hmac_value
                    udp_socket.sendto(data, cmd2_addr)
                    message_lenght_sent.setdefault(node2_cn, []).append((0x14, len(data)))
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Sent 0x14 to 2CMD {node2_cn} at {cmd2_addr}: Timestamp={int(timestamp*1e6)}")

                elif cred_type == 0x02:
                    if node1_cn == cmd_cn:
                        # Update gcs_sessions with new credential details
                        gcs_addr = next((addr for addr, info in gcs_sessions.items() if info["gcs_cn"] == node2_cn), None)
                        if not gcs_addr:
                            messagebox.showerror("Error", f"Selected GCS {node2_cn} not connected")
                            return
                        gcs_sessions[gcs_addr].update({
                            "hash": cred_hash,
                            "cred_timestamp": timestamp,
                            "capacity_string": capacity_string,
                            "cred_lifetime": lifetime
                        })
                        # Create and send 0x13 message with empty UXV_CN
                        type_byte = b'\x13'
                        cred_len_bytes = len(cred).to_bytes(4, 'big')
                        payload = cred_len_bytes + cred
                        hmac_value = compute_hmac(type_byte, payload, timestamp_bytes, gcs_sessions[gcs_addr]["session_key_sending"])
                        data = type_byte + payload + timestamp_bytes + hmac_value
                        udp_socket.sendto(data, gcs_addr)
                        message = f"{cmd_cn} sent 0x13 message to {node2_cn}"
                        serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                        message_lenght_sent.setdefault(node2_cn, []).append((0x13, len(data)))
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Sent 0x13 to GCS {node2_cn} at {gcs_addr}: Timestamp={int(timestamp*1e6)}")
                    else:
                        # Send 0x14 message to 2CMD with GCS_CN
                        cmd2_addr = next((addr for addr, info in cmd2_sessions.items() if info["2cmd_cn"] == node1_cn), None)
                        if not cmd2_addr:
                            messagebox.showerror("Error", f"Selected 2CMD {node1_cn} not connected")
                            return
                        type_byte = b'\x14'

                        cred_len_bytes = len(cred).to_bytes(4, 'big')
                        payload = cred_len_bytes + cred
                        hmac_value = compute_hmac(type_byte, payload, timestamp_bytes, cmd2_sessions[cmd2_addr]["session_key_sending"])
                        data = type_byte + payload + timestamp_bytes + hmac_value
                        udp_socket.sendto(data, cmd2_addr)
                        message_lenght_sent.setdefault(node1_cn, []).append((0x14, len(data)))
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Sent 0x14 to 2CMD {node1_cn} at {cmd2_addr}: GCS={node2_cn}, Timestamp={int(timestamp*1e6)}")
                        
                        indirect_credentials[node1_cn, node2_cn, ] = {
                            "type": cred_type,
                            "pu1": node1_pu,
                            "pu2": node2_pu,
                            "timestamp": timestamp,
                            "lifetime": lifetime,
                            "capacity_string": capacity_string,
                            "cred_hash": cred_hash
                        }

                else:  # cred_type == 0x03
                    if node1_cn == cmd_cn:
                        # Send 0x13 message to GCS with UXV_CN
                        gcs_addr = next((addr for addr, info in gcs_sessions.items() if info["gcs_cn"] == self.node1_gcs_var.get()), None)
                        if not gcs_addr:
                            messagebox.showerror("Error", f"Selected GCS {self.node1_gcs_var.get()} not connected")
                            return
                        type_byte = b'\x13'
                        cred_len_bytes = len(cred).to_bytes(4, 'big')
                        payload = cred_len_bytes + cred
                        hmac_value = compute_hmac(type_byte, payload, timestamp_bytes, gcs_sessions[gcs_addr]["session_key_sending"])
                        data = type_byte + payload + timestamp_bytes + hmac_value
                        udp_socket.sendto(data, gcs_addr)
                        message = f"{cmd_cn} sent 0x13 to {self.node1_gcs_var.get()}"
                        serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                        message_lenght_sent.setdefault(self.node1_gcs_var.get(), []).append((0x13, len(data)))
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Sent 0x13 to GCS {self.node1_gcs_var.get()} at {gcs_addr}: UXV={node2_cn}, Timestamp={int(timestamp*1e6)}")
                        
                        indirect_credentials[node1_cn, self.node1_gcs_var.get(), node2_cn ] = {
                            "type": cred_type,
                            "pu1": node1_pu,
                            "pu2": node2_pu,
                            "timestamp": timestamp,
                            "lifetime": lifetime,
                            "capacity_string": capacity_string,
                            "cred_hash": cred_hash
                        }
                    else:
                        # Send 0x14 message to 2CMD with GCS_CN and UXV_CN
                        cmd2_addr = next((addr for addr, info in cmd2_sessions.items() if info["2cmd_cn"] == node1_cn), None)
                        if not cmd2_addr:
                            messagebox.showerror("Error", f"Selected 2CMD {node1_cn} not connected")
                            return
                        type_byte = b'\x14'
                        cred_len_bytes = len(cred).to_bytes(4, 'big')
                        payload = cred_len_bytes + cred
                        hmac_value = compute_hmac(type_byte, payload, timestamp_bytes, cmd2_sessions[cmd2_addr]["session_key_sending"])
                        data = type_byte + payload + timestamp_bytes + hmac_value
                        udp_socket.sendto(data, cmd2_addr)
                        message_lenght_sent.setdefault(node1_cn, []).append((0x14, len(data)))
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Sent 0x14 to 2CMD {node1_cn} at {cmd2_addr}: GCS={self.node1_gcs_var.get()}, UXV={node2_cn}, Timestamp={int(timestamp*1e6)}")
                        
                        indirect_credentials[node1_cn, self.node1_gcs_var.get(), node2_cn ] = {
                            "type": cred_type,
                            "pu1": node1_pu,
                            "pu2": node2_pu,
                            "timestamp": timestamp,
                            "lifetime": lifetime,
                            "capacity_string": capacity_string
                        }

            messagebox.showinfo("Success", f"Credential created: {filename}")
            self.destroy()
        except Exception as e:
            messagebox.showerror("Error", f"Failed to create credential: {e}")

class AccessRevocationDialog(tk.Toplevel):
    def __init__(self, parent):
        super().__init__(parent)
        self.title("Access Revocation")
        self.transient(parent)
        self.grab_set()
        self.geometry("600x400")
        tk.Label(self, text="Select Credentials to Revoke:").pack(pady=5)
        self.listbox = tk.Listbox(self, selectmode=tk.MULTIPLE, height=10, width=80)
        self.listbox.cred_map = {}
        credentials = load_credentials(CREDENTIAL_DIR, PUcmd)
        
        cert_map = scan_certificates()
        pu_to_cn = {}
        for cert_type in ['uxv', 'gcs', 'cmd', '2cmd']:
            for cn, pu,_ in cert_map[cert_type]:
                pu_der = pu.public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo)
                pu_to_cn[pu_der] = cn
        
        for cred in credentials:
            pu1_der = cred['pu1'].public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo)
            pu2_der = cred['pu2'].public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo)
            node1_cn = pu_to_cn.get(pu1_der, 'Unknown')
            node2_cn = pu_to_cn.get(pu2_der, 'Unknown')
            filename = f"{node1_cn}_to_{node2_cn}_{int(cred['timestamp']*1e6)}.cred"
            self.listbox.insert(tk.END, filename)
            self.listbox.cred_map[filename] = cred
        
        self.listbox.pack(pady=5)
        
        tk.Button(self, text="Revoke", command=self.revoke).pack(pady=5)
        tk.Button(self, text="Cancel", command=self.destroy).pack(pady=5)

    def revoke(self):
        try:
            selected_indices = self.listbox.curselection()
            if not selected_indices:
                messagebox.showerror("Error", "No credentials selected")
                return
            revoked_hashes = []
            for idx in selected_indices:
                filename = self.listbox.get(idx)
                cred = self.listbox.cred_map[filename]
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] Revoking credential: {filename}, timestamp={cred['timestamp']}, lifetime={cred['lifetime']}, timestamp+lifetime={cred['timestamp']+cred['lifetime']}")
                revoked_hashes.append((cred["hash"], cred["timestamp"]+cred["lifetime"], filename))
            
            with crl_lock:
                global crl, crl_timestamp, crl_lifetime
                crl.extend(revoked_hashes)
                crl_data, crl_timestamp, crl_lifetime = create_crl(crl, PRcmd)
            
            for old_file in os.listdir(CRL_DIR):
                if old_file.endswith(".crl"):
                    try:
                        os.remove(os.path.join(CRL_DIR, old_file))
                    except Exception as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Failed to remove old CRL {old_file}: {e}")
            
            os.makedirs(CRL_DIR, exist_ok=True)
            crl_filename = os.path.join(CRL_DIR, f"crl_{int(crl_timestamp*1e6)}.crl")
            with open(crl_filename, 'wb') as f:
                f.write(crl_data)
            
            with clients_lock:
                
                for addr, session_info in list(gcs_sessions.items()):
                    session_key = session_info["session_key_sending"]
                    type_byte = b'\x04'
                    timestamp_bytes = struct.pack('<Q', int(crl_timestamp * 1e6))
                    hmac_value = compute_hmac(type_byte, crl_data, timestamp_bytes, session_key)
                    data = type_byte + crl_data + timestamp_bytes + hmac_value
                    udp_socket.sendto(data, addr)
                    message = f"{cmd_cn} sent 0x04 to  {session_info['gcs_cn']}"
                    serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                    message_lenght_sent.setdefault(session_info['gcs_cn'], []).append((0x04, len(data)))
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Sent CRL to GCS {session_info['gcs_cn']} at {addr}")
                
                for addr, session_info in list(cmd2_sessions.items()):
                    session_key = session_info["session_key_sending"]
                    type_byte = b'\x04'
                    timestamp_bytes = struct.pack('<Q', int(crl_timestamp * 1e6))
                    hmac_value = compute_hmac(type_byte, crl_data, timestamp_bytes, session_key)
                    data = type_byte + crl_data + timestamp_bytes + hmac_value
                    udp_socket.sendto(data, addr)
                    message_lenght_sent.setdefault(session_info['2cmd_cn'], []).append((0x04, len(data)))
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Sent CRL to 2CMD {session_info['2cmd_cn']} at {addr}")
                
                for addr, session_info in list(gcs_sessions.items()):
                    for h, expiration,_  in revoked_hashes:
                        if session_info["hash"] == h:
                            gcs_cn = session_info["gcs_cn"]
                            del gcs_sessions[addr]
                            with network_lock:
                                gcs_connections[cmd_cn].discard(gcs_cn)
                                if gcs_cn in network_map:
                                    del network_map[gcs_cn]
                                root.after(0, update_network_view)
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{cmd_cn}] Removed session for GCS {gcs_cn} at {addr} due to CRL")
                            if gcs_cn in node_notebooks:
                                try:
                                    notebook = node_notebooks[gcs_cn]
                                    for widget in notebook_frame.winfo_children():
                                        if isinstance(widget, ttk.Label) and widget.winfo_name() == f"label_{gcs_cn}":
                                            widget.destroy()
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{cmd_cn}] Removed label for GCS {gcs_cn}")
                                            break
                                    notebook.pack_forget()
                                    notebook.destroy()
                                    del node_notebooks[gcs_cn]
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{cmd_cn}] Removed notebook for GCS {gcs_cn}")
                                except tk.TclError as e:
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{cmd_cn}] Error removing notebook for GCS {gcs_cn}: {e}")
                
                for addr, session_info in list(cmd2_sessions.items()):
                    for h, expiration,_  in revoked_hashes:
                        if session_info["hash"] == h:
                            cmd2_cn = session_info["2cmd_cn"]
                            del cmd2_sessions[addr]
                            with network_lock:
                                gcs_connections[cmd2_cn].clear()
                                if cmd2_cn in network_map:
                                    del network_map[cmd2_cn]
                                root.after(0, update_network_view)
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{cmd_cn}] Removed session for 2CMD {cmd2_cn} at {addr} due to CRL")
                            if cmd2_cn in node_notebooks:
                                try:
                                    notebook = node_notebooks[cmd2_cn]
                                    for widget in notebook_frame.winfo_children():
                                        if isinstance(widget, ttk.Label) and widget.winfo_name() == f"label_{cmd2_cn}":
                                            widget.destroy()
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{cmd_cn}] Removed label for 2CMD {cmd2_cn}")
                                            break
                                    notebook.pack_forget()
                                    notebook.destroy()
                                    del node_notebooks[cmd2_cn]
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{cmd_cn}] Removed notebook for 2CMD {cmd2_cn}")
                                except tk.TclError as e:
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{cmd_cn}] Error removing notebook for 2CMD {cmd2_cn}: {e}")
                
                
                # Remove indirect credentials whose cred_hash is in revoked_hashes
                for key in list(indirect_credentials.keys()):
                    for h, expiration,_  in revoked_hashes:
                        if indirect_credentials[key].get("cred_hash") == h:
                            del indirect_credentials[key]
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{cmd_cn}] Removed indirect credential for {key} due to revocation")
            

            
            messagebox.showinfo("Success", "CRL created and sent to nodes")
            self.destroy()
        except Exception as e:
            messagebox.showerror("Error", f"Failed to revoke access: {e}")


class CertificateRevocationDialog(tk.Toplevel):
    def __init__(self, parent):
        super().__init__(parent)
        self.title("Revoke Certificates")
        self.geometry("600x400")
        self.transient(parent)
        self.grab_set()

        tk.Label(self, text="Select Certificates to Revoke:").pack(pady=5)
        self.listbox = tk.Listbox(self, selectmode=tk.MULTIPLE, height=15, width=80)
        self.cert_map = {}
        certs = scan_certificates()
        for category in certs:
            for (cn, pu, serial) in certs[category]:
                fname = f"{cn}.crt"
                full_path = os.path.join(CERT_DIR, fname)
                self.cert_map[fname] = full_path
                self.listbox.insert(tk.END, fname)
        self.listbox.pack(pady=5)

        tk.Button(self, text="Revoke Selected", command=self.revoke_selected).pack(pady=5)
        tk.Button(self, text="Cancel", command=self.destroy).pack(pady=5)

    def revoke_selected(self):
        selected_indices = list(self.listbox.curselection())
        if not selected_indices:
            messagebox.showerror("Error", "No certificates selected.")
            return

        try:
            # Revoke each selected certificate using OpenSSL
            for idx in selected_indices:
                fname = self.listbox.get(idx)
                cert_path = self.cert_map[fname]
                subprocess.run([
                    OPENSSL_PATH, "ca",
                    "-config", CA_CONF_PATH,
                    "-revoke", cert_path
                ], check=True)
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] Revoked certificate: {fname}")

            # Generate CRL in PEM format
            timestamp = int(time.time() * 1e6)
            crl_pem = os.path.join(CRL_CERT_DIR, f"ca_{timestamp}.crl.pem")
            subprocess.run([
                OPENSSL_PATH, "ca",
                "-gencrl",
                "-config", CA_CONF_PATH,
                "-out", crl_pem
            ], check=True)
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Generated PEM CRL: {crl_pem}")

            # Convert PEM CRL to DER format
            crl_der = os.path.join(CRL_CERT_DIR, f"ca_{timestamp}.crl")
            subprocess.run([
                OPENSSL_PATH, "crl",
                "-in", crl_pem,
                "-out", crl_der,
                "-outform", "DER"
            ], check=True)
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Converted to DER CRL: {crl_der}")

            messagebox.showinfo("Success", f"CRL created:\n{crl_der}")

            # Send CRL DER using message type 0x16 to all nodes
            with open(crl_der, 'rb') as f:
                crl_data = f.read()

            new_crl = load_der_x509_crl(crl_data, default_backend())
            revoked_serials = {entry.serial_number for entry in new_crl}
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Revoked serials: {revoked_serials}")
            timestamp_bytes = struct.pack('<Q', int(time.time() * 1e6))
            type_byte = b'\x16'

            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Sessions to send CRL to: {len(gcs_sessions)} GCS, {len(cmd2_sessions)} 2CMDs")

            with clients_lock:
                for session_dict in [gcs_sessions, cmd2_sessions]:
                    for addr, session in session_dict.items():
                        session_key = session["session_key_sending"]
                        hmac_value = compute_hmac(type_byte, crl_data, timestamp_bytes, session_key)
                        msg = type_byte + crl_data + timestamp_bytes + hmac_value
                        udp_socket.sendto(msg, addr)
                        message_lenght_sent.setdefault(session.get('gcs_cn', session.get('2cmd_cn')), []).append((0x16, len(msg)))
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Sent 0x16 (CRL for certificates) to {session.get('gcs_cn', session.get('2cmd_cn'))} at {addr}")

                # Remove sessions whose peer certificates got revoked
                for addr, session in list(gcs_sessions.items()):
                    peer_serial = session.get("peer_serial")
                    if peer_serial in revoked_serials:
                        gcs_cn = session["gcs_cn"]
                        del gcs_sessions[addr]
                        with network_lock:
                            gcs_connections[cmd_cn].discard(gcs_cn)
                            if gcs_cn in network_map:
                                del network_map[gcs_cn]
                            root.after(0, update_network_view)
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Removed session for GCS {gcs_cn} at {addr} due to certificate revocation")
                        if gcs_cn in node_notebooks:
                            try:
                                notebook = node_notebooks[gcs_cn]
                                for widget in notebook_frame.winfo_children():
                                    if isinstance(widget, ttk.Label) and widget.winfo_name() == f"label_{gcs_cn}":
                                        widget.destroy()
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{cmd_cn}] Removed label for GCS {gcs_cn}")
                                        break
                                notebook.pack_forget()
                                notebook.destroy()
                                del node_notebooks[gcs_cn]
                                for (sysid, node_cn) in list(sitls.keys()):
                                    if node_cn == gcs_cn:
                                        try:
                                            canvas.delete(sitls[(sysid, node_cn)]["marker"])
                                            canvas.delete(sitls[(sysid, node_cn)]["text"])
                                            notebook.forget(sitls[(sysid, node_cn)]["tab"])
                                            sitls[(sysid, node_cn)]["tab"].destroy()
                                            del sitls[(sysid, node_cn)]
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{cmd_cn}] Removed SITL {(sysid, node_cn)} due to certificate revocation")
                                        except tk.TclError as e:
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{cmd_cn}] Error removing SITL {(sysid, node_cn)}: {e}")
                                    
                            except tk.TclError as e:
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd_cn}] Error removing notebook for GCS {gcs_cn}: {e}")

                for addr, session in list(cmd2_sessions.items()):
                    peer_serial = session.get("peer_serial")
                    if peer_serial in revoked_serials:
                        cmd2_cn = session["2cmd_cn"]
                        del cmd2_sessions[addr]
                        with network_lock:
                            gcs_connections[cmd2_cn].clear()
                            if cmd2_cn in network_map:
                                del network_map[cmd2_cn]
                            root.after(0, update_network_view)
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Removed session for 2CMD {cmd2_cn} at {addr} due to certificate revocation")
                        if cmd2_cn in node_notebooks:
                            try:
                                notebook = node_notebooks[cmd2_cn]
                                for widget in notebook_frame.winfo_children():
                                    if isinstance(widget, ttk.Label) and widget.winfo_name() == f"label_{cmd2_cn}":
                                        widget.destroy()
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{cmd_cn}] Removed label for 2CMD {cmd2_cn}")
                                        break
                                notebook.pack_forget()
                                notebook.destroy()
                                del node_notebooks[cmd2_cn]
                                for (sysid, node_cn) in list(sitls.keys()):
                                    if node_cn == cmd2_cn:
                                        try:
                                            canvas.delete(sitls[(sysid, node_cn)]["marker"])
                                            canvas.delete(sitls[(sysid, node_cn)]["text"])
                                            notebook.forget(sitls[(sysid, node_cn)]["tab"])
                                            sitls[(sysid, node_cn)]["tab"].destroy()
                                            del sitls[(sysid, node_cn)]
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{cmd_cn}] Removed SITL {(sysid, node_cn)} due to certificate revocation")
                                        except tk.TclError as e:
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{cmd_cn}] Error removing SITL {(sysid, node_cn)}: {e}")
                            except tk.TclError as e:
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd_cn}] Error removing notebook for 2CMD {cmd2_cn}: {e}")

                # Remove indirect credentials that involve revoked certificates
                keys_to_delete = []
                for key in list(indirect_credentials.keys()):
                    if len(key) == 3:
                        node1, node2, node3 = key
                    elif len(key) == 2:
                        node1, node2 = key
                        node3 = None  # or '' or skip depending on your logic
                    else:
                        raise ValueError(f"Invalid key length in indirect_credentials: {key}")
                    cn_list = [node1, node2, node3]
                    for cn in cn_list:
                        found_serial = None
                        for category in self.cert_map:
                            for entry in self.cert_map[category]:
                                if entry[0] == cn:
                                    found_serial = entry[2]
                                    break
                            if found_serial is not None:
                                break
                        if found_serial in revoked_serials:
                            keys_to_delete.append(key)
                            break
                for key in keys_to_delete:
                    del indirect_credentials[key]
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Removed indirect credential involving CNs: {key}")

            self.destroy()

        except subprocess.CalledProcessError as e:
            messagebox.showerror("OpenSSL Error", f"OpenSSL command failed:\n{e}")
        except Exception as e:
            messagebox.showerror("Error", str(e))
            
            
            


def compute_hmac(type_byte, payload, timestamp_bytes, session_key):
    h = hmac.HMAC(session_key, hashes.SHA256())
    h.update(type_byte + payload + timestamp_bytes)
    return h.finalize()[:16]


def verify_policy(msg_type, capacity_string, session, mav_type=None):
    """Verify if a message type is allowed based on the capacity string and connection type."""
    global gcs_permissions, cmd2_permissions
    access_levels = ["Access1", "Access2", "Access3"]
    capabilities = capacity_string.split(",") if capacity_string else []
    has_access = any(level in capabilities for level in access_levels)
    
    if not any(level in capabilities for level in access_levels):
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] No access for Node with capacity {capacity_string} for message type {msg_type}")
        return False

    
    
    # Determine connection type
    is_gcs = "gcs_cn" in session
    is_2cmd = "2cmd_cn" in session
    
    
    # Select appropriate permissions based on connection type
    permissions = gcs_permissions if is_gcs else cmd2_permissions if is_2cmd else {}
    
    for capacity in capabilities:
        perm = permissions.get(capacity)
        if perm is None:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Capability {capacity} not found in permissions for Node with capacity {capacity_string}")
            continue

        if isinstance(perm, list):
            if msg_type in perm:
                return True
        elif isinstance(perm, dict):
            allowed = perm.get(msg_type)
            if allowed is None:
                return True
            if mav_type and mav_type in allowed:
                return True
    
    if mav_type:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] Message type {msg_type}, MAVLink: {mav_type} not allowed for NODE with capacity {capacity_string}")
        return False
    else:   
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] Message type {msg_type} not allowed for NODE with capacity {capacity_string}")
        return False

def verify_hmac(data, session_key, cn, msg_type, addr, offset):
    global number_gap_drop
    if len(data) < 15:
        popup_queue.put(("Message Error", f"Message too short for {cn}\nMessage Type: {msg_type}\n", cn))
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] Verification failed for {cn}: Message too short")
        return None

    type_byte = data[0:1]
    payload = data[1:-24]
    timestamp_bytes = data[-24:-16]
    received_hmac = data[-16:]
    computed_hmac = compute_hmac(type_byte, payload, timestamp_bytes, session_key)
    timestamp = struct.unpack('<Q', timestamp_bytes)[0]
    current_time = int(time.time() * 1e6)

    adjusted_timestamp = timestamp - offset
    gap = abs(adjusted_timestamp - current_time)
    
    logger.info(f"[{cmd_cn}] HMAC verification for {cn}:")
    #logger.info(f"[{cmd_cn}]   Computed HMAC: {computed_hmac.hex()}")
    #logger.info(f"[{cmd_cn}]   Received HMAC: {received_hmac.hex()}")
    logger.info(f"[{cmd_cn}]   Timestamp: {timestamp}, Adjusted: {adjusted_timestamp}, Current: {current_time}, Offset: {offset}, Gap: {gap} μs")
    
    if computed_hmac != received_hmac:
        popup_queue.put(("HMAC Verification Failed", f"Possible tampering detected for {cn}\nMessage Type: {msg_type}\n", cn))
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] HMAC verification failed for {cn}")
        return None
    if LOG_MODE in (1, 2):
        logger.info(f"[{cmd_cn}] HMAC verification succeeded for {cn}, gap: {gap} μs")
    if timestamp in client_timestamps.get(cn, deque(maxlen=200)):
        popup_queue.put(("Timestamp Error", f"Repeated timestamp for {cn}\nMessage Type: {msg_type}\nTimestamp: {timestamp}\n", cn))
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] Timestamp verification failed for {cn}: Duplicate")
        return None
    if gap > 3000000:
        number_gap_drop += 1
        popup_queue.put(("Timestamp Error", f"Timestamp out of window for {cn}\nMessage Type: {msg_type}\nTimestamp: {timestamp}\n", cn))
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] Timestamp verification failed for {cn}: Outside 400ms window")
        return None
    
    client_timestamps.setdefault(cn, deque(maxlen=200)).append(timestamp)
    return type_byte, payload, gap



def establish_cmd2_connection(ip, mtls_port, udp_port, cred, cred_hash, cred_timestamp, cred_lifetime, cmd2_cn, capacity_string):
    message = f"{cmd_cn} initializating connection to {cmd2_cn}"
    serv_temp_sock.sendto(message.encode('utf-8'), server_address)  # Dummy send to set the socket's source port
    
    initial_time = time.time()*1e6
    max_attempts = 3
    for attempt in range(1, max_attempts + 1):
        try:
            context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
            context.load_cert_chain(certfile=CMD_CERT, keyfile=CMD_KEY)
            context.load_verify_locations(CA_CERT)
            context.verify_mode = ssl.CERT_REQUIRED
            client_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            secure_socket = context.wrap_socket(client_socket, server_hostname=ip)
            secure_socket.connect((ip, mtls_port))
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] mTLS connected to 2CMD {cmd2_cn} at {ip}:{mtls_port}")
            
            cert_der = secure_socket.getpeercert(binary_form=True)
            cert_obj = x509.load_der_x509_certificate(cert_der, default_backend())
            peer_cn = cert_obj.subject.get_attributes_for_oid(x509.NameOID.COMMON_NAME)[0].value
            peer_public_key = cert_obj.public_key()
            peer_serial = cert_obj.serial_number
            
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Received Peer certificate CN: {peer_cn}, Serial: {peer_serial}")
            crl = load_latest_cert_crl(CRL_CERT_DIR)
            if crl:
                revoked_serials = {r.serial_number for r in crl}
                if peer_serial in revoked_serials:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Connection rejected: peer certificate serial {peer_serial} of {peer_cn} is revoked.")
                    secure_socket.close()
                    return
            
            if not isinstance(peer_public_key, EllipticCurvePublicKey):
                raise ValueError("Expected EC public key")
            
            if peer_cn != cmd2_cn:
                raise ValueError(f"Peer CN {peer_cn} does not match expected {cmd2_cn}")
            
            secure_socket.send(len(cred).to_bytes(4, 'big') + cred)
            
            ready_token = recv_exact(secure_socket, 1)
            if ready_token != TIME_SYNC_READY_TOKEN:
                raise ValueError("Unexpected time sync readiness token from UXV")
            try:
                time_sync_logger = logger.info if LOG_MODE in (1, 2) else None
                ts_result = perform_time_sync(
                    secure_socket,
                    role="client",
                    logger=time_sync_logger,
                    log_prefix=f"[{cmd_cn}] Time sync with {peer_cn}: ",
                )
            except TimeSyncError as e:
                raise ValueError(f"Time synchronisation failed with {peer_cn}: {e}") from e
            offset = ts_result.offset_us

            offset_per_node.setdefault(cmd2_cn, []).append(offset)
            
            shared_secret = PRcmd.exchange(ec.ECDH(), peer_public_key)

            session_key_sending = HKDF(
                algorithm=hashes.SHA256(),
                length=SESSION_KEY_LENGTH,
                salt=None,
                info=b"session_key_sending",
            ).derive(shared_secret)
            
            session_key_receiving = HKDF(
                algorithm=hashes.SHA256(),
                length=SESSION_KEY_LENGTH,
                salt=None,
                info=b"session_key_receiving",
            ).derive(shared_secret)
            
            if not session_key_sending or not session_key_receiving:
                raise Exception("Key derivation failed")
            
            addr = (ip, udp_port)
            with clients_lock:
                cmd2_sessions[addr] = {
                    "shared_secret": shared_secret,
                    "session_key_sending": session_key_sending,
                    "session_key_receiving": session_key_receiving,
                    "offset": offset,
                    "2cmd_cn": cmd2_cn,
                    "2cmd_pu": cert_obj.public_key(),
                    "hash": cred_hash,
                    "last_map_time": time.time(),
                    "mtls_port": mtls_port,
                    "capacity_string": capacity_string,
                    "session_created_at": time.time(),
                    "cred_timestamp": cred_timestamp,
                    "cred_lifetime": cred_lifetime,
                    "peer_serial": peer_serial,
                    "renewal_count": 0,
                }
                client_timestamps[cmd2_cn] = deque(maxlen=200)
                popup_counts[cmd2_cn] = []
            
            local_udp_port = udp_socket.getsockname()[1]
            try:
                secure_socket.sendall(local_udp_port.to_bytes(2, 'big'))  # Send UDP port
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] Sent UDP port {local_udp_port} to 2CMD {cmd2_cn}")
            except Exception as e:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] Failed to send UDP port to 2CMD {cmd2_cn}: {e}")
                return
            
            if cmd2_cn not in node_notebooks:
                cmd2_notebook = ttk.Notebook(notebook_frame)
                cmd2_notebook.pack(fill=tk.BOTH, expand=True)
                # Check if label already exists to avoid duplicates
                for widget in notebook_frame.winfo_children():
                    if isinstance(widget, ttk.Label) and widget.winfo_name() == f"label_{cmd2_cn}":
                        break
                else:
                    cmd2_label = ttk.Label(notebook_frame, text=f"2CMD: {cmd2_cn}", name=f"label_{cmd2_cn}")
                    cmd2_label.pack()
                node_notebooks[cmd2_cn] = cmd2_notebook
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] Created notebook for 2CMD {cmd2_cn}")
            
            final_time=time.time()*1e6
            connection_establishement_time.setdefault(cmd2_cn,[]).append(final_time-initial_time)
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Initial timestamp for {cmd_cn}-{cmd2_cn} connection: {initial_time} μs")
                logger.info(f"[{cmd_cn}] Connection establishment time for 2CMD {cmd2_cn}: {final_time-initial_time} μs")
            secure_socket.close()
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Session established for 2CMD {cmd2_cn} at {addr} with capacity level {capacity_string}")
            return
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Attempt {attempt} to connect to 2CMD {cmd2_cn} failed: {e}")
            popup_queue.put(("Error", f"Attempt {attempt} to connect to 2CMD {cmd2_cn} failed: {e}",attempt, cmd2_cn))

            if attempt < max_attempts:
                time.sleep(1)  # brief pause before retry
                continue
            # after 3rd failure:
            popup_queue.put(("Connection Error",f"Failed to connect to 2CMD {cmd2_cn} after {max_attempts} attempts:\n{e}",cmd2_cn))
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Giving up on connecting to 2CMD {cmd2_cn} after {max_attempts} attempts.")
            return
        
def establish_gcs_connection(ip, mtls_port, udp_port, cred, cred_hash, cred_timestamp, cred_lifetime, gcs_cn, capacity_string):
    message = f"{cmd_cn} initializating connection to {gcs_cn}"
    serv_temp_sock.sendto(message.encode('utf-8'), server_address)
    initial_time = time.time()*1e6
    max_attempts = 3
    for attempt in range(1, max_attempts + 1):    
        try:
            context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
            context.load_cert_chain(certfile=CMD_CERT, keyfile=CMD_KEY)
            context.load_verify_locations(CA_CERT)
            context.verify_mode = ssl.CERT_REQUIRED
            client_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            secure_socket = context.wrap_socket(client_socket, server_hostname=ip)
            secure_socket.connect((ip, mtls_port))
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] mTLS connected to GCS {gcs_cn} at {ip}:{mtls_port}")
            
            cert_der = secure_socket.getpeercert(binary_form=True)
            cert_obj = x509.load_der_x509_certificate(cert_der, default_backend())
            peer_cn = cert_obj.subject.get_attributes_for_oid(x509.NameOID.COMMON_NAME)[0].value
            peer_public_key = cert_obj.public_key()
            peer_serial = cert_obj.serial_number
            
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Received Peer certificate CN: {peer_cn}, Serial: {peer_serial}")
            crl = load_latest_cert_crl(CRL_CERT_DIR)
            if crl:
                revoked_serials = {r.serial_number for r in crl}
                if peer_serial in revoked_serials:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Connection rejected: peer certificate serial {peer_serial} of {peer_cn} is revoked.")
                    secure_socket.close()
                    return
            
            if not isinstance(peer_public_key, EllipticCurvePublicKey):
                raise ValueError("Expected EC public key")
            try:
                ssl.match_hostname(secure_socket.getpeercert(), ip)
            except ssl.CertificateError as e:
                secure_socket.close()
                raise ValueError(f"Peer certificate does not match expected IP {ip}: {e}") from e
            if peer_cn != gcs_cn:
                raise ValueError(f"Peer CN {peer_cn} does not match expected {gcs_cn}")
            
            secure_socket.send(len(cred).to_bytes(4, 'big') + cred)
            
            ready_token = recv_exact(secure_socket, 1)
            if ready_token != TIME_SYNC_READY_TOKEN:
                raise ValueError("Unexpected time sync readiness token from UXV")
                
            try:
                time_sync_logger = logger.info if LOG_MODE in (1, 2) else None
                ts_result = perform_time_sync(
                    secure_socket,
                    role="client",
                    logger=time_sync_logger,
                    log_prefix=f"[{cmd_cn}] Time sync with {peer_cn}: ",
                )
            except TimeSyncError as e:
                raise ValueError(f"Time synchronisation failed with {peer_cn}: {e}") from e
            offset = ts_result.offset_us
            
            offset_per_node.setdefault(gcs_cn, []).append(offset)
            
            shared_secret = PRcmd.exchange(ec.ECDH(), peer_public_key)

            session_key_sending = HKDF(
                algorithm=hashes.SHA256(),
                length=SESSION_KEY_LENGTH,
                salt=None,
                info=b"session_key_sending",
            ).derive(shared_secret)
            
            session_key_receiving = HKDF(
                algorithm=hashes.SHA256(),
                length=SESSION_KEY_LENGTH,
                salt=None,
                info=b"session_key_receiving",
            ).derive(shared_secret)
            
            if not session_key_sending:
                raise Exception("Key derivation failed for sending")
            
            if not session_key_receiving:
                raise Exception("Key derivation failed for receiving")
            
            addr = (ip, udp_port)
            with clients_lock:
                gcs_sessions[addr] = {
                    "shared_secret": shared_secret,
                    "session_key_sending": session_key_sending,
                    "session_key_receiving": session_key_receiving,
                    "offset": offset,
                    "gcs_cn": gcs_cn,
                    "gcs_pu": cert_obj.public_key(),
                    "hash": cred_hash,
                    "last_map_time": time.time(),
                    "mtls_port": mtls_port,
                    "capacity_string": capacity_string,
                    "session_created_at": time.time(),
                    "cred_timestamp": cred_timestamp,
                    "cred_lifetime": cred_lifetime,
                    "peer_serial": peer_serial,
                    "renewal_count": 0,
                }
                client_timestamps[gcs_cn] = deque(maxlen=200)
                popup_counts[gcs_cn] = []
            
            with network_lock:
                gcs_connections[cmd_cn].add(gcs_cn)
            
            local_udp_port = udp_socket.getsockname()[1]
            try:
                secure_socket.sendall(local_udp_port.to_bytes(2, 'big'))  # Send UDP port
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] Sent UDP port {local_udp_port} to GCS {gcs_cn}")
            except Exception as e:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] Failed to send UDP port to GCS {gcs_cn}: {e}")
                return
            
            if gcs_cn not in node_notebooks:
                gcs_notebook = ttk.Notebook(notebook_frame)
                gcs_notebook.pack(fill=tk.BOTH, expand=True)
                # Check if label already exists to avoid duplicates
                for widget in notebook_frame.winfo_children():
                    if isinstance(widget, ttk.Label) and widget.winfo_name() == f"label_{gcs_cn}":
                        break
                else:
                    gcs_label = ttk.Label(notebook_frame, text=f"GCS: {gcs_cn}", name=f"label_{gcs_cn}")
                    gcs_label.pack()
                node_notebooks[gcs_cn] = gcs_notebook
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] Created notebook for GCS {gcs_cn}")
            final_time=time.time()*1e6
            connection_establishement_time.setdefault(gcs_cn,[]).append(final_time-initial_time)
            print(f"[{cmd_cn}] Initial timestamp for cmd-gcs connection - {initial_time} μs ")
            print(f"[{cmd_cn}] Connection establishment time for GCS {gcs_cn}: {final_time-initial_time} μs")
            secure_socket.close()
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Session established for GCS {gcs_cn} at {addr}")
            return
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Attempt {attempt} to connect to GCS {gcs_cn} failed: {e}")
            popup_queue.put(("Error", f"Attempt {attempt} to connect to GCS {gcs_cn} failed: {e}",attempt, gcs_cn))
            if attempt < max_attempts:
                time.sleep(1)  # brief pause before retry
                continue
            # after 3rd failure:
            popup_queue.put(("Connection Error",f"Failed to connect to GCS {gcs_cn} after {max_attempts} attempts:\n{e}", gcs_cn))
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Giving up on connecting to GCS {gcs_cn} after {max_attempts} attempts.")
            return
        
        
def check_node_timeouts():
    current_time = time.time()
    with clients_lock:
        for addr, session_info in list(gcs_sessions.items()):
            if current_time - session_info["last_map_time"] > NETWORK_MAP_INTERVAL:
                gcs_cn = session_info["gcs_cn"]
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] GCS {gcs_cn} at {addr} timed out (no 0x06 message)")
                del gcs_sessions[addr]
                pending_dh.pop(addr, None)
                if gcs_cn in node_notebooks:
                    try:
                        notebook = node_notebooks[gcs_cn]
                        for widget in notebook_frame.winfo_children():
                            if isinstance(widget, ttk.Label) and widget.winfo_name() == f"label_{gcs_cn}":
                                widget.destroy()
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd_cn}] Removed label for GCS {gcs_cn}")
                                break
                        notebook.pack_forget()
                        notebook.destroy()
                        del node_notebooks[gcs_cn]
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Removed notebook for GCS {gcs_cn}")
                    except tk.TclError as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Error removing notebook for GCS {gcs_cn}: {e}")
                popup_queue.put(("Timeout", f"GCS {gcs_cn} disconnected due to timeout", gcs_cn))
                with network_lock:
                    gcs_connections[cmd_cn].discard(gcs_cn)
                    if gcs_cn in network_map:
                        del network_map[gcs_cn]
                    root.after(0, update_network_view)
                credentials = load_credentials(CREDENTIAL_DIR, PUcmd)
                latest_cred = None
                latest_ts = 0
                with crl_lock:
                    for cred in credentials:
                        if cred["type"] == 0x02 and cred["pu2"].public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo) == \
                           session_info["gcs_pu"].public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo) and cred["timestamp"] > latest_ts and \
                           cred["hash"] not in crl:
                            latest_cred = cred
                            latest_ts = cred["timestamp"]
                    if latest_cred:
                        threading.Thread(target=establish_gcs_connection, args=(addr[0], session_info.get("mtls_port"), addr[1], latest_cred["raw"], session_info["hash"], session_info["cred_timestamp"], session_info["cred_lifetime"], gcs_cn, session_info["capacity_string"]), daemon=True).start()
        
        for addr, session_info in list(cmd2_sessions.items()):
            if current_time - session_info["last_map_time"] > NETWORK_MAP_INTERVAL:
                cmd2_cn = session_info["2cmd_cn"]
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] 2CMD {cmd2_cn} at {addr} timed out (no 0x10 message)")
                del cmd2_sessions[addr]
                pending_dh.pop(addr, None)
                if cmd2_cn in node_notebooks:
                    try:
                        notebook = node_notebooks[cmd2_cn]
                        for widget in notebook_frame.winfo_children():
                            if isinstance(widget, ttk.Label) and widget.winfo_name() == f"label_{cmd2_cn}":
                                widget.destroy()
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd_cn}] Removed label for 2CMD {cmd2_cn}")
                                break
                        notebook.pack_forget()
                        notebook.destroy()
                        del node_notebooks[cmd2_cn]
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Removed notebook for 2CMD {cmd2_cn}")
                    except tk.TclError as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Error removing notebook for 2CMD {cmd2_cn}: {e}")
                popup_queue.put(("Timeout", f"2CMD {cmd2_cn} disconnected due to timeout", cmd2_cn))
                with network_lock:
                    gcs_connections[cmd2_cn].clear()
                    if cmd2_cn in network_map:
                        del network_map[cmd2_cn]
                    root.after(0, update_network_view)
                credentials = load_credentials(CREDENTIAL_DIR, PUcmd)
                latest_cred = None
                latest_ts = 0
                with crl_lock:
                    for cred in credentials:
                        if cred["type"] == 0x01 and cred["pu2"].public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo) == \
                           session_info["2cmd_pu"].public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo) and cred["timestamp"] > latest_ts and \
                           cred["hash"] not in crl:
                            latest_cred = cred
                            latest_ts = cred["timestamp"]
                    if latest_cred:
                        threading.Thread(target=establish_cmd2_connection, args=(addr[0], session_info.get("mtls_port"), addr[1], latest_cred["raw"], session_info["hash"], session_info["cred_timestamp"], session_info["cred_lifetime"], cmd2_cn, session_info["capacity_string"]), daemon=True).start()
    root.after(1000, check_node_timeouts)

def process_popups():
    try:
        popup_data = popup_queue.get_nowait()
        if len(popup_data) == 3:
            title, message, cn = popup_data
        elif len(popup_data) == 2:
            title, message = popup_data
            cn = None  # ou outro valor default
        else:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Unexpected popup format: {popup_data}")
            return
        current_time = time.time()
        popup_counts[cn] = [t for t in popup_counts.get(cn, []) if current_time - t < 60]
        if len(popup_counts[cn]) < 5:
            popup_counts[cn].append(current_time)
            messagebox.showerror(title, message)
    except Empty:
        pass
    root.after(10, process_popups)

def update_network_view():
    with network_lock:
        network_text.configure(state='normal')
        network_text.delete('1.0', tk.END)
        network_text.insert(tk.END, "CMD\n")
        for gcs_cn in sorted(gcs_connections[cmd_cn]):
            network_text.insert(tk.END, f"  {gcs_cn}\n")
            for uxv_cn in sorted(network_map.get(gcs_cn, [])):
                network_text.insert(tk.END, f"    {uxv_cn}\n")
        for cmd2_cn in sorted(gcs_connections.keys()):
            if cmd2_cn != cmd_cn and cmd2_cn in [info["2cmd_cn"] for addr, info in cmd2_sessions.items()]:
                network_text.insert(tk.END, f"  {cmd2_cn}\n")
                for gcs_cn in sorted(gcs_connections[cmd2_cn]):
                    network_text.insert(tk.END, f"    {gcs_cn}\n")
                    for uxv_cn in sorted(network_map.get(gcs_cn, [])):
                        network_text.insert(tk.END, f"      {uxv_cn}\n")
        network_text.configure(state='disabled')
    
    # Only update the dropdown if the dialog exists and is in a valid state
    if hasattr(root, 'new_connection_dialog_instance') and root.new_connection_dialog_instance.winfo_exists():
        root.new_connection_dialog_instance.update_node1_gcs_dropdown()
    
    if hasattr(root, 'new_change_capacity_instance') and root.new_change_capacity_instance.winfo_exists():
        root.new_change_capacity_instance.update_node1_gcs_dropdown()

def send_waypoint_wrapper():
    send_button.config(state=tk.DISABLED)
    try:
        file_path = filedialog.askopenfilename(filetypes=[("Waypoint files", "*.waypoints")])
        if not file_path:
            return
        if not file_path.lower().endswith('.waypoints'):
            popup_queue.put(("File Error", "Please select a .waypoints file", "waypoint"))
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Invalid file extension")
            return
        
        dialog = tk.Toplevel(root)
        dialog.title("Select Node")
        dialog.geometry("300x200")
        
        tk.Label(dialog, text="Select Node(s) to send mission:").pack(pady=5)
        listbox = tk.Listbox(dialog, selectmode=tk.MULTIPLE, height=5)
        with clients_lock:
            for addr, session_info in gcs_sessions.items():
                listbox.insert(tk.END, session_info["gcs_cn"])
            for addr, session_info in cmd2_sessions.items():
                listbox.insert(tk.END, session_info["2cmd_cn"])
        listbox.pack(pady=5)
        
        def on_submit():
            selected_indices = listbox.curselection()
            if not selected_indices:
                messagebox.showerror("Error", "Please select at least one node")
                return
            selected_nodes = []
            with clients_lock:
                for idx in selected_indices:
                    cn = listbox.get(idx)
                    for addr, session_info in gcs_sessions.items():
                        if session_info["gcs_cn"] == cn:
                            selected_nodes.append(('gcs', addr))
                            break
                    for addr, session_info in cmd2_sessions.items():
                        if session_info["2cmd_cn"] == cn:
                            selected_nodes.append(('2cmd', addr))
                            break
            if selected_nodes:
                threading.Thread(target=send_waypoint, args=(file_path, selected_nodes), daemon=True).start()
                dialog.destroy()
            else:
                messagebox.showerror("Error", "No valid nodes selected")
        
        tk.Button(dialog, text="Send", command=on_submit).pack(pady=5)
        tk.Button(dialog, text="Cancel", command=dialog.destroy).pack(pady=5)
        dialog.transient(root)
        dialog.grab_set()
    finally:
        send_button.config(state=tk.NORMAL)

def send_waypoint(file_path, nodes):
    try:
        with open(file_path, 'rb') as f:
            payload = f.read()
        timestamp = int(time.time() * 1e6)
        timestamp_bytes = struct.pack('<Q', timestamp)
        type_byte = b'\x02'
        with clients_lock:
            for node_type, addr in nodes:
                session_info = gcs_sessions.get(addr, cmd2_sessions.get(addr))
                if not session_info:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] No session for {node_type} at {addr}")
                    continue
                session_key = session_info["session_key_sending"]
                cn = session_info.get("gcs_cn", session_info.get("2cmd_cn"))
                hmac_value = compute_hmac(type_byte, payload, timestamp_bytes, session_key)
                data = type_byte + payload + timestamp_bytes + hmac_value
                udp_socket.sendto(data, addr)
                message_lenght_sent.setdefault(cn, []).append((0x02, len(data)))
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] Sent waypoint mission to {node_type} {cn}: Type=0x02, Timestamp={timestamp}, Size={len(payload)}, File={os.path.basename(file_path)}")
        popup_queue.put(("Success", "Waypoint mission sent successfully", "waypoint"))
    except Exception as e:
        popup_queue.put(("Send Error", f"Failed to send mission: {e}", "waypoint"))
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] Error sending waypoint: {e}")


def send_disconnection():
    """Send periodic 0x12 heartbeat to all connected GCSs and 2CMDs."""
    with clients_lock:
        for session_dict in [gcs_sessions, cmd2_sessions]:
            for addr, session in session_dict.items():
                if verify_policy(b'\x07', session["capacity_string"], session):
                    type_byte = b'\x07'
                    payload = cmd_cn.encode('utf-8')
                    timestamp = int(time.time() * 1e6)
                    timestamp_bytes = struct.pack('<Q', timestamp)
                    hmac_value = compute_hmac(type_byte, payload, timestamp_bytes, session["session_key_sending"])
                    message = type_byte + payload + timestamp_bytes + hmac_value
                    udp_socket.sendto(message, addr)
                    message_lenght_sent.setdefault(session.get('gcs_cn', session.get('2cmd_cn')), []).append((0x07, len(message)))
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Sent Disconnection to {session.get('gcs_cn', session.get('2cmd_cn'))} at {addr} on timestamp: {timestamp}")
         

def resize_map_and_redraw(event):
    """Handles canvas resizing, redraws the map, and repositions all SITL markers."""
    global current_map_photo, current_map_width, current_map_height
    
    # Get the new size of the canvas
    canvas_width = event.width
    canvas_height = event.height

    # Avoid processing tiny, invalid sizes during initial setup
    if canvas_width < 2 or canvas_height < 2 or original_map_image is None:
        return

    # Calculate aspect ratios to maintain proportions
    img_aspect = original_map_image.width / original_map_image.height
    canvas_aspect = canvas_width / canvas_height

    # Determine the new image dimensions to fit the canvas without distortion
    if canvas_aspect > img_aspect:
        # Canvas is wider than the image, so height is the limiting factor
        new_h = canvas_height
        new_w = int(new_h * img_aspect)
    else:
        # Canvas is taller than the image, so width is the limiting factor
        new_w = canvas_width
        new_h = int(new_w / img_aspect)

    # Update the global variables for the current map dimensions
    current_map_width = new_w
    current_map_height = new_h
    
    # Resize the original high-quality image
    resized_image = original_map_image.resize((new_w, new_h), Image.Resampling.LANCZOS)
    current_map_photo = ImageTk.PhotoImage(resized_image)

    # Redraw everything on the canvas
    canvas.delete("all")
    canvas.create_image(0, 0, anchor=tk.NW, image=current_map_photo)

    # Reposition all existing SITL markers according to the new map size
    for sitl_key, sitl_info in sitls.items():
        telemetry = sitl_info.get("telemetry", {})
        lat = telemetry.get("lat")
        lon = telemetry.get("lon")

        if lat is not None and lon is not None:
            if lon1 <= lon <= lon2 and lat2 <= lat <= lat1:
                # Use the NEW dimensions for calculation
                x_pixel = (lon - lon1) / (lon2 - lon1) * current_map_width
                y_pixel = (lat1 - lat) / (lat1 - lat2) * current_map_height
                
                # Re-create the markers (since we cleared the canvas)
                marker_radius = 5
                sitl_info["marker"] = canvas.create_oval(
                    x_pixel - marker_radius, y_pixel - marker_radius,
                    x_pixel + marker_radius, y_pixel + marker_radius,
                    fill=sitl_info["color"], # Keep original color
                )
                sitl_info["text"] = canvas.create_text(x_pixel, y_pixel, text=str(sitl_key[0]), fill="white")

def setup_mavlink_and_gui():
    global udp_socket, canvas, send_button, photo, notebook_frame, network_text, network_frame
    global original_map_image, current_map_photo, lon1, lat1, lon2, lat2, IMAGE_WIDTH, IMAGE_HEIGHT
    
    if LOG_MODE in (1, 2):
        logger.info(f"[{cmd_cn}] Starting MAVLink and GUI setup")
    
    image_path = os.path.join(CERT_DIR, "mission_image", "mission_image.tif")

    try:
        with rasterio.open(image_path) as dataset:
            IMAGE_WIDTH = dataset.width
            IMAGE_HEIGHT = dataset.height
            lon1, lat2, lon2, lat1 = dataset.bounds.left, dataset.bounds.bottom, dataset.bounds.right, dataset.bounds.top
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd_cn}] Loaded GeoTIFF image from {image_path}, dimensions: {IMAGE_WIDTH}x{IMAGE_HEIGHT}, bounds: {dataset.bounds}")

            image_data = dataset.read([1, 2, 3])
            image_array = image_data.transpose((1, 2, 0))
            original_map_image = Image.fromarray(image_array) # Store the original PIL image
    except Exception as e:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] Error loading GeoTIFF image {image_path}: {e}")
        root.destroy()
        exit(1)

    udp_socket = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    udp_socket.setblocking(False)
    udp_socket.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 65536)
    udp_socket.bind(("", 0))
    local_udp_port = udp_socket.getsockname()[1]
    if LOG_MODE in (1, 2):
        logger.info(f"[{cmd_cn}] UDP socket bound to dynamic port: {udp_socket.getsockname()[1]}")
    
    mav = mavutil.mavlink_connection('udp:127.0.0.1:14500', source_system=255)
    
    threading.Thread(target=session_key_monitor, daemon=True).start()
    threading.Thread(target=cleanup_pending_dh, daemon=True).start()
    threading.Thread(target=send_heartbeat, daemon=True).start()
    threading.Thread(target=credential_expiry_monitor, daemon=True).start()
    threading.Thread(target=indirect_credential_expiry_monitor, daemon=True).start()
    threading.Thread(target=certificate_renewal_monitor, daemon=True).start()
    threading.Thread(target=crl_lifetime_monitor, daemon=True).start()
    
    
    root.deiconify()
    root.title("Drone Tracker")
    

    canvas = tk.Canvas(root)
        
    network_frame = tk.Frame(root)
    network_frame.pack(side=tk.LEFT, fill=tk.Y)
    network_label = tk.Label(network_frame, text="Network Mapping", font=("Arial", 12, "bold"))
    network_label.pack(anchor='w')
    network_text = tk.Text(network_frame, width=20, height=30, font=("Courier", 10))
    network_text.pack(fill=tk.BOTH, expand=True)
    network_text.configure(state='disabled')
    
    canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
    canvas.bind('<Configure>', resize_map_and_redraw)
    
    def create_new_connection_dialog():
        dialog = NewConnectionDialog(root)
        root.new_connection_dialog_instance = dialog
        
    def create_change_capacity_dialog():
        dialog = ChangeCapacityDialog(root)
        root.new_change_capacity_instance = dialog

    
    sidebar = tk.Frame(root, bd=1, relief=tk.SOLID)
    sidebar.pack(side=tk.RIGHT, fill=tk.Y, padx=5, pady=5)
    tk.Button(sidebar, text="New Connection", command=lambda: create_new_connection_dialog()).pack(pady=10)
    tk.Button(sidebar, text="Access Revocation", command=lambda: AccessRevocationDialog(root)).pack(pady=10)
    tk.Button(sidebar, text="Change Capacity", command=lambda: create_change_capacity_dialog()).pack(pady=10)
    send_button = tk.Button(sidebar, text="Send Waypoint Mission", command=send_waypoint_wrapper)
    send_button.pack(pady=10)
    
    tk.Button(sidebar, text="Revoke Certificates", command=lambda:CertificateRevocationDialog(root)).pack(pady=10)
    
    notebook_frame = ttk.Frame(root)
    notebook_frame.pack(fill=tk.BOTH, expand=True)
    
    def update_gui():
        global color_index
        current_time = time.time()

        while True:
            try:
                data, addr = udp_socket.recvfrom(65536)
                global message_processing_time
                message_processing_start_time = time.perf_counter()
                logger.info(f"[{cmd_cn}] message start timestamp {message_processing_start_time}")
                #logger.info(f"[{cmd_cn}] Received UDP from {addr}, Type={data[0:1].hex()}")
                session_info = gcs_sessions.get(addr, cmd2_sessions.get(addr))
                if not session_info:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] No session for addr {addr}")
                    continue
                cn = session_info.get("gcs_cn", session_info.get("2cmd_cn"))
                msg_type = data[0] if data else None
                message_lenght_received.setdefault(cn, []).append((msg_type, len(data)))
                session_key = session_info["session_key_receiving"]
                capacity_string = session_info.get("capacity_string", "")
                offset = session_info.get("offset", 0)
                result = verify_hmac(data, session_key, cn, data[0:1].hex(), addr, offset)
                
                type_byte = data[0:1]
                if type_byte not in VALID_TYPES:
                    popup_queue.put(("Type Error", f"Invalid message type: {type_byte.hex()} for {cn}\n", cn))
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Invalid type for {cn}: {type_byte.hex()}")
                    return None
                
                if not verify_policy(type_byte, capacity_string, session_info):
                    popup_queue.put(("Policy Error", f"Message type {type_byte.hex()} not allowed for {cn} with capabilities {capacity_string}\n", cn))
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Policy violation: Message type {type_byte.hex()} not allowed for {cn}")
                    return None
                if not result:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Verification failed for {cn}, Type={data[0:1].hex()}")
                    continue
                type_byte, payload, gap = result
                gap_values_per_connection.setdefault(cn, []).append((type_byte,gap))
                timestamp = struct.unpack('<Q', data[-24:-16])[0]

                if type_byte == b'\x01':
                    len_cn = payload[0]
                    uxv_cn = payload[1:1+len_cn].decode('utf-8')
                    mavlink_data = payload[1+len_cn:]
                    parsed_msgs = mav.mav.parse_buffer(mavlink_data)
                    msg = parsed_msgs[0] if parsed_msgs else None
                    if msg:
                        msg_type = msg.get_type()
                        sysid = msg.get_srcSystem()
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Received from {cn}:Type={data[0:1].hex()}  Type_mgs={msg_type}, SysID={sysid}, UXV={uxv_cn}")
                        
                        sitl_key = (sysid, cn)
                        if msg_type == "HEARTBEAT":
                            with sysid_to_gcs_lock:
                                sysid_to_uxv_cn[sysid] = uxv_cn
                                sysid_to_gcs[sysid] = cn  # Still update mapping for other logic
                                #logger.info(f"[{cmd_cn}] SYSID {sysid} mapped to UXV {uxv_cn}, Node {cn}")

                            node_notebook = node_notebooks.get(cn)
                            if not node_notebook:
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd_cn}] No notebook for Node {cn}")
                                continue

                            if sitl_key not in sitls and len(sitls) < MAX_SITLS * len(node_notebooks):
                                color = colors[color_index % len(colors)]
                                color_index += 1
                                marker = canvas.create_oval(-10, -10, -10, -10, fill=color)
                                text = canvas.create_text(-10, -10, text=str(sysid), fill="white")
                                tab = tk.Frame(node_notebook)
                                telemetry_label = tk.Label(tab, text="Telemetry: Waiting for data...")
                                telemetry_label.pack()
                                node_notebook.add(tab, text=f"{uxv_cn} (SysID {sysid})")
                                sitls[sitl_key] = {
                                    "marker": marker,
                                    "text": text,
                                    "tab": tab,
                                    "telemetry_label": telemetry_label,
                                    "last_timestamp": current_time,
                                    "telemetry": {},
                                    "color": color
                                    
                                }
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd_cn}] Added SITL {sitl_key} for Node {cn} with color {color}")

                        if sitl_key in sitls and msg:
                            sitls[sitl_key]["last_timestamp"] = current_time
                            if msg_type == "GLOBAL_POSITION_INT":
                                lat = msg.lat / 1e7
                                lon = msg.lon / 1e7
                                sitls[sitl_key]["telemetry"]["lat"] = lat
                                sitls[sitl_key]["telemetry"]["lon"] = lon
                                if lon1 <= lon <= lon2 and lat2 <= lat <= lat1:
                                    x_pixel = (lon - lon1) / (lon2 - lon1) * current_map_width
                                    y_pixel = (lat1 - lat) / (lat1 - lat2) * current_map_height
                                    marker_radius = 5
                                    canvas.coords(sitls[sitl_key]["marker"],
                                                x_pixel - marker_radius, y_pixel - marker_radius,
                                                x_pixel + marker_radius, y_pixel + marker_radius)
                                    canvas.coords(sitls[sitl_key]["text"], x_pixel, y_pixel)
                                else:
                                    canvas.coords(sitls[sitl_key]["marker"], -10, -10, -10, -10)
                                    canvas.coords(sitls[sitl_key]["text"], -10, -10)
                            elif msg_type == "VFR_HUD":
                                sitls[sitl_key]["telemetry"]["groundspeed"] = msg.groundspeed
                                sitls[sitl_key]["telemetry"]["altitude"] = msg.alt
                                sitls[sitl_key]["telemetry"]["climb"] = msg.climb
                                sitls[sitl_key]["telemetry"]["heading"] = msg.heading

                            telemetry = sitls[sitl_key]["telemetry"]
                            telemetry_text = (f"Telemetry:\n"
                                            f"Groundspeed: {telemetry.get('groundspeed', 0):.2f} m/s\n"
                                            f"Altitude: {telemetry.get('altitude', 0):.2f} m\n"
                                            f"Vertical Speed: {telemetry.get('climb', 0):.2f} m/s\n"
                                            f"Heading: {telemetry.get('heading', 0)}°")
                            try:
                                if sitls[sitl_key]["telemetry_label"].winfo_exists():
                                    sitls[sitl_key]["telemetry_label"].config(text=telemetry_text)
                                else:
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{cmd_cn}] Telemetry label for {sitl_key} no longer exists")
                            except tk.TclError as e:
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd_cn}] Error updating telemetry label for {sitl_key}: {e}")

                elif type_byte == b'\x06':
                    with clients_lock:
                        if addr in gcs_sessions:
                            gcs_sessions[addr]["last_map_time"] = current_time
                            gcs_cn = gcs_sessions[addr]["gcs_cn"]
                        else:
                            gcs_cn = None
                    if gcs_cn:
                        offset = 0
                        uxvs_for_this_gcs = []
                        while offset < len(payload):
                            len_gcs_cn = payload[offset]
                            offset += 1
                            gcs_cn_from_payload = payload[offset:offset+len_gcs_cn].decode('utf-8')
                            offset += len_gcs_cn
                            len_uxv_cn = payload[offset]
                            offset += 1
                            uxv_cn = payload[offset:offset+len_uxv_cn].decode('utf-8')
                            offset += len_uxv_cn
                            gcs_cn = gcs_cn_from_payload
                            uxvs_for_this_gcs.append(uxv_cn)
                        with network_lock:
                            gcs_connections[cmd_cn].add(gcs_cn)
                            network_map[gcs_cn] = uxvs_for_this_gcs
                        root.after(0, update_network_view)
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Received network mapping from GCS {gcs_cn}: {uxvs_for_this_gcs}")
                        with sysid_to_gcs_lock:
                            for sysid, mapped_uxv_cn in sysid_to_uxv_cn.items():
                                if mapped_uxv_cn in uxvs_for_this_gcs:
                                    sysid_to_gcs[sysid] = gcs_cn
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{cmd_cn}] Updated sysid_to_gcs: SysID={sysid} maps to GCS {gcs_cn}")

                elif type_byte == b'\x10':
                    with clients_lock:
                        if addr in cmd2_sessions:
                            cmd2_sessions[addr]["last_map_time"] = current_time
                            cmd2_cn = cmd2_sessions[addr]["2cmd_cn"]
                        else:
                            cmd2_cn = None
                    if cmd2_cn:
                        offset = 0
                        gcs_to_uxvs = {}
                        while offset < len(payload):
                            len_gcs_cn = payload[offset]
                            offset += 1
                            gcs_cn = payload[offset:offset+len_gcs_cn].decode('utf-8')
                            offset += len_gcs_cn
                            len_uxv_cn = payload[offset]
                            offset += 1
                            uxv_cn = payload[offset:offset+len_uxv_cn].decode('utf-8')
                            offset += len_uxv_cn
                            gcs_to_uxvs.setdefault(gcs_cn, []).append(uxv_cn)
                        with network_lock:
                            gcs_connections[cmd2_cn] = set(gcs_to_uxvs.keys())
                            network_map[cmd2_cn] = list(gcs_to_uxvs.keys())
                            for gcs_cn, uxvs in gcs_to_uxvs.items():
                                network_map[gcs_cn] = uxvs
                        root.after(0, update_network_view)
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Received network mapping from 2CMD {cmd2_cn}: {gcs_to_uxvs}")
                        with sysid_to_gcs_lock:
                            for sysid, mapped_uxv_cn in sysid_to_uxv_cn.items():
                                for gcs_cn, uxvs in gcs_to_uxvs.items():
                                    if mapped_uxv_cn in uxvs:
                                        sysid_to_gcs[sysid] = gcs_cn
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{cmd_cn}] Updated sysid_to_gcs: SysID={sysid} maps to GCS {gcs_cn}")

                elif type_byte == b'\x07':
                    node_cn_bytes = payload.decode('utf-8')
                    with clients_lock:
                        if addr in gcs_sessions:
                            gcs_cn = gcs_sessions[addr]["gcs_cn"]
                            if node_cn_bytes == gcs_cn:
                                del gcs_sessions[addr]
                                with network_lock:
                                    gcs_connections[cmd_cn].discard(gcs_cn)
                                    if gcs_cn in network_map:
                                        del network_map[gcs_cn]
                                    root.after(0, update_network_view)
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd_cn}] Removed session for GCS {gcs_cn} at {addr} due to GCS shutdown")
                                if gcs_cn in node_notebooks:
                                    try:
                                        notebook = node_notebooks[gcs_cn]
                                        for widget in notebook_frame.winfo_children():
                                            if isinstance(widget, ttk.Label) and widget.winfo_name() == f"label_{gcs_cn}":
                                                widget.destroy()
                                                if LOG_MODE in (1, 2):
                                                    logger.info(f"[{cmd_cn}] Removed label for GCS {gcs_cn}")
                                                break
                                        notebook.pack_forget()
                                        notebook.destroy()
                                        del node_notebooks[gcs_cn]
                                        # Remove associated SITL entries
                                        for (sysid, node_cn) in list(sitls.keys()):
                                            if node_cn == gcs_cn:
                                                try:
                                                    canvas.delete(sitls[(sysid, node_cn)]["marker"])
                                                    canvas.delete(sitls[(sysid, node_cn)]["text"])
                                                    notebook.forget(sitls[(sysid, node_cn)]["tab"])
                                                    sitls[(sysid, node_cn)]["tab"].destroy()
                                                    del sitls[(sysid, node_cn)]
                                                    if LOG_MODE in (1, 2):
                                                        logger.info(f"[{cmd_cn}] Removed SITL {(sysid, node_cn)} due to GCS shutdown")
                                                except tk.TclError as e:
                                                    if LOG_MODE in (1, 2):
                                                        logger.info(f"[{cmd_cn}] Error removing SITL {(sysid, node_cn)}: {e}")
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{cmd_cn}] Removed notebook for GCS {gcs_cn}")
                                    except tk.TclError as e:
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{cmd_cn}] Error removing notebook for GCS {gcs_cn}: {e}")
                        elif addr in cmd2_sessions:
                            cmd2_cn = cmd2_sessions[addr]["2cmd_cn"]
                            if node_cn_bytes == cmd2_cn:
                                del cmd2_sessions[addr]
                                with network_lock:
                                    gcs_connections[cmd2_cn].clear()
                                    if cmd2_cn in network_map:
                                        del network_map[cmd2_cn]
                                    root.after(0, update_network_view)
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd_cn}] Removed session for 2CMD {cmd2_cn} at {addr} due to 2CMD shutdown")
                                if cmd2_cn in node_notebooks:
                                    try:
                                        notebook = node_notebooks[cmd2_cn]
                                        for widget in notebook_frame.winfo_children():
                                            if isinstance(widget, ttk.Label) and widget.winfo_name() == f"label_{cmd2_cn}":
                                                widget.destroy()
                                                if LOG_MODE in (1, 2):
                                                    logger.info(f"[{cmd_cn}] Removed label for 2CMD {cmd2_cn}")
                                                break
                                        notebook.pack_forget()
                                        notebook.destroy()
                                        del node_notebooks[cmd2_cn]
                                        # Remove associated SITL entries
                                        for (sysid, node_cn) in list(sitls.keys()):
                                            if node_cn == cmd2_cn:
                                                try:
                                                    canvas.delete(sitls[(sysid, node_cn)]["marker"])
                                                    canvas.delete(sitls[(sysid, node_cn)]["text"])
                                                    notebook.forget(sitls[(sysid, node_cn)]["tab"])
                                                    sitls[(sysid, node_cn)]["tab"].destroy()
                                                    del sitls[(sysid, node_cn)]
                                                    if LOG_MODE in (1, 2):
                                                        logger.info(f"[{cmd_cn}] Removed SITL {(sysid, node_cn)} due to 2CMD shutdown")
                                                except tk.TclError as e:
                                                    if LOG_MODE in (1, 2):
                                                        logger.info(f"[{cmd_cn}] Error removing SITL {(sysid, node_cn)}: {e}")
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{cmd_cn}] Removed notebook for 2CMD {cmd2_cn}")
                                    except tk.TclError as e:
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{cmd_cn}] Error removing notebook for 2CMD {cmd2_cn}: {e}")
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Received disconnection from {node_cn_bytes}")

        

                elif type_byte == b'\x11':
                    message = f"{cmd_cn} Received 0x11 from {addr}, renewing session key."
                    serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                    session = gcs_sessions.get(addr) or cmd2_sessions.get(addr)
                    if not session:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Received 0x11 from unknown session at {addr}")
                        continue
                    if addr not in pending_dh:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] Unexpected 0x11 received from {addr}")
                        continue
                    shared_secret = session.get("shared_secret")
                    if not shared_secret:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd_cn}] No shared secret stored for {addr}, cannot renew")
                        continue
                    salt=payload
                    
                    new_session_key_sending = HKDF(
                        algorithm=hashes.SHA256(),
                        length=SESSION_KEY_LENGTH,
                        salt=salt,
                        info=b"session_key_renewed_sending",
                    ).derive(shared_secret)
                    
                    new_session_key_receiving = HKDF(
                        algorithm=hashes.SHA256(),
                        length=SESSION_KEY_LENGTH,
                        salt=salt,
                        info=b"session_key_renewed_receiving",
                    ).derive(shared_secret)
                    
                    session["session_key_sending"] = new_session_key_sending
                    session["session_key_receiving"] = new_session_key_receiving

                    session["session_created_at"] = time.time()
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] Session key renewed with {session.get('2cmd_cn', session.get('gcs_cn', 'peer'))} at {addr}")
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] New session key sending = {new_session_key_sending.hex()}")
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd_cn}] New session key receiving = {new_session_key_receiving.hex()}")
                    del pending_dh[addr]
                    message = f"{cmd_cn} Ended key renewal"
                    serv_temp_sock.sendto(message.encode('utf-8'), server_address)

                final_time=time.perf_counter()
                message_processing_time.append((final_time - message_processing_start_time)*1e6)  # Convert to microseconds
                logger.info(f"[{cmd_cn}] message final timestamp: {final_time} processing time: {(final_time - message_processing_start_time)*1e6}")
                message = f"{cmd_cn} Ended key renewal"
                serv_temp_sock.sendto(message.encode('utf-8'), server_address)
            except BlockingIOError:
                break
            except Exception as e:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd_cn}] Error processing UDP data: {e}")
                continue

        # Clean up timed-out SITLs
        #for sitl_key in list(sitls.keys()):
        #    sysid, node_cn = sitl_key
        #    if current_time - sitls[sitl_key]["last_timestamp"] > 10:
        #        try:
        #            canvas.delete(sitls[sitl_key]["marker"])
        #            canvas.delete(sitls[sitl_key]["text"])
        #            node_notebook = node_notebooks.get(node_cn)
        #            if node_notebook:
        #                try:
        #                    if sitls[sitl_key]["tab"].winfo_exists():
        #                        node_notebook.forget(sitls[sitl_key]["tab"])
        #                        sitls[sitl_key]["tab"].destroy()
        #                        if LOG_MODE in (1, 2):
        #                            logger.info(f"[{cmd_cn}] Removed tab for {sitl_key}")
        #                    else:
        #                        if LOG_MODE in (1, 2):
        #                            logger.info(f"[{cmd_cn}] Tab for {sitl_key} already destroyed")
        #                except tk.TclError as e:
        #                    if LOG_MODE in (1, 2):
        #                        logger.info(f"[{cmd_cn}] Error removing tab for {sitl_key}: {e}")
        #            del sitls[sitl_key]
        #            if LOG_MODE in (1, 2):
        #                logger.info(f"[{cmd_cn}] Removed SITL {sitl_key} due to timeout")
        #        except tk.TclError as e:
        #            if LOG_MODE in (1, 2):
        #                logger.info(f"[{cmd_cn}] Error removing SITL {sitl_key}: {e}")

        root.after(10, update_gui)
    
    def cleanup():
        global running
        running = False
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd_cn}] Cleaning up...")
            
        def _format_msg_type(msg_type):
            return "Unknown" if msg_type is None else f"0x{msg_type:02X}"

        if message_lenght_received:
            for node_cn, records in message_lenght_received.items():
                if not records:
                    continue
                type_totals = {}
                total_length = 0
                total_count = 0
                for msg_type, length in records:
                    total_length += length
                    total_count += 1
                    entry = type_totals.setdefault(msg_type, {"count": 0, "total_length": 0})
                    entry["count"] += 1
                    entry["total_length"] += length

                print(f"[{cmd_cn}] Message statistics for {node_cn} receiving:")
                for msg_type, stats in sorted(type_totals.items(), key=lambda item: (-1 if item[0] is None else item[0])):
                    avg_type_length = stats["total_length"] / stats["count"]
                    print(f"[{cmd_cn}] Type {_format_msg_type(msg_type)}: Average length {avg_type_length:.2f} bytes over {stats['count']} messages (Total: {stats['total_length']} bytes)")
                overall_avg = total_length / total_count if total_count else 0
                print(f"[{cmd_cn}] Total messages received: {total_count}, Average length: {overall_avg:.2f} bytes (Total: {total_length} bytes)")

        if message_lenght_sent:
            for node_cn, records in message_lenght_sent.items():
                if not records:
                    continue
                type_totals = {}
                total_length = 0
                total_count = 0
                for msg_type, length in records:
                    total_length += length
                    total_count += 1
                    entry = type_totals.setdefault(msg_type, {"count": 0, "total_length": 0})
                    entry["count"] += 1
                    entry["total_length"] += length

                print(f"[{cmd_cn}] Message statistics for {node_cn} sending:")
                for msg_type, stats in sorted(type_totals.items(), key=lambda item: (-1 if item[0] is None else item[0])):
                    avg_type_length = stats["total_length"] / stats["count"]
                    print(f"[{cmd_cn}] Type {_format_msg_type(msg_type)}: Average length {avg_type_length:.2f} bytes over {stats['count']} messages (Total: {stats['total_length']} bytes)")
                overall_avg = total_length / total_count if total_count else 0
                print(f"[{cmd_cn}] Total messages sent: {total_count}, Average length: {overall_avg:.2f} bytes (Total: {total_length} bytes)")
        if message_processing_time:
            avg_processing_time = sum(message_processing_time) / len(message_processing_time)
            print(f"[{cmd_cn}] Average message processing time: {avg_processing_time:.2f} μs for {len(message_processing_time)} messages")

        if offset_per_node:
            # Calculate and print the average for each specific node
            for node, times in offset_per_node.items():
                if not times:
                    continue
                # Use the corrected variables and a more accurate description in the print statement.
                print(f"[{cmd_cn}] offset {node}: {times} μs")
        
        if connection_establishement_time:
            overall_total_time = 0
            overall_total_count = 0
            
            # Calculate and print the average for each specific node
            for node, times in connection_establishement_time.items():
                if not times:
                    continue
                
                # --- FIX ---
                # Sum the list of times for the current node, not the entire dictionary.
                node_total_time = sum(times)
                node_connection_count = len(times)
                node_avg_time = node_total_time / node_connection_count
                
                # Use the corrected variables and a more accurate description in the print statement.
                print(f"[{cmd_cn}] Average connection establishment time for {node}: {node_avg_time:.2f} μs over {node_connection_count} connection(s)")
                
                # Add the node's totals to the overall counters
                overall_total_time += node_total_time
                overall_total_count += node_connection_count

            # Calculate and print the overall average after the loop
            if overall_total_count > 0:
                overall_avg_time = overall_total_time / overall_total_count
                print(f"[{cmd_cn}] Overall average connection establishment time: {overall_avg_time:.2f} μs over {overall_total_count} total connection(s)")

        print(f"[{cmd_cn}] Number of messages droped due to gap: {number_gap_drop}")
        with gap_values_lock:
            overall_total_gap = 0
            overall_total_count = 0

            for node_cn, records in gap_values_per_connection.items():
                if not records:
                    print(f"[{cmd_cn}] No gap values recorded for {node_cn}")
                    continue

                type_totals = {}
                node_total_gap = 0
                node_total_count = 0

                for msg_type, gap in records:
                    node_total_gap += gap
                    node_total_count += 1
                    entry = type_totals.setdefault(msg_type, {"count": 0, "total_gap": 0})
                    entry["count"] += 1
                    entry["total_gap"] += gap

                print(f"[{cmd_cn}] Gap statistics for {node_cn}:")
                for msg_type, stats in sorted(type_totals.items(), key=lambda item: item[0]):
                    avg_type_gap = stats["total_gap"] / stats["count"]
                    print(f"[{cmd_cn}] Type {msg_type}: Average gap {avg_type_gap:.2f} μs over {stats['count']} message(s)")

                node_avg_gap = node_total_gap / node_total_count if node_total_count else 0
                print(f"[{cmd_cn}] Total messages: {node_total_count}, Average gap: {node_avg_gap:.2f} μs")

                overall_total_gap += node_total_gap
                overall_total_count += node_total_count

            if overall_total_count:
                overall_avg_gap = overall_total_gap / overall_total_count
                print(f"[{cmd_cn}] Overall average gap across all nodes: {overall_avg_gap:.2f} μs over {overall_total_count} message(s)")
            else:
                if not gap_values_per_connection:
                    print(f"[{cmd_cn}] No gap values recorded for any node")
                else:
                    print(f"[{cmd_cn}] No gap values recorded across all nodes")
        try:
            send_disconnection()
        except Exception as e:
            print(f"[{cmd_cn}] Error sending disconnections: {e}")
        try:
            udp_socket.close()
            print(f"[{cmd_cn}] UDP socket closed")
        except Exception as e:
            print(f"[{cmd_cn}] Error closing UDP socket: {e}")
        try:
            root.destroy()
            print(f"[{cmd_cn}] Tkinter root destroyed")
        except Exception as e:
            print(f"[{cmd_cn}] Error destroying Tkinter root: {e}")
        try:
            listener.stop()
        except Exception:
            pass
        
        
    
    def signal_handler(sig, frame):
        
        print(f"[{cmd_cn}] Received signal {sig}, initiating cleanup...")
        cleanup()  
        sys.exit(0)
    
    # Register the handlers (only if logging is enabled)
    if LOG_MODE in (0, 1, 2):
        signal.signal(signal.SIGINT, signal_handler)
        signal.signal(signal.SIGTERM, signal_handler)
        
    root.protocol("WM_DELETE_WINDOW", cleanup)
    update_gui()
    check_node_timeouts()
    process_popups()
    root.mainloop()

    def signal_handler(sig, frame):
        print(f"[{cmd_cn}] Received signal {sig}, initiating cleanup...")
        cleanup()
        sys.exit(0)
    
if __name__ == "__main__":
    try:
        gcs_permissions, cmd2_permissions = load_policies()
        setup_mavlink_and_gui()
    except Exception as e:
        print(f"[{cmd_cn}] Fatal error: {e}")
        root.destroy()
        exit(1)