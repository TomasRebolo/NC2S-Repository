import socket
import ssl
import sys
import threading
import time
import hashlib
import struct
import tkinter as tk
from tkinter import messagebox
from collections import deque
from queue import Queue, Empty
from cryptography.hazmat.primitives import hashes, hmac
from cryptography.hazmat.primitives.asymmetric import dh
from cryptography.hazmat.primitives.kdf.hkdf import HKDF
from cryptography.hazmat.primitives.serialization import Encoding, PublicFormat, load_pem_public_key, load_der_public_key
from cryptography.hazmat.primitives.asymmetric import padding
from cryptography.hazmat.primitives import serialization
from cryptography import x509
from cryptography.hazmat.backends import default_backend
from pymavlink import mavutil
import os
from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.x509 import load_der_x509_certificate
from cryptography.hazmat.primitives.asymmetric.ec import EllipticCurvePublicKey
from cryptography.x509 import load_pem_x509_certificate, load_der_x509_certificate, NameOID
from cryptography.x509 import load_der_x509_crl
import datetime
import logging
import logging.handlers
import queue
from logging.handlers import QueueHandler, QueueListener
import glob
from datetime import datetime, timezone
from zoneinfo import ZoneInfo
import json

from time_sync_utilis import (
    TIME_SYNC_READY_TOKEN,
    TimeSyncError,
    perform_time_sync,
    recv_exact,
)

# Get SITL ID and ports from command-line arguments
if len(sys.argv) != 6:
    print("Usage: python3 sitl_bridge.py <sitl_id> <sitl_tcp_port> <mtls_port> <udp_port>")
    print("Example: python3 sitl_bridge.py sitl1 5760 14550 15002")
    sys.exit(1)

sitl_id = sys.argv[1]  # e.g., "sitl1"
sitl_tcp_port = int(sys.argv[2])  # e.g., 5760
MTLS_PORT = int(sys.argv[3])  # e.g., 14550
UDP_PORT = int(sys.argv[4])  # e.g., 15002
LOG_MODE = sys.argv[5]

# Validate LOG_MODE
if LOG_MODE not in ['0', '1', '2']:
    print(f"Invalid log_mode: {LOG_MODE}. Must be 0 (no logging), 1 (console only), or 2 (console and file).")
    sys.exit(1)
LOG_MODE = int(LOG_MODE)
# Certificate and credential paths
CERT_DIR = rf"C:\Users\Admin\Desktop\tecnico\tese\tese\cert1\{sitl_id}"
CREDENTIAL_DIR = f"{CERT_DIR}\\credentials"
CRL_DIR = f"{CERT_DIR}\\crl"
CLIENT_CERT = f"{CERT_DIR}\\{sitl_id}.crt"
CLIENT_KEY = f"{CERT_DIR}\\{sitl_id}.key"
CA_CERT = f"{CERT_DIR}\\ca.crt"
CMD_CERT = f"{CERT_DIR}\\cmd.crt"
CRL_FILE = f"{CRL_DIR}\\crl_{{}}.crl"
POLICY_FILE = f"{CERT_DIR}\\mission_policy\\mission_policy.json"
# Session variables
SESSION_KEY_LENGTH = 32
SESSION_KEY_LIFETIME = 3 * 60
CRL_LIFETIME_SECONDS = 365 * 24 * 60 * 60 

session_contexts = {}  # {(sender_ip,port): {"session_key": key, "offset": offset, "sysid": sid, "client_cn": cn, "public_key": pu, "hash": hash}}
pending_dh = {}  # addr → {"private_key": ..., "start_time": ..., "initiator": True}


# Valid message types
VALID_TYPES = [b'\x01', b'\x02', b'\x03', b'\x04', b'\x05', b'\x06', b'\x07', b'\x11', b'\x15', b'\x16', b'\x17']

serv_temp_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
server_address = ('172.18.11.204', 8080)

global latest_crl, latest_time
latest_crl = None
latest_time = None


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

# Thread safety
lock = threading.Lock()

# Timestamp and pop-up tracking
client_timestamps = {sitl_id: deque(maxlen=200)}  # Deque of last 200 timestamps
popup_counts = {sitl_id: []}  # List of pop-up times (seconds)
popup_queue = Queue()  # Queue for pop-up requests

# Tkinter root for main thread
root = tk.Tk()
root.withdraw()

# Prepare log path
log_path = os.path.join(CERT_DIR, f"{sitl_id}_log.txt")
os.makedirs(CERT_DIR, exist_ok=True)

# Create and clear the root logger
logger = logging.getLogger()
logger.setLevel(logging.DEBUG)
logger.handlers.clear()

# Common formatter
formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')

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

    if LOG_MODE in (1, 2):
        sys.stdout = StreamToLogger(logger.info)
    sys.stderr = StreamToLogger(logger.error)

# Startup message for modes 1 and 2
if LOG_MODE in (1, 2):
    logger.info(f"[{sitl_id}] Logging initialized (mode={LOG_MODE})")
    if LOG_MODE in (1, 2):
        logger.info(f"[{sitl_id}] PID: {os.getpid()}")

# Load PUcmd for credential verification
try:
    with open(CMD_CERT, 'rb') as f:
        cmd_cert = x509.load_pem_x509_certificate(f.read(), default_backend())
    PUcmd = cmd_cert.public_key()
    if LOG_MODE in (1, 2):
        logger.info(f"[{sitl_id}] Loaded PUcmd from {CMD_CERT}")
except Exception as e:
    PUcmd = None
    if LOG_MODE in (1, 2):
        logger.info(f"[{sitl_id}] Failed to load PUcmd: {e}")
    sys.exit(1)

try:
    with open(CLIENT_KEY, 'rb') as f:
        PRuxv = serialization.load_pem_private_key(f.read(), None, default_backend())
except Exception as e:
    PRuxv = None
    if LOG_MODE in (1, 2):
        logger.info(f"[{sitl_id}] Failed to load PRuxv: {e}")    

global sitl_cert, sitl_serial, PUsitl, sitl_cn

try:
    with open(CLIENT_CERT, 'rb') as f:
        sitl_cert = x509.load_pem_x509_certificate(f.read(), default_backend())
    PUsitl = sitl_cert.public_key()
    sitl_cn = sitl_cert.subject.get_attributes_for_oid(x509.NameOID.COMMON_NAME)[0].value
    sitl_serial = sitl_cert.serial_number
    if LOG_MODE in (1, 2):
        logger.info(f"[{sitl_cn}] Loaded PUsilt from {sitl_cn} Serial: {sitl_serial}")
except Exception as e:
    PUsitl = None
    if LOG_MODE in (1, 2):
        logger.info(f"[{sitl_id}] Failed to load PUcmd: {e}")
    sys.exit(1)
    
try:
    with open(CA_CERT, 'rb') as f:
        ca_cert = load_pem_x509_certificate(f.read(), default_backend())
        ca_pubkey = ca_cert.public_key()
except Exception as e:
    ca_pubkey = None
    if LOG_MODE in (1, 2):
        logger.info(f"[{sitl_id}] Failed to load ca_pubkey: {e}") 

# CRL management

crl_timestamp = 0
global current_crl
current_crl = None
global uxv_permitions_sending, uxv_permitions_receiving

global credentials
credentials = []

current_cert_crl = None
CRL_CERT_DIR = os.path.join(CERT_DIR, "CRL_CERTIFICATES")
os.makedirs(CRL_CERT_DIR, exist_ok=True)
crl_cert_lock = threading.Lock()



def load_crl():
    """Load the latest CRL from file."""
    global current_crl
    try:
        if not os.path.exists(CRL_DIR):
            if LOG_MODE in (1, 2):
                logger.info(f"[{sitl_id}] CRL directory {CRL_DIR} does not exist")
            return
        crl_files = [f for f in os.listdir(CRL_DIR) if f.startswith('crl_') and f.endswith('.crl')]
        if not crl_files:
            if LOG_MODE in (1, 2):
                logger.info(f"[{sitl_id}] No CRL files found in {CRL_DIR}")
            return
        latest_crl = max(crl_files, key=lambda x: int(x.split('_')[1].replace('.crl', '')))
        filepath = os.path.join(CRL_DIR, latest_crl)
        with open(filepath, 'rb') as f:
            crl_data = f.read()
        payload = crl_data[:-2]  # remove last 2 bytes that give signature length
        sig_len = int.from_bytes(crl_data[-2:], 'big')
        signature = payload[-sig_len:]
        payload = payload[:-sig_len]
        PUcmd.verify(signature, payload, ec.ECDSA(hashes.SHA256()))
        timestamp = int.from_bytes(payload[:8], 'big') / 1e6
        lifetime = int.from_bytes(payload[8:16], 'big')
        if time.time() >= timestamp + lifetime:
            raise ValueError("CRL expired")
        
        hashess = []
        if len(payload) > 16:
            hashess = [payload[i:i+32].hex() for i in range(16, len(payload), 32)]

        current_crl = {"timestamp": timestamp, "lifetime": lifetime, "hashes": set(hashess), "raw": crl_data}
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] Loaded CRL: {latest_crl}, Timestamp={timestamp}, Hashes={len(hashess)}")
        return current_crl
    except Exception as e:
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] Failed to load CRL: {e}")

def verify_credential(cred, pucmd, PUuxv, peer_pu=None):
    """Verify credential signature, timestamp, lifetime, and public keys."""
    if not isinstance(cred, bytes):
        raise ValueError(f"Credential must be bytes, got {type(cred)}")
    if len(cred) < 256:
        raise ValueError(f"Credential too short: {len(cred)} bytes, expected at least 256")

    try:
        current_crl = load_crl()
        if current_crl is None:
            raise ValueError("No valid CRL found")
        
        sig_len = int.from_bytes(cred[-2:], 'big')  # last 2 bytes = sig_len
        signature = cred[-(2 + sig_len):-2]         # signature is before the 2 bytes
        payload = cred[:-(sig_len + 2)] 
        cred_body_len = len(cred) - sig_len - 2 # the rest is payload
        pucmd.verify(signature, payload, ec.ECDSA(hashes.SHA256()))

        type_byte = cred[0]
        offset = 1
        len_pu1 = int.from_bytes(cred[offset:offset+2], 'big')
        offset += 2
        pu1_der = cred[offset:offset+len_pu1]
        pu1 = load_der_public_key(pu1_der, default_backend())
        offset += len_pu1
        len_pu2 = int.from_bytes(cred[offset:offset+2], 'big')
        offset += 2
        pu2_der = cred[offset:offset+len_pu2]
        pu2 = load_der_public_key(pu2_der, default_backend())
        offset += len_pu2
        timestamp = int.from_bytes(cred[offset : offset + 8], "big") / 1e6
        lifetime = int.from_bytes(cred[offset + 8 : offset + 16], "big")
        offset += 16

        capacity_string = None
        if type_byte in [0x02, 0x03]:
            if offset >= cred_body_len:
                raise ValueError("Missing capability string in credential")
        str_len = cred[offset]
        offset += 1
        if offset + str_len > cred_body_len:
            raise ValueError("Invalid capability string length")
        capacity_string = cred[offset:offset + str_len].decode('utf-8')
        offset += str_len

        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] Verifying credential: Type={type_byte}, Current time={time.time()}, Timestamp={timestamp}, Lifetime={lifetime}, Expires={timestamp + lifetime}")
        if time.time() >= timestamp + lifetime:
            raise ValueError("Credential expired")

        cred_hash = hashlib.sha256(cred).hexdigest()
        if cred_hash in current_crl["hashes"]:
            raise ValueError("Credential is revoked in CRL")


        if pu1_der != peer_pu.public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo):
            raise ValueError("PU1 does not match peer certificate")
        if pu2_der != PUuxv.public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo):
            raise ValueError("PU2 does not match local certificate")

        return {"type": type_byte, "pu1": pu1, "pu2": pu2, "timestamp": timestamp, "lifetime": lifetime, "capacity_string": capacity_string, "raw": cred, "hash": cred_hash}
    
    except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{sitl_id}] Credential signature verification failed: {e}")
            if LOG_MODE in (1, 2):
                logger.info(f"[{sitl_id}] Payload: {payload.hex()}")
            if LOG_MODE in (1, 2):
                logger.info(f"[{sitl_id}] Signature: {signature.hex()}")
            raise ValueError(f"Signature verification failed: {e}")


def load_latest_cert_crl(crl_dir):
    global latest_crl, latest_time,current_cert_crl

    # Only consider files ending in .crl or .crl.der
    crl_files = [f for f in os.listdir(crl_dir) if f.endswith(".crl") or f.endswith(".crl.der")]
    if not crl_files:
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] No CRL files found in {crl_dir}")
        return None

    for crl_file in crl_files:
        crl_path = os.path.join(crl_dir, crl_file)
        try:
            with open(crl_path, "rb") as f:
                crl_data = f.read()
                cert_crl = load_der_x509_crl(crl_data, default_backend())
                ca_pubkey.verify(cert_crl.signature,cert_crl.tbs_certlist_bytes, ec.ECDSA(cert_crl.signature_hash_algorithm))
                now = datetime.now()
                if LOG_MODE in (1, 2):
                    logger.info(f"NOW: {now}, CRL NEXT UPDATE: {cert_crl.next_update_utc}")
                if cert_crl.next_update < now:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{sitl_id}] Skipping expired CRL '{crl_file}': Next update was {cert_crl.next_update_utc}")
                    return None
                if LOG_MODE in (1, 2):
                    logger.info(f"[{sitl_id}] before the if Loaded CRL: {cert_crl}, latest_time: {latest_time}, cert_crl.last_update={cert_crl.last_update_utc}")
                
                if latest_time is None or cert_crl.last_update > latest_time:
                    latest_time = cert_crl.last_update
                    latest_crl = cert_crl
                if LOG_MODE in (1, 2):
                    logger.info(f"[{sitl_id}] after the if Loaded CRL: {cert_crl}, latest_time: {latest_time}, cert_crl.last_update={cert_crl.last_update_utc}")
                
            current_cert_crl = {
                    "timestamp": int(latest_crl.last_update_utc.timestamp() * 1e6),
                    "revoked_serials": {r.serial_number for r in cert_crl} if cert_crl else set(),
                     }    
            
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{sitl_id}] Skipping invalid CRL '{crl_file}': {e}")
            return None

    return latest_crl

def compute_hmac(type_byte, payload, timestamp_bytes, current_session_key):
    """Compute HMAC over type + payload + timestamp."""
    h = hmac.HMAC(current_session_key, hashes.SHA256())
    h.update(type_byte + payload + timestamp_bytes)
    return h.finalize()[:16]


def verify_policy(msg_type, capacity_string, role, mav_type=None):
    #logger.info(f"[{sitl_id}] Verifying policy for message type {msg_type.hex()} with capacity string '{capacity_string}' and role '{role}'")
    """Verify if a message type is allowed based on the capacity string, connection type, and role."""
    access_levels = ["Access1", "Access2", "Access3", "SendWaypoint"]
    capabilities = capacity_string.split(",") if capacity_string else []
    if not any(level in capabilities for level in access_levels):
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] No valid access level in capacity string: {capacity_string}")
        return False
    
    
    # SITL acts as a UXV, so use UXV permissions
    permissions = uxv_permissions_sending if role == "sender" else uxv_permissions_receiving
    
    for capability in capabilities:
        perm = permissions.get(capability)
        if perm is None:
            if LOG_MODE in (1, 2):
                logger.info(f"[{sitl_id}] Capability {capability} not found in permissions")
            continue
        if isinstance(perm, list):
            if msg_type in perm:
                return True
        elif isinstance(perm, dict):
            if msg_type in perm:
                allowed = perm[msg_type]
                if allowed is None:
                    return True
                if mav_type and mav_type in allowed:    
                    return True
    if LOG_MODE in (1, 2):
        logger.info(f"[{sitl_id}] No valid permission found for message type {msg_type.hex()} with capacity string {capacity_string} and role {role}")
    return False

def verify_hmac(data, session_info, client_id, msg_type):
    global number_gap_drop
    """Verify HMAC and timestamp; supports key renewal with pending_session_key."""
    if len(data) < 15:
        popup_queue.put(("Message Error",
                         f"Message too short for {client_id}\nMessage Type: {msg_type}\n",
                         client_id))
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] Verification failed: Message too short")
        return None

    type_byte = data[0:1]
    if type_byte not in VALID_TYPES:
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] Ignored invalid type: {type_byte.hex()}")
        return None

    payload = data[1:-24]
    timestamp_bytes = data[-24:-16]
    received_hmac = data[-16:]
    timestamp = struct.unpack('<Q', timestamp_bytes)[0]
    current_time = int(time.time() * 1e6)
    offset = session_info["offset"]
    adjusted_timestamp = timestamp + offset
    gap = abs(adjusted_timestamp - current_time)

    if timestamp in client_timestamps.get(client_id, deque(maxlen=200)):
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] Repeated timestamp for {client_id}")
        popup_queue.put(("Timestamp Error",
                         f"Repeated timestamp detected for {client_id}\nType: {msg_type}\nTimestamp: {timestamp}", client_id))
        return None

    if gap > 400000:
        number_gap_drop += 1
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] Timestamp {timestamp} is out of sync ({gap} μs)")
        popup_queue.put(("Timestamp Error",
                         f"Timestamp out of window for {client_id}\nGap: {gap} μs", client_id))
        return None

    # Try with current key
    computed_hmac = compute_hmac(type_byte, payload, timestamp_bytes, session_info["current_session_key_receiving"])
    if computed_hmac == received_hmac:
        pass
        #logger.info(f"[{sitl_id}] HMAC verified with current session key, gap={gap} μs")
    elif session_info.get("session_state") == "pending_renewal" and session_info.get("pending_session_key_sending") and session_info.get("pending_session_key_receiving"):
        computed_hmac_pending = compute_hmac(type_byte, payload, timestamp_bytes, session_info["pending_session_key_receiving"])
        if computed_hmac_pending == received_hmac:
            #logger.info(f"[{sitl_id}] HMAC matched with pending key — promoting new session keys:")
            #logger.info(f"[{sitl_id}] current_session_key_sending: {session_info['pending_session_key_sending'].hex()}")
            #logger.info(f"[{sitl_id}] current_session_key_receiving: {session_info['pending_session_key_receiving'].hex()}")
            
            session_info["current_session_key_sending"] = session_info["pending_session_key_sending"]
            session_info["current_session_key_receiving"] = session_info["pending_session_key_receiving"]
            session_info["pending_session_key_sending"] = None
            session_info["pending_session_key_receiving"] = None
            session_info["session_state"] = "established"
            session_info["session_created_at"] = time.time()
            session_info["real_renewal_count"] = session_info["pending_renewal_count"]
            message = f"{sitl_id} Session with {client_id} renewed successfully"
            serv_temp_sock.sendto(message.encode('utf-8'), server_address)
        else:
            if LOG_MODE in (1, 2):
                logger.info(f"[{sitl_id}] HMAC failed with both current and pending keys")
            return None
    else:
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] HMAC failed with current key and no valid pending key to try")
        return None

    

    client_timestamps.setdefault(client_id, deque(maxlen=200)).append(timestamp)
    return (type_byte, payload, gap)

def load_policies():
    try:
        with open(POLICY_FILE, 'r') as f:
            data = json.load(f)
        # Convert hex strings to bytes
        def convert(section):
            converted = {}
            for cap, value in section.items():
                # Simple list of hex strings → list of bytes
                if isinstance(value, list):
                    converted[cap] = [bytes.fromhex(h) for h in value]
                # Dict mapping hex to allowed MAVLink names
                elif isinstance(value, dict):
                    inner = {}
                    for hex_code, names in value.items():
                        inner[bytes.fromhex(hex_code)] = None if names is None else list(names)
                    converted[cap] = inner
                else:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{sitl_id}] Unknown policy format for {cap}")
            return converted

        uxv_permissions_sending = convert(data.get("uxv_permissions_sending", {}))
        uxv_permissions_receiving = convert(data.get("uxv_permissions_receiving", {}))
        
        if not uxv_permissions_sending or not uxv_permissions_receiving:
            raise ValueError("Missing or empty policy sections in JSON")
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] Loaded policies from {POLICY_FILE}")
        return uxv_permissions_sending, uxv_permissions_receiving
    except FileNotFoundError:
        logger.error(f"[{sitl_id}] Policy file not found: {POLICY_FILE}. Using default hardcoded policies.")

    except Exception as e:
        logger.error(f"[{sitl_id}] Failed to load policies: {e}. Using defaults.")


def send_disconnection():
    """Send 0x07 disconnection message to thirdparty and UXVs."""
    try:
        with lock:
            # Enviar para CMDs e 2CMDs (thirdparty)
            for gcs_addr, gcs_info in session_contexts.items():
                timestamp = int(time.time() * 1e6)
                timestamp_bytes = struct.pack('<Q', timestamp)
                payload = sitl_cn.encode('utf-8')
                hmac_value = compute_hmac(b'\x07', payload, timestamp_bytes, gcs_info["current_session_key_sending"])
                message = b'\x07' + payload + timestamp_bytes + hmac_value
                udp_socket.sendto(message, gcs_addr)
                message_lenght_sent.setdefault(gcs_info['client_cn'], []).append((0x07, len(message)))
                if LOG_MODE in (1, 2):
                    logger.info(f"[{sitl_cn}] Sent 0x07 disconnection to {gcs_info['client_cn']}")
    except Exception as e:
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_cn}] Disconnection error: {e}")

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
                logger.info(f"[{sitl_id}] [CLEAN] Deleted backup: {f}")
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{sitl_id}] [CLEAN-ERROR] {f}: {e}")

def process_popups():
    """Process pop-up messages from the queue."""
    try:
        title, message, client_id = popup_queue.get_nowait()
        current_time = time.time()
        popup_counts[client_id] = [t for t in popup_counts.get(client_id, []) if current_time - t < 60]
        if len(popup_counts[client_id]) < 5:
            popup_counts[client_id].append(current_time)
            messagebox.showerror(title, message)
    except Empty:
        pass
    root.after(10, process_popups)


def session_key_expiry_monitor():
    while running:
        now = time.time()
        with lock:
            for addr in list(session_contexts):
                session = session_contexts[addr]
                created = session.get("session_created_at", 0)
                if now - created >= SESSION_KEY_LIFETIME:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{sitl_id}] Session key expired for {session['client_cn']} at {addr}, deleting session")
                    del session_contexts[addr]
                    client_timestamps.pop(session["client_cn"], None)
                    popup_counts.pop(session["client_cn"], None)
                    popup_queue.put(("Session Expired", f"Session key for {session['client_cn']} expired", sitl_id))
        time.sleep(10)

def handle_client_connection(client_socket, addr, sitl_connection):
    """Handle incoming mTLS connection from GCS."""
    try:
        initial_time = time.time()*1e6
        cert_der = client_socket.getpeercert(binary_form=True)
        if not cert_der:
            raise ValueError("No certificate received from client")
        
        cert_obj = x509.load_der_x509_certificate(cert_der, default_backend())
        client_public_key = cert_obj.public_key()
        gcs_cn = cert_obj.subject.get_attributes_for_oid(NameOID.COMMON_NAME)[0].value
        peer_serial = cert_obj.serial_number
        
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] mTLS connection from {gcs_cn} at {addr}, peer serial: {peer_serial}")
        cert_crl = load_latest_cert_crl(CRL_CERT_DIR)
        if cert_crl is None:
                raise ValueError("No valid CRL found")
        if cert_crl is not None:
            revoked_serials = {r.serial_number for r in cert_crl}
            if peer_serial in revoked_serials:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{sitl_id}] Connection rejected: peer certificate serial {peer_serial} of {gcs_cn} is revoked.")
                client_socket.close()
                return
        
        
        if not isinstance(client_public_key, EllipticCurvePublicKey):
            raise ValueError("Expected EC public key")
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] mTLS from {addr}, CN: {gcs_cn}, peer serial: {peer_serial}")

        if not gcs_cn.startswith("GCS"):
            raise ValueError(f"Unexpected CN: {gcs_cn}")
        try:
            # Use the peer IP from the provided addr tuple instead of undefined 'ip'
            ssl.match_hostname(client_socket.getpeercert(), addr[0])
        except ssl.CertificateError as e:
            client_socket.close()
            raise ValueError(f"Peer certificate does not match expected IP {addr[0]}: {e}") from e
        client_socket.settimeout(20.0)
        cred_len_bytes = client_socket.recv(4)
        if len(cred_len_bytes) != 4:
            raise ValueError("Invalid credential length")
        cred_len = int.from_bytes(cred_len_bytes, 'big')
        if cred_len < 256 or cred_len > 2048:
            raise ValueError(f"Invalid credential size: {cred_len}")
        cred = b""
        while len(cred) < cred_len:
            chunk = client_socket.recv(cred_len - len(cred))
            if not chunk:
                raise ValueError("Incomplete credential")
            cred += chunk
        client_socket.settimeout(None)
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] Received 0x03 credential from {addr}, Length={len(cred)}")

        cred_data = verify_credential(cred, PUcmd, PUsitl, peer_pu=client_public_key)
        if cred_data["type"] != 0x03:
            raise ValueError("Received credential is not 0x03")
        
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] Verified 0x03 credential from GCS")
        
        try:
            client_socket.sendall(TIME_SYNC_READY_TOKEN)
            time_sync_logger = logger.info if LOG_MODE in (1, 2) else None
            ts_result = perform_time_sync(
                client_socket,
                role="server",
                logger=time_sync_logger,
                log_prefix=f"[{sitl_id}] Time sync with {gcs_cn}: ",
            )
        except TimeSyncError as e:
            raise ValueError(f"Time synchronisation failed: {e}") from e
        offset = ts_result.offset_us

        offset_per_node.setdefault(gcs_cn, []).append(offset)

        filename = f"{gcs_cn}_to_{sitl_id}_{int(cred_data['timestamp'])}.cred"
        filepath = os.path.join(CREDENTIAL_DIR, filename)
        os.makedirs(os.path.dirname(filepath), exist_ok=True)
        with open(filepath, 'wb') as f:
            f.write(cred)
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] Saved credential: {filename}")

        credentials.append({
                "filename": filename,
                "type": cred_data["type"],
                "pu1": cred_data["pu1"],
                "pu2": cred_data["pu2"],
                "timestamp": cred_data["timestamp"],
                "lifetime": cred_data["lifetime"],
                "raw": cred,
                "capacity_string": cred_data["capacity_string"],
                "hash": cred_data["hash"]
            })
        
        
        shared_secret = PRuxv.exchange(ec.ECDH(), client_public_key)
        
        session_key_receiving = HKDF(
            algorithm=hashes.SHA256(),
            length=SESSION_KEY_LENGTH,
            salt=None,
            info=b"session_key_sending",
        ).derive(shared_secret)
        
        session_key_sending = HKDF(
            algorithm=hashes.SHA256(),
            length=SESSION_KEY_LENGTH,
            salt=None,
            info=b"session_key_receiving",
        ).derive(shared_secret)
        
        if not session_key_receiving or not session_key_sending:
            raise Exception("Session key failed on HKDF")
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] Session key established with {gcs_cn} keys:")
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] Session_key_sending {session_key_sending.hex()}")
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] Session_key_receiving {session_key_receiving.hex()}")
        
        try:
            port_bytes = client_socket.recv(2)
            if len(port_bytes) != 2:
                raise ValueError("Failed to receive UDP port from CMD")
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{sitl_id}] Failed to receive or register UDP port: {e}")
            return
        
        udp_port = int.from_bytes(port_bytes, 'big')
        sender_ip = client_socket.getpeername()[0]
        with lock:
            session_contexts[(sender_ip, udp_port)] = {
                "shared_secret": shared_secret,
                "current_session_key_sending": session_key_sending,
                "current_session_key_receiving": session_key_receiving,
                "pending_session_key_sending": None,
                "pending_session_key_receiving": None, 
                "session_state": "established",
                "offset": offset,
                "client_cn": gcs_cn,
                "public_key": client_public_key,
                "capacity_string": cred_data["capacity_string"],
                "hash": cred_data["hash"],
                "renewal_start_time": None,
                "session_created_at": time.time(),
                "filename": filename,
                "cred_timestamp": cred_data["timestamp"],
                "cred_lifetime": cred_data["lifetime"],
                "peer_serial": peer_serial,
                "real_renewal_count": 0,
                "pending_renewal_count": 0,
                "last_heartbeat": time.time(),
            }
        final_time = time.time()*1e6
        logger.info(f"[{sitl_id}] connection with {gcs_cn} final time:{final_time}, offset={offset} μs")
        message = f"{sitl_id} finished connection establishment with {gcs_cn}"
        serv_temp_sock.sendto(message.encode('utf-8'), server_address)
        connection_establishement_time.setdefault(gcs_cn,[]).append(final_time - initial_time)
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] Connection established with {gcs_cn} Time taken: {final_time - initial_time} μs")
        popup_queue.put(("Connection Success", f"Connected to GCS {gcs_cn} at {addr[0]}:{addr[1]} with capacity string {cred_data['capacity_string']}", sitl_id))
        return True, client_socket, gcs_cn
    except Exception as e:
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] Client connection failed: {e}")
        popup_queue.put(("Connection Error", f"Failed to connect to GCS at {addr[0]}:{addr[1]}: {e}",sitl_id))
        return False, None, None, None

def check_node_timeouts():
    NETWORK_MAP_INTERVAL = 30  # segundos
    while running:
        now = time.time()
        with lock:
            for addr, session in list(session_contexts.items()):
                if now - session["last_heartbeat"] > NETWORK_MAP_INTERVAL:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{sitl_id}] GCS {session['client_cn']} at {addr} timed out — closing session.")
                    del session_contexts[addr]
                    pending_dh.pop(addr, None)         
        time.sleep(10)

def start_mtls_server(sitl_connection, udp_socket):
    """Start mTLS server to accept connections from GCS."""
    server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    server_socket.bind(('', MTLS_PORT))
    server_socket.listen(5)
    if LOG_MODE in (1, 2):
        logger.info(f"[{sitl_id}] mTLS server started on port {MTLS_PORT}")

    context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
    context.load_cert_chain(certfile=CLIENT_CERT, keyfile=CLIENT_KEY)
    context.load_verify_locations(CA_CERT)
    context.verify_mode = ssl.CERT_REQUIRED

    while running:
        try:
            client_socket, addr = server_socket.accept()
            secure_socket = context.wrap_socket(client_socket, server_side=True)
            if LOG_MODE in (1, 2):
                logger.info(f"[{sitl_id}] Accepted mTLS connection from {addr}")
            success, secure_client_socket, gcs_cn = handle_client_connection(secure_socket, addr, sitl_connection)
            if success:
                threading.Thread(target=receive_messages, args=(udp_socket, sitl_connection, secure_client_socket, addr), daemon=True).start()
            else:
                try:
                    secure_socket.close()
                except:
                    pass
        except Exception as e:
            if running:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{sitl_id}] Error accepting connection: {e}")

def receive_messages(udp_socket, sitl_connection, secure_socket=None, addr=None):
    """Receive and process UDP messages from GCS."""
    global current_crl, credentials, message_processing_time
    while running:
        try:
            message_processing_start = time.time()*1e6
            data, addr = udp_socket.recvfrom(1024)
            type_byte = data[0:1]
            msg_type = type_byte.hex()
            if LOG_MODE in (1, 2):
                logger.info(f"[{sitl_id}] Received UDP from {addr}, msg_type={msg_type} at: {int(time.time()* 1e6)}")

            # Handle other message types (require existing session)
            with lock:
                session_info = session_contexts.get(addr)
                if not session_info:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{sitl_id}] No session for {addr}")
                    continue
                client_cn = session_info["client_cn"]
                current_session_key = session_info["current_session_key_receiving"]  # Use current key
                offset = session_info["offset"]
                capacity_string = session_info["capacity_string"]
                
            msg_type_value = data[0] if data else None
            message_lenght_received.setdefault(client_cn, []).append((msg_type_value, len(data)))
            
            result = verify_hmac(data, session_info, client_cn, msg_type)
            if not result:
                continue
            type_byte, payload, gap = result
            timestamp = struct.unpack('<Q', data[-24:-16])[0]
            gap_values_per_connection.setdefault(client_cn, []).append((type_byte,gap))
            if type_byte == b'\x01':
                parsed_msgs = sitl_connection.mav.parse_buffer(payload)
                if parsed_msgs and parsed_msgs[0]:
                    msg = parsed_msgs[0]
                    mav_type = msg.get_type()
                    if verify_policy(type_byte, capacity_string, "receiver", mav_type=mav_type):
                        #logger.info(f"[{sitl_id}] Valid 0x01 message from {client_cn} at {addr}: Type={mav_type}, Timestamp={timestamp}")
                        if mav_type == "HEARTBEAT":
                                session_info["last_heartbeat"] = time.time()
                                #logger.info(f"[{sitl_id}] Updated last_heartbeat for {client_cn} at {addr}")
                        sitl_connection.write(payload)
                        
                        #logger.info(f"[{sitl_id}] Forwarded to SITL: Type=0x01, Timestamp={timestamp}")
                    else:
                        #logger.info(f"[{sitl_id}] Invalid 0x01 message from {client_cn} at {addr}: Type={msg_type}, Timestamp={timestamp}")
                        popup_queue.put(("Invalid Message",f"Invalid 0x01 message from {client_cn} at {addr}\nType: {mav_type}\nTimestamp: {timestamp}",sitl_id))

            elif type_byte == b'\x04':
                message = f"{sitl_id} Received 0x04 message from {client_cn}"
                serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                if verify_policy(type_byte, capacity_string, "receiver"):
                    try:
                        sig_len = int.from_bytes(payload[-2:], 'big')
                        signature = payload[-(sig_len + 2):-2]
                        crl_payload = payload[:-(sig_len + 2)]
                        PUcmd.verify(signature, crl_payload, ec.ECDSA(hashes.SHA256()))
                        new_timestamp = int.from_bytes(crl_payload[:8], 'big') / 1e6
                        lifetime = int.from_bytes(crl_payload[8:16], 'big')
                        if time.time() >= new_timestamp + lifetime:
                            raise ValueError("CRL expired")
                        new_hashes = [crl_payload[i:i+32].hex() for i in range(16, len(crl_payload), 32)]
                        
                        new_crl = {"timestamp": new_timestamp, "lifetime": lifetime, "hashes": set(new_hashes), "raw": payload}
                        
                        if current_crl is None or new_timestamp > current_crl["timestamp"]:
        
                            os.makedirs(CRL_DIR, exist_ok=True)
                            for old_file in os.listdir(CRL_DIR):
                                if old_file.endswith(".crl"):
                                    try:
                                        os.remove(os.path.join(CRL_DIR, old_file))
                                    except Exception as e:
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[GCS] Failed to remove old CRL {old_file}: {e}")
                            crl_filename = os.path.join(CRL_DIR, f"crl_{int(new_timestamp * 1e6)}.crl")
                            current_crl = new_crl
                            with open(crl_filename, 'wb') as f:
                                f.write(payload)
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{sitl_id}] Updated CRL: Timestamp={new_timestamp}, Hashes={len(new_hashes)}")
                            with lock:
                                for addr, info in list(session_contexts.items()):
                                        if info["hash"] in new_crl["hashes"]:
                                            for cred in credentials:
                                                if cred["hash"] == info["hash"]:
                                                    credentials.remove(cred)
                                                    try:
                                                        os.remove(os.path.join(CREDENTIAL_DIR, cred["filename"]))
                                                        if LOG_MODE in (1, 2):
                                                            logger.info(f"[{sitl_id}] Removed credential file {cred['filename']} for revoked session {info['client_cn']}")
                                                    except Exception as e:
                                                        if LOG_MODE in (1, 2):
                                                            logger.info(f"[{sitl_id}] Failed to remove credential file {cred['filename']}: {e}")
                                                    break
                                            message = f"{sitl_id} Terminated session with {client_cn}"
                                            serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                                            session_contexts.pop(addr)
                                            client_timestamps.pop(info["client_cn"], None)
                                            popup_counts.pop(info["client_cn"], None)
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{sitl_id}] Terminated session {info['client_cn']} at {addr} due to CRL")
                    except Exception as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{sitl_id}] Failed to process CRL: {e}")
                        popup_queue.put(("Error",
                                        f"Failed to process CRL: {e}",
                                        sitl_id))

            elif type_byte == b'\x07':
                if verify_policy(type_byte, capacity_string, "receiver"):
                    try:
                        gcs_cn_received = payload.decode('utf-8')
                        if gcs_cn_received == client_cn:
                            with lock:
                                if addr in session_contexts:
                                    del session_contexts[addr]
                                    client_timestamps.pop(client_cn, None)
                                    popup_counts.pop(client_cn, None)
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{sitl_id}] Terminated session for {client_cn} at {addr} due to 0x07")
                                    popup_queue.put(("Disconnection",f"GCS {client_cn} disconnected",sitl_id))
                    except Exception as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{sitl_id}] Failed to process 0x07: {e}")
            
            
            elif type_byte == b'\x11':
                message = f"{sitl_id} received 0x11 from {client_cn}"
                serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                if verify_policy(type_byte, capacity_string, "receiver"):
                    try:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{sitl_id}] Handling 0x11 message from {client_cn} at {addr}")
                                
                        shared_secret = session_info.get("shared_secret")
                        
                        if not shared_secret:
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{sitl_id}] No shared secret stored for {addr}, cannot renew")
                            continue
                        
                        if session_info["session_state"] == "pending_renewal":
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{sitl_id}] Already renewed {client_cn}, skipping")
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{sitl_id}] Pending session keys:")
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{sitl_id}] pending_session_key_sending: {session_info['pending_session_key_sending'].hex()}")
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{sitl_id}] pending_session_key_receiving: {session_info['pending_session_key_receiving'].hex()}")
                            new_session_key_sending = session_info["pending_session_key_sending"]
                            new_session_key_receiving = session_info["pending_session_key_receiving"]
                            
                        else: 
                                salt = os.urandom(4)
                                new_session_key_sending = HKDF(
                                    algorithm=hashes.SHA256(),
                                    length=SESSION_KEY_LENGTH,
                                    salt=salt,
                                    info=b"session_key_renewed_receiving",
                                ).derive(shared_secret)
                                
                                new_session_key_receiving = HKDF(
                                    algorithm=hashes.SHA256(),
                                    length=SESSION_KEY_LENGTH,
                                    salt=salt,
                                    info=b"session_key_renewed_sending",
                                ).derive(shared_secret)
                                
                                session_info["pending_session_key_sending"] = new_session_key_sending
                                session_info["pending_session_key_receiving"] = new_session_key_receiving
                                session_info["session_state"] = "pending_renewal"
                                session_info["renewal_start_time"] = time.time()
                            
                            
                        # Send 0x11 response using current key
                        timestamp = struct.pack('<Q', int(time.time() * 1e6))
                        hmac = compute_hmac(b'\x11', salt, timestamp, session_info["current_session_key_sending"])
                        response = b'\x11' + salt + timestamp + hmac
                        udp_socket.sendto(response, addr)
                        message = f"{sitl_id} sent 0x11 response to {client_cn}"
                        serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                        message_lenght_sent.setdefault(session_info['client_cn'], []).append((0x11, len(response)))
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{sitl_id}] Sent 0x11 response to {client_cn} at {addr}, new pending keys:")
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{sitl_id}] pending_session_key_sending: {session_info['pending_session_key_sending'].hex()}")
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{sitl_id}] pending_session_key_receiving: {session_info['pending_session_key_receiving'].hex()}")
                    except Exception as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{sitl_id}] Error handling 0x11: {e}")
                        popup_queue.put(("Key Renewal Error",f"Error processing 0x11 from {client_cn}: {e}",client_cn))
                        
            elif type_byte == b'\x15':
                message = f"{sitl_id} Received 0x15 message from {client_cn}"
                serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                if LOG_MODE in (1, 2):
                    logger.info(f"[{sitl_id}] Received 0x15 message from {client_cn} at {addr}")
                if verify_policy(type_byte, capacity_string, "receiver"):
                    try:
                        #logger.info(f"[{sitl_id}] Handling 0x15 message from {client_cn} at {addr}")
                        
                        cred_len = int.from_bytes(payload[:4], 'big')
                        if cred_len < 256 or cred_len > 2048:
                            raise ValueError(f"Invalid credential size: {cred_len}")
                        credent = payload[4:4+cred_len]
                        cred_data = verify_credential(credent, PUcmd, PUsitl, peer_pu=session_info["public_key"])
                        if cred_data["type"] != 0x03:
                            raise ValueError("Received credential in 0x15 is not 0x03")
                        
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{sitl_id}] Verified 0x15 credential from {client_cn}")
                        
                        
                        if cred_data["timestamp"] > session_info["cred_timestamp"]:
                            filename = f"{client_cn}_to_{sitl_id}_{int(cred_data['timestamp'])}.cred"
                            filepath = os.path.join(CREDENTIAL_DIR, filename)
                            
                            for old_file in os.listdir(CREDENTIAL_DIR):
                                    
                                    if old_file.startswith(f"{client_cn}_to_{sitl_id}_") and old_file.endswith(".cred"):
                                        try:
                                            os.remove(os.path.join(CREDENTIAL_DIR, old_file))
                                        except Exception as e:
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{sitl_id}] Failed to remove old credentials {old_file}: {e}")
                            
                            for cred in credentials:
                                if cred["filename"].startswith(f"{client_cn}_to_{sitl_id}_") and cred["filename"].endswith(".cred"):
                                                try:
                                                    credentials.remove(cred)
                                                except Exception as e:
                                                    if LOG_MODE in (1, 2):
                                                        logger.info(f"[{sitl_id}] Failed to remove old credential from memory {cred['filename']}: {e}")
                            
                            os.makedirs(os.path.dirname(filepath), exist_ok=True)
                            with open(filepath, 'wb') as f:
                                f.write(credent)
                            #logger.info(f"[{sitl_id}] Saved new credential: {filename}")
                            
                            session_info["hash"] = cred_data["hash"]
                            session_info["cred_timestamp"] = cred_data["timestamp"]
                            session_info["capacity_string"] = cred_data["capacity_string"]
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{sitl_id}] Updated session for {client_cn}: New timestamp={cred_data['timestamp']}, New capacity_string={cred_data['capacity_string']} at timestamp: {int(time.time()*1e6)}")
                            
                            credentials.append({
                                        "filename": filename,
                                        "type": cred_data["type"],
                                        "pu1": cred_data["pu1"],
                                        "pu2": cred_data["pu2"],
                                        "timestamp": cred_data["timestamp"],
                                        "lifetime": cred_data["lifetime"],
                                        "hash": cred_data["hash"],
                                        "capacity_string": cred_data["capacity_string"],
                                        "raw": credent
                                        })
                            
                            message = f"{sitl_id} Ended Processing 0x15 with new credential"
                            serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                        else:
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{sitl_id}] Credential timestamp {cred_data['timestamp']} not fresher than current {session_info['cred_timestamp']}")
                    except Exception as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{sitl_id}] Error handling 0x15: {e}")
                        popup_queue.put(("Credential Update Error", f"Error processing 0x15 from {client_cn}: {e}", client_cn))        

            elif type_byte == b'\x16':
                if verify_policy(type_byte, capacity_string, "receiver"):
                    try:
                        # Separar partes da mensagem
                        crl_data = payload  # payload já contém o crl_data (em formato DER)

                        # Verifica assinatura da CRL
                        crl_obj = x509.load_der_x509_crl(crl_data, default_backend())
                        ca_pubkey.verify(crl_obj.signature,crl_obj.tbs_certlist_bytes,ec.ECDSA(crl_obj.signature_hash_algorithm))
                        #logger.info(f"[{sitl_id}] Received and validated 0x16 certificate CRL from {client_cn} at {addr}")
                        crl_timestamp = int(crl_obj.last_update.timestamp() * 1e6)
                        # Guardar CRL no diretório apropriado
                        revoked_serials = {entry.serial_number for entry in crl_obj}
                        #logger.info(f"[{sitl_id}] Revoked serials: {revoked_serials}")
                        with crl_cert_lock:
                            global current_cert_crl
                            #logger.info(f"[{sitl_id}] current_cert_crl timestamp: {current_cert_crl['timestamp']}, crl_timestamp: {crl_timestamp}")
                            
                            if current_cert_crl is None or crl_timestamp > current_cert_crl["timestamp"]:
                                # Remover CRL anterior
                                for f in os.listdir(CRL_CERT_DIR):
                                    if f.endswith(".crl.der"):
                                        try:
                                            os.remove(os.path.join(CRL_CERT_DIR, f))
                                        except Exception as e:
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{sitl_id}] Failed to remove old certificate CRL: {e}")
                                # Guardar nova CRL
                                crl_filename = f"certcrl_{crl_timestamp}.crl.der"
                                crl_path = os.path.join(CRL_CERT_DIR, crl_filename)
                                with open(crl_path, "wb") as f:
                                    f.write(crl_data)

                                current_cert_crl = {
                                    "timestamp": crl_timestamp,
                                    "revoked_serials": revoked_serials
                                }
                                #logger.info(f"[{sitl_id}] Updated certificate CRL: Timestamp={crl_timestamp}, Revoked Serials={revoked_serials}")
                                
                        with lock:
                                for addr, info in list(session_contexts.items()):
                                    
                                    if info.get("peer_serial") in revoked_serials:
                                        session_contexts.pop(addr)
                                        client_timestamps.pop(info["client_cn"], None)
                                        popup_counts.pop(info["client_cn"], None)
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{sitl_id}] Terminated GCS session {info['client_cn']} at {addr} due to CERT CRL")
                        
                        logger.info(f"[{sitl_id}] Processed 0x16 certificate CRL from {client_cn}, end timestamp: {time.time()*1e6}")
                        

                    except Exception as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{sitl_id}] Failed to process 0x16 certificate CRL: {e}")
                        popup_queue.put((
                            "CRL Error",
                            f"Failed to process certificate CRL from {client_cn}: {e}",
                            sitl_id
                        ))

            
            elif type_byte == b'\x17':
                if verify_policy(type_byte, capacity_string, "receiver"):
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{sitl_id}] Handling 0x17 certificate update from {client_cn} at {addr}")
                    global sitl_cert, sitl_serial
                    cert_der = payload
                    cert_obj = load_der_x509_certificate(cert_der, default_backend())
                    
                    try:
                        ca_pubkey.verify(
                            cert_obj.signature,
                            cert_obj.tbs_certificate_bytes,
                            ec.ECDSA(cert_obj.signature_hash_algorithm)
                        )
                    except Exception as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{sitl_id}] 0x17 cert rejected: CA signature verification failed: {e}")
                        continue

                    # 2) Enforce validity window
                    now = datetime.now(timezone.utc)
                    # cryptography>=41 provides *_utc properties; fall back if needed
                    not_before = getattr(cert_obj, "not_valid_before_utc", cert_obj.not_valid_before.replace(tzinfo=timezone.utc))
                    not_after  = getattr(cert_obj, "not_valid_after_utc",  cert_obj.not_valid_after.replace(tzinfo=timezone.utc))
                    if not (not_before <= now <= not_after):
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{sitl_id}] 0x17 cert rejected: outside validity window "
                                    f"({not_before.isoformat()} .. {not_after.isoformat()}), now={now.isoformat()}")
                        continue

                    
                    
                    client_pu = cert_obj.public_key()
                    client_cn = cert_obj.subject.get_attributes_for_oid(NameOID.COMMON_NAME)[0].value
                    cert_serial = cert_obj.serial_number
                    
                    cert_crl = load_latest_cert_crl(CRL_CERT_DIR)
                    if cert_crl is None:
                        raise ValueError("No valid CRL found")
                    if cert_crl is not None:
                        revoked_serials = {r.serial_number for r in cert_crl}
                        if cert_serial in revoked_serials:
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{sitl_id}] Certificate rejected: peer certificate serial {cert_serial} of {client_cn} is revoked.")
                            continue
                    
                    if client_cn == sitl_cn and client_pu == PUsitl:
                        
                        if cert_obj.not_valid_before > sitl_cert.not_valid_before:
                            try:
                                crt_path  = os.path.join(CERT_DIR, f"{client_cn}.crt")
                                if os.path.exists(crt_path):
                                    ts = int(time.time())
                                    backup = os.path.join(CERT_DIR, f"{client_cn}_{ts}.crt.bak")
                                    try:
                                        os.replace(crt_path, backup)
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{sitl_id}] [BACKUP] {client_cn}: {backup}")
                                    except Exception as e:
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{sitl_id}] [WARN] Could not backup {crt_path}: {e}")
                                
                                sitl_cert = cert_obj
                                
                                filename = f"{client_cn}.crt"
                                filepath = os.path.join(CERT_DIR, filename)
                                os.makedirs(os.path.dirname(filepath), exist_ok=True)
                                with open(filepath, 'wb') as f:
                                    f.write(payload)

                                sitl_serial = cert_serial
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{sitl_id}] Updated own certificate with the new one received via 0x17.")
                                _purge_old_backups(client_cn)
                            except Exception as e:
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{sitl_id}] Failed to update certificate: {e}")
                        else:
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{sitl_id}] Received certificate is not newer than the current one; no update performed.")
                            
                        continue
            
            message_processing_time.append(time.time()*1e6 - message_processing_start)
        except BlockingIOError:
            pass
        except Exception as e:
            if running:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{sitl_id}] Error receiving from GCS: {e}")
         # Increased to reduce CPU contention

    if secure_socket:
        try:
            secure_socket.close()
        except:
            pass

def send_messages(udp_socket, sitl_connection):
    """Send messages from SITL to GCS."""
    global running
    while running:
        try:
            msg = sitl_connection.recv_msg()
            if msg is not None:
                payload = msg.get_msgbuf()
                msg_type = msg.get_type()
                #logger.info(f"[{sitl_id}] Received from SITL: Type={msg_type}")
                with lock:
                    if not session_contexts:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{sitl_id}] No sessions to send to, continuing to receive SITL messages")
                        pass
                    else:
                        for addr, session in session_contexts.items():
                            current_session_key = session["current_session_key_sending"]
                            capacity_string = session["capacity_string"]
                            if verify_policy(b'\x01', session["capacity_string"], "sender", mav_type=msg_type):
                                timestamp = int(time.time() * 1e6)
                                timestamp_bytes = struct.pack('<Q', timestamp)
                                type_byte = b'\x01'
                                hmac_value = compute_hmac(type_byte, payload, timestamp_bytes, current_session_key)
                                message = type_byte + payload + timestamp_bytes + hmac_value
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{sitl_id}] Sending to GCS: {session['client_cn']} at {addr}: Type={msg_type}, Timestamp={timestamp} ")
                                try:
                                    udp_socket.sendto(message, addr)
                                    message_lenght_sent.setdefault(session['client_cn'], []).append((0x01, len(message)))
                                    #logger.info(f"[{sitl_id}] Sent to GCS: {session["client_cn"]} at {addr}: Type={msg_type}, Timestamp={timestamp}, cap_level={capacity_string}")
                                except BlockingIOError:
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{sitl_id}] UDP sendto blocked for {addr}, skipping")
                                    continue
                                except socket.error as se:
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{sitl_id}] Failed to send to {addr}: {se}")
                                    continue
                    #logger.info(f"[{sitl_id}] Lock released in send_messages")
        except Exception as e:
            if running:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{sitl_id}] Error sending to GCS: {e}")
          # Increased to reduce CPU contention


def credential_expiry_monitor():
    while running:
        now = time.time() # Current time in microseconds
        with lock:
            for addr in list(session_contexts):
                session = session_contexts[addr]
                expiry_time = session["cred_timestamp"] + session["cred_lifetime"]
                if now >= expiry_time:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{sitl_id}] now: {now}, Expiry time: {expiry_time}, Cred_timestamp: {session['cred_timestamp']}, Lifetime: {session['cred_lifetime']}")
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{sitl_id}] Credential for {session['client_cn']} at {addr} expired - deleting session")
                    del session_contexts[addr]
                    client_timestamps.pop(session["client_cn"], None)
                    popup_counts.pop(session["client_cn"], None)
        time.sleep(10)

def monitor_threads():
    while running:
        if LOG_MODE in (1, 2):
            logger.info(f"[{sitl_id}] Active threads: {[t.name for t in threading.enumerate()]} at {time.time()}")
        time.sleep(1)

# Main logic
running = True
try:
    if LOG_MODE in (1, 2):
        logger.info(f"[{sitl_id}] Connecting to SITL on TCP port {sitl_tcp_port}...")
    sitl_connection = mavutil.mavlink_connection(f'tcp:127.0.0.1:{sitl_tcp_port}')
    while True:
        msg = sitl_connection.recv_msg()
        if msg is not None:
            if LOG_MODE in (1, 2):
                logger.info(f"[{sitl_id}] Connected to SITL via TCP")
            break
        time.sleep(0.1)

    load_crl()
    current_cert_crl = load_latest_cert_crl(CRL_CERT_DIR)
    root.after(10, process_popups)
    uxv_permissions_sending, uxv_permissions_receiving = load_policies()
    udp_socket = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    udp_socket.setblocking(False)
    udp_socket.bind(('', UDP_PORT))
    if LOG_MODE in (1, 2):
        logger.info(f"[{sitl_id}] Bound UDP socket to port {UDP_PORT}")

    mtls_thread = threading.Thread(target=start_mtls_server, args=(sitl_connection, udp_socket), daemon=True)
    send_thread = threading.Thread(target=send_messages, args=(udp_socket, sitl_connection), daemon=True)
    mtls_thread.start()
    send_thread.start()
    threading.Thread(target=monitor_threads, daemon=True).start()
    threading.Thread(target=credential_expiry_monitor, daemon=True).start()
    threading.Thread(target=session_key_expiry_monitor, daemon=True).start()
    #threading.Thread(target=check_node_timeouts, daemon=True).start()

    root.mainloop()

except Exception as e:
    if LOG_MODE in (1, 2):
        logger.info(f"[{sitl_id}] Error: {e}")
finally:
    running = False
    def _format_msg_type(msg_type):
        return "Unknown" if msg_type is None else f"0x{msg_type:02X}"

    def _print_message_stats(records_dict, direction):
        for node_cn, records in records_dict.items():
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

            print(f"[{sitl_id}] Message statistics for {node_cn} {direction}:")
            for msg_type, stats in sorted(type_totals.items(), key=lambda item: (-1 if item[0] is None else item[0])):
                avg_type_length = stats["total_length"] / stats["count"]
                print(f"[{sitl_id}] Type {_format_msg_type(msg_type)}: Average length {avg_type_length:.2f} bytes over {stats['count']} messages (Total: {stats['total_length']} bytes)")
            overall_avg = total_length / total_count if total_count else 0
            print(f"[{sitl_id}] Total messages {direction}: {total_count}, Average length: {overall_avg:.2f} bytes (Total: {total_length} bytes)")

    if message_lenght_received:
        _print_message_stats(message_lenght_received, "receiving")
    if message_lenght_sent:
        _print_message_stats(message_lenght_sent, "sending")
    if message_processing_time:
        avg_processing_time = sum(message_processing_time) / len(message_processing_time)
        print(f"[{sitl_id}] Average message processing time: {avg_processing_time:.2f} μs for {len(message_processing_time)} messages")
    
    
    if offset_per_node:
            # Calculate and print the average for each specific node
            for node, times in offset_per_node.items():
                if not times:
                    continue
                # Use the corrected variables and a more accurate description in the print statement.
                print(f"[{sitl_id}] offset {node}: {times} μs")
    
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
                print(f"[{sitl_id}] Average connection establishment time for {node}: {node_avg_time:.2f} μs over {node_connection_count} connection(s)")
                
                # Add the node's totals to the overall counters
                overall_total_time += node_total_time
                overall_total_count += node_connection_count

            # Calculate and print the overall average after the loop
            if overall_total_count > 0:
                overall_avg_time = overall_total_time / overall_total_count
                print(f"[{sitl_id}] Overall average connection establishment time: {overall_avg_time:.2f} μs over {overall_total_count} total connection(s)")
    
    
    print(f"[{sitl_id}] Number of messages dropped due to gap: {number_gap_drop}")
    with gap_values_lock:
        overall_total_gap = 0
        overall_total_count = 0

        for node_cn, records in gap_values_per_connection.items():
            if not records:
                print(f"[{sitl_id}] No gap values recorded for {node_cn}")
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

            print(f"[{sitl_id}] Gap statistics for {node_cn}:")
            for msg_type, stats in sorted(type_totals.items(), key=lambda item: item[0]):
                avg_type_gap = stats["total_gap"] / stats["count"]
                print(f"[{sitl_id}] Type {msg_type}: Average gap {avg_type_gap:.2f} μs over {stats['count']} message(s)")

            node_avg_gap = node_total_gap / node_total_count if node_total_count else 0
            print(f"[{sitl_id}] Total messages: {node_total_count}, Average gap: {node_avg_gap:.2f} μs")

            overall_total_gap += node_total_gap
            overall_total_count += node_total_count

        if overall_total_count:
            overall_avg_gap = overall_total_gap / overall_total_count
            print(f"[{sitl_id}] Overall average gap across all nodes: {overall_avg_gap:.2f} μs over {overall_total_count} message(s)")
        else:
            if not gap_values_per_connection:
                print(f"[{sitl_id}] No gap values recorded for any node")
            else:
                print(f"[{sitl_id}] No gap values recorded across all nodes")
    try:
        send_disconnection()
    except:
        pass
    try:
        udp_socket.close()
    except:
        pass
    try:
        udp_socket.close()
    except:
        pass
    try:
        sitl_connection.close()
    except:
        pass
    try:
        root.destroy()
    except:
        pass
    try:
        listener.stop()
    except:
        pass
    print(f"[{sitl_id}] Shut down")
