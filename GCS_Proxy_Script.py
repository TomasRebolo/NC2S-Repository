import socket
import os
import ssl
import threading
import struct
import time
import tkinter as tk
from tkinter import messagebox
from collections import deque
from queue import Queue, Empty
from cryptography.hazmat.primitives import hashes, hmac, serialization
from cryptography.hazmat.primitives.asymmetric import dh, padding
from cryptography.hazmat.primitives.kdf.hkdf import HKDF
from cryptography.hazmat.primitives.serialization import Encoding, PublicFormat, load_pem_public_key, load_der_public_key
from cryptography.hazmat.primitives.serialization import load_pem_private_key
from cryptography.x509 import load_pem_x509_certificate, load_der_x509_certificate, NameOID
from cryptography.hazmat.backends import default_backend
from pymavlink import mavutil
import sys
import hashlib
from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.x509 import load_der_x509_certificate
from cryptography.hazmat.primitives.asymmetric.ec import EllipticCurvePublicKey
from cryptography.x509 import load_der_x509_crl
from cryptography.x509 import SubjectAlternativeName
import cryptography.x509 as x509
import datetime
import cProfile
import pstats
import io
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

pr = cProfile.Profile()

# Configuration from command-line arguments
if len(sys.argv) != 7:
    print(f" Usage: gcs_router.py <gcs_name> <mtls_port> <udp_port> <MISSION_PLANNER_PORT> <MISSION_PLANNER_RECEIVE_PORT>")
    print(f"PID: {os.getpid()}")
    sys.exit(1)

GCS_NAME = sys.argv[1]
MTLS_PORT = int(sys.argv[2])
UDP_PORT = int(sys.argv[3])
MISSION_PLANNER_PORT = int(sys.argv[4])
MISSION_PLANNER_RECEIVE_PORT = int(sys.argv[5])
LOG_MODE = sys.argv[6]

# Validate LOG_MODE
if LOG_MODE not in ['0', '1', '2']:
    print(f"Invalid log_mode: {LOG_MODE}. Must be 0 (no logging), 1 (console only), or 2 (console and file).")
    sys.exit(1)
LOG_MODE = int(LOG_MODE)
MISSION_PLANNER_IP = "127.0.0.1"

VALID_TYPES = [b'\x01', b'\x02', b'\x03', b'\x04', b'\x05', b'\x06', b'\x07', b'\x11', b'\x12', b'\x13', b'\x14', b'\x15', b'\x16', b'\x17']
#CERT_DIR = rf"C:\Users\BRAVO\Desktop\Rebolo\tese\cert1\{GCS_NAME}"
CERT_DIR = rf"C:\Users\Admin\Desktop\tecnico\tese\NC2S_Repository\NC2S-Repository\cert1\{GCS_NAME}"
MISSION_DIR = f"{CERT_DIR}\\missions"
GCS_CERT = f"{CERT_DIR}\\{GCS_NAME}.crt"
GCS_KEY = f"{CERT_DIR}\\{GCS_NAME}.key"
CA_CERT = f"{CERT_DIR}\\ca.crt"
CREDENTIAL_DIR = f"{CERT_DIR}\\credentials"
CRL_DIR = f"{CERT_DIR}\\crl"
CMD_CERT = os.path.join(CERT_DIR, "cmd.crt")
POLICY_DIR = os.path.join(CERT_DIR, "mission_policy")
POLICY_FILE = os.path.join(POLICY_DIR, "mission_policy.json")  # Adjust path as needed
CRL_LIFETIME_SECONDS = 365 * 24 * 60 * 60  # 1 year
# Prepare log path
log_path = os.path.join(CERT_DIR, f"{GCS_NAME}_log.txt")
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

    sys.stdout = StreamToLogger(logger.info)
    sys.stderr = StreamToLogger(logger.error)

# Startup message for modes 1 and 2
if LOG_MODE in (1, 2):
    logger.info(f"[{GCS_NAME}] Logging initialized (mode={LOG_MODE})")
    if LOG_MODE in (1, 2):
        logger.info(f"[{GCS_NAME}] PID: {os.getpid()}")



serv_temp_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
server_address = ('172.18.6.212', 8080)

# Session key
SESSION_KEY_LENGTH = 32
SESSION_KEY_LIFETIME = 3 * 60
SESSION_RENEW_THRESHOLD = 3*30

global message_lenght_sent
message_lenght_sent = {}
global message_lenght_received
message_lenght_received = {}

global LAST_GPS_MESSAGE 
LAST_GPS_MESSAGE = {}


global UXV_HEARTBEAT
UXV_HEARTBEAT = {}

last_gps_message = threading.Lock()
uxv_heartbeat = threading.Lock()

global connection_establishement_time
connection_establishement_time = {}
global offset_per_node
offset_per_node = {}
uxv_sessions = {}  # {(ip,port): {"session_key": key, "offset": offset, "uxv_cn": cn, "hash": hash}}
session_contexts = {}  # {(sender_ip,port): {"session_key": key, "offset": offset, "sysid": sid, "client_cn": cn, "public_key": pu, "hash": hash}}
pending_dh = {}  # addr → {"private_key": ..., "start_time": ..., "initiator": True}
clients_lock = threading.RLock()
sysid_to_cn = {}  # {sysid: client_cn}
sysid_to_cn_lock = threading.RLock()
client_timestamps = {}
popup_counts = {}
popup_queue = Queue()
running = True
global credentials
credentials = []
credentials_lock = threading.Lock()
current_crl = None
crl_lock = threading.Lock()

global message_processing_time
message_processing_time = []
global gap_values_per_connection
gap_values_per_connection = {}

gap_values_lock = threading.Lock()
global number_gap_drop
number_gap_drop = 0
global latest_crl, latest_time
latest_crl = None
latest_time = None

# Tkinter
root = tk.Tk()
root.withdraw()
global uxv_permissions_sending, uxv_permissions_receiving, thirdparty_permissions_sending, thirdparty_permissions_receiving
global gcs_cert, GCS_cn, gcs_serial, PUgcs
try:
    with open(GCS_CERT, 'rb') as f:
        gcs_cert = load_pem_x509_certificate(f.read(), default_backend())
    GCS_cn = gcs_cert.subject.get_attributes_for_oid(NameOID.COMMON_NAME)[0].value
    gcs_serial = gcs_cert.serial_number
    PUgcs = gcs_cert.public_key()
    if LOG_MODE in (1, 2):
        logger.info(f"[{GCS_cn}] Loaded {GCS_CERT} with serial {gcs_serial}")
    if LOG_MODE in (1, 2):
        logger.info(f"[{GCS_cn}] PUgcs: {PUgcs}")
except Exception as e:
    PUgcs = None
    if LOG_MODE in (1, 2):
        logger.info(f"[{GCS_cn}] Failed to load PUgcs: {e}")
    
try:
    with open(GCS_KEY, 'rb') as f:
        PRgcs = serialization.load_pem_private_key(f.read(), None, default_backend())
except Exception as e:
    PRgcs = None
    if LOG_MODE in (1, 2):
        logger.info(f"[{GCS_cn}] Failed to load PRgcs: {e}")    
    
try:
    with open(CMD_CERT, 'rb') as f:
        cmd_cert = load_pem_x509_certificate(f.read(), default_backend())
    PUcmd = cmd_cert.public_key()
    CMD_cn = cmd_cert.subject.get_attributes_for_oid(NameOID.COMMON_NAME)[0].value
    if LOG_MODE in (1, 2):
        logger.info(f"[{GCS_cn}] Loaded PUcmd from {CMD_CERT}")
except Exception as e:
    PUcmd = None
    if LOG_MODE in (1, 2):
        logger.info(f"[{GCS_cn}] Failed to load PUcmd: {e}")
    
try:
    with open(CA_CERT, 'rb') as f:
        ca_cert = load_pem_x509_certificate(f.read(), default_backend())
        ca_pubkey = ca_cert.public_key()
except Exception as e:
    ca_pubkey = None
    if LOG_MODE in (1, 2):
        logger.info(f"[{GCS_cn}] Failed to load ca_pubkey: {e}") 


current_cert_crl = None
CRL_CERT_DIR = os.path.join(CERT_DIR, "CRL_CERTIFICATES")
os.makedirs(CRL_CERT_DIR, exist_ok=True)
crl_cert_lock = threading.Lock()

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
                        logger.info(f"[{GCS_cn}] Unknown policy format for {cap}")
            return converted

        uxv_permissions_sending = convert(data.get("uxv_permissions_sending", {}))
        uxv_permissions_receiving = convert(data.get("uxv_permissions_receiving", {}))
        thirdparty_permissions_sending = convert(data.get("thirdparty_permissions_sending", {}))
        thirdparty_permissions_receiving = convert(data.get("thirdparty_permissions_receiving", {}))
        
        if not uxv_permissions_sending or not uxv_permissions_receiving:
            raise ValueError("Missing or empty policy sections in JSON")
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] Loaded policies from {POLICY_FILE}")
        return uxv_permissions_sending, uxv_permissions_receiving, thirdparty_permissions_sending, thirdparty_permissions_receiving
    except FileNotFoundError:
        logger.error(f"[{GCS_cn}] Policy file not found: {POLICY_FILE}. Using default hardcoded policies.")
        
    except Exception as e:
        logger.error(f"[{GCS_cn}] Failed to load policies: {e}. Using defaults.")


def verify_credential(cred, pucmd, PUgcs, peer_pu=None):
    """Verify credential signature, type, lifetime, and PUs."""
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
        lifetime = int.from_bytes(cred[offset + 8 : offset + 16], "big") / 1e6
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
            logger.info(f"[{GCS_cn}] Verifying credential: Type={type_byte:02x}, Timestamp={timestamp}, Lifetime={lifetime}, Current time={time.time()}")
        if time.time() >= timestamp + lifetime:
            raise ValueError("Credential expired")
        
        # Check CRL
        cred_hash = hashlib.sha256(cred).hexdigest()
        with crl_lock:
            if cred_hash in current_crl["hashes"]:
                raise ValueError("Credential is revoked")
        
        if peer_pu is None:
           if type_byte == 0x02:
                if pu2_der != PUgcs.public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo):
                    raise ValueError("Invalid PUs in 0x02")
           elif type_byte == 0x03:
                if pu1_der != PUgcs.public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo):
                    raise ValueError("Invalid PUgcs in 0x03")
        
        else:
            if type_byte == 0x02:
                if pu1_der != peer_pu.public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo) or \
                pu2_der != PUgcs.public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo):
                    raise ValueError("Invalid PUs in 0x02")
            elif type_byte == 0x03:
                if pu1_der != PUgcs.public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo):
                    raise ValueError("Invalid PUgcs in 0x03")
        
        return {
            "type": type_byte,
            "pu1": pu1,
            "pu2": pu2,
            "timestamp": timestamp,
            "lifetime": lifetime,
            "capacity_string": capacity_string,
            "hash": cred_hash
        }
    except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] Credential signature verification failed: {e}")
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] Payload: {payload.hex()}")
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] Signature: {signature.hex()}")
            raise ValueError(f"Signature verification failed: {e}")

def load_credentials():
    """Load and verify credentials."""
    global credentials
    credentials = []
    if not os.path.exists(CREDENTIAL_DIR):
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] No credential dir: {CREDENTIAL_DIR}")
        return credentials
    
    for filename in os.listdir(CREDENTIAL_DIR):
        if filename.endswith('.cred'):
            filepath = os.path.join(CREDENTIAL_DIR, filename)
            try:
                with open(filepath, 'rb') as f:
                    cred = f.read()
                data = verify_credential(cred, PUcmd, PUgcs)
                credentials.append({
                    "filename": filename,
                    "type": data["type"],
                    "pu1": data["pu1"],
                    "pu2": data["pu2"],
                    "timestamp": data["timestamp"],
                    "lifetime": data["lifetime"],
                    "hash": data["hash"],
                    "capacity_string": data["capacity_string"],
                    "raw": cred
                })
                if LOG_MODE in (1, 2):
                    logger.info(f"[{GCS_cn}] Loaded credential: {filename} (Type: 0x{data['type']:02x})")
            except ValueError as e:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{GCS_cn}] Skipped credential: {filename}: {e}")
            except Exception as e:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{GCS_cn}] Skipped credential: {filename}: Failed to read: {e}")
    
    if not credentials:
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] No valid credentials in {CREDENTIAL_DIR}")
    return credentials


def initiate_dh_key_renewal(addr, session, cn):
    if LOG_MODE in (1, 2):
        logger.info(f"[{GCS_cn}] Initiating DH key renewal with {session.get('uxv_cn', 'unknown')} at {addr}")
    message = f"{GCS_cn} initating key renewal with  {session.get('uxv_cn', 'unknown')}, sent 0x11"
    serv_temp_sock.sendto(message.encode('utf-8'), server_address)
    timestamp_bytes = struct.pack('<Q', int(time.time() * 1e6))
    hmac_value = compute_hmac(b'\x11', GCS_cn.encode('utf-8'), timestamp_bytes, session["session_key_sending"])
    msg = b'\x11' + GCS_cn.encode('utf-8') + timestamp_bytes + hmac_value
    uxv_socket.sendto(msg, addr)
    
    message_lenght_sent.setdefault(cn, []).append((11 , len(msg)))
    
    with clients_lock:
        pending_dh[addr] = {
            "start_time": time.time(),
            "initiator": True,
            "retry_count": pending_dh.get(addr, {}).get("retry_count", 0) + 1  # Increment retry count
        }
    if LOG_MODE in (1, 2):
        logger.info(f"[{GCS_cn}] Sent 0x11 to {session.get('uxv_cn', 'unknown')} at {addr}, Retry count: {pending_dh[addr]['retry_count']}")

def session_key_monitor():
    while running:
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] Key monitor thread")
        now = time.time()
        with clients_lock:
            for addr, session in list(uxv_sessions.items()):
                created = session.get("session_created_at", 0)
                cn = session.get("uxv_cn", "unknown")
                if now - created >= SESSION_KEY_LIFETIME - SESSION_RENEW_THRESHOLD:
                    if addr not in pending_dh:
                        initiate_dh_key_renewal(addr, session, cn)
            for addr, session in list(session_contexts.items()):
                    created = session.get("session_created_at", 0)
                    if now - created >= SESSION_KEY_LIFETIME:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] CMD session key expired for {session.get('client_cn', 'unknown')} at {addr}, deleting session")
                        del session_contexts[addr]
        time.sleep(10)

def credential_expiry_monitor():
    while running:
        now = time.time()
        with clients_lock:
            for session_dict in [session_contexts, uxv_sessions]:
                for addr, session in list(session_dict.items()):
                    expiry_time = session["cred_timestamp"] + session["cred_lifetime"]
                    if now >= expiry_time:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] now: {now}, Expiry time: {expiry_time}, Cred_timestamp: {session["cred_timestamp"]}, Lifetime: {session['cred_lifetime']}")
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Credential for {session.get('client_cn', session.get('uxv_cn', 'unknown'))} at {addr} expired - deleting session")
                        del session_dict[addr]
                        if session_dict is uxv_sessions:
                            LAST_GPS_MESSAGE.pop(session["uxv_cn"], None)
                            UXV_HEARTBEAT.pop(session["uxv_cn"], None)
                        
        time.sleep(10)

def cleanup_pending_dh():
    max_retries = 3  # Maximum number of retry attempts
    while running:
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] Cleanup pending DH renewals")
        now = time.time()
        with clients_lock:
            for addr in list(pending_dh):
                if now - pending_dh[addr]["start_time"] > 10:
                    retry_count = pending_dh[addr]["retry_count"]
                    if retry_count < max_retries:
                        session = uxv_sessions.get(addr)
                        if session:
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{GCS_cn}] Retrying DH renewal with {session.get('uxv_cn', 'unknown')} at {addr}, Attempt {retry_count}/{max_retries}")
                            initiate_dh_key_renewal(addr, session, session.get('uxv_cn', 'unknown'))
                        else:
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{GCS_cn}] No session found for {addr}, removing from pending_dh")
                            del pending_dh[addr]
                    else:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Exhausted retries ({max_retries}) for DH renewal with {addr}")
                        del pending_dh[addr]
                        session = uxv_sessions.get(addr)
                        if session:
                            popup_queue.put(("Key Renewal Failed", f"Failed to renew session key with {session.get('uxv_cn', 'unknown')} after {max_retries} attempts, deleting the session an try to reconnect", session.get('uxv_cn', 'unknown')))
                            connect_to_uxv(uxv_cn=session["uxv_cn"],uxv_ip=session["uxv_ip"],uxv_mtls_port=session["mtls_port"],uxv_udp_port=addr[1],cred_03=session["cred_03"],cred_timestamp=session["cred_timestamp"],cred_lifetime=session["cred_lifetime"],capacity_string=session["capacity_string"])
        time.sleep(5)
        
        


def load_crl():
    """Load the latest CRL."""
    global current_crl
    if not os.path.exists(CRL_DIR):
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] No CRL dir: {CRL_DIR}")
        return None
    
    crl_files = [f for f in os.listdir(CRL_DIR) if f.endswith('.crl')]
    if not crl_files:
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] No CRL files found in {CRL_DIR}")
        return None
    
    latest_crl = max(crl_files, key=lambda x: float(x.split('_')[-1].replace('.crl', '')))
    filepath = os.path.join(CRL_DIR, latest_crl)
    try:
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
        if len(payload) > 16:  # Check if payload has more than timestamp + lifetime
            hashess = [payload[i:i+32].hex() for i in range(16, len(payload), 32)]
        current_crl = {"timestamp": timestamp, "lifetime": lifetime, "hashes": set(hashess), "raw": crl_data}
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] Loaded CRL: {latest_crl}, Timestamp={timestamp}")
        return current_crl
    except Exception as e:
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] Failed to load CRL {latest_crl}: {e}")
        return None

def load_latest_cert_crl(crl_dir):
    global latest_crl, latest_time, current_cert_crl

    # Only consider files ending in .crl or .crl.der
    crl_files = [f for f in os.listdir(crl_dir) if f.endswith(".crl") or f.endswith(".crl.der")]
    if not crl_files:
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] No CRL files found in {crl_dir}")
        return None

    for crl_file in crl_files:
        crl_path = os.path.join(crl_dir, crl_file)
        try:
            with open(crl_path, "rb") as f:
                crl_data = f.read()
                cert_crl = load_der_x509_crl(crl_data, default_backend())
                ca_pubkey.verify(cert_crl.signature,cert_crl.tbs_certlist_bytes, ec.ECDSA(cert_crl.signature_hash_algorithm))
                now = datetime.now(timezone.utc)
                if LOG_MODE in (1, 2):
                    logger.info(f"NOW: {now}, CRL NEXT UPDATE: {cert_crl.next_update_utc}")
                if cert_crl.next_update_utc < now:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{GCS_cn}] Skipping expired CRL '{crl_file}': Next update was {cert_crl.next_update_utc}")
                    return None
                
                if LOG_MODE in (1, 2):
                    logger.info(f"[{GCS_cn}] Loaded CRL: {crl_file}, Last Update={cert_crl.last_update_utc}")
                if latest_time is None or cert_crl.last_update_utc > latest_time:
                    latest_time = cert_crl.last_update_utc
                    latest_crl = cert_crl
                    
                current_cert_crl = {
                    "timestamp": int(latest_crl.last_update_utc.timestamp() * 1e6),
                    "revoked_serials": {r.serial_number for r in cert_crl} if cert_crl else set(),
                     }      
                
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] Skipping invalid CRL '{crl_file}': {e}")
            return None

    return latest_crl

current_crl = load_crl()
credentials = load_credentials()
current_cert_crl = load_latest_cert_crl(CRL_CERT_DIR)

# mTLS server
server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
server_socket.bind(('0.0.0.0', MTLS_PORT))
server_socket.listen(5)
context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
context.load_cert_chain(certfile=GCS_CERT, keyfile=GCS_KEY)
context.load_verify_locations(CA_CERT)
context.verify_mode = ssl.CERT_REQUIRED
secure_socket = context.wrap_socket(server_socket, server_side=True)
secure_socket.settimeout(1.0)
if LOG_MODE in (1, 2):
    logger.info(f"[{GCS_cn}] mTLS server on port {MTLS_PORT}...")

# UDP sockets
udp_socket = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
udp_socket.setblocking(False)
udp_socket.bind(("", UDP_PORT))
if LOG_MODE in (1, 2):
    logger.info(f"[{GCS_cn}] Bound UDP port {UDP_PORT} for thirdparty")

uxv_socket = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
uxv_socket.setblocking(False)
uxv_socket.bind(("", 0))
local_udp_port = uxv_socket.getsockname()[1]
if LOG_MODE in (1, 2):
    logger.info(f"[{GCS_cn}] Bound UDP port {uxv_socket.getsockname()[1]} for UXVs")

# Mission Planner socket
mp_socket = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
mp_socket.setblocking(False)
mp_socket.bind(("", MISSION_PLANNER_RECEIVE_PORT))
if LOG_MODE in (1, 2):
    logger.info(f"[{GCS_cn}] Bound UDP port {MISSION_PLANNER_RECEIVE_PORT} for Mission Planner")

# MAVLink
mav = mavutil.mavlink_connection('udp:127.0.0.1:14500', source_system=255)

def compute_hmac(type_byte, payload, timestamp_bytes, session_key):
     
    timestamp_start = int(time.time() * 1e6)    
    """Compute HMAC."""
    h = hmac.HMAC(session_key, hashes.SHA256())
    h.update(type_byte + payload + timestamp_bytes)
    current_time = int(time.time() * 1e6)
    #logger.info(f"[{GCS_cn}] start-current compute hmac: {timestamp_start-current_time}")
    return h.finalize()[:16]


def verify_policy(msg_type, capability_string, session, role, mav_type=None):
    #logger.info(f"[{GCS_cn}] Verifying policy for message type {msg_type.hex()} with capability string '{capability_string}' and role '{role}'")
    #timestamp_start = int(time.time() * 1e6)
    """Verify if a message type is allowed based on the capability string and connection type."""
    access_levels = ["Access1", "Access2", "Access3"]
    capabilities = capability_string.split(",") if capability_string else []
    if not any(level in capabilities for level in access_levels):
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] No access for Node with capacity {capability_string} for message type {msg_type}")
        return False
    
    # Determine connection type
    is_uxv = "uxv_cn" in session
    is_thirdparty = "client_cn" in session
    
    # Select permissions based on connection type and role
    if is_uxv:
        permissions = uxv_permissions_sending if role == "sender" else uxv_permissions_receiving
    elif is_thirdparty:
        permissions = thirdparty_permissions_sending if role == "sender" else thirdparty_permissions_receiving
    else:
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] Unknown connection type")
        return False
    
    for capability in capabilities:
        perm = permissions.get(capability)
        if perm is None:
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] Capability {capability} not found in permissions for Node with capacity {capability_string}")
            continue
        if isinstance(perm, list):
            if msg_type in perm:
                #logger.info(f"[{GCS_cn}] start-current mgs in permitions: {timestamp_start-current_time}")
                return True
        elif isinstance(perm, dict):
            if msg_type in perm:
                allowed = perm[msg_type]
                if allowed is None or (mav_type and mav_type in allowed):
                    #logger.info(f"[{GCS_cn}] start-current mav_type: {timestamp_start-current_time}")
                    return True
    if mav_type:
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] Message type {msg_type.hex()}, Mavlink: {mav_type} not allowed for Node with role: {role} and capacity {capability_string}")
        return False
    else:
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] Message type {msg_type.hex()} not allowed for Node with role: {role} and capacity {capability_string}")
        return False
    #current_time = int(time.time() * 1e6) 
    #logger.info(f"[{GCS_cn}] start-current mgs not allowed: {timestamp_start-current_time}")
    

def verify_hmac(data, session_info, client_cn, msg_type):
    global number_gap_drop
    timestamp_start = int(time.time()*1e6)
    """Verify HMAC and timestamp; supports optional key renewal with pending_session_key."""
    if len(data) < 15:
        popup_queue.put(("Message Error", f"Message too short for {client_cn}\nType: {msg_type}\n", client_cn))
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] Verification failed for {client_cn}: Too short")
        return None

    type_byte = data[0:1]
    if type_byte not in VALID_TYPES:
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] Invalid type for {client_cn}: {type_byte.hex()}")
        return None

    payload = data[1:-24]
    timestamp_bytes = data[-24:-16]
    received_hmac = data[-16:]
    timestamp = struct.unpack('<Q', timestamp_bytes)[0]
    offset = session_info["offset"]
    role = session_info.get("time_sync_role")
    if role == "server":
        adjusted_timestamp = timestamp + offset
    else:
        adjusted_timestamp = timestamp - offset
    current_time = int(time.time() * 1e6)
    gap = abs(adjusted_timestamp - current_time)
    #logger.info(f"[{GCS_cn}] start-current hmac init: {timestamp_start-current_time} μs")
    # Try current session key
    computed_hmac = compute_hmac(type_byte, payload, timestamp_bytes, session_info["session_key_receiving"])
    #logger.info(f"[{GCS_cn}] HMAC verification for {client_cn}:")
    #logger.info(f"[{GCS_cn}]   Received HMAC: {received_hmac.hex()}")
    logger.info(f"[{GCS_cn}]   Timestamp: {timestamp}, Adjusted: {adjusted_timestamp}, Current: {current_time}, Offset: {offset}, Gap: {gap} μs")
    if computed_hmac == received_hmac:
        #logger.info(f"[{GCS_cn}]   Computed HMAC with current key: {computed_hmac.hex()}")
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] HMAC verified with current session key, gap: {gap} μs")
    elif ("pending_session_key_receiving" in session_info and "session_state" in session_info and session_info["session_state"] == "pending_renewal" and
        session_info["pending_session_key_receiving"] is not None):
        computed_hmac_pending = compute_hmac(type_byte, payload, timestamp_bytes, session_info["pending_session_key_receiving"])
        #logger.info(f"[{GCS_cn}]   Computed HMAC with pending key: {computed_hmac.hex()}")
        if computed_hmac_pending == received_hmac:
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] HMAC matched with pending key — promoting new session keys:")
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] pending_session_key_receiving: {session_info["pending_session_key_receiving"].hex()}")
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] pending_session_key_sending: {session_info["pending_session_key_sending"].hex()}")
            session_info["session_key_sending"] = session_info["pending_session_key_sending"]
            session_info["session_key_receiving"] = session_info["pending_session_key_receiving"]
            session_info["pending_session_key_sending"] = None
            session_info["pending_session_key_receiving"] = None
            session_info["session_state"] = "established"
            session_info["session_created_at"] = time.time()
            session_info["real_renewal_count"] = session_info["pending_renewal_count"]
            message = f"{CMD_cn} Renewed session keys with {client_cn} "
            serv_temp_sock.sendto(message.encode('utf-8'), server_address)
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] Promoted pending session keys for {client_cn} TIMESTAMP: {(time.time()*1e6)}")
        else:
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] HMAC failed with both current and pending keys")
            return None
    else:
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] HMAC failed with current key and no valid pending key")
        return None

    if timestamp in client_timestamps.get(client_cn, deque(maxlen=200)):
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] Timestamp verification failed for {client_cn}: Duplicate")
        popup_queue.put(("Timestamp Error", f"Repeated timestamp for {client_cn}\nType={msg_type}\n", client_cn))
        return None
    if gap > 4000000:
        number_gap_drop += 1
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] Timestamp verification failed for {client_cn}: Outside 400ms window")
        current_time = int(time.time() * 1e6) 
        #if LOG_MODE in (1, 2):
         #   logger.info(f"[{GCS_cn}] start-current hmac gap: {timestamp_start-current_time}")
        popup_queue.put(("Timestamp Error", f"Timestamp outside window for {client_cn}\nGap: {gap} μs", client_cn))
        return None

    client_timestamps.setdefault(client_cn, deque(maxlen=200)).append(timestamp)
    #logger.info(f"[{GCS_cn}] Verified for {client_cn}")
    current_time = int(time.time() * 1e6) 
    #logger.info(f"[{GCS_cn}] start-current hmac total: {timestamp_start-current_time}")
    return (type_byte, payload, gap)


def process_popups():
    """Process popup messages."""
    try:
        title, message, client_cn = popup_queue.get_nowait()
        current_time = time.time()
        popup_counts[client_cn] = [t for t in popup_counts.get(client_cn, []) if current_time - t < 60]
        if len(popup_counts[client_cn]) < 5:
            popup_counts[client_cn].append(current_time)
            messagebox.showerror(title, message)
    except Empty:
        pass
    root.after(10, process_popups)




def connect_to_uxv(uxv_cn, uxv_ip, uxv_mtls_port, uxv_udp_port, cred_03, cred_timestamp, cred_lifetime, capacity_string):
    message = f"{GCS_cn} intilized connection establishment with {uxv_cn}"
    serv_temp_sock.sendto(message.encode('utf-8'), server_address)
    initial_time = time.time()*1e6
    global offset_per_node
    """Establish mTLS connection to UXV with retry logic."""
    max_retries = 3
    retry_delay = 2  # seconds
    attempt = 0
    client_socket = None
    secure_socket = None
    
    while attempt < max_retries:
        try:
            attempt += 1
            client_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
            context.load_cert_chain(certfile=GCS_CERT, keyfile=GCS_KEY)
            context.load_verify_locations(CA_CERT)
            context.verify_mode = ssl.CERT_REQUIRED
            secure_socket = context.wrap_socket(client_socket, server_hostname=uxv_ip)
            
            secure_socket.connect((uxv_ip, uxv_mtls_port))
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] mTLS to UXV {uxv_cn} at {uxv_ip}:{uxv_mtls_port} (Attempt {attempt})")
            
            cert_der = secure_socket.getpeercert(binary_form=True)
            if not cert_der:
                raise ValueError("No certificate received from UXV")
            
            cert_obj = load_der_x509_certificate(cert_der, default_backend())
            uxv_pu = cert_obj.public_key()
            uxv_cn_received = cert_obj.subject.get_attributes_for_oid(NameOID.COMMON_NAME)[0].value
            peer_serial = cert_obj.serial_number
            
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] Received certificate from UXV {uxv_cn}: CN={uxv_cn_received}, Serial={peer_serial}")
            cert_crl = load_latest_cert_crl(CRL_CERT_DIR)
            if cert_crl is None:
                raise ValueError("No valid CRL found")
            if cert_crl is not None:
                revoked_serials = {r.serial_number for r in cert_crl}
                if peer_serial in revoked_serials:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{GCS_cn}] Connection rejected: peer certificate serial {peer_serial} of {uxv_cn_received} is revoked.")
                    secure_socket.close()
                    return
            
            
            
            if uxv_cn_received != uxv_cn:
                raise ValueError(f"CN mismatch: expected {uxv_cn}, received {uxv_cn_received}")
            
            if not isinstance(uxv_pu, EllipticCurvePublicKey):
                raise ValueError("Expected EC public key")
            
            # Send 0x03 credential
            secure_socket.sendall(len(cred_03).to_bytes(4, 'big') + cred_03)
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] Sent 0x03 to UXV {uxv_cn}: Length={len(cred_03)}")
            
            ready_token = recv_exact(secure_socket, 1)
            if ready_token != TIME_SYNC_READY_TOKEN:
                raise ValueError("Unexpected time sync readiness token from UXV")
            try:
                time_sync_logger = logger.info if LOG_MODE in (1, 2) else None
                ts_result = perform_time_sync(
                    secure_socket,
                    role="client",
                    logger=time_sync_logger,
                    log_prefix=f"[{GCS_cn}] Time sync with {uxv_cn}: ",
                )
            except TimeSyncError as e:
                raise ValueError(f"Time synchronisation failed with {uxv_cn}: {e}") from e
            offset = ts_result.offset_us
            
            offset_per_node.setdefault(uxv_cn, []).append(offset)
            
            
            shared_secret = PRgcs.exchange(ec.ECDH(), uxv_pu)

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
            
            # Store in uxv_sessions
            cred_hash = hashlib.sha256(cred_03).hexdigest()
            with clients_lock:
                uxv_sessions[(uxv_ip, uxv_udp_port)] = {
                    "time_sync_role": "client",
                    "cred_03": cred_03,
                    "shared_secret": shared_secret,
                    "session_key_sending": session_key_sending,
                    "session_key_receiving": session_key_receiving,
                    "offset": offset,
                    "uxv_cn": uxv_cn,
                    "uxv_pu": uxv_pu,
                    "capacity_string": capacity_string, 
                    "mtls_port": uxv_mtls_port,
                    "uxv_ip": uxv_ip,
                    "session_created_at": time.time(),
                    "hash": cred_hash,
                    "cred_timestamp": cred_timestamp,
                    "cred_lifetime": cred_lifetime,
                    "peer_serial": peer_serial,
                    "last_heartbeat": time.time(),
                    "renewal_count": 0,
                }
                if LOG_MODE in (1, 2):
                    logger.info(f"[{GCS_cn}] Added UXV session for {uxv_cn} at {uxv_ip}:{uxv_udp_port} with capacity level {capacity_string}")
            
            local_udp_port = uxv_socket.getsockname()[1]
            try:
                secure_socket.sendall(local_udp_port.to_bytes(2, 'big'))  # Send UDP port
                if LOG_MODE in (1, 2):
                    logger.info(f"[{GCS_cn}] Sent UDP port {local_udp_port} to GCS {uxv_cn}")
            except Exception as e:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{GCS_cn}] Failed to send UDP port to GCS {uxv_cn}: {e}")
                return
            
            client_timestamps[uxv_cn] = deque(maxlen=200)
            popup_counts[uxv_cn] = []
            break  # Success, exit retry loop
            
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] Failed to connect to UXV {uxv_cn} (Attempt {attempt}/{max_retries}): {e}")
            if attempt < max_retries:
                time.sleep(retry_delay)
            else:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{GCS_cn}] Exhausted retries for UXV {uxv_cn}")
                popup_queue.put(("Connection Failed", f"Failed to connect to UXV {uxv_cn} after {max_retries} attempts", uxv_cn))
        finally:
            final_time = time.time()*1e6
            connection_establishement_time.setdefault(uxv_cn,[]).append(final_time - initial_time)
            logger.info(f"[{GCS_cn}] Connection establishment to {uxv_cn} initial time: {initial_time} μs")
            logger.info(f"[{GCS_cn}] Connection establishment time to UXV {uxv_cn}: {final_time - initial_time} μs")
            if secure_socket:
                try:
                    secure_socket.close()
                except:
                    pass
            if client_socket:
                try:
                    client_socket.close()
                except:
                    pass
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] Closed mTLS connection attempt to UXV {uxv_cn}")

def handle_mtls_client(client_socket, addr):
    initial_time = time.time()*1e6
    """Handle mTLS client (thirdparty, CMD, or 2CMD)."""
    global credentials, offset_per_node
    client_cn = "Unknown"
    try:
        cert_der = client_socket.getpeercert(binary_form=True)
        if not cert_der:
            raise ValueError("No certificate received from client")
        
        cert_obj = load_der_x509_certificate(cert_der, default_backend())
        client_pu = cert_obj.public_key()
        client_cn = cert_obj.subject.get_attributes_for_oid(NameOID.COMMON_NAME)[0].value
        peer_serial = cert_obj.serial_number
        
        cert_crl = load_latest_cert_crl(CRL_CERT_DIR)
        if cert_crl is None:
            raise ValueError("No valid CRL found")
        if cert_crl is not None:
            revoked_serials = {r.serial_number for r in cert_crl}
            if peer_serial in revoked_serials:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{GCS_cn}] Connection rejected: peer certificate serial {peer_serial} of {client_cn} is revoked.")
                client_socket.close()
                return

        if client_cn not in CMD_cn or client_cn.startswith("2CMD"):
            raise ValueError(f"Unexpected CN: {client_cn}")

        ip_matched_san = False
        try:
            # Attempt to get the SAN extension
            san = cert_obj.extensions.get_extension_for_class(SubjectAlternativeName)
            # Check for IP addresses in the SAN extension
            if san.value.get_values_for_type(x509.IPAddress):
                for san_ip in san.value.get_values_for_type(x509.IPAddress):
                    if str(san_ip) == addr[0]:
                        ip_matched_san = True
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Host IP ({addr[0]}) matched Subject Alternative Name: {san_ip}")
                        break
        except x509.ExtensionNotFound:
            raise ValueError("No Subject Alternative Name extension found in certificate")
        
        if not ip_matched_san:
            raise ValueError(f"Host identity verification failed: Connection IP ({addr[0]}) does not match CN or any Subject Alternative Name in the certificate.")
    
        if not isinstance(client_pu, EllipticCurvePublicKey):
            raise ValueError("Expected EC public key")
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] mTLS from {addr}, CN: {client_cn} with peer_serial={peer_serial}" )
        
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
        
        # Verify credential
        cred_data = verify_credential(cred, PUcmd, PUgcs, client_pu)
        if cred_data is None:
            raise ValueError("Invalid credential or crl expired")
            
            

        if cred_data["type"] != 0x02:
            raise ValueError(f"Expected 0x02 credential from {client_cn}")
        
        try:
            client_socket.sendall(TIME_SYNC_READY_TOKEN)
            time_sync_logger = logger.info if LOG_MODE in (1, 2) else None
            ts_result = perform_time_sync(
                client_socket,
                role="server",
                logger=time_sync_logger,
                log_prefix=f"[{GCS_cn}] Time sync with {client_cn}: ",
            )
        except TimeSyncError as e:
            raise ValueError(f"Time synchronisation failed: {e}") from e
        offset = ts_result.offset_us

        offset_per_node.setdefault(client_cn, []).append(offset)
        # Save credential
        filename = f"{client_cn}_to_{GCS_cn}_{cred_data['timestamp']}.cred"
        filepath = os.path.join(CREDENTIAL_DIR, filename)
        os.makedirs(os.path.dirname(filepath), exist_ok=True)
        with open(filepath, 'wb') as f:
            f.write(cred)
        with credentials_lock:
            credentials.append({
                "filename": filename,
                "type": cred_data["type"],
                "pu1": cred_data["pu1"],
                "pu2": cred_data["pu2"],
                "timestamp": cred_data["timestamp"],
                "lifetime": cred_data["lifetime"],
                "hash": cred_data["hash"],
                "capacity_string": cred_data["capacity_string"],
                "raw": cred
            })
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] Saved 0x02 credential: {filename}")
        
        
        
        shared_secret = PRgcs.exchange(ec.ECDH(), client_pu)
        
        session_key_sending = HKDF(
            algorithm=hashes.SHA256(),
            length=SESSION_KEY_LENGTH,
            salt=None,
            info=b"session_key_receiving",
        ).derive(shared_secret)
        
        session_key_receiving = HKDF(
            algorithm=hashes.SHA256(),
            length=SESSION_KEY_LENGTH,
            salt=None,
            info=b"session_key_sending",
        ).derive(shared_secret)
        
        if not session_key_sending:
            raise Exception("Session key failed sending on HKDF")
        
        if not session_key_receiving:
            raise Exception("Session key failed receiving on HKDF")
        
        try:
            port_bytes = client_socket.recv(2)
            if len(port_bytes) != 2:
                raise ValueError("Failed to receive UDP port from CMD")

            udp_port = int.from_bytes(port_bytes, 'big')
            sender_ip = client_socket.getpeername()[0]
            session_contexts[(sender_ip, udp_port)] = {
                "time_sync_role": "server",
                "shared_secret": shared_secret,
                "session_key_sending": session_key_sending,
                "session_key_receiving": session_key_receiving,
                "offset": offset,
                "sysid": None,
                "client_cn": client_cn,
                "public_key": client_pu,
                "hash": cred_data["hash"],  # optional if you want to track credential hash
                "capacity_string": cred_data["capacity_string"],
                "session_created_at": time.time(),
                "pending_session_key_sending": None,
                "pending_session_key_receiving": None,
                "session_state": "established",
                "renewal_start_time": None,
                "cred_timestamp": cred_data["timestamp"],
                "cred_lifetime": cred_data["lifetime"],
                "peer_serial": peer_serial,
                "real_renewal_count": 0,
                "pending_renewal_count": 0,
                "last_heartbeat": time.time(),
            }
            
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] Registered CMD {client_cn} on {sender_ip}:{udp_port} in session_contexts")
            final_time = time.time()*1e6
            print(f"[{GCS_cn}] Final timestamp for cmd-gcs connection - {final_time} μs ")
            
            message = f"{GCS_cn} finished connection establishment with {client_cn}"
            serv_temp_sock.sendto(message.encode('utf-8'), server_address)
            
            connection_establishement_time.setdefault(client_cn, []).append(final_time - initial_time)
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] Connection establishment time for {client_cn}: {final_time - initial_time} μs") 
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] Failed to receive or register UDP port: {e}")
            return
        
    except Exception as e:
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] mTLS error for {client_cn} at {addr}: {e}")
    finally:
        client_socket.close()
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] Closed mTLS for {client_cn}")

def handle_thirdparty_udp():
    """Handle UDP messages from thirdparty (CMD or 2CMD)."""
    global current_crl, credentials 
    global message_processing_time
    while running:
        try:
            message_processing_start = time.time()*1e6
            data, addr = udp_socket.recvfrom(65536)
            type_byte = data[0:1]
            msg_type = type_byte.hex()
            
            # Handle other message types (require existing session)
            session_info = session_contexts.get(addr)
            if not session_info:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{GCS_cn}] No thirdparty session for {addr}")
                continue
            client_cn = session_info["client_cn"]
            session_key = session_info["session_key_receiving"]
            offset = session_info["offset"]
            capacity_string = session_info["capacity_string"]

            message_lenght_received.setdefault(client_cn, []).append((msg_type , len(data)))
            
            result = verify_hmac(data, session_info, client_cn, msg_type)
            if not result:
                continue
            
            type_byte, payload, gap = result
            timestamp = struct.unpack('<Q', data[-24:-16])[0]
            gap_values_per_connection.setdefault(client_cn, []).append((type_byte,gap))
            if type_byte == b'\x02':
                if verify_policy(type_byte, capacity_string, session_info, role="receiver"):
                    try:
                        os.makedirs(MISSION_DIR, exist_ok=True)
                        filename = f"mission_{int(timestamp)}.waypoints"
                        filepath = os.path.join(MISSION_DIR, filename)
                        with open(filepath, 'wb') as f:
                            f.write(payload)
                        popup_queue.put(("Mission Saved",
                                        f"Mission saved to {filename}\nSize: {len(payload)} bytes\n",
                                        client_cn))
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Received waypoint mission: Type=0x02, Timestamp={timestamp}, Size={len(payload)}, Saved={filepath}")
                    except OSError as e:
                        popup_queue.put(("Error", f"Failed to save mission: {e}", client_cn))
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Failed to save mission: {e}")
            
            elif type_byte == b'\x05':
                logger.info(f"[{GCS_cn}] received 0x05 -----------")
                message = f"{GCS_cn} Received 0x05 message from {client_cn}"
                serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                if verify_policy(type_byte, capacity_string, session_info, role="receiver"):
                    try:
                        offset = 0
                        len_cn = payload[offset]
                        offset += 1
                        uxv_cn = payload[offset:offset+len_cn].decode('utf-8')
                        offset += len_cn
                        len_ip = payload[offset]
                        offset += 1
                        uxv_ip = payload[offset:offset+len_ip].decode('ascii')
                        offset += len_ip
                        uxv_mtls_port = int.from_bytes(payload[offset:offset+4], 'big')
                        offset += 4
                        uxv_udp_port = int.from_bytes(payload[offset:offset+4], 'big')
                        offset += 4
                        cred_len = int.from_bytes(payload[offset:offset+4], 'big')
                        offset += 4
                        cred_03 = payload[offset:offset+cred_len]
                        
                        cred_data = verify_credential(cred_03, PUcmd, PUgcs)
                        if cred_data is None:
                            raise ValueError("Invalid 0x03 credential or crl expired")
                        if cred_data["type"] != 0x03:
                            raise ValueError("Invalid credential type in 0x05")
                        
                        filename = f"{GCS_cn}_to_{uxv_cn}_{cred_data['timestamp']}.cred"
                        filepath = os.path.join(CREDENTIAL_DIR, filename)
                        os.makedirs(os.path.dirname(filepath), exist_ok=True)
                        with open(filepath, 'wb') as f:
                            f.write(cred_03)
                        with credentials_lock:
                            credentials.append({
                                "filename": filename,
                                "type": cred_data["type"],
                                "pu1": cred_data["pu1"],
                                "pu2": cred_data["pu2"],
                                "timestamp": cred_data["timestamp"],
                                "lifetime": cred_data["lifetime"],
                                "hash": cred_data["hash"],
                                "capacity_string": cred_data["capacity_string"],
                                "raw": cred_03
                            })
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Saved 0x03 credential: {filename}")
                        
                        threading.Thread(target=connect_to_uxv, args=(uxv_cn, uxv_ip, uxv_mtls_port, uxv_udp_port, cred_03, cred_data["timestamp"], cred_data["lifetime"], cred_data["capacity_string"]), daemon=True).start()
                        popup_queue.put(("Connection Initiated",
                                        f"Initiating connection to UXV {uxv_cn} at {uxv_ip}:{uxv_mtls_port}",
                                        client_cn))
                    except Exception as e:
                        popup_queue.put(("Error", f"Failed to process 0x05: {e}", client_cn))
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Failed to process 0x05: {e}")
            
            elif type_byte == b'\x04':
                message = f"{GCS_cn} Received 0x04 message from {client_cn}"
                serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                if verify_policy(type_byte, capacity_string, session_info, role="receiver"):
                    try:
                        sig_len = int.from_bytes(payload[-2:], 'big')
                        signature = payload[-(sig_len + 2):-2]
                        crl_payload = payload[:-(sig_len + 2)]
                        PUcmd.verify(signature, crl_payload, ec.ECDSA(hashes.SHA256()))
                        crl_timestamp = int.from_bytes(crl_payload[:8], 'big') / 1e6
                        lifetime = int.from_bytes(crl_payload[8:16], 'big')
                        if time.time() >= crl_timestamp + lifetime:
                            raise ValueError("CRL expired")
                        # Parse hashes as 32-byte binary sequences
                        crl_hashes = []
                        offset = 16
                        while offset < len(crl_payload):
                            if offset + 32 <= len(crl_payload):
                                crl_hashes.append(crl_payload[offset:offset+32].hex())  # Convert to hex for consistency
                                offset += 32
                            else:
                                break
                        new_crl = {"timestamp": crl_timestamp, "lifetime": lifetime, "hashes": set(crl_hashes), "raw": payload}
                        
                        with crl_lock:
                            if current_crl is None or crl_timestamp > current_crl["timestamp"]:

                                

                                os.makedirs(CRL_DIR, exist_ok=True)
                                for old_file in os.listdir(CRL_DIR):
                                    if old_file.endswith(".crl"):
                                        try:
                                            os.remove(os.path.join(CRL_DIR, old_file))
                                        except Exception as e:
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{GCS_cn}] Failed to remove old CRL {old_file}: {e}")
                                crl_filename = f"crl_{crl_timestamp}.crl"
                                with open(os.path.join(CRL_DIR, crl_filename), 'wb') as f:
                                    f.write(payload)
                                current_crl = new_crl
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{GCS_cn}] Updated CRL: Timestamp={crl_timestamp}, Hashes={len(crl_hashes)}")
                                
                                # Terminate revoked sessions
                                with clients_lock:
                                    for addr, info in list(session_contexts.items()):
                                        if info["hash"] in crl_hashes:
                                            for cred in credentials:
                                                if cred["hash"] == info["hash"]:
                                                    credentials.remove(cred)
                                                    try:
                                                        os.remove(os.path.join(CREDENTIAL_DIR, cred["filename"]))
                                                        if LOG_MODE in (1, 2):
                                                            logger.info(f"[{GCS_cn}] Removed credential file {cred['filename']} for revoked session {info['client_cn']}")
                                                    except Exception as e:
                                                        if LOG_MODE in (1, 2):
                                                            logger.info(f"[{GCS_cn}] Failed to remove credential file {cred['filename']}: {e}")
                                                    break
                                            session_contexts.pop(addr)
                                            client_timestamps.pop(info["client_cn"], None)
                                            popup_counts.pop(info["client_cn"], None)
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{GCS_cn}] Terminated thirdparty session {info['client_cn']} at {addr} due to CRL")
                                                    
                                    # Forward CRL to all UXVs and terminate revoked UXV sessions
                                    for addr, info in list(uxv_sessions.items()):
                                        
                                        timestamp = int(time.time() * 1e6)
                                        timestamp_bytes = struct.pack('<Q', timestamp)
                                        session_key = info["session_key_sending"]
                                        hmac_value = compute_hmac(b'\x04', payload, timestamp_bytes, session_key)
                                        message = b'\x04' + payload + timestamp_bytes + hmac_value
                                        uxv_socket.sendto(message, addr)  # UDP
                                        message = f"{GCS_cn} forward CredRL to {info['uxv_cn']}"
                                        serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                                        message_lenght_sent.setdefault(info['uxv_cn'], []).append((4,len(message)))
                                        
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{GCS_cn}] Forwarded CRL to UXV {info['uxv_cn']} at {addr} timestamp:{timestamp}")

                                        if info["hash"] in crl_hashes:
                                            for cred in credentials:
                                                if cred["hash"] == info["hash"]:
                                                    credentials.remove(cred)
                                                    try:
                                                        os.remove(os.path.join(CREDENTIAL_DIR, cred["filename"]))
                                                        if LOG_MODE in (1, 2):
                                                            logger.info(f"[{GCS_cn}] Removed credential file {cred['filename']} for revoked UXV {info['uxv_cn']}")
                                                    except Exception as e:
                                                        if LOG_MODE in (1, 2):
                                                            logger.info(f"[{GCS_cn}] Failed to remove credential file {cred['filename']}: {e}")
                                                    break
                                            uxv_sessions.pop(addr)
                                            LAST_GPS_MESSAGE.pop(info["uxv_cn"], None)
                                            UXV_HEARTBEAT.pop(session["uxv_cn"], None)
                                            client_timestamps.pop(info["uxv_cn"], None)
                                            popup_counts.pop(info["uxv_cn"], None)
                                            message = f"{GCS_cn} Terminated connectio with {info['uxv_cn']} due to CRL"
                                            serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{GCS_cn}] Terminated UXV session {info['uxv_cn']} at {addr} due to CRL at {timestamp}")
                                        with sysid_to_cn_lock:
                                            sysid_to_remove = [sid for sid, cn in sysid_to_cn.items() if cn == info["uxv_cn"]]
                                            for sid in sysid_to_remove:
                                                sysid_to_cn.pop(sid)
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{GCS_cn}] Removed SYSIDs {sysid_to_remove} for revoked UXV {info['uxv_cn']}")
                                        
                    except Exception as e:
                        popup_queue.put(("Error", f"Failed to process CRL: {e}", client_cn))
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Failed to process 0x04: {e}")
            
            elif type_byte == b'\x07':
                if verify_policy(type_byte, capacity_string, session_info, role="receiver"):
                    try:
                        received_cn = payload.decode('utf-8')
                        if received_cn == client_cn:
                            with clients_lock:
                                session_contexts.pop(addr, None)
                                client_timestamps.pop(client_cn, None)
                                popup_counts.pop(client_cn, None)
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{GCS_cn}] Terminated session for {client_cn} at {addr} due to 0x07 message")
                            popup_queue.put(("Session Terminated", f"Session for {client_cn} terminated via 0x07", client_cn))
                        else:
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{GCS_cn}] Invalid CN in 0x07 from {client_cn}: expected {client_cn}, received {received_cn}")
                    except UnicodeDecodeError:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Invalid CN encoding in 0x07 from {addr}")
                    except Exception as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Failed to process 0x07 from {client_cn}: {e}")

                        
            
            elif type_byte == b'\x11':
                client_cn = None
    
                if verify_policy(type_byte, capacity_string, session_info, role="receiver"):
                    try:
                        client_cn = payload.decode('utf-8')
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Handling 0x11 message from {client_cn} at {addr}")
                        message = f"{GCS_cn} Received 0x11 message from {client_cn}"
                        serv_temp_sock.sendto(message.encode('utf-8'), server_address)


                        

                        shared_secret = session_info.get("shared_secret")
                        if not shared_secret:
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{GCS_cn}] No shared secret stored for {addr}, cannot renew")
                            return
                        
                        if session_info["session_state"] == "pending_renewal":
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{GCS_cn}] Already renewed {client_cn}, skipping")
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{GCS_cn}] pending_session_key_sending: {session_info['pending_session_key_sending'].hex()}")
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{GCS_cn}] pending_session_key_receiving: {session_info['pending_session_key_receiving'].hex()}")
                            new_session_key_sending= session_info["pending_session_key_sending"]
                            new_session_key_receiving = session_info["pending_session_key_receiving"]
                        
                        else: 
                                
                                salt = os.urandom(4)  # Generate a random salt
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
                            
                        # Send 0x11 response using current session key
                        
                        response_timestamp = struct.pack('<Q', int(time.time() * 1e6))
                        hmac_value = compute_hmac(b'\x11', salt, response_timestamp, session_info.get("session_key_sending"))
                        response = b'\x11' + salt + response_timestamp + hmac_value
                        udp_socket.sendto(response, addr)
                        message_lenght_sent.setdefault(client_cn, []).append((11,len(response)))
                        message = f"{GCS_cn} sent 0x11 response to {client_cn}"
                        serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Sent 0x11 response to {client_cn} at {addr}, new pending keys:")
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] pending_session_key_sending: {session_info['pending_session_key_sending'].hex()}")
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] pending_session_key_receiving: {session_info['pending_session_key_receiving'].hex()}")

                    except Exception as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Error handling 0x11: {e}")
                        popup_queue.put(("Key Renewal Error", f"Error processing 0x11 from {client_cn}: {e}", client_cn))
                else:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{GCS_cn}] Policy verification failed for 0x11 from {client_cn}")
                continue
            
            elif type_byte == b'\x12':
                if verify_policy(type_byte, capacity_string, session_info, role="receiver"):
                    try:
                        received_cn = payload.decode('utf-8')
                        session_info["last_heartbeat"] = time.time()
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Received 0x12 heartbeat from CMD: {received_cn}")
                        # Optionally: update last heartbeat timestamp, or store it in a dict for monitoring
                    except Exception as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Error decoding 0x12 heartbeat payload: {e}")
            
            
            elif type_byte == b'\x13':
                message = f"{GCS_cn} Received 0x13 message from {client_cn}"
                serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                if LOG_MODE in (1, 2):
                    logger.info(f"[{GCS_cn}] Received 0x13 from {client_cn}")
                if verify_policy(type_byte, capacity_string, session_info, role="receiver"):
                    try:
                        offset = 0
                        cred_len = int.from_bytes(payload[offset:offset+4], 'big')
                        offset += 4
                        credent = payload[offset:offset+cred_len]
                        offset += cred_len
                        
                        cred_data = verify_credential(credent, PUcmd, PUgcs, session_info["public_key"])
                        if cred_data is None:
                            raise ValueError("Invalid credential or crl expired")

                        
                        if cred_data["type"] == 0x02:
                            
                            for addr, info in session_contexts.items():
                                if cred_data["timestamp"] > info["cred_timestamp"]:
                                    
                                    
                                    for old_file in os.listdir(CREDENTIAL_DIR):
                                        
                                        if old_file.startswith(f"{client_cn}_to_{GCS_cn}_") and old_file.endswith(".cred"):
                                            try:
                                                os.remove(os.path.join(CREDENTIAL_DIR, old_file))
                                            except Exception as e:
                                                if LOG_MODE in (1, 2):
                                                    logger.info(f"[{GCS_cn}] Failed to remove old credentials {old_file}: {e}")
                                    
                                    for cred in credentials:
                                        if cred["filename"].startswith(f"{client_cn}_to_{GCS_cn}_") and cred["filename"].endswith(".cred"):
                                            try:
                                                credentials.remove(cred)
                                            except Exception as e:
                                                if LOG_MODE in (1, 2):
                                                    logger.info(f"[{GCS_cn}] Failed to remove old credential from memory {cred['filename']}: {e}")
                                                             
                                    filename = f"{client_cn}_to_{GCS_cn}_{cred_data['timestamp']}.cred"
                                    filepath = os.path.join(CREDENTIAL_DIR, filename)
                                    os.makedirs(os.path.dirname(filepath), exist_ok=True)
                                
                                    with open(filepath, 'wb') as f:
                                        f.write(credent)
                                        
                                        
                                    info["hash"] = cred_data["hash"]
                                    info["cred_timestamp"] = cred_data["timestamp"]
                                    info["capacity_string"] = cred_data["capacity_string"]
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{GCS_cn}] Updated session_contexts for {info['client_cn']} with new 0x02 cred: {cred_data['hash']}")
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
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{GCS_cn}] Replaced 0x02 credential with newer timestamp: {cred_data['timestamp']}")
                                    break 
                        
                        
                        elif cred_data["type"] == 0x03:
                            with clients_lock:
                                for addr, info in uxv_sessions.items():
                                    if info["uxv_pu"] == cred_data["pu2"] and cred_data["timestamp"] > info["cred_timestamp"]:
                                        
                                        # Send 0x15 to UXV
                                        timestamp = int(time.time() * 1e6)
                                        timestamp_bytes = struct.pack('<Q', timestamp)
                                        cred_len_bytes = len(credent).to_bytes(4, 'big')
                                        payload_15 = cred_len_bytes + credent
                                        hmac_value = compute_hmac(b'\x15', payload_15, timestamp_bytes, info["session_key_sending"])
                                        message = b'\x15' + payload_15 + timestamp_bytes + hmac_value
                                        uxv_socket.sendto(message, addr)
                                        message = f"{GCS_cn} Sent 0x15 message to {info['uxv_cn']}"
                                        serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                                        message_lenght_sent.setdefault(info["uxv_cn"], []).append((15,len(message)))
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{GCS_cn}] Sent 0x15 to UXV {info["uxv_cn"]} at {addr} with cred: {cred_data["hash"]} at timestamp {timestamp}")
                                        
                                        for old_file in os.listdir(CREDENTIAL_DIR):
                                            if old_file.startswith(f"{GCS_cn}_to_{info['uxv_cn']}_") and old_file.endswith(".cred"):
                                                try:
                                                    os.remove(os.path.join(CREDENTIAL_DIR, old_file))
                                                except Exception as e:
                                                    if LOG_MODE in (1, 2):
                                                        logger.info(f"[{GCS_cn}] Failed to remove old credentials {old_file}: {e}")
                                        
                                        for cred in credentials:
                                            if cred["filename"].startswith(f"{GCS_cn}_to_{info['uxv_cn']}_") and cred["filename"].endswith(".cred"):
                                                try:
                                                    credentials.remove(cred)
                                                except Exception as e:
                                                    if LOG_MODE in (1, 2):
                                                        logger.info(f"[{GCS_cn}] Failed to remove old credential from memory {cred['filename']}: {e}")
                                                  
                                        filename = f"{GCS_cn}_to_{info["uxv_cn"]}_{cred_data['timestamp']}.cred"
                                        filepath = os.path.join(CREDENTIAL_DIR, filename)
                                        os.makedirs(os.path.dirname(filepath), exist_ok=True)
                                        with open(filepath, 'wb') as f:
                                            f.write(credent)
                                        
                                        info["hash"] = cred_data["hash"]
                                        info["cred_timestamp"] = cred_data["timestamp"]
                                        info["capacity_string"] = cred_data["capacity_string"]
                                        info["cred_03"] = credent
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{GCS_cn}] Updated uxv_sessions for {info["uxv_cn"]} with new 0x03 cred: {cred_data["hash"]} at timestamp {time.time() * 1e6}")
                                        
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
                                        
                                        message = f"{GCS_cn} Ended processing 0x13 and replaced the credential {client_cn}"
                                        serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                                        break
                                        
                    except Exception as e:
                        popup_queue.put(("Error", f"Failed to process 0x13: {e}", client_cn))
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Failed to process 0x13: {e}")

            
            elif type_byte == b'\x16':
                if verify_policy(type_byte, capacity_string, session_info, role="receiver"):
                    global current_cert_crl
                    try:
                        crl_data = payload
                        new_crl = load_der_x509_crl(crl_data, default_backend())
                        ca_pubkey.verify(new_crl.signature, new_crl.tbs_certlist_bytes, ec.ECDSA(new_crl.signature_hash_algorithm))
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Received valid certificate CRL from {client_cn} at {addr}")
                        crl_timestamp = int(new_crl.last_update_utc.timestamp() * 1e6)
                        revoked_serials = {entry.serial_number for entry in new_crl}

                        
                        if current_cert_crl is None or crl_timestamp > current_cert_crl["timestamp"]:
                            # Remover CRL anterior
                            for f in os.listdir(CRL_CERT_DIR):
                                if f.endswith(".crl.der"):
                                    try:
                                        os.remove(os.path.join(CRL_CERT_DIR, f))
                                    except Exception as e:
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{GCS_cn}] Failed to remove old certificate CRL: {e}")
                            # Guardar nova CRL
                            crl_filename = f"certcrl_{crl_timestamp}.crl.der"
                            crl_path = os.path.join(CRL_CERT_DIR, crl_filename)
                            with open(crl_path, "wb") as f:
                                f.write(crl_data)

                            with crl_cert_lock:
                                current_cert_crl = {
                                    "timestamp": crl_timestamp,
                                    "revoked_serials": revoked_serials
                                }
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{GCS_cn}] Updated certificate CRL: Timestamp={crl_timestamp}, Revoked Serials={revoked_serials}")

                            
                            
                            # Encerrar sessões revogadas
                            with clients_lock:
                                for addr, info in list(session_contexts.items()):
                                    if info.get("peer_serial") in revoked_serials:
                                        session_contexts.pop(addr)
                                        client_timestamps.pop(info["client_cn"], None)
                                        popup_counts.pop(info["client_cn"], None)
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{GCS_cn}] Terminated thirdparty session {info['client_cn']} at {addr} due to CERT CRL")

                                for addr, info in list(uxv_sessions.items()):
                                    # Reenviar 0x16 para UXV
                                    timestamp_now = int(time.time() * 1e6)
                                    timestamp_bytes = struct.pack('<Q', timestamp_now)
                                    session_key = info["session_key_sending"]
                                    hmac_value = compute_hmac(b'\x16', payload, timestamp_bytes, session_key)
                                    message = b'\x16' + payload + timestamp_bytes + hmac_value
                                    uxv_socket.sendto(message, addr)
                                    message_lenght_sent.setdefault(info['uxv_cn'], []).append((16,len(message)))
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{GCS_cn}] Forwarded certificate CRL (0x16) to UXV {info['uxv_cn']} at {addr} Timestamp: {timestamp_now}")
                                    
                                    if info.get("peer_serial") in revoked_serials:
                                        uxv_sessions.pop(addr)
                                        LAST_GPS_MESSAGE.pop(info["uxv_cn"], None)
                                        UXV_HEARTBEAT.pop(session["uxv_cn"], None)
                                        client_timestamps.pop(info["uxv_cn"], None)
                                        popup_counts.pop(info["uxv_cn"], None)
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{GCS_cn}] Terminated UXV session {info['uxv_cn']} at {addr} due to CERT CRL")
                                    with sysid_to_cn_lock:
                                        sysid_to_remove = [sid for sid, cn in sysid_to_cn.items() if cn == info["uxv_cn"]]
                                        for sid in sysid_to_remove:
                                            sysid_to_cn.pop(sid)
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{GCS_cn}] Removed SYSIDs {sysid_to_remove} for revoked UXV {info['uxv_cn']}")
                            logger.info(f"[{GCS_cn}] Timestamp for final 0x16 processing: {int(time.time() * 1e6)}")

                    except Exception as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Error handling certificate CRL: {e}")

            elif type_byte == b'\x17':
                if verify_policy(type_byte, capacity_string, session_info, role="receiver"):
                    global gcs_cert, gcs_serial
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{GCS_cn}] Handling 0x17 message from {client_cn} at {addr}")
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
                            logger.info(f"[{GCS_cn}] 0x17 cert rejected: CA signature verification failed: {e}")
                        continue

                    # 2) Enforce validity window
                    now = datetime.now(timezone.utc)
                    # cryptography>=41 provides *_utc properties; fall back if needed
                    not_before = getattr(cert_obj, "not_valid_before_utc", cert_obj.not_valid_before.replace(tzinfo=timezone.utc))
                    not_after  = getattr(cert_obj, "not_valid_after_utc",  cert_obj.not_valid_after.replace(tzinfo=timezone.utc))
                    if not (not_before <= now <= not_after):
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] 0x17 cert rejected: outside validity window "
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
                                logger.info(f"[{GCS_cn}] Certificate rejected: peer certificate serial {cert_serial} of {client_cn} is revoked.")
                            continue
                    
                    if client_cn == GCS_cn and client_pu == PUgcs:
                        
                        if cert_obj.not_valid_before > gcs_cert.not_valid_before:
                            try:
                                crt_path  = os.path.join(CERT_DIR, f"{client_cn}.crt")
                                if os.path.exists(crt_path):
                                    ts = int(time.time())
                                    backup = os.path.join(CERT_DIR, f"{client_cn}_{ts}.crt.bak")
                                    try:
                                        os.replace(crt_path, backup)
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{GCS_cn}] [BACKUP] {client_cn}: {backup}")
                                    except Exception as e:
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{GCS_cn}] [WARN] Could not backup {crt_path}: {e}")
                                
                                gcs_cert = cert_obj
                                
                                filename = f"{client_cn}.crt"
                                filepath = os.path.join(CERT_DIR, filename)
                                os.makedirs(os.path.dirname(filepath), exist_ok=True)
                                with open(filepath, 'wb') as f:
                                    f.write(payload)

                                gcs_serial = cert_serial
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{GCS_cn}] Updated own certificate with the new one received via 0x17.")
                                _purge_old_backups(client_cn)
                            except Exception as e:
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{GCS_cn}] Failed to update certificate: {e}")
                        else:
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{GCS_cn}] Received certificate is not newer than the current one; no update performed.")
                            
                        continue
                    
                    else:
                        for addr, session in uxv_sessions.items():
                            if session["uxv_cn"] == client_cn:
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{GCS_cn}] Forwarding message to UXV {client_cn} at {addr}")
                                if verify_policy(type_byte, session["capacity_string"], session, role="sender"):
                                    timestamp_bytes = struct.pack('<Q', int(time.time() * 1e6))
                                    h = compute_hmac(b'\x17', payload, timestamp_bytes, session["session_key_sending"])
                                    uxv_socket.sendto(b'\x17' + payload + timestamp_bytes + h, addr)
                                    message_lenght_sent.setdefault(client_cn, []).append((17,len(b'\x17' + payload + timestamp_bytes + h)))
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{GCS_cn}] 0x17 to UXV {client_cn} at {addr}")
                                    continue 

            message_processing_time.append(time.time()*1e6 - message_processing_start)                

        except BlockingIOError:
            pass
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] Thirdparty UDP error: {e}")


def send_periodic_gps():
    """Send periodic GPS_RAW_INT messages to Mission Planner."""
    while running:
        try:
            with last_gps_message:
                if LAST_GPS_MESSAGE:
                    for client_cn, gps_payload in LAST_GPS_MESSAGE.items():
                        for addr, session in session_contexts.items():
                            session_key = session["session_key_sending"]
                            capacity_string = session["capacity_string"]
                            if verify_policy(b'\x01', capacity_string, session, role="sender", mav_type="GLOBAL_POSITION_INT"):
                                uxv_cn_bytes = client_cn.encode("utf-8")
                                len_cn_byte = bytes([len(uxv_cn_bytes)])
                                telemetry_payload = len_cn_byte + uxv_cn_bytes + gps_payload
                                timestamp = int(time.time() * 1e6)
                                timestamp_bytes = struct.pack('<Q', timestamp)
                                hmac_value = compute_hmac(b'\x01', telemetry_payload, timestamp_bytes, session_key)
                                message = b'\x01' + telemetry_payload + timestamp_bytes + hmac_value
                                udp_socket.sendto(message, addr)
                                message_lenght_sent.setdefault(session['client_cn'], []).append((1,len(message)))
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{GCS_cn}] Sent periodic GPS to {session['client_cn']}: Timestamp={timestamp}")
            time.sleep(10)  # Adjust the interval as needed
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] Error sending periodic GPS: {e}")   

def send_periodic_uxvs_heartbeats():
    """Send periodic GPS_RAW_INT messages to Mission Planner."""
    while running:
        try:
            with uxv_heartbeat:
                if UXV_HEARTBEAT:
                    for client_cn, gps_payload in UXV_HEARTBEAT.items():
                        for addr, session in session_contexts.items():
                            session_key = session["session_key_sending"]
                            capacity_string = session["capacity_string"]
                            if verify_policy(b'\x01', capacity_string, session, role="sender", mav_type="HEARTBEAT"):
                                uxv_cn_bytes = client_cn.encode("utf-8")
                                len_cn_byte = bytes([len(uxv_cn_bytes)])
                                telemetry_payload = len_cn_byte + uxv_cn_bytes + gps_payload
                                timestamp = int(time.time() * 1e6)
                                timestamp_bytes = struct.pack('<Q', timestamp)
                                hmac_value = compute_hmac(b'\x01', telemetry_payload, timestamp_bytes, session_key)
                                message = b'\x01' + telemetry_payload + timestamp_bytes + hmac_value
                                udp_socket.sendto(message, addr)
                                message_lenght_sent.setdefault(session['client_cn'], []).append((1,len(message)))
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{GCS_cn}] Sent periodic HEARTBEAT to {session['client_cn']}: Timestamp={timestamp}")
            time.sleep(10)  # Adjust the interval as needed
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] Error sending periodic HEARTBEAT: {e}")     

def check_node_timeouts():
    NETWORK_MAP_INTERVAL = 30  # segundos
    while running:
        now = time.time()
        with clients_lock:
            for addr, session in list(uxv_sessions.items()):
                last_time = session["last_heartbeat"]
                if LOG_MODE in (1, 2):
                    logger.info(f"[{GCS_cn}] Checking UXV session {session['uxv_cn']} last map time: {last_time}, now: {now}")
                if now - last_time > NETWORK_MAP_INTERVAL:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{GCS_cn}] UXV {session['uxv_cn']} at {addr} timed out — closing session and reconnecting.")
                    del uxv_sessions[addr]
                    LAST_GPS_MESSAGE.pop(session["uxv_cn"], None)
                    UXV_HEARTBEAT.pop(session["uxv_cn"], None)
                    pending_dh.pop(addr, None)
                    connect_to_uxv(uxv_cn=session["uxv_cn"],uxv_ip=session["uxv_ip"],uxv_mtls_port=session["mtls_port"],uxv_udp_port=addr[1],cred_03=session["cred_03"],cred_timestamp=session["cred_timestamp"],cred_lifetime=session["cred_lifetime"],capacity_string=session["capacity_string"])      
            
            for addr, session in list(session_contexts.items()):
                if now - session["last_heartbeat"] > NETWORK_MAP_INTERVAL:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{GCS_cn}] Thirdparty {session['client_cn']} at {addr} timed out — closing session.")
                    del session_contexts[addr]
                    pending_dh.pop(addr, None)          
        time.sleep(10)


def handle_uxv():
    """Handle UDP messages from UXVs."""
    global message_processing_time
    
    while running:
        try:
            message_processing_start = time.time()*1e6
            timestamp_start = int(time.time() * 1e6)
            data, addr = uxv_socket.recvfrom(65536)
            type_byte = data[0:1]
            msg_type = type_byte.hex()
            session_info = uxv_sessions.get(addr)
            if not session_info:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{GCS_cn}] No UXV session for {addr}")
                continue
            client_cn = session_info["uxv_cn"]
            session_key = session_info["session_key_receiving"]
            offset = session_info["offset"] 
            
            message_lenght_received.setdefault(client_cn, []).append((msg_type,len(data)))
            
            result = verify_hmac(data, session_info, client_cn, msg_type)
            if not result:
                continue
            type_byte, payload, gap = result
            timestamp = struct.unpack('<Q', data[-24:-16])[0]
            

            gap_values_per_connection.setdefault(client_cn, []).append((type_byte, gap))
            
            if type_byte == b'\x01':
                #logger.info(f"[{GCS_cn}] Received {type_byte.hex()} from {client_cn} session at {addr}")
                parsed_msgs = mav.mav.parse_buffer(payload)
                if parsed_msgs and parsed_msgs[0]:
                    msg = parsed_msgs[0]
                    msg_type = msg.get_type()
                    sysid = msg.get_srcSystem()
                    if verify_policy(type_byte, session_info["capacity_string"], session_info, role="receiver", mav_type=msg_type):
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Received {type_byte.hex()} From UXV {client_cn}: Type={msg_type}, SysID={sysid}, Timestamp={timestamp}")
                        
                        if msg_type == "HEARTBEAT":
                            with sysid_to_cn_lock:
                                sysid_to_cn[sysid] = client_cn
                                session_info["last_heartbeat"] = time.time()
                            global UXV_HEARTBEAT
                            with uxv_heartbeat:
                                UXV_HEARTBEAT[(client_cn)] = payload
                            mp_socket.sendto(payload, (MISSION_PLANNER_IP, MISSION_PLANNER_PORT))
                            continue
                            #logger.info(f"[{GCS_cn}] Updated SYSID {sysid} for {client_cn}")
                        
                        elif msg_type == "GLOBAL_POSITION_INT":
                            global LAST_GPS_MESSAGE
                            with last_gps_message:
                                LAST_GPS_MESSAGE[(client_cn)] = payload
                            mp_socket.sendto(payload, (MISSION_PLANNER_IP, MISSION_PLANNER_PORT))
                            continue
                        
                        mp_socket.sendto(payload, (MISSION_PLANNER_IP, MISSION_PLANNER_PORT))
                        #logger.info(f"[{GCS_cn}] Forwarded to Mission Planner: Type={msg_type}, Timestamp={timestamp}")
                        
                        for cmd_addr, cmd_info in session_contexts.items():
                            if cmd_info:
                                cmd_session_key = cmd_info["session_key_sending"]
                                cmd_capacity_string = cmd_info["capacity_string"]

                                # Check if the message should be forwarded based on capacity level
                                if verify_policy(type_byte, cmd_capacity_string, cmd_info, role="sender", mav_type=msg_type):
                                    uxv_cn_bytes = client_cn.encode("utf-8")
                                    len_cn_byte = bytes([len(uxv_cn_bytes)])
                                    telemetry_payload = len_cn_byte + uxv_cn_bytes + payload
                                    timestamp = int(time.time() * 1e6)
                                    timestamp_bytes = struct.pack('<Q', timestamp)
                                    hmac_value = compute_hmac(b'\x01', telemetry_payload, timestamp_bytes, cmd_session_key)
                                    message = b'\x01' + telemetry_payload + timestamp_bytes + hmac_value
                                    udp_socket.sendto(message, cmd_addr)
                                    message_lenght_sent.setdefault(cmd_info['client_cn'], []).append((1,len(message)))
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{GCS_cn}] Forwarded to {cmd_info['client_cn']}: Type={msg_type}, Timestamp={timestamp}")
                                    current_time = int(time.time() * 1e6) 
                                    #logger.info(f"[{GCS_cn}] start-current handle_uxv_0x01: {timestamp_start-current_time}")
                            
                            else:
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{GCS_cn}] No CMD session found")

            
            elif type_byte == b'\x07':
                if LOG_MODE in (1, 2):
                    logger.info(f"[{GCS_cn}] Received {type_byte.hex()} from {client_cn} session at {addr}")
                if verify_policy(type_byte, session_info["capacity_string"], session_info, role="receiver"):
                    try:
                        received_cn = payload.decode('utf-8')
                        if received_cn == client_cn:
                            with clients_lock:
                                uxv_sessions.pop(addr, None)
                                LAST_GPS_MESSAGE.pop(session_info["uxv_cn"], None)
                                UXV_HEARTBEAT.pop(session["uxv_cn"], None)
                                client_timestamps.pop(client_cn, None)
                                popup_counts.pop(client_cn, None)
                            with sysid_to_cn_lock:
                                sysid_to_remove = [sid for sid, cn in sysid_to_cn.items() if cn == client_cn]
                                for sid in sysid_to_remove:
                                    sysid_to_cn.pop(sid)
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{GCS_cn}] Terminated UXV session for {client_cn} at {addr} due to 0x07 message")
                            popup_queue.put(("Session Terminated", f"UXV session for {client_cn} terminated via 0x07", client_cn))
                        else:
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{GCS_cn}] Invalid CN in 0x07 from UXV {client_cn}: expected {client_cn}, received {received_cn}")
                    except UnicodeDecodeError:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Invalid CN encoding in 0x07 from UXV at {addr}")
                    except Exception as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Failed to process 0x07 from UXV {client_cn}: {e}")
                
            elif type_byte == b'\x11':
                if LOG_MODE in (1, 2):
                    logger.info(f"[{GCS_cn}] Received 0x11 from {client_cn} at {addr}")
                message = f"{GCS_cn} received 0x11 from {client_cn}"
                serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                if verify_policy(type_byte, session_info["capacity_string"], session_info, role="receiver"):
                    session = uxv_sessions.get(addr) 
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{GCS_cn}] Received {type_byte.hex()} from {client_cn} session at {addr}")
                    if not session:
                        return

                    if addr not in pending_dh:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Unexpected 0x11 received from {addr}")
                        return

                    shared_secret = session_info.get("shared_secret") 
                    if not shared_secret:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] No shared secret stored for {addr}, cannot renew")
                        return     
                    salt=payload                
                    new_key_sending = HKDF(
                        algorithm=hashes.SHA256(), 
                        length=SESSION_KEY_LENGTH,
                        salt=salt, 
                        info=b"session_key_renewed_sending",
                    ).derive(shared_secret)
                    
                    new_key_receiving = HKDF(
                        algorithm=hashes.SHA256(), 
                        length=SESSION_KEY_LENGTH,
                        salt=salt, 
                        info=b"session_key_renewed_receiving",
                    ).derive(shared_secret)
                    
                    
                    session["session_key_sending"] = new_key_sending
                    session["session_key_receiving"] = new_key_receiving
                    session["session_created_at"] = time.time()
                    message = f"{GCS_cn} Ended key renewal with {client_cn}"
                    serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{GCS_cn}] Session key renewed with {client_cn} at {addr}")
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{GCS_cn}] New session keys:")
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{GCS_cn}] session_key_sending: {session['session_key_sending'].hex()}")
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{GCS_cn}] session_key_receiving: {session['session_key_receiving'].hex()}")
                    del pending_dh[addr]                
            
            message_processing_time.append(time.time()*1e6 - message_processing_start)
            current_time = int(time.time() * 1e6) 
            #logger.info(f"[{GCS_cn}] start-current handle_uxv_total: {timestamp_start-current_time}")    
        except BlockingIOError:
            pass
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] UXV UDP error: {e}")
        
    
    

def handle_mission_planner():
    """Handle messages from Mission Planner."""
    while running:
        try:
            data, addr = mp_socket.recvfrom(1024)
            if data:
                parsed_msgs = mav.mav.parse_buffer(data)
                msg_type = parsed_msgs[0].get_type() if parsed_msgs else "Unknown"
                sysid = parsed_msgs[0].target_system if parsed_msgs and hasattr(parsed_msgs[0], 'target_system') else None
                timestamp = int(time.time() * 1e6)
                timestamp_bytes = struct.pack('<Q', timestamp)
                if LOG_MODE in (1, 2):
                    logger.info(f"[{GCS_cn}] Mission Planner: Type={msg_type}, Timestamp={timestamp}, Target SYSID={sysid}")
                
                with sysid_to_cn_lock:
                    target_cn = sysid_to_cn.get(sysid) if sysid else None
                    
                with clients_lock: 
                    if target_cn:
                        for (sender_ip, sender_port), session_info in uxv_sessions.items():
                            if session_info["uxv_cn"] == target_cn:
                                if verify_policy(b'\x01', session_info["capacity_string"], session_info, role="sender", mav_type=msg_type):
                                    hmac_value = compute_hmac(b'\x01', data, timestamp_bytes, session_info["session_key_sending"])
                                    message = b'\x01' + data + timestamp_bytes + hmac_value
                                    uxv_socket.sendto(message, (sender_ip, sender_port))
                                    message_lenght_sent.setdefault(target_cn, []).append((1,len(message)))
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{GCS_cn}] Sent to UXV {target_cn}: Type={msg_type}, Timestamp={timestamp}")
                                    break
                    else:
                        for (sender_ip, sender_port), session_info in uxv_sessions.items():
                            try:
                                hmac_value = compute_hmac(b'\x01', data, timestamp_bytes, session_info["session_key_sending"])
                                message = b'\x01' + data + timestamp_bytes + hmac_value
                                uxv_socket.sendto(message, (sender_ip, sender_port))
                                message_lenght_sent.setdefault(session_info['uxv_cn'], []).append((1,len(message)))
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{GCS_cn}] Broadcast to UXV {session_info['uxv_cn']}: Type={msg_type}, Timestamp={timestamp}")
                            except Exception as e:
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{GCS_cn}] Broadcast error to {session_info['uxv_cn']}: {e}")
        except BlockingIOError:
            pass
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] Mission Planner error: {e}")
        

def send_network_mapping():
    """Send 0x06 network mapping to CMD and 2CMD terminals."""
    while running:
        #logger.info(f"[{GCS_cn}] send_network_map before the try block")
        try:
            #logger.info(f"[{GCS_cn}] send_network_map outside clients_lock")
            with clients_lock:
                #logger.info(f"[{GCS_cn}] send_network_map inside clients_lock")
                for addr, session_info in session_contexts.items():
                    if verify_policy(b'\x06', session_info["capacity_string"], session_info, role="sender"):
                        type_byte = b'\x06'
                        # Build payload with GCS and UXV CN pairs
                        payload = b''
                        with sysid_to_cn_lock:
                            for sysid, uxv_cn in sysid_to_cn.items():
                                gcs_cn_bytes = GCS_cn.encode('utf-8')
                                uxv_cn_bytes = uxv_cn.encode('utf-8')
                                payload += bytes([len(gcs_cn_bytes)]) + gcs_cn_bytes
                                payload += bytes([len(uxv_cn_bytes)]) + uxv_cn_bytes
                        # If no UXVs, send empty payload to indicate no connections
                        timestamp = int(time.time() * 1e6)
                        timestamp_bytes = struct.pack('<Q', timestamp)
                        hmac_value = compute_hmac(type_byte, payload, timestamp_bytes, session_info["session_key_sending"])
                        data = type_byte + payload + timestamp_bytes + hmac_value
                        udp_socket.sendto(data, addr)
                        message_lenght_sent.setdefault(session_info['client_cn'], []).append((6,len(data)))
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{GCS_cn}] Sent 0x06 network mapping to {session_info['client_cn']} at {addr}: Payload size={len(payload)} at {timestamp}")
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] Error sending network mapping: {e}")
        time.sleep(5)  # Send every 20 seconds

def send_disconnection():
    """Send 0x07 disconnection message to thirdparty."""
    try:
        with clients_lock:
            for cmd_addr, cmd_info in session_contexts.items():
                if verify_policy(b'\x07', cmd_info["capacity_string"], cmd_info, role="sender"):
                    timestamp = int(time.time() * 1e6)
                    timestamp_bytes = struct.pack('<Q', timestamp)
                    payload = GCS_cn.encode('utf-8')
                    hmac_value = compute_hmac(b'\x07', payload, timestamp_bytes, cmd_info["session_key_sending"])
                    message = b'\x07' + payload + timestamp_bytes + hmac_value
                    udp_socket.sendto(message, cmd_addr)
                    message_lenght_sent.setdefault(cmd_info['client_cn'], []).append((7,len(message)))
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{GCS_cn}] Sent 0x07 disconnection to {cmd_info['client_cn']}")
                
            for uxv_addr, uxv_info in uxv_sessions.items():
                if verify_policy(b'\x07', uxv_info["capacity_string"], uxv_info, role="sender"):
                    timestamp = int(time.time() * 1e6)
                    timestamp_bytes = struct.pack('<Q', timestamp)
                    payload = GCS_cn.encode('utf-8')
                    hmac_value = compute_hmac(b'\x07', payload, timestamp_bytes, uxv_info["session_key_sending"])
                    message = b'\x07' + payload + timestamp_bytes + hmac_value
                    uxv_socket.sendto(message, uxv_addr)
                    message_lenght_sent.setdefault(uxv_info['uxv_cn'], []).append((7,len(message)))
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{GCS_cn}] Sent 0x07 disconnection to UXV {uxv_info['uxv_cn']}")
    except Exception as e:
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] Disconnection error: {e}")

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
                logger.info(f"[{GCS_cn}] [CLEAN] Deleted backup: {f}")
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] [CLEAN-ERROR] {f}: {e}")

# Start threads
try:
    root.after(10, process_popups)
    mp_thread = threading.Thread(target=handle_mission_planner, daemon=True)
    mp_thread.start()
    thirdparty_thread = threading.Thread(target=handle_thirdparty_udp, daemon=True)
    thirdparty_thread.start()
    uxv_thread = threading.Thread(target=handle_uxv, daemon=True)
    uxv_thread.start()
    network_thread = threading.Thread(target=send_network_mapping, daemon=True)
    network_thread.start()
    threading.Thread(target=session_key_monitor, daemon=True).start()
    threading.Thread(target=cleanup_pending_dh, daemon=True).start()
    threading.Thread(target=credential_expiry_monitor, daemon=True).start()
    threading.Thread(target=check_node_timeouts, daemon=True).start()
    threading.Thread(target=send_periodic_gps, daemon=True).start()
    threading.Thread(target=send_periodic_uxvs_heartbeats, daemon=True).start()

    
    
    
except Exception as e:
    if LOG_MODE in (1, 2):
        logger.info(f"[{GCS_cn}] Failed to start threads: {e}")

pr.enable()
# Main loop
try:
    uxv_permissions_sending, uxv_permissions_receiving, thirdparty_permissions_sending, thirdparty_permissions_receiving = load_policies()
    while running:
        try:
            client_socket, addr = secure_socket.accept()
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] mTLS connection from {addr}")
            mtls_thread = threading.Thread(target=handle_mtls_client, args=(client_socket, addr), daemon=True)
            mtls_thread.start()
        except socket.timeout:
            continue
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{GCS_cn}] Failed to start mTLS thread: {e}")
            continue
except KeyboardInterrupt:
    if LOG_MODE in (1, 2):
        logger.info(f"[{GCS_cn}] Shutting down...")
    send_disconnection()
    running = False
            # Compute and log average gap values per connection
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

            print(f"[{GCS_cn}] Message statistics for {node_cn} receiving:")
            for msg_type, stats in sorted(type_totals.items(), key=lambda item: item[0]):
                avg_type_length = stats["total_length"] / stats["count"]
                print(f"[{GCS_cn}] Type {msg_type}: Average length {avg_type_length:.2f} bytes over {stats['count']} messages (Total: {stats['total_length']} bytes)")
            overall_avg = total_length / total_count if total_count else 0
            print(f"[{GCS_cn}] Total messages received: {total_count}, Average length: {overall_avg:.2f} bytes (Total: {total_length} bytes)")
        
        
        
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

            print(f"[{GCS_cn}] Message statistics for {node_cn} sending:")
            for msg_type, stats in sorted(type_totals.items(), key=lambda item: item[0]):
                avg_type_length = stats["total_length"] / stats["count"]
                print(f"[{GCS_cn}] Type {msg_type}: Average length {avg_type_length:.2f} bytes over {stats['count']} messages (Total: {stats['total_length']} bytes)")
            overall_avg = total_length / total_count if total_count else 0
            print(f"[{GCS_cn}] Total messages sent: {total_count}, Average length: {overall_avg:.2f} bytes (Total: {total_length} bytes)")
    
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
            print(f"[{GCS_cn}] Average connection establishment time for {node}: {node_avg_time:.2f} μs over {node_connection_count} connection(s)")
            
            # Add the node's totals to the overall counters
            overall_total_time += node_total_time
            overall_total_count += node_connection_count

        # Calculate and print the overall average after the loop
        if overall_total_count > 0:
            overall_avg_time = overall_total_time / overall_total_count
            print(f"[{GCS_cn}] Overall average connection establishment time: {overall_avg_time:.2f} μs over {overall_total_count} total connection(s)")
    
    if offset_per_node:
        
        # Calculate and print the average for each specific node
        for node, times in offset_per_node.items():
            if not times:
                continue
            # Use the corrected variables and a more accurate description in the print statement.
            print(f"[{GCS_cn}] offset {node}: {times} μs")
            
                   
            
    if message_processing_time:
        avg_processing_time = sum(message_processing_time) / len(message_processing_time)
        print(f"[{GCS_cn}] Average message processing time: {avg_processing_time:.2f} μs for {len(message_processing_time)} messages")
    
    print(f"[{GCS_cn}] number of packets dropted due to gap: {number_gap_drop}")
    with gap_values_lock:
        overall_total_gap = 0
        overall_total_count = 0

        for node_cn, records in gap_values_per_connection.items():
            if not records:
                print(f"[{GCS_cn}] No gap values recorded for {node_cn}")
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

            print(f"[{GCS_cn}] Gap statistics for {node_cn}:")
            for msg_type, stats in sorted(type_totals.items(), key=lambda item: item[0]):
                avg_type_gap = stats["total_gap"] / stats["count"]
                print(f"[{GCS_cn}] Type {msg_type}: Average gap {avg_type_gap:.2f} μs over {stats['count']} message(s)")

            node_avg_gap = node_total_gap / node_total_count if node_total_count else 0
            print(f"[{GCS_cn}] Total messages: {node_total_count}, Average gap: {node_avg_gap:.2f} μs")

            overall_total_gap += node_total_gap
            overall_total_count += node_total_count

        if overall_total_count:
            overall_avg_gap = overall_total_gap / overall_total_count
            print(f"[{GCS_cn}] Overall average gap across all nodes: {overall_avg_gap:.2f} μs over {overall_total_count} message(s)")
        else:
            if not gap_values_per_connection:
                print(f"[{GCS_cn}] No gap values recorded for any node")
            else:
                print(f"[{GCS_cn}] No gap values recorded across all nodes")
finally:
    running = False
    try:
        udp_socket.close()
    except OSError:
        pass
    try:
        uxv_socket.close()
    except OSError:
        pass
    try:
        secure_socket.close()
    except OSError:
        pass
    try:
        mp_socket.close()
    except OSError:
        pass
    
    try:
        pr.disable()
        s = io.StringIO()
        ps = pstats.Stats(pr, stream=s).sort_stats('cumulative')
        ps.dump_stats(os.path.join(CERT_DIR, "script_profile.prof"))
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] Profiling data saved to {os.path.join(CERT_DIR, 'script_profile.prof')}")
        if LOG_MODE in (1, 2):
            logger.info(f"[{GCS_cn}] Shut down")
        listener.stop()
    except Exception:
        pass
    try:
        root.destroy()
    except Exception:
        pass

    
    
