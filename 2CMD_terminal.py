import math
import tkinter as tk
from tkinter import simpledialog, messagebox, filedialog
from PIL import Image, ImageTk
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
from collections import defaultdict
import sys
from collections import defaultdict
from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.x509 import load_der_x509_certificate
from cryptography.hazmat.primitives.asymmetric.ec import EllipticCurvePublicKey
import hashlib
from cryptography.x509 import load_der_x509_crl
import datetime
import rasterio
import logging
import logging.handlers
import queue
from logging.handlers import QueueHandler, QueueListener
import glob
import json

from time_sync_utilis import (
    TIME_SYNC_READY_TOKEN,
    TimeSyncError,
    perform_time_sync,
    recv_exact,
)

# Configuration
VALID_TYPES = [b'\x01', b'\x02', b'\x03', b'\x04', b'\x05', b'\x06', b'\x07', b'\x08', b'\x09', b'\x10', b'\x11', b'\x12', b'\x13', b'\x14', b'\x16', b'\x17']   
MAX_SITLS = 10
SESSION_KEY_LENGTH = 32
NETWORK_MAP_INTERVAL = 30
SESSION_KEY_LIFETIME = 3 * 60
SESSION_RENEW_THRESHOLD = 3*30
CRL_LIFETIME_SECONDS = 365 * 24 * 60 * 60
LOG_MODE = 0
def load_config(cmd2_name):
    global CERT_DIR, CREDENTIAL_DIR, CRL_DIR, CMD2_CERT, CMD2_KEY, CA_CERT, MISSION_DIR, CRL_CERT_DIR, POLICY_FILE, PR2cmd, PU2cmd, cmd2_cert, cmd2_cn, PUcmd, current_cert_crl, ca_pubkey, ca_cert
    CERT_DIR = rf"C:\Users\Admin\Desktop\tecnico\tese\tese\cert1\{cmd2_name}"
    MISSION_DIR = f"{CERT_DIR}\\missions"
    CREDENTIAL_DIR = os.path.join(CERT_DIR, "credentials")
    CRL_DIR = os.path.join(CERT_DIR, "crl")
    CMD2_CERT = os.path.join(CERT_DIR, f"{cmd2_name}.crt")  # 2CMD certificate
    CMD2_KEY = os.path.join(CERT_DIR, f"{cmd2_name}.key")   # 2CMD private key
    CA_CERT = os.path.join(CERT_DIR, "ca.crt")
    POLICY_DIR = os.path.join(CERT_DIR, "mission_policy")
    POLICY_FILE = os.path.join(POLICY_DIR, "mission_policy.json")  # Adjust path as needed
    current_cert_crl = None
    CRL_CERT_DIR = os.path.join(CERT_DIR, "CRL_CERTIFICATES")
    os.makedirs(CRL_CERT_DIR, exist_ok=True)
    
    # Load PR2cmd and PU2cmd
    with open(CMD2_KEY, 'rb') as f:
        PR2cmd = serialization.load_pem_private_key(f.read(), None, default_backend())
    with open(CMD2_CERT, 'rb') as f:
        cmd2_cert = x509.load_pem_x509_certificate(f.read(), default_backend())
    PU2cmd = cmd2_cert.public_key()
    cmd2_cn = cmd2_cert.subject.get_attributes_for_oid(x509.NameOID.COMMON_NAME)[0].value

    # Load PUcmd for credential verification
    with open(os.path.join(CERT_DIR, "cmd.crt"), 'rb') as f:
        cmd_cert = x509.load_pem_x509_certificate(f.read(), default_backend())
    PUcmd = cmd_cert.public_key()
    
    try:
        with open(CA_CERT, 'rb') as f:
            ca_cert = x509.load_pem_x509_certificate(f.read(), default_backend())
            ca_pubkey = ca_cert.public_key()
    except Exception as e:
        ca_pubkey = None
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] Failed to load ca_pubkey: {e}") 


serv_temp_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
server_address = ('172.18.6.212', 8080)

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
listener=None
global number_gap_drop
number_gap_drop = 0
session_contexts = {}  # {(sender_ip,port): {"session_key": key, "offset": offset, "client_cn": cn, "public_key": pu, "hash": hash}}
gcs_sessions = {}  # {(ip,port): {"session_key": key, "offset": offset, "gcs_cn": cn, "gcs_pu": gcs_pu, "hash": hash, "mtls_port": mtls_port}}
pending_dh = {}  # addr → {"private_key": ..., "start_time": ..., "initiator": True}
clients_lock = threading.Lock()
sysid_to_gcs = {}  # {sysid: gcs_cn}
sysid_to_uxv_cn = {}  # {sysid: uxv_cn}
sysid_to_gcs_lock = threading.Lock()
client_timestamps = {}  # {client_cn: deque(maxlen=200)}
popup_counts = {}  # {client_cn: [timestamps]}
popup_queue = Queue()
running = True
crl = []  # List of credential hashes
crl_timestamp = 0
crl_lock = threading.Lock()
network_map = defaultdict(list)  # gcs_cn → [uxv1, uxv2, ...]
active_gcs = set()  # gcs_cn
network_lock = threading.Lock()
network_text = None
network_frame = None
cmd_addr = None  # CMDterminal address for sending 0x10 messages
credentials = []
current_crl = None
crl_cert_lock = threading.Lock()
logger = None
log_queue = None
queue_handler = None
file_handler = None
console_handler = None

global gap_values_per_connection
gap_values_per_connection = {}
gap_values_lock = threading.Lock()
# SITL tracking
sitls = {}
colors = ["red", "blue", "green", "yellow", "purple", "orange", "cyan", "magenta", "brown", "pink"]
color_index = 0
gcs_notebooks = {}  # {gcs_cn: ttk.Notebook}

global gcs_permissions_sending, gcs_permissions_receiving, cmd_permissions_sending, cmd_permissions_receiving

# Tkinter root
root = tk.Tk()
root.withdraw()

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

def is_valid_ipv4(ip):
    pattern = r'^(?:(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.){3}(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)$'
    return bool(re.match(pattern, ip))

def verify_credential(cred, pucmd, own_pu, peer_pu=None):
    try:
        current_crl = load_crl()
        if current_crl is None:
            raise ValueError("No CRL loaded")
        sig_len = int.from_bytes(cred[-2:], 'big')  # last 2 bytes = sig_len
        signature = cred[-(2 + sig_len):-2]         # signature is before the 2 bytes
        payload = cred[:-(sig_len + 2)] 
        cred_body_len = len(cred) - sig_len - 2 # the rest is payload
        pucmd.verify(signature, payload, ec.ECDSA(hashes.SHA256()))
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
        lifetime = int.from_bytes(cred[offset + 8 : offset + 16], "big")
        offset += 16

        capacity_string = None
        if type_byte in [0x01, 0x02, 0x03]:
            if offset >= cred_body_len:
                raise ValueError("Missing capability string in credential")
        str_len = cred[offset]
        offset += 1
        if offset + str_len > cred_body_len:
            raise ValueError("Invalid capability string length")
        capacity_string = cred[offset:offset + str_len].decode('utf-8')
        offset += str_len

        if time.time() >= timestamp + lifetime:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] Credential expired: Timestamp={timestamp}, Lifetime={lifetime}, Current={time.time()}")
            raise ValueError("Credential expired")

        cred_hash = hashlib.sha256(cred).hexdigest()
        with crl_lock:
            if cred_hash in current_crl["hashes"]:
                raise ValueError("Credential is revoked")

        if type_byte == 0x01:
            if peer_pu and pu1_der != peer_pu.public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo):
                raise ValueError("Peer public key mismatch (PU1)")
            if own_pu and pu2_der != own_pu.public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo):
                raise ValueError("Own public key mismatch (PU2)")
        elif type_byte == 0x02:
            if own_pu and pu1_der != own_pu.public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo):
                raise ValueError("Own public key mismatch (PU1)")
        # For 0x03, only verify signature and lifetime (no public key checks)

        return {
            "type": type_byte,
            "pu1": pu1,
            "pu2": pu2,
            "timestamp": timestamp,
            "lifetime": lifetime,
            "capacity_string": capacity_string,
            "raw": cred,
            "hash": cred_hash
        }
    except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] Credential verification failed: {e}")
            
def send_heartbeat():
    """Send periodic 0x12 heartbeat to all connected GCSs and 2CMDs."""
    while running:
        with clients_lock:
  
            for addr, session in gcs_sessions.items():
                if verify_policy(b'\x12', session["capacity_string"], session, "sender"):
                    type_byte = b'\x12'
                    payload = cmd2_cn.encode('utf-8')
                    timestamp = int(time.time() * 1e6)
                    timestamp_bytes = struct.pack('<Q', timestamp)
                    hmac_value = compute_hmac(type_byte, payload, timestamp_bytes, session["session_key_sending"])
                    message = type_byte + payload + timestamp_bytes + hmac_value
                    gcs_socket.sendto(message, addr)
                    message_lenght_sent.setdefault(session.get('gcs_cn', 'unknown'), []).append((0x12, len(message)))
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd2_cn}] Sent 0x12 heartbeat to {session.get('gcs_cn', 'unknown')} at {addr}")
        time.sleep(5)  

def verify_policy(msg_type, capacity_string, session, role, mav_type=None):
    #logger.info(f"[{cmd2_cn}] Verifying policy for message type {msg_type.hex()} with capacity {capacity_string} and role {role}")
    """Verify if a message type is allowed based on the capacity string and connection type."""
    access_levels = ["Access1", "Access2", "Access3"]
    capabilities = capacity_string.split(",") if capacity_string else []
    
    if not any(level in capabilities for level in access_levels):
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] No access for node with capacity {capacity_string} to message type {msg_type.hex()}")
        return False

    # Identify connection type
    is_gcs = "gcs_cn" in session
    is_cmd = "client_cn" in session  # CMD session

    if is_gcs:
        permissions = gcs_permissions_sending if role == "sender" else gcs_permissions_receiving
    elif is_cmd:
        permissions = cmd_permissions_sending if role == "sender" else cmd_permissions_receiving
    else:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] Unknown connection type")
        return False

    for capability in capabilities:
        perm = permissions.get(capability)
        if perm is None:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] Capability {capability} not found in permissions for Node with capacity {capacity_string}")
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
            logger.info(f"[{cmd2_cn}] Message type {msg_type.hex()}, Mavlink: {mav_type} not allowed for node with capacity {capacity_string}")
        return False
    else:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] Message type {msg_type.hex()} not allowed for node with capacity {capacity_string}")
        return False


def load_credentials(cred_dir, pucmd):
    credentials = []
    if not os.path.exists(cred_dir):
        return credentials
    for filename in os.listdir(cred_dir):
        try:
            with open(os.path.join(cred_dir, filename), 'rb') as f:
                cred = f.read()
            cred_data = verify_credential(cred, pucmd, PU2cmd)
           
            credentials.append({
                "type": cred_data["type"],
                "pu1": cred_data["pu1"],
                "pu2": cred_data["pu2"],
                "timestamp": cred_data["timestamp"],
                "lifetime": cred_data["lifetime"],
                "raw": cred,
                "capacity_string": cred_data["capacity_string"],
                "hash": cred_data["hash"]
            })
        except ValueError as e:
            if "expired" in str(e).lower():
                messagebox.showwarning("Expired Credential", f"Credential {filename} is expired and will be ignored.")
            else:
                messagebox.showerror("Invalid Credential", f"Credential {filename} failed verification: {e}")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load credential {filename}: {e}")
    return credentials



def load_crl():
    global current_crl
    if not os.path.exists(CRL_DIR):
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] No CRL dir: {CRL_DIR}")
        return None

    crl_files = [f for f in os.listdir(CRL_DIR) if f.endswith('.crl')]
    if not crl_files:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] No CRL files found in {CRL_DIR}")
        return None

    latest_crl = max(crl_files, key=lambda x: float(x.split('_')[-1].replace('.crl', '')))
    filepath = os.path.join(CRL_DIR, latest_crl)
    try:
        with open(filepath, 'rb') as f:
            crl_data = f.read()
        sig_len = int.from_bytes(crl_data[-2:], 'big')
        signature = crl_data[-(2 + sig_len):-2]
        payload = crl_data[:-(2 + sig_len)]

            # Verifica assinatura EC
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
            logger.info(f"[{cmd2_cn}] Loaded CRL: {latest_crl}, Timestamp={timestamp}")
        return current_crl
    except Exception as e:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] Failed to load CRL {latest_crl}: {e}")
        return None


def load_latest_cert_crl(crl_dir):
    global latest_crl, latest_time, current_cert_crl

    
    # Only consider files ending in .crl or .crl.der
    crl_files = [f for f in os.listdir(crl_dir) if f.endswith(".crl") or f.endswith(".crl.der")]
    if not crl_files:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] No CRL files found in {crl_dir}")
        return None

    for crl_file in crl_files:
        crl_path = os.path.join(crl_dir, crl_file)
        try:
            with open(crl_path, "rb") as f:
                crl_data = f.read()
                cert_crl = load_der_x509_crl(crl_data, default_backend())
                ca_pubkey.verify(cert_crl.signature,cert_crl.tbs_certlist_bytes, ec.ECDSA(cert_crl.signature_hash_algorithm))
                now = datetime.datetime.now(datetime.timezone.utc)
                if LOG_MODE in (1, 2):
                    logger.info(f"NOW: {now}, CRL NEXT UPDATE: {cert_crl.next_update_utc}")
                if cert_crl.next_update_utc < now:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd2_cn}] Skipping expired CRL '{crl_file}': Next update was {cert_crl.next_update_utc}")
                    return None
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd2_cn}] Loaded CRL: {crl_file}, Last Update={cert_crl.last_update_utc}")
                if latest_time is None or cert_crl.last_update_utc > latest_time:
                    latest_time = cert_crl.last_update_utc
                    latest_crl = cert_crl
                    
                if latest_crl:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd2_cn}] Latest CRL: {crl_file}, Last Update={latest_crl.last_update_utc}")
                    
                current_cert_crl = {
                    "timestamp": int(latest_crl.last_update_utc.timestamp() * 1e6),
                    "revoked_serials": {r.serial_number for r in cert_crl} if cert_crl else set(),
                     }    
                
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] Skipping invalid CRL '{crl_file}': {e}")
            return None

    return latest_crl


def load_policies(POLICY_FILE):
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
                        logger.info(f"[{cmd2_cn}] Unknown policy format for {cap}")
            return converted

        gcs_permissions_sending = convert(data.get("gcs_permissions_sending", {}))
        gcs_permissions_receiving = convert(data.get("gcs_permissions_receiving", {}))
        cmd_permissions_sending = convert(data.get("cmd_permissions_sending", {}))
        cmd_permissions_receiving = convert(data.get("cmd_permissions_receiving", {}))
        
        if not gcs_permissions_sending or not gcs_permissions_receiving:
            raise ValueError("Missing or empty policy sections in JSON")
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] Loaded policies from {POLICY_FILE}")
        return gcs_permissions_sending, gcs_permissions_receiving, cmd_permissions_sending, cmd_permissions_receiving
    except FileNotFoundError:
        logger.error(f"[{cmd2_cn}] Policy file not found: {POLICY_FILE}. Using default hardcoded policies.")
        
    except Exception as e:
        logger.error(f"[{cmd2_cn}] Failed to load policies: {e}. Using defaults.")

def initiate_dh_key_renewal(addr, session):
    if LOG_MODE in (1, 2):
        logger.info(f"[{cmd2_cn}] Initiating DH key renewal with {session.get('gcs_cn', 'unknown')} at {addr}")

    timestamp_bytes = struct.pack('<Q', int(time.time() * 1e6))
    hmac_value = compute_hmac(b'\x11', cmd2_cn.encode('utf-8'), timestamp_bytes, session["session_key_sending"])
    msg = b'\x11' + cmd2_cn.encode('utf-8') + timestamp_bytes + hmac_value
    gcs_socket.sendto(msg, addr)
    message_lenght_sent.setdefault(session.get('gcs_cn', 'unknown'), []).append((0x11, len(msg)))
    pending_dh[addr] = {
        "start_time": time.time(),
        "initiator": True,
        "retry_count": pending_dh.get(addr, {}).get("retry_count", 0) + 1  # Increment retry count
    }
    if LOG_MODE in (1, 2):
        logger.info(f"[{cmd2_cn}] Sent 0x11 to {session.get('gcs_cn', 'unknown')} at {addr}")
    
def session_key_monitor():
    while running:
        #logger.info(f"[{cmd2_cn}] Key monitor thread")
        now = time.time()
        with clients_lock:
                for addr, session in list(gcs_sessions.items()):
                    created = session.get("session_created_at", 0)
                    if now - created >= SESSION_KEY_LIFETIME - SESSION_RENEW_THRESHOLD:
                        if addr not in pending_dh:
                            initiate_dh_key_renewal(addr, session)
                for addr, session in list(session_contexts.items()):
                    created = session.get("session_created_at", 0)
                    if now - created >= SESSION_KEY_LIFETIME:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] CMD session key expired for {session.get('client_cn', 'unknown')} at {addr}, deleting session")
                        del session_contexts[addr]
        time.sleep(10)

def credential_expiry_monitor():
    while running:
        now = time.time()
        with clients_lock:
            for addr, session in list(session_contexts.items()):
                expiry_time = session["credential_timestamp"] + session["credential_lifetime"]
                if now >= expiry_time:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd2_cn}] Credential for {session.get('client_cn')} at {addr} expired - deleting session")
                    del session_contexts[addr]
            for addr, session in list(gcs_sessions.items()):
                expiry_time = session["credential_timestamp"] + session["credential_lifetime"]
                if now >= expiry_time:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd2_cn}] Credential for {session.get('gcs_cn')} at {addr} expired - deleting session")
                    popup_queue.put(("Credential Expired", f"Credential for {session.get('gcs_cn', 'unknown')} at {addr} expired, deleting session", session.get("gcs_cn", "unknown")))
                    session = gcs_sessions.pop(addr, None)
                    gcs_cn=session.get("gcs_cn", "unknown")
                    with network_lock:
                        active_gcs.discard(gcs_cn)
                        if gcs_cn in network_map:
                            del network_map[gcs_cn]
                        update_network_view()
                    if gcs_cn in gcs_notebooks:
                        try:
                            notebook = gcs_notebooks[gcs_cn]
                            for widget in notebook_frame.winfo_children():
                                if isinstance(widget, ttk.Label) and widget.winfo_name() == f"label_{gcs_cn}":
                                    widget.destroy()
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{cmd2_cn}] Removed label for GCS {gcs_cn}")
                                    break
                            notebook.pack_forget()
                            notebook.destroy()
                            del gcs_notebooks[gcs_cn]
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{cmd2_cn}] Removed notebook for GCS {gcs_cn}")
                        except tk.TclError as e:
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{cmd2_cn}] Error removing notebook for GCS {gcs_cn}: {e}")

                
                        
        time.sleep(10)

def cleanup_pending_dh():
    max_retries = 3  # Maximum number of retry attempts
    while running:
        #logger.info(f"[{cmd2_cn}] Cleanup pending DH renewals")
        now = time.time()
        with clients_lock:
            for addr in list(pending_dh):
                if now - pending_dh[addr]["start_time"] > 10:
                    retry_count = pending_dh[addr]["retry_count"]
                    if retry_count < max_retries:
                        session = gcs_sessions.get(addr)
                        if session:
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{cmd2_cn}] Retrying DH renewal with {session.get('gcs_cn', 'unknown')} at {addr}, Attempt {retry_count}/{max_retries}")
                            initiate_dh_key_renewal(addr, session)
                        else:
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{cmd2_cn}] No session found for {addr}, removing from pending_dh")
                            del pending_dh[addr]
                    else:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] Exhausted retries ({max_retries}) for DH renewal with {addr}")
                        del pending_dh[addr]
                        session = gcs_sessions.pop(addr, None)
                        if session:
                            popup_queue.put(("Key Renewal Failed", f"Failed to renew session key with {session.get('gcs_cn', 'unknown')} after {max_retries} attempts, deleting the session and retry connection", session.get('gcs_cn', 'unknown')))
                            gcs_cn=session.get("gcs_cn", "unknown")
                            with network_lock:
                                active_gcs.discard(gcs_cn)
                                if gcs_cn in network_map:
                                    del network_map[gcs_cn]
                                update_network_view()
                            if gcs_cn in gcs_notebooks:
                                try:
                                    notebook = gcs_notebooks[gcs_cn]
                                    for widget in notebook_frame.winfo_children():
                                        if isinstance(widget, ttk.Label) and widget.winfo_name() == f"label_{gcs_cn}":
                                            widget.destroy()
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{cmd2_cn}] Removed label for GCS {gcs_cn}")
                                            break
                                    notebook.pack_forget()
                                    notebook.destroy()
                                    del gcs_notebooks[gcs_cn]
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{cmd2_cn}] Removed notebook for GCS {gcs_cn}")
                                except tk.TclError as e:
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{cmd2_cn}] Error removing notebook for GCS {gcs_cn}: {e}")
                            popup_queue.put(("Timeout", f"GCS {gcs_cn} disconnected due to timeout", gcs_cn))
                            credentials = load_credentials(CREDENTIAL_DIR, PUcmd)
                            latest_cred = None
                            latest_ts = 0
                            with crl_lock:
                                for cred in credentials:
                                    if cred["type"] == 0x02 and cred["pu2"].public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo) == \
                                    session["gcs_pu"].public_bytes(Encoding.DER, PublicFormat.SubjectPublicKeyInfo) and cred["timestamp"] > latest_ts and \
                                    cred["hash"] not in crl:
                                        latest_cred = cred
                                        latest_ts = cred["timestamp"]
                                if latest_cred:
                                    threading.Thread(target=establish_gcs_connection, args=(addr[0], session.get("mtls_port"), addr[1], latest_cred["raw"], session["hash"], session["cred_timestamp"], session["cred_lifetime"], gcs_cn, session["capacity_string"]), daemon=True).start()

        time.sleep(5)


def scan_certificates():
    cert_map = {"uxv": [], "gcs": [], "cmd": [], "2cmd": []}
    try:
        ca_cert = x509.load_pem_x509_certificate(open(CA_CERT, 'rb').read(), default_backend())
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] Loaded CA certificate: {CA_CERT}")
    except Exception as e:
        messagebox.showerror("Error", f"Failed to load CA certificate: {e}")
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] Failed to load CA certificate: {e}")
        return cert_map
    
    revoked_serials = set()
    try:
        cert_crl = load_latest_cert_crl(CRL_CERT_DIR)
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] load_latest_cert_crl returned: {cert_crl}")
        if cert_crl is not None:
            revoked_serials = {entry.serial_number for entry in cert_crl}
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] Loaded CRL with {revoked_serials}")
        else:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] No valid CRL found in {CRL_CERT_DIR}")
    except Exception as e:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] Failed to load certificate CRL: {e}")
    
    files_found = False
    for cert_file in os.listdir(CERT_DIR):
        if cert_file.endswith('.crt') and cert_file != 'ca.crt':
            files_found = True
            cert_path = os.path.join(CERT_DIR, cert_file)
            try:
                cert = x509.load_pem_x509_certificate(open(cert_path, 'rb').read(), default_backend())
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd2_cn}] Loaded certificate: {cert_file}")
                ca_cert.public_key().verify(
                    cert.signature,
                    cert.tbs_certificate_bytes,
                    padding.PKCS1v15(),
                    cert.signature_hash_algorithm
                )
                cn = cert.subject.get_attributes_for_oid(x509.NameOID.COMMON_NAME)[0].value
                pu = cert.public_key()
                if not isinstance(pu, rsa.RSAPublicKey) or pu.key_size != 2048:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd2_cn}] Skipped {cert_file}: Not RSA 2048-bit")
                    continue
                if cn.startswith("sitl"):
                    cert_map["uxv"].append((cn, pu))
                elif cn.lower().startswith("gcs"):
                    cert_map["gcs"].append((cn, pu))
                elif cn.lower() == "cmd":
                    cert_map["cmd"].append((cn, pu))
                elif cn.lower().startswith("2cmd"):
                    cert_map["2cmd"].append((cn, pu))
                else:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd2_cn}] Skipped {cert_file}: Unknown CN {cn}")
            except Exception as e:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd2_cn}] Skipped {cert_file}: {e}")
                continue
    
    if not files_found:
        messagebox.showerror("Error", f"No .crt files found in {CERT_DIR}")
    return cert_map

BACKUP_KEEP_LAST = 0

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
                logger.info(f"[{cmd2_cn}] [CLEAN] Deleted backup: {f}")
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] [CLEAN-ERROR] {f}: {e}")

def compute_hmac(type_byte, payload, timestamp_bytes, session_key):
    h = hmac.HMAC(session_key, hashes.SHA256())
    h.update(type_byte + payload + timestamp_bytes)
    return h.finalize()[:16]

def verify_hmac(data, session_info, client_cn, msg_type):
    global number_gap_drop
    """Verify HMAC and timestamp; supports optional key renewal with pending_session_key."""
    if len(data) < 15:
        popup_queue.put(("Message Error", f"Message too short for {client_cn}\nType: {msg_type}\n", client_cn))
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] Verification failed for {client_cn}: Too short")
        return None

    type_byte = data[0:1]
    if type_byte not in VALID_TYPES:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] Invalid type for {client_cn}: {type_byte.hex()}")
        return None

    payload = data[1:-24]
    timestamp_bytes = data[-24:-16]
    received_hmac = data[-16:]
    timestamp = struct.unpack('<Q', timestamp_bytes)[0]
    current_time = int(time.time() * 1e6)
    offset = session_info["offset"]
    role = session_info.get("time_sync_role")
    if role == "server":
        adjusted_timestamp = timestamp + offset
    else:
        adjusted_timestamp = timestamp - offset
    gap = abs(adjusted_timestamp - current_time)

    # Try current session key
    computed_hmac = compute_hmac(type_byte, payload, timestamp_bytes, session_info["session_key_receiving"])
    #logger.info(f"[{cmd2_cn}] HMAC verification for {client_cn}:")
    #logger.info(f"[{cmd2_cn}]   Received HMAC: {received_hmac.hex()}")
    #logger.info(f"[{cmd2_cn}]   Timestamp: {timestamp}, Adjusted: {adjusted_timestamp}, Current: {current_time}, Offset: {offset}, Gap: {gap} μs")
    if computed_hmac == received_hmac:
        #logger.info(f"[{cmd2_cn}]   Computed HMAC with current key: {computed_hmac.hex()}")
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] HMAC verified with current session key, gap: {gap} μs")
    elif ("pending_session_key_sending" in session_info and "session_state" in session_info and session_info["session_state"] == "pending_renewal" and
        session_info["pending_session_key_sending"] is not None):
        computed_hmac_pending = compute_hmac(type_byte, payload, timestamp_bytes, session_info["pending_session_key_receiving"])
        #logger.info(f"[{cmd2_cn}]   Computed HMAC with pending key: {computed_hmac.hex()}")
        if computed_hmac_pending == received_hmac:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] HMAC matched with pending key — promoting new session keys")
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] pending_session_key_sending   {session_info['pending_session_key_sending'].hex()}")
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] pending_session_key_receiving {session_info['pending_session_key_receiving'].hex()}")
            session_info["session_key_sending"] = session_info["pending_session_key_sending"]
            session_info["session_key_receiving"] = session_info["pending_session_key_receiving"]
            session_info["pending_session_key_sending"] = None
            session_info["pending_session_key_receiving"] = None
            session_info["session_state"] = "established"
            session_info["session_created_at"] = time.time()
            session_info["real_renewal_count"] = session_info["pending_renewal_count"]
        else:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] HMAC failed with both current and pending keys")
            return None
    else:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] HMAC failed with current key and no valid pending key")
        return None

    if timestamp in client_timestamps.get(client_cn, deque(maxlen=200)):
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] Timestamp verification failed for {client_cn}: Duplicate")
        popup_queue.put(("Timestamp Error", f"Repeated timestamp for {client_cn}\nType={msg_type}\n", client_cn))
        return None
    if gap > 2000000:
        number_gap_drop += 1
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] Timestamp verification failed for {client_cn}: Outside 400ms window")
        popup_queue.put(("Timestamp Error", f"Timestamp outside window for {client_cn}\nGap: {gap} μs", client_cn))
        return None

    client_timestamps.setdefault(client_cn, deque(maxlen=200)).append(timestamp)
    #logger.info(f"[{cmd2_cn}] Verified for {client_cn}")
    return (type_byte, payload, gap)



def mtls_server(mtls_port):
    context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
    context.load_cert_chain(certfile=CMD2_CERT, keyfile=CMD2_KEY)
    context.load_verify_locations(CA_CERT)
    context.verify_mode = ssl.CERT_REQUIRED
    server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    server_socket.bind(('0.0.0.0', mtls_port))
    server_socket.listen(5)
    secure_socket = context.wrap_socket(server_socket, server_side=True)
    secure_socket.settimeout(1.0)
    if LOG_MODE in (1, 2):
        logger.info(f"[{cmd2_cn}] mTLS server started on port {mtls_port}")

    while running:
        try:
            client_socket, addr = secure_socket.accept()
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] mTLS connection from {addr}")
            threading.Thread(target=handle_mtls_client, args=(client_socket, addr), daemon=True).start()
        except socket.timeout:
            continue
        except Exception as e:
            if running:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd2_cn}] mTLS server error: {e}")
    secure_socket.close()
    server_socket.close()

def handle_mtls_client(client_socket, addr):
    try:
        initial_time = time.time()*1e6
        cert_der = client_socket.getpeercert(binary_form=True)
        cert_obj = x509.load_der_x509_certificate(cert_der, default_backend())
        client_cn = cert_obj.subject.get_attributes_for_oid(x509.NameOID.COMMON_NAME)[0].value
        client_pu = cert_obj.public_key()
        client_serial = cert_obj.serial_number
        
        
        cert_crl = load_latest_cert_crl(CRL_CERT_DIR)
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] Loaded CRL: {cert_crl}")
        if cert_crl is None:
            raise ValueError("No valid CRL found")
            return
        revoked_serials = {r.serial_number for r in cert_crl} if cert_crl else set()
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] loaded latest_crl - Revoked serials: {revoked_serials}")
        
        if client_serial in revoked_serials:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] Connection rejected: peer certificate serial {client_serial} of {client_cn} is revoked.")
            client_socket.close()
            return
        
        if not client_cn.lower() == "cmd":
            raise ValueError(f"Invalid peer CN: {client_cn}")
        if not isinstance(client_pu, EllipticCurvePublicKey):
            raise ValueError("Expected EC public key")
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] mTLS from {addr}, CN: {client_cn}")
        
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
        cred_data = verify_credential(cred, PUcmd, PU2cmd, client_pu)
        if cred_data is None:
            raise ValueError("Credential verification failed")
        if cred_data["type"] != 0x01:
            raise ValueError(f"Expected 0x01 credential, got 0x{cred_data['type']:02x}")
        
        try:
            client_socket.sendall(TIME_SYNC_READY_TOKEN)
            time_sync_logger = logger.info if LOG_MODE in (1, 2) else None
            ts_result = perform_time_sync(
                client_socket,
                role="server",
                logger=time_sync_logger,
                log_prefix=f"[{cmd2_cn}] Time sync with {client_cn}: ",
            )
        except TimeSyncError as e:
            raise ValueError(f"Time synchronisation failed: {e}") from e
        offset = ts_result.offset_us
        
        offset_per_node.setdefault(client_cn, []).append(offset)
        
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] Clock offset for {client_cn} (server - client): {offset} μs")
        filename = f"{client_cn}_to_{cmd2_cn}_{cred_data['timestamp']}.cred"
        filepath = os.path.join(CREDENTIAL_DIR, filename)
        os.makedirs(os.path.dirname(filepath), exist_ok=True)
        with open(filepath, 'wb') as f:
            f.write(cred_data["raw"])
        
        
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
            logger.info(f"[{cmd2_cn}] Saved 0x01 credential: {filename}") 

        
        shared_secret = PR2cmd.exchange(ec.ECDH(), client_pu)
        
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
        
        if not session_key_sending or not session_key_receiving:
            raise Exception("DH key exchange failed")
        
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
                "credential_timestamp": cred_data["timestamp"],
                "credential_lifetime": cred_data["lifetime"],
                "peer_serial": client_serial,
                "real_renewal_count": 0,
                "pending_renewal_count": 0,
                "last_heartbeat": time.time(),
            }
            global cmd_addr
            cmd_addr = (sender_ip, udp_port)
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] Registered CMD {client_cn} on {sender_ip}:{udp_port} in session_contexts")

        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] Failed to receive or register UDP port: {e}")
            return
        
    except Exception as e:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] mTLS error for {client_cn} at {addr}: {e}")
    finally:
        final_time = time.time()*1e6
        message = f"{cmd2_cn} finished connection establishment with {client_cn}"
        serv_temp_sock.sendto(message.encode('utf-8'), server_address)
        connection_establishement_time.setdefault(client_cn,[]).append(final_time - initial_time)
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] final timestamp for {client_cn} connectio {final_time} μs")
            logger.info(f"[{cmd2_cn}] Connection establishment time: {final_time - initial_time} μs")
        client_socket.close()
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] Closed mTLS for {client_cn}")

def establish_gcs_connection(ip, mtls_port, udp_port, cred, cred_hash, credential_timestamp, cred_lifetime, gcs_cn, capacity_string):
    message = f"{cmd2_cn} initializing connection to {gcs_cn}"
    serv_temp_sock.sendto(message.encode('utf-8'), server_address)
    
    max_attempts = 3
    initial_time= time.time()*1e6
    for attempt in range(1, max_attempts + 1):
        client_socket = None
        secure_socket = None
        try:
            context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
            context.load_cert_chain(certfile=CMD2_CERT, keyfile=CMD2_KEY)
            context.load_verify_locations(CA_CERT)
            context.verify_mode = ssl.CERT_REQUIRED
            client_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            secure_socket = context.wrap_socket(client_socket, server_hostname=ip)
            secure_socket.connect((ip, mtls_port))
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] mTLS connected to GCS {gcs_cn} at {ip}:{mtls_port}")
            
            cert_der = secure_socket.getpeercert(binary_form=True)
            cert_obj = x509.load_der_x509_certificate(cert_der, default_backend())
            peer_cn = cert_obj.subject.get_attributes_for_oid(x509.NameOID.COMMON_NAME)[0].value
            peer_public_key = cert_obj.public_key()
            
            peer_serial = cert_obj.serial_number
            
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] {gcs_cn}:{peer_cn}, Serial: {peer_serial}")
            
            cert_crl = load_latest_cert_crl(CRL_CERT_DIR)
            if cert_crl is not None:
                revoked_serials = {r.serial_number for r in cert_crl}
                if peer_serial in revoked_serials:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd2_cn}] Connection rejected: peer certificate serial {peer_serial} of {peer_cn} is revoked.")
                    secure_socket.close()
                    return
            else:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd2_cn}] No valid CRL found, skipping revocation check for {peer_cn}")
                raise ValueError("No valid CRL found")
            
            if peer_cn != gcs_cn:
                raise ValueError(f"Peer CN {peer_cn} does not match expected {gcs_cn}")
            
            if not isinstance(peer_public_key, EllipticCurvePublicKey):
                raise ValueError("Expected EC public key")
            
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
                    log_prefix=f"[{cmd2_cn}] Time sync with {peer_cn}: ",
                )
            except TimeSyncError as e:
                raise ValueError(f"Time synchronisation failed with {peer_cn}: {e}") from e
            offset = ts_result.offset_us
            
            offset_per_node.setdefault(gcs_cn, []).append(offset)
            
            shared_secret = PR2cmd.exchange(ec.ECDH(), peer_public_key)

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
                raise Exception("DH key exchange failed")
            
            addr = (ip, udp_port)
            with clients_lock:
                gcs_sessions[addr] = {
                    "time_sync_role": "client",
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
                    "credential_timestamp": credential_timestamp,
                    "credential_lifetime": cred_lifetime,
                    "peer_serial": peer_serial,
                    "renewal_count": 0,
                }
                client_timestamps[gcs_cn] = deque(maxlen=200)
                popup_counts[gcs_cn] = []
                
            gcs_port = gcs_socket.getsockname()[1]    
            try:
                secure_socket.sendall(gcs_port.to_bytes(2, 'big'))  # Send UDP port
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd2_cn}] Sent UDP port {gcs_port} to GCS {gcs_cn}")
            except Exception as e:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd2_cn}] Failed to send UDP port to GCS {gcs_cn}: {e}")
                return

            
            if gcs_cn not in gcs_notebooks:
                gcs_notebook = ttk.Notebook(notebook_frame)
                gcs_notebook.pack(fill=tk.BOTH, expand=True)
                gcs_label = ttk.Label(notebook_frame, text=f"GCS: {gcs_cn}", name=f"label_{gcs_cn}")
                gcs_label.pack()
                gcs_notebooks[gcs_cn] = gcs_notebook
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd2_cn}] Created notebook for GCS {gcs_cn}")
                return
            
        except Exception as e:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] Attempt {attempt} to connect to GCS {gcs_cn} failed: {e}")
            popup_queue.put(("Error", f"Attempt {attempt} to connect to GCS {gcs_cn} failed: {e}",attempt, gcs_cn))
            if attempt < max_attempts:
                time.sleep(1)  # brief pause before retry
                continue
            # after 3rd failure:
            popup_queue.put(("Connection Error",f"Failed to connect to GCS {gcs_cn} after {max_attempts} attempts:\n{e}", gcs_cn))
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] Giving up on connecting to GCS {gcs_cn} after {max_attempts} attempts.")
            return
        finally:
            final_time = time.time()*1e6
            connection_establishement_time.setdefault(gcs_cn,[]).append(final_time - initial_time)
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] connetion with {gcs_cn} initial timestamp: {initial_time}")
                logger.info(f"[{cmd2_cn}] Connection establishment time to GCS {gcs_cn}: {final_time - initial_time} μs")
            if secure_socket:
                secure_socket.close()
            if client_socket:
                client_socket.close()
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] Closed mTLS connection to GCS {gcs_cn}")
            
def check_gcs_timeouts():
    current_time = time.time()
    with clients_lock:
        for addr, session_info in list(gcs_sessions.items()):
            if current_time - session_info["last_map_time"] > NETWORK_MAP_INTERVAL:
                gcs_cn = session_info["gcs_cn"]
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd2_cn}] GCS {gcs_cn} at {addr} timed out (no 0x06 message)")
                del gcs_sessions[addr]
                pending_dh.pop(addr, None)
                with network_lock:
                        active_gcs.discard(gcs_cn)
                        if gcs_cn in network_map:
                            del network_map[gcs_cn]
                        update_network_view()
                if gcs_cn in gcs_notebooks:
                    try:
                        notebook = gcs_notebooks[gcs_cn]
                        for widget in notebook_frame.winfo_children():
                            if isinstance(widget, ttk.Label) and widget.winfo_name() == f"label_{gcs_cn}":
                                widget.destroy()
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd2_cn}] Removed label for GCS {gcs_cn}")
                                break
                        notebook.pack_forget()
                        notebook.destroy()
                        del gcs_notebooks[gcs_cn]
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] Removed notebook for GCS {gcs_cn}")
                    except tk.TclError as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] Error removing notebook for GCS {gcs_cn}: {e}")
                popup_queue.put(("Timeout", f"GCS {gcs_cn} disconnected due to timeout", gcs_cn))
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
        
        for addr, session in list(session_contexts.items()):
            last_heartbeat = session["last_heartbeat"]
            if current_time - last_heartbeat > NETWORK_MAP_INTERVAL:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd2_cn}] CMD {session.get('client_cn', 'unknown')} at {addr} timed out (no messages)")
                del session_contexts[addr]
    root.after(1000, check_gcs_timeouts)


#def monitor_threads():
 #   while running:
  #      print(f"[{cmd2_cn}] Active threads: {[t.name for t in threading.enumerate()]} at {time.time()}")
   #     time.sleep(1)

def send_waypoint_wrapper():
    global send_button
    send_button.config(state=tk.DISABLED)
    try:
        file_path = filedialog.askopenfilename(filetypes=[("Waypoint files", "*.waypoints")])
        if not file_path:
            return
        if not file_path.lower().endswith('.waypoints'):
            popup_queue.put(("File Error", "Please select a .waypoints file", "waypoint"))
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] Invalid file extension")
            return
        
        dialog = tk.Toplevel(root)
        dialog.title("Select Node")
        dialog.geometry("300x200")
        
        tk.Label(dialog, text="Select Node(s) to send mission:").pack(pady=5)
        listbox = tk.Listbox(dialog, selectmode=tk.MULTIPLE, height=5)
        with clients_lock:
            for addr, session_info in gcs_sessions.items():
                listbox.insert(tk.END, session_info["gcs_cn"])
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
                session_info = gcs_sessions.get(addr) 
                if not session_info:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd2_cn}] No session for {node_type} at {addr}")
                    continue
                session_key = session_info["session_key_sending"]
                cn = session_info.get("gcs_cn", session_info.get("2cmd_cn"))
                hmac_value = compute_hmac(type_byte, payload, timestamp_bytes, session_key)
                data = type_byte + payload + timestamp_bytes + hmac_value
                gcs_socket.sendto(data, addr)
                message_lenght_sent.setdefault(session_info['gcs_cn'], []).append((0x02, len(data)))
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd2_cn}] Sent waypoint mission to {node_type} {cn}: Type=0x02, Timestamp={timestamp}, Size={len(payload)}, File={os.path.basename(file_path)}")
        popup_queue.put(("Success", "Waypoint mission sent successfully", "waypoint"))
    except Exception as e:
        popup_queue.put(("Send Error", f"Failed to send mission: {e}", "waypoint"))
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] Error sending waypoint: {e}")

def send_disconnection():
    """Send 0x07 disconnection messages to CMD and GCSs."""
    try:
        with clients_lock:
            # Enviar para o CMD
            for cmd_addr, cmd_info in session_contexts.items():
                timestamp = int(time.time() * 1e6)
                timestamp_bytes = struct.pack('<Q', timestamp)
                payload = cmd2_cn.encode('utf-8')
                hmac_value = compute_hmac(b'\x07', payload, timestamp_bytes, cmd_info["session_key_sending"])
                message = b'\x07' + payload + timestamp_bytes + hmac_value
                cmd_socket.sendto(message, cmd_addr)
                message_lenght_sent.setdefault(cmd_info['client_cn'], []).append((0x07, len(message)))
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd2_cn}] Sent 0x07 disconnection to CMD {cmd_info['client_cn']}")

            # Enviar para os GCSs
            for gcs_addr, gcs_info in gcs_sessions.items():
                timestamp = int(time.time() * 1e6)
                timestamp_bytes = struct.pack('<Q', timestamp)
                payload = cmd2_cn.encode('utf-8')
                hmac_value = compute_hmac(b'\x07', payload, timestamp_bytes, gcs_info["session_key_sending"])
                message = b'\x07' + payload + timestamp_bytes + hmac_value
                gcs_socket.sendto(message, gcs_addr)
                message_lenght_sent.setdefault(gcs_info['gcs_cn'], []).append((0x07, len(message)))
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd2_cn}] Sent 0x07 disconnection to GCS {gcs_info['gcs_cn']}")
    except Exception as e:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] Disconnection error: {e}")


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

def process_popups():
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

def update_network_view():
    with network_lock:
        network_text.configure(state='normal')
        network_text.delete('1.0', tk.END)
        network_text.insert(tk.END, f"2CMD: {cmd2_cn}\n")
        for gcs in sorted(active_gcs):
            network_text.insert(tk.END, f"  {gcs}\n")
            for uxv in network_map[gcs]:
                network_text.insert(tk.END, f"    {uxv}\n")
        network_text.configure(state='disabled')

def send_network_map_to_cmd():
    if not cmd_addr:
        root.after(5000, send_network_map_to_cmd)
        return
    with network_lock:
        payload = b''
        for gcs_cn in active_gcs:
            gcs_cn_bytes = gcs_cn.encode('utf-8')
            uxv_list = network_map.get(gcs_cn, [])
            if not uxv_list:
                payload += bytes([len(gcs_cn_bytes)]) + gcs_cn_bytes + bytes([0])  # zero UXVs
            else:
                for uxv_cn in uxv_list:
                    uxv_cn_bytes = uxv_cn.encode('utf-8')
                    payload += bytes([len(gcs_cn_bytes)]) + gcs_cn_bytes + bytes([len(uxv_cn_bytes)]) + uxv_cn_bytes

    with clients_lock:
        session_info = session_contexts.get(cmd_addr)
        if not session_info:
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] No session for CMD at {cmd_addr}")
            root.after(5000, send_network_map_to_cmd)
            return
        session_key = session_info["session_key_sending"]
    type_byte = b'\x10'  # 0x10
    timestamp = int(time.time() * 1e6)
    timestamp_bytes = struct.pack('<Q', timestamp)
    hmac_value = compute_hmac(type_byte, payload, timestamp_bytes, session_key)
    data = type_byte + payload + timestamp_bytes + hmac_value
    cmd_socket.sendto(data, cmd_addr)
    message_lenght_sent.setdefault(cmd2_cn, []).append((0x10, len(data)))
    if LOG_MODE in (1, 2):
        logger.info(f"[{cmd2_cn}] Sent 0x10 network map to CMD at {cmd_addr}: {len(payload)} bytes")
    root.after(5000, send_network_map_to_cmd)

def handle_cmd_udp():
    global message_processing_time
    while running:
        try:
            message_processing_time_start = time.time()*1e6
            data, addr = cmd_socket.recvfrom(65536)
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] Received UDP from CMDterminal at {addr}, Type={data[0:1].hex()} at:{int(time.time() * 1e6)}")
            
            session_info = session_contexts.get(addr)
            if not session_info:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd2_cn}] No session for CMDterminal at {addr}, checking for 0x03")
                continue

            client_cn = session_info["client_cn"]
            session_key = session_info["session_key_receiving"]
            msg_type = data[0] if data else None
            message_lenght_received.setdefault(client_cn, []).append((msg_type, len(data)))
            result = verify_hmac(data, session_info, client_cn, data[0:1].hex())
            if not result:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd2_cn}] Verification failed for {client_cn}, Type={data[0:1].hex()}")
                continue
            type_byte, payload, gap = result
            timestamp = struct.unpack('<Q', data[-24:-16])[0]
            gap_values_per_connection.setdefault(client_cn, []).append((type_byte,gap))
            if type_byte == b'\x04':
                if verify_policy(type_byte, session_info["capacity_string"],session_info, "receiveer"):
                    global current_crl
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
                                                logger.info(f"[{cmd2_cn}] Failed to remove old CRL {old_file}: {e}")
                                crl_filename = f"crl_{crl_timestamp}.crl"
                                with open(os.path.join(CRL_DIR, crl_filename), 'wb') as f:
                                    f.write(payload)
                                current_crl = new_crl
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd2_cn}] Updated CRL: Timestamp={crl_timestamp}, Hashes={len(crl_hashes)}")
                        with clients_lock:
                            # Revoke CMDterminal sessions
                            for cmd_addr, cmd_info in list(session_contexts.items()):
                                if cmd_info["hash"] in crl_hashes:
                                    for cred in credentials:
                                                if cred["hash"] == cmd_info["hash"]:
                                                    credentials.remove(cred)
                                                    try:
                                                        os.remove(os.path.join(CREDENTIAL_DIR, cred["filename"]))
                                                        if LOG_MODE in (1, 2):
                                                            logger.info(f"[{cmd2_cn}] Removed credential file {cred['filename']} for revoked session {cmd_info['client_cn']}")
                                                    except Exception as e:
                                                        if LOG_MODE in (1, 2):
                                                            logger.info(f"[{cmd2_cn}] Failed to remove credential file {cred['filename']}: {e}")
                                                    break
                                    del session_contexts[cmd_addr]
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{cmd2_cn}] Revoked CMD session for {cmd_info['client_cn']} at {cmd_addr}")
                                    popup_queue.put(("Revoked", f"CMD {cmd_info['client_cn']} session revoked", cmd_info["client_cn"]))
                            # Revoke GCS sessions
                            for gcs_addr, gcs_info in list(gcs_sessions.items()):
                                gcs_session_key = gcs_info["session_key_sending"]
                                timestamp_bytes = struct.pack('<Q', int(time.time() * 1e6))
                                hmac_value = compute_hmac(b'\x04', payload, timestamp_bytes, gcs_session_key)
                                forward_data = b'\x04' + payload + timestamp_bytes + hmac_value
                                gcs_socket.sendto(forward_data, gcs_addr)
                                message_lenght_sent.setdefault(gcs_info['gcs_cn'], []).append((0x04, len(forward_data)))
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd2_cn}] Forwarded 0x04 CRL to GCS {gcs_info['gcs_cn']} at {gcs_addr}")
                                
                                if gcs_info["hash"] in crl_hashes:
                                    for cred in credentials:
                                                if cred["hash"] == gcs_info["hash"]:
                                                    credentials.remove(cred)
                                                    try:
                                                        os.remove(os.path.join(CREDENTIAL_DIR, cred["filename"]))
                                                        if LOG_MODE in (1, 2):
                                                            logger.info(f"[{cmd2_cn}] Removed credential file {cred['filename']} for revoked session {gcs_info['gcs_cn']}")
                                                    except Exception as e:
                                                        if LOG_MODE in (1, 2):
                                                            logger.info(f"[{cmd2_cn}] Failed to remove credential file {cred['filename']}: {e}")
                                                    break
                                    
                                    del gcs_sessions[gcs_addr]
                                    
                                    active_gcs.discard(gcs_info["gcs_cn"])
                                    if gcs_info["gcs_cn"] in network_map:
                                        del network_map[gcs_info["gcs_cn"]]
                                    
                                    if gcs_info["gcs_cn"] in gcs_notebooks:
                                        try:
                                            notebook = gcs_notebooks[gcs_info["gcs_cn"]]
                                            for widget in notebook_frame.winfo_children():
                                                if isinstance(widget, ttk.Label) and widget.winfo_name() == f"label_{gcs_info['gcs_cn']}":
                                                    widget.destroy()
                                                    break
                                            notebook.pack_forget()
                                            notebook.destroy()
                                            del gcs_notebooks[gcs_info["gcs_cn"]]
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{cmd2_cn}] Removed notebook for GCS {gcs_info['gcs_cn']}")
                                        except tk.TclError as e:
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{cmd2_cn}] Error removing notebook for GCS {gcs_info['gcs_cn']}: {e}")
                                    popup_queue.put(("Revoked", f"GCS {gcs_info['gcs_cn']} session revoked", gcs_info["gcs_cn"]))
                                root.after(0, update_network_view)
                    except Exception as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] CRL verification failed: {e}")
            
            elif type_byte == b'\x02':
                if verify_policy(type_byte, session_info["capacity_string"], session_info, "receiveer"):
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
                            logger.info(f"[{cmd2_cn}] Received waypoint mission: Type=0x02, Timestamp={timestamp}, Size={len(payload)}, Saved={filepath}")
                    except OSError as e:
                        popup_queue.put(("Error", f"Failed to save mission: {e}", client_cn))
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] Failed to save mission: {e}")
            
            
            elif type_byte == b'\x07':
                if verify_policy(type_byte, session_info["capacity_string"], session_info, "receiveer"):
                    with clients_lock:
                        del session_contexts[addr]
                    popup_queue.put(("Disconnected", f"CMD {client_cn} disconnected", client_cn))
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd2_cn}] CMD {client_cn} at {addr} disconnected via 0x07")
                        
            elif type_byte == b'\x08':
                message = f"{cmd2_cn} received 0x08 from {client_cn}"
                serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                if verify_policy(type_byte, session_info["capacity_string"], session_info, "receiveer"):
                    try:
                        offset = 0
                        len_gcs_cn = payload[offset]
                        offset += 1
                        gcs_cn = payload[offset:offset+len_gcs_cn].decode('utf-8')
                        offset += len_gcs_cn
                        len_uxv_cn = payload[offset]
                        offset += 1
                        uxv_cn = payload[offset:offset+len_uxv_cn].decode('utf-8')
                        offset += len_uxv_cn
                        len_ip = payload[offset]
                        offset += 1
                        ip = payload[offset:offset+len_ip].decode('ascii')
                        offset += len_ip
                        mtls_port = int.from_bytes(payload[offset:offset+4], 'big')
                        offset += 4
                        udp_port = int.from_bytes(payload[offset:offset+4], 'big')
                        offset += 4
                        cred_len = int.from_bytes(payload[offset:offset+4], 'big')
                        offset += 4
                        cred = payload[offset:offset+cred_len]
                        
                        cred_data = verify_credential(cred, PUcmd, PU2cmd)  # Verify 0x03 credential
                        
                        if cred_data is None or cred_data["type"] != 0x03:
                            raise ValueError(f"[{cmd2_cn}] Invalid credential for 0x03: {cred_data}")
                        
                        with clients_lock:
                            gcs_addr = next((addr for addr, info in gcs_sessions.items() if info["gcs_cn"] == gcs_cn), None)
                            if not gcs_addr:
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd2_cn}] No session for GCS {gcs_cn}")
                                continue
                            gcs_session_key = gcs_sessions[gcs_addr]["session_key_sending"]
                        type_byte_05 = b'\x05'
                        uxv_cn_bytes = uxv_cn.encode('utf-8')
                        ip_bytes = ip.encode('ascii')
                        mtls_port_bytes = mtls_port.to_bytes(4, 'big')
                        udp_port_bytes = udp_port.to_bytes(4, 'big')
                        cred_len_bytes = len(cred).to_bytes(4, 'big')
                        payload_05 = bytes([len(uxv_cn_bytes)]) + uxv_cn_bytes + bytes([len(ip_bytes)]) + ip_bytes + mtls_port_bytes + udp_port_bytes + cred_len_bytes + cred
                        timestamp_bytes = struct.pack('<Q', int(time.time() * 1e6))
                        hmac_value = compute_hmac(type_byte_05, payload_05, timestamp_bytes, gcs_session_key)
                        data_05 = type_byte_05 + payload_05 + timestamp_bytes + hmac_value
                        gcs_socket.sendto(data_05, gcs_addr)
                        message_lenght_sent.setdefault(gcs_cn, []).append((0x05, len(data_05)))
                        message = f"{cmd2_cn} send 0x05 to {gcs_cn}"
                        serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] Sent 0x05 to GCS {gcs_cn} at {gcs_addr}: UXV={uxv_cn}, Timestamp={timestamp}")
                    except Exception as e:
                        logger.error(f"[{cmd2_cn}] Failed to process or send 0x05 to GCS {gcs_cn} at {gcs_addr}: {e}")
                        
            elif type_byte == b'\x09':
                message = f"{cmd2_cn} received 0x09 from  {client_cn}"
                serv_temp_sock.sendto(message.encode('utf-8'), server_address)
                
                if verify_policy(type_byte, session_info["capacity_string"],session_info, "receiver"):
                    offset = 0
                    len_uxv_cn = payload[offset]
                    offset += 1
                    gcs_cn = payload[offset:offset+len_uxv_cn].decode('utf-8')
                    offset += len_uxv_cn
                    len_ip = payload[offset]
                    offset += 1
                    ip = payload[offset:offset+len_ip].decode('ascii')
                    offset += len_ip
                    mtls_port = int.from_bytes(payload[offset:offset+4], 'big')
                    offset += 4
                    udp_port = int.from_bytes(payload[offset:offset+4], 'big')
                    offset += 4
                    cred_len = int.from_bytes(payload[offset:offset+4], 'big')
                    offset += 4
                    cred = payload[offset:offset+cred_len]
                    cred_data=verify_credential(cred, PUcmd, PU2cmd)  # Verify 0x02 credential
                    if cred_data is None or cred_data["type"] != 0x02:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] Invalid credential for GCS {gcs_cn} in 0x09")
                        continue
                    filename = f"{cmd2_cn}_to_{gcs_cn}_{cred_data['timestamp']}.cred"
                    filepath = os.path.join(CREDENTIAL_DIR, filename)
                    os.makedirs(os.path.dirname(filepath), exist_ok=True)
                    with open(filepath, 'wb') as f:
                        f.write(cred_data["raw"])
                        
                    
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
                        logger.info(f"[{cmd2_cn}] Saved 0x02 credential: {filename}")
                    
                    threading.Thread(target=establish_gcs_connection, args=(ip, mtls_port, udp_port, cred, cred_data["hash"], cred_data["timestamp"], cred_data["lifetime"], gcs_cn, cred_data["capacity_string"]), daemon=True).start()
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd2_cn}] Processing 0x09: Connecting to GCS {gcs_cn} at {ip}:{mtls_port}/{udp_port}")

            elif type_byte == b'\x11':
                if verify_policy(type_byte, session_info["capacity_string"],session_info, "receiveer"):
                    try:

                        shared_secret = session_info["shared_secret"]
                        if not shared_secret:
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{cmd2_cn}] No shared secret stored for {addr}, cannot renew")
                            continue
                        if session_info["session_state"] == "pending_renewal":
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{cmd2_cn}] Already renewed {client_cn}, skipping")
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{cmd2_cn}] Pending session keys:")
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{cmd2_cn}] pending_session_key_sending: {session_info['pending_session_key_sending'].hex()}")
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{cmd2_cn}] pending_session_key_receiving: {session_info['pending_session_key_receiving'].hex()}")
                            new_session_key= session_info["pending_session_key"]
                        else: 
                            
                            salt=os.urandom(4)
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
                                
                            
                        timestamp = int(time.time() * 1e6)
                        response_timestamp = struct.pack('<Q', timestamp)
                        hmac_value = compute_hmac(b'\x11', salt, response_timestamp, session_info["session_key_sending"])
                        response = b'\x11' + salt + response_timestamp + hmac_value
                        cmd_socket.sendto(response, addr)
                        message_lenght_sent.setdefault(client_cn, []).append((0x11, len(response)))
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] Sent 0x11 response to {client_cn} at {addr} at: {timestamp}, new pending keys: ")
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] pending_session_key_sending: {session_info['pending_session_key_sending'].hex()}")
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] pending_session_key_receiving: {session_info['pending_session_key_receiving'].hex()}")

                    except Exception as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] Error handling 0x11: {e}")
                        popup_queue.put(("Key Renewal Error", f"Error processing 0x11 from {client_cn}: {e}", client_cn))

            elif type_byte == b'\x12':
                if verify_policy(type_byte, session_info["capacity_string"],session_info, "receiveer"):
                    try:
                        received_cn = payload.decode('utf-8')
                        session_info["last_heartbeat"] = time.time()
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] Received 0x12 heartbeat from CMD: {received_cn}")
                        # Optionally: update last heartbeat timestamp, or store it in a dict for monitoring
                    except Exception as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] Error decoding 0x12 heartbeat payload: {e}")
                        
            elif type_byte == b'\x14':
                if verify_policy(type_byte, session_info["capacity_string"], session_info, "receiver"):
                    try:
                        offset = 0
                        cred_len = int.from_bytes(payload[offset:offset+4], 'big')
                        offset += 4
                        credent = payload[offset:offset+cred_len]
                        
                        cred_data = verify_credential(credent, PUcmd, PU2cmd, PUcmd)
                        if cred_data is None:
                            raise ValueError(f"[{cmd2_cn}] Invalid credential or no CRL for 0x14: {cred}")
                        
                        if cred_data["type"] == 0x01:
                            # Credential for this 2CMD
                            old_timestamp = session_info["credential_timestamp"]
                            if cred_data["timestamp"] > old_timestamp:
                                session_info["credential_timestamp"] = cred_data["timestamp"]
                                session_info["capacity_string"] = cred_data["capacity_string"]
                                session_info["hash"] = cred_data["hash"]
                                
                                for old_file in os.listdir(CREDENTIAL_DIR):
                                        
                                        if old_file.startswith(f"{client_cn}_to_{cmd2_cn}_") and old_file.endswith(".cred"):
                                            try:
                                                os.remove(os.path.join(CREDENTIAL_DIR, old_file))
                                            except Exception as e:
                                                if LOG_MODE in (1, 2):
                                                    logger.info(f"[{cmd2_cn}] Failed to remove old credentials {old_file}: {e}")

                                for cred in credentials:
                                    if cred["filename"].startswith(f"{client_cn}_to_{cmd2_cn}_") and cred["filename"].endswith(".cred"):
                                        try:
                                            credentials.remove(cred)
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{cmd2_cn}] Removed old credential record {cred['filename']} from memory")
                                        except Exception as e:
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{cmd2_cn}] Failed to remove old credential from memory {cred['filename']}: {e}")
                                                
                                filename = f"{client_cn}_to_{cmd2_cn}_{cred_data['timestamp']}.cred"
                                filepath = os.path.join(CREDENTIAL_DIR, filename)
                                os.makedirs(os.path.dirname(filepath), exist_ok=True)
                                with open(filepath, 'wb') as f:
                                    f.write(cred_data["raw"])
                                
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd2_cn}] Updated 0x01 credential for 2CMD")

                                
                                credentials.append({
                                    "filename": filename,
                                    "type": cred_data["type"],
                                    "pu1": cred_data["pu1"],
                                    "pu2": cred_data["pu2"],
                                    "timestamp": cred_data["timestamp"],
                                    "lifetime": cred_data["lifetime"],
                                    "hash": cred_data["hash"],
                                    "capacity_string": cred_data["capacity_string"],
                                    "raw": cred_data["raw"]
                                })
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd2_cn}] Saved 0x02 credential: {filename}")
                        elif cred_data["type"] == 0x02:
                            # Credential for GCS
                            with clients_lock:
                                for addr, gcs_info in gcs_sessions.items():
                                    
                                    if gcs_info["gcs_pu"] == cred_data["pu2"] and cred_data["timestamp"] > gcs_info["credential_timestamp"]:
                                        gcs_info["credential_timestamp"] = cred_data["timestamp"]
                                        gcs_info["capacity_string"] = cred_data["capacity_string"]
                                        gcs_info["hash"] = cred_data["hash"]
                                        
                                        for old_file in os.listdir(CREDENTIAL_DIR):
                                        
                                            if old_file.startswith(f"{cmd2_cn}_to_{gcs_cn}_") and old_file.endswith(".cred"):
                                                try:
                                                    os.remove(os.path.join(CREDENTIAL_DIR, old_file))
                                                except Exception as e:
                                                    if LOG_MODE in (1, 2):
                                                        logger.info(f"[{cmd2_cn}] Failed to remove old credentials {old_file}: {e}")
                                        
                                        for cred in credentials:
                                            if cred["filename"].startswith(f"{cmd2_cn}_to_{gcs_cn}_") and cred["filename"].endswith(".cred"):
                                                try:
                                                    credentials.remove(cred)
                                                    if LOG_MODE in (1, 2):
                                                        logger.info(f"[{cmd2_cn}] Removed old credential record {cred['filename']} from memory")
                                                except Exception as e:
                                                    if LOG_MODE in (1, 2):
                                                        logger.info(f"[{cmd2_cn}] Failed to remove old credential from memory {cred['filename']}: {e}")
                                        
                                        filename = f"{cmd2_cn}_to_{gcs_cn}_{cred_data['timestamp']}.cred"
                                        filepath = os.path.join(CREDENTIAL_DIR, filename)
                                        os.makedirs(os.path.dirname(filepath), exist_ok=True)
                                        with open(filepath, 'wb') as f:
                                            f.write(cred_data["raw"])
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{cmd2_cn}] Updated 0x02 credential for GCS {gcs_cn}")

                                        credentials.append({
                                            "filename": filename,
                                            "type": cred_data["type"],
                                            "pu1": cred_data["pu1"],
                                            "pu2": cred_data["pu2"],
                                            "timestamp": cred_data["timestamp"],
                                            "lifetime": cred_data["lifetime"],
                                            "hash": cred_data["hash"],
                                            "capacity_string": cred_data["capacity_string"],
                                            "raw": cred_data["raw"]
                                        })
                                        
                                        # Send as 0x13 to GCS
                                        type_byte_13 = b'\x13'
                                        cred_len_bytes = len(credent).to_bytes(4, 'big')
                                        payload_13 = cred_len_bytes + credent
                                        timestamp_bytes = struct.pack('<Q', int(time.time() * 1e6))
                                        hmac_value = compute_hmac(type_byte_13, payload_13, timestamp_bytes, gcs_info["session_key_sending"])
                                        message_13 = type_byte_13 + payload_13 + timestamp_bytes + hmac_value
                                        gcs_socket.sendto(message_13, addr)
                                        message_lenght_sent.setdefault(session.get('gcs_cn', 'unknown'), []).append((0x13, len(message_13)))
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{cmd2_cn}] Forwarded 0x02 credential (0x13) to GCS {gcs_cn}")
                                
                        elif cred_data["type"] == 0x03:
                            # Credential for UXV (via GCS)
                            with clients_lock:
                                for addr, gcs_info in gcs_sessions.items():
                                    if gcs_info["gcs_pu"] == cred_data["pu1"]: 
                                        type_byte_13 = b'\x13'
                                        cred_len_bytes = len(credent).to_bytes(4, 'big')
                                        payload_13 = cred_len_bytes + credent
                                        timestamp_bytes = struct.pack('<Q', int(time.time() * 1e6))
                                        hmac_value = compute_hmac(type_byte_13, payload_13, timestamp_bytes, gcs_sessions[gcs_addr]["session_key_sending"])
                                        message_13 = type_byte_13 + payload_13 + timestamp_bytes + hmac_value
                                        gcs_socket.sendto(message_13, addr)
                                        message_lenght_sent.setdefault(session.get('gcs_cn', 'unknown'), []).append((0x13, len(message_13)))
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{cmd2_cn}] Forwarded 0x03 credential (0x13) to GCS {gcs_cn} for UXV")

                    except Exception as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] Failed to process 0x14 credential update: {e}")

            
            elif type_byte == b'\x16':
                if verify_policy(type_byte, session_info["capacity_string"], session_info, "receiver"):
                    global current_cert_crl
                    try:
                        crl_data = payload
                        new_crl = load_der_x509_crl(crl_data, default_backend())
                        ca_pubkey.verify(new_crl.signature, new_crl.tbs_certlist_bytes, ec.ECDSA(new_crl.signature_hash_algorithm))
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] Received valid certificate CRL from {client_cn} at {addr}")
                        crl_timestamp = int(new_crl.last_update_utc.timestamp() * 1e6)
                        revoked_serials = {entry.serial_number for entry in new_crl}
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] CRL Timestamp: {crl_timestamp}, current_cert_crl: {current_cert_crl}, Revoked Serials: {revoked_serials}")
                        with crl_cert_lock:
                            if crl_timestamp > current_cert_crl["timestamp"]:
                                # Remover CRL anterior
                                for f in os.listdir(CRL_CERT_DIR):
                                    if f.endswith(".crl.der"):
                                        try:
                                            os.remove(os.path.join(CRL_CERT_DIR, f))
                                        except Exception as e:
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{cmd2_cn}] Failed to remove old certificate CRL: {e}")
                                # Guardar nova CRL
                                crl_filename = f"certcrl_{crl_timestamp}.crl.der"
                                crl_path = os.path.join(CRL_CERT_DIR, crl_filename)
                                with open(crl_path, "wb") as f:
                                    f.write(crl_data)

                                current_cert_crl = {
                                    "timestamp": crl_timestamp,
                                    "revoked_serials": revoked_serials
                                }
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd2_cn}] Updated certificate CRL: Timestamp={crl_timestamp}, Revoked Serials={revoked_serials}")
                                
                                with clients_lock:
                                    # Revoke CMDterminal sessions
                                    for addr, session in list(session_contexts.items()):
                                        peer_serial = session["peer_serial"]
                                        if peer_serial in revoked_serials:
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{cmd2_cn}] Revoked CMD session for {session['client_cn']} at {addr}")
                                            popup_queue.put(("Revoked", f"CMD {session['client_cn']} session revoked", session["client_cn"]))
                                            del session_contexts[addr]
                                        
                                    # Revoke GCS sessions
                                    for gcs_addr, gcs_info in list(gcs_sessions.items()):
                                        gcs_session_key = gcs_info["session_key_sending"]
                                        timestamp_bytes = struct.pack('<Q', int(time.time() * 1e6))
                                        hmac_value = compute_hmac(b'\x16', crl_data, timestamp_bytes, gcs_session_key)
                                        forward_data = b'\x16' + crl_data + timestamp_bytes + hmac_value
                                        gcs_socket.sendto(forward_data, gcs_addr)
                                        message_lenght_sent.setdefault(gcs_info['gcs_cn'], []).append((0x16, len(forward_data)))
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{cmd2_cn}] Forwarded 0x16 certificate CRL to GCS {gcs_info['gcs_cn']} at {gcs_addr}")
                                        peer_serial = gcs_info["peer_serial"]
                                        
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{cmd2_cn}] Checking GCS {gcs_info['gcs_cn']} with serial - {peer_serial}, revoked serials - {revoked_serials}")
                                        if peer_serial in revoked_serials:
                                            del gcs_sessions[gcs_addr]
                                            gcs_cn = gcs_info["gcs_cn"]
                                            if gcs_cn in gcs_notebooks:
                                                try:
                                                    notebook = gcs_notebooks[gcs_cn]
                                                    for widget in notebook_frame.winfo_children():
                                                        if isinstance(widget, ttk.Label) and widget.winfo_name() == f"label_{gcs_cn}":
                                                            widget.destroy()
                                                            break
                                                    notebook.pack_forget()
                                                    notebook.destroy()
                                                    del gcs_notebooks[gcs_info["gcs_cn"]]
                                                    if LOG_MODE in (1, 2):
                                                        logger.info(f"[{cmd2_cn}] Removed notebook for GCS {gcs_cn}")
                                                except tk.TclError as e:
                                                    if LOG_MODE in (1, 2):
                                                        logger.info(f"[{cmd2_cn}] Error removing notebook for GCS {gcs_cn}: {e}")
                                            
                                            if gcs_cn in active_gcs:
                                                active_gcs.remove(gcs_cn)
                                            if gcs_cn in network_map:
                                                del network_map[gcs_cn]
                                            update_network_view()
                                            popup_queue.put(("Revoked", f"GCS {gcs_cn} session revoked", gcs_info["gcs_cn"]))
                                        
                    except Exception as e:
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] CRL certificates verification failed: {e}")
            

            elif type_byte == b'\x17':
                if verify_policy(type_byte, session_info["capacity_string"], session_info, "receiver"):
                    global cmd2_cert
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
                            logger.info(f"[{cmd2_cn}] 0x17 cert rejected: CA signature verification failed: {e}")
                        continue

                    # 2) Enforce validity window
                    now = datetime.datetime.now(datetime.timezone.utc)
                    # cryptography>=41 provides *_utc properties; fall back if needed
                    not_before = getattr(cert_obj, "not_valid_before_utc", cert_obj.not_valid_before.replace(tzinfo=datetime.timezone.utc))
                    not_after  = getattr(cert_obj, "not_valid_after_utc",  cert_obj.not_valid_after.replace(tzinfo=datetime.timezone.utc))
                    if not (not_before <= now <= not_after):
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] 0x17 cert rejected: outside validity window "
                                    f"({not_before.isoformat()} .. {not_after.isoformat()}), now={now.isoformat()}")
                        continue

                    
                    
                    client_pu = cert_obj.public_key()
                    client_cn = cert_obj.subject.get_attributes_for_oid(x509.NameOID.COMMON_NAME)[0].value
                    cert_serial = cert_obj.serial_number
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd2_cn}] 0x17 cert from {client_cn}, serial {cert_serial}")
                    cert_crl = load_latest_cert_crl(CRL_CERT_DIR)
                    if cert_crl is None:
                        raise ValueError("No valid CRL found")
                    if cert_crl is not None:
                        revoked_serials = {r.serial_number for r in cert_crl}
                        if cert_serial in revoked_serials:
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{cmd2_cn}] Certificate rejected: peer certificate serial {cert_serial} of {client_cn} is revoked.")
                            continue
                    
                    if client_cn == cmd2_cn and client_pu == PU2cmd:

                        if cert_obj.not_valid_before > cmd2_cert.not_valid_before:
                            try:
                                crt_path  = os.path.join(CERT_DIR, f"{client_cn}.crt")
                                if os.path.exists(crt_path):
                                    ts = int(time.time())
                                    backup = os.path.join(CERT_DIR, f"{client_cn}_{ts}.crt.bak")
                                    try:
                                        os.replace(crt_path, backup)
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{cmd2_cn}] [BACKUP] {client_cn}: {backup}")
                                    except Exception as e:
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{cmd2_cn}] [WARN] Could not backup {crt_path}: {e}")
                                
                                cmd2_cert = cert_obj
                                
                                filename = f"{client_cn}.crt"
                                filepath = os.path.join(CERT_DIR, filename)
                                os.makedirs(os.path.dirname(filepath), exist_ok=True)
                                with open(filepath, 'wb') as f:
                                    f.write(payload)

                                
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd2_cn}] Updated own certificate with the new one received via 0x17.")
                                _purge_old_backups(client_cn)
                            except Exception as e:
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd2_cn}] Failed to update certificate: {e}")
                        else:
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{cmd2_cn}] Received certificate is not newer than the current one; no update performed.")
                        continue    
                        

                    elif client_cn.lower().startswith("gcs"):
                        for addr, session in  gcs_sessions.items():
                            if session["gcs_cn"] == client_cn and client_pu == session["gcs_pu"]:
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd2_cn}] Forwarding message to GCS {client_cn} at {addr}")
                                if verify_policy(b'\x17', session["capacity_string"], session, "sender"):
                                    timestamp_bytes = struct.pack('<Q', int(time.time() * 1e6))
                                    h = compute_hmac(b'\x17', payload, timestamp_bytes, session["session_key_sending"])
                                    gcs_socket.sendto(b'\x17' + payload + timestamp_bytes + h, addr)
                                    message_lenght_sent.setdefault(client_cn, []).append((0x17, len(b'\x17' + payload + timestamp_bytes + h)))
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{cmd2_cn}] 0x17 to GCS {client_cn} at {addr}")
                                    continue
                                
                    elif client_cn.lower().startswith("sitl"):
                        for gcs, uxv_list in network_map.items():
                            # Check if the UXV's CN is in the list of UXVs for this GCS
                            if client_cn in uxv_list:
                                # Now find the active session for that GCS to get its address
                                for addr, session in gcs_sessions.items():
                                    if session["gcs_cn"] == gcs:
                                        if LOG_MODE in (1, 2):
                                            logger.info(f"[{cmd2_cn}] Found GCS {gcs} at {addr} for UXV {client_cn}. Forwarding message.")
                                        if verify_policy(b'\x17', session["capacity_string"], session, "sender"):
                                            timestamp_bytes = struct.pack('<Q', int(time.time() * 1e6))
                                            h = compute_hmac(b'\x17', payload, timestamp_bytes, session["session_key_sending"])
                                            gcs_socket.sendto(b'\x17' + payload + timestamp_bytes + h, addr)
                                            message_lenght_sent.setdefault(gcs, []).append((0x17, len(b'\x17' + payload + timestamp_bytes + h)))
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{cmd2_cn}] Sent 0x17 to GCS {gcs} at {addr} for UXV {client_cn}")
                                            continue
                                        
            message_processing_time.append(time.time()*1e6 - message_processing_time_start)                
        except BlockingIOError:
            pass
        except Exception as e:
            if running:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd2_cn}] Error processing CMD UDP message: {e}")
        

def handle_gcs_udp():
    global color_index, lon1, lon2, lat1, lat2, IMAGE_WIDTH, IMAGE_HEIGHT, message_processing_time
    while running:
        try:
            message_processing_start = time.time()*1e6
            data, addr = gcs_socket.recvfrom(65536)
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] Received UDP from GCS at {addr}, Type={data[0:1].hex()}")
            
            session_info = gcs_sessions.get(addr)
            if not session_info:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd2_cn}] No session for GCS at {addr}")
                continue
            client_cn = session_info["gcs_cn"]
            msg_type = data[0] if data else None
            message_lenght_received.setdefault(client_cn, []).append((msg_type, len(data)))
            session_key = session_info["session_key_receiving"]
            result = verify_hmac(data, session_info, client_cn, data[0:1].hex())
            if not result:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd2_cn}] Verification failed for {client_cn}, Type={data[0:1].hex()}")
                continue
            type_byte, payload, gap = result
            timestamp = struct.unpack('<Q', data[-24:-16])[0]
            gap_values_per_connection.setdefault(client_cn, []).append((type_byte,gap))
            
            if type_byte == b'\x01':
                len_cn = payload[0]
                uxv_cn = payload[1:1+len_cn].decode('utf-8')
                mavlink_data = payload[1+len_cn:]
                parsed_msgs = mav.mav.parse_buffer(mavlink_data)
                
                if parsed_msgs and parsed_msgs[0]:
                    msg = parsed_msgs[0]
                    msg_type = msg.get_type()
                    sysid = msg.get_srcSystem()
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd2_cn}] Received from GCS {client_cn}: Type={msg_type}, SysID={sysid}, UXV={uxv_cn}")
                    if verify_policy(type_byte, session_info["capacity_string"], session_info, "receiver", mav_type=msg_type):
                        
                        # Forward to CMDterminal
                        for cmd_addr, cmd_info in session_contexts.items():
                            cmd_session_key = cmd_info["session_key_sending"]
                            cmd_capacity_string = cmd_info["capacity_string"]
                            if verify_policy(b'\x01', cmd_capacity_string, cmd_info, "sender"):
                                timestamp = int(time.time() * 1e6)
                                timestamp_bytes = struct.pack('<Q', timestamp)
                                hmac_value = compute_hmac(b'\x01', payload, timestamp_bytes, cmd_session_key)
                                forward_data = b'\x01' + payload + timestamp_bytes + hmac_value
                                cmd_socket.sendto(forward_data, cmd_addr)
                                message_lenght_sent.setdefault(cmd_info['client_cn'], []).append((0x01, len(forward_data)))
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd2_cn}] Forwarded 0x01 to CMD at {cmd_addr}: SysID={sysid}, UXV={uxv_cn}")
                        
                        if msg_type == "HEARTBEAT":
                            with sysid_to_gcs_lock:
                                sysid_to_uxv_cn[sysid] = uxv_cn
                                sysid_to_gcs[sysid] = client_cn
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd2_cn}] SYSID {sysid} mapped to UXV {uxv_cn}, GCS {client_cn}")
                            
                            gcs_notebook = gcs_notebooks.get(client_cn)
                            if not gcs_notebook:
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd2_cn}] No notebook for GCS {client_cn}")
                                continue
                            
                            # Check if a tab for this uxv_cn already exists in the notebook
                            tab_exists = False
                            for tab in gcs_notebook.tabs():
                                if gcs_notebook.tab(tab, "text") == uxv_cn:
                                    tab_exists = True
                                    # If tab exists, ensure sitls[sysid] points to it
                                    if sysid in sitls:
                                        sitls[sysid]["tab"] = gcs_notebook.nametowidget(tab)
                                        sitls[sysid]["telemetry_label"] = gcs_notebook.nametowidget(tab).winfo_children()[0]
                                    break
                            
                            # Reparent or create a new tab if necessary
                            if sysid in sitls and not tab_exists:
                                try:
                                    current_parent = sitls[sysid]["tab"].winfo_parent()
                                    expected_parent = gcs_notebook.winfo_name()
                                    if current_parent != expected_parent:
                                        old_notebook = None
                                        for cn, nb in gcs_notebooks.items():
                                            try:
                                                if sitls[sysid]["tab"] in nb.winfo_children():
                                                    old_notebook = nb
                                                    break
                                            except tk.TclError:
                                                continue
                                        if old_notebook:
                                            try:
                                                old_notebook.forget(sitls[sysid]["tab"])
                                                if LOG_MODE in (1, 2):
                                                    logger.info(f"[{cmd2_cn}] Removed sysid={sysid} tab from old notebook")
                                            except tk.TclError as e:
                                                if LOG_MODE in (1, 2):
                                                    logger.info(f"[{cmd2_cn}] Error removing tab: {e}")
                                        try:
                                            gcs_notebook.add(sitls[sysid]["tab"], text=uxv_cn)
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{cmd2_cn}] Moved sysid={sysid} tab to GCS {client_cn} notebook")
                                        except tk.TclError as e:
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{cmd2_cn}] Error adding tab: {e}")
                                            # If adding fails, do not create a new tab; skip to avoid duplication
                                            continue
                                except tk.TclError as e:
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{cmd2_cn}] Error during tab reparenting: {e}")
                                    # Skip creating a new tab to avoid duplication
                                    continue
                            
                            # Create a new tab only if sysid is not in sitls and no tab exists for uxv_cn
                            if sysid not in sitls and len(sitls) < MAX_SITLS and not tab_exists:
                                color = colors[color_index % len(colors)]
                                color_index += 1
                                marker = canvas.create_oval(-10, -10, -10, -10, fill=color)
                                text = canvas.create_text(-10, -10, text=str(sysid), fill="white")
                                tab = tk.Frame(gcs_notebook)
                                telemetry_label = tk.Label(tab, text="Telemetry: Waiting for data...")
                                telemetry_label.pack()
                                gcs_notebook.add(tab, text=uxv_cn)
                                sitls[sysid] = {
                                    "marker": marker,
                                    "text": text,
                                    "tab": tab,
                                    "telemetry_label": telemetry_label,
                                    "last_timestamp": time.time(),
                                    "telemetry": {},
                                    "color": color
                                }
                                if LOG_MODE in (1, 2):
                                    logger.info(f"[{cmd2_cn}] Added SITL sysid={sysid} for GCS {client_cn} with color {color}")
                        
                        if sysid in sitls and msg:
                            sitls[sysid]["last_timestamp"] = time.time()
                            if msg_type == "GLOBAL_POSITION_INT":
                                lat = msg.lat / 1e7
                                lon = msg.lon / 1e7
                                sitls[sysid]["telemetry"]["lat"] = lat
                                sitls[sysid]["telemetry"]["lon"] = lon
                                if lon1 <= lon <= lon2 and lat2 <= lat <= lat1:
                                    x_pixel = (lon - lon1) / (lon2 - lon1) * current_map_width
                                    y_pixel = (lat1 - lat) / (lat1 - lat2) * current_map_height
                                    marker_radius = 5
                                    canvas.coords(sitls[sysid]["marker"],
                                                x_pixel - marker_radius, y_pixel - marker_radius,
                                                x_pixel + marker_radius, y_pixel + marker_radius)
                                    canvas.coords(sitls[sysid]["text"], x_pixel, y_pixel)
                                else:
                                    canvas.coords(sitls[sysid]["marker"], -10, -10, -10, -10)
                                    canvas.coords(sitls[sysid]["text"], -10, -10)
                            elif msg_type == "VFR_HUD":
                                sitls[sysid]["telemetry"]["groundspeed"] = msg.groundspeed
                                sitls[sysid]["telemetry"]["altitude"] = msg.alt
                                sitls[sysid]["telemetry"]["climb"] = msg.climb
                                sitls[sysid]["telemetry"]["heading"] = msg.heading
                            
                            telemetry = sitls[sysid]["telemetry"]
                            telemetry_text = (f"Telemetry:\n"
                                            f"Groundspeed: {telemetry.get('groundspeed', 0):.2f} m/s\n"
                                            f"Altitude: {telemetry.get('altitude', 0):.2f} m\n"
                                            f"Vertical Speed: {telemetry.get('climb', 0):.2f} m/s\n"
                                            f"Heading: {telemetry.get('heading', 0)}°")
                            sitls[sysid]["telemetry_label"].config(text=telemetry_text)
            
            elif type_byte == b'\x06':
                if verify_policy(type_byte, session_info["capacity_string"], session_info, "receiver"):
                    with clients_lock:
                        if addr in gcs_sessions:
                            gcs_sessions[addr]["last_map_time"] = time.time()
                            gcs_cn = gcs_sessions[addr]["gcs_cn"]
                        else:
                            continue
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
                        uxvs_for_this_gcs.append(uxv_cn)
                    with network_lock:
                        active_gcs.add(gcs_cn)
                        network_map[gcs_cn] = uxvs_for_this_gcs
                    root.after(0, update_network_view)
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd2_cn}] Received network mapping from {gcs_cn}: {uxvs_for_this_gcs}")
            
            elif type_byte == b'\x07':
                if verify_policy(type_byte, session_info["capacity_string"], session_info, "receiver"):
                    gcs_cn_bytes = payload.decode('utf-8')
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd2_cn}] Received disconnection from GCS {gcs_cn_bytes}")
                    with network_lock:
                        active_gcs.discard(gcs_cn_bytes)
                        if gcs_cn_bytes in network_map:
                            del network_map[gcs_cn_bytes]
                    root.after(0, update_network_view)
                    with clients_lock:
                        if addr in gcs_sessions:
                            del gcs_sessions[addr]
                            if gcs_cn_bytes in gcs_notebooks:
                                try:
                                    notebook = gcs_notebooks[gcs_cn_bytes]
                                    for widget in notebook_frame.winfo_children():
                                        if isinstance(widget, ttk.Label) and widget.winfo_name() == f"label_{gcs_cn_bytes}":
                                            widget.destroy()
                                            if LOG_MODE in (1, 2):
                                                logger.info(f"[{cmd2_cn}] Removed label for GCS {gcs_cn_bytes}")
                                            break
                                    notebook.pack_forget()
                                    notebook.destroy()
                                    del gcs_notebooks[gcs_cn_bytes]
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{cmd2_cn}] Removed notebook for GCS {gcs_cn_bytes}")
                                except tk.TclError as e:
                                    if LOG_MODE in (1, 2):
                                        logger.info(f"[{cmd2_cn}] Error removing notebook for GCS {gcs_cn_bytes}: {e}")
                            popup_queue.put(("Disconnected", f"GCS {gcs_cn_bytes} disconnected", gcs_cn_bytes))
                        
            elif type_byte == b'\x11':
                if verify_policy(type_byte, session_info["capacity_string"], session_info, "receiver"):

                        if addr not in pending_dh:
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{cmd2_cn}] Unexpected 0x11 received from {addr}")
                            continue

                        shared_secret = session_info["shared_secret"] 
                        if not shared_secret:
                            if LOG_MODE in (1, 2):
                                logger.info(f"[{cmd2_cn}] No shared secret stored for {addr}, cannot renew")
                            continue
                        
                        salt=payload              
                        new_key_sending = HKDF(
                            algorithm=hashes.SHA256(), 
                            length=SESSION_KEY_LENGTH,
                            salt=salt,
                            info=b"session_key_renewed_sending"
                        ).derive(shared_secret)
                        
                        new_key_receiving = HKDF(
                            algorithm=hashes.SHA256(), 
                            length=SESSION_KEY_LENGTH,
                            salt=salt,
                            info=b"session_key_renewed_receiving"
                        ).derive(shared_secret)
                        
                        session_info["session_key_sending"] = new_key_sending
                        session_info["session_key_receiving"] = new_key_receiving
                        session_info["session_created_at"] = time.time()
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] Session key renewed with {session_info.get('gcs_cn', 'peer')} at {addr}")
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] New session keys:")
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] new key sending: {new_key_sending.hex()}")
                        if LOG_MODE in (1, 2):
                            logger.info(f"[{cmd2_cn}] new key receiving: {new_key_receiving.hex()}")
                        del pending_dh[addr]            

            message_processing_time.append(time.time()*1e6 - message_processing_start)
        except BlockingIOError:
            pass
        except Exception as e:
            if running:
                if LOG_MODE in (1, 2):
                    logger.info(f"[{cmd2_cn}] Error processing GCS UDP message: {e}")
       

def update_gui():
    current_time = time.time()
    for sysid in list(sitls.keys()):
        if current_time - sitls[sysid]["last_timestamp"] > 30:
            popup_queue.put(("SITL Disconnected", f"SITL sysid={sysid} stopped transmitting", sitls[sysid]["telemetry"].get("gcs_cn", "unknown")))
            canvas.delete(sitls[sysid]["marker"])
            canvas.delete(sitls[sysid]["text"])
            gcs_notebook = gcs_notebooks.get(sysid_to_gcs.get(sysid))
            if gcs_notebook:
                try:
                    gcs_notebook.forget(sitls[sysid]["tab"])
                except tk.TclError as e:
                    if LOG_MODE in (1, 2):
                        logger.info(f"[{cmd2_cn}] Error removing disconnected tab: {e}")
            del sitls[sysid]
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] Removed SITL sysid={sysid} due to disconnection")
    root.after(100, update_gui)

def setup_mavlink_and_gui(mtls_port, udp_port, listener=None):
    global cmd_socket, gcs_socket, canvas, photo, notebook_frame, network_text, network_frame, lon1, lat2, lon2, lat1,IMAGE_WIDTH, IMAGE_HEIGHT
    global original_map_image, current_map_photo, lon1, lat1, lon2, lat2, IMAGE_WIDTH, HEIGHT
    
    if LOG_MODE in (1, 2):
        logger.info(f"[{cmd2_cn}] Starting MAVLink and GUI setup")
    
    image_path = os.path.join(CERT_DIR, "mission_image", "mission_image.tif")
    
    try:
        with rasterio.open(image_path) as dataset:
            IMAGE_WIDTH = dataset.width
            IMAGE_HEIGHT = dataset.height
            lon1, lat2, lon2, lat1 = dataset.bounds.left, dataset.bounds.bottom, dataset.bounds.right, dataset.bounds.top
            if LOG_MODE in (1, 2):
                logger.info(f"[{cmd2_cn}] Loaded GeoTIFF image from {image_path}, dimensions: {IMAGE_WIDTH}x{IMAGE_HEIGHT}, bounds: {dataset.bounds}")

            image_data = dataset.read([1, 2, 3])
            image_array = image_data.transpose((1, 2, 0))
            original_map_image = Image.fromarray(image_array) # Store the original PIL image
    except Exception as e:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] Error loading GeoTIFF image {image_path}: {e}")
        root.destroy()
        exit(1)
    
    # Set up UDP sockets
    cmd_socket = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    cmd_socket.setblocking(False)
    cmd_socket.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 65536)
    cmd_socket.bind(("", udp_port))
    if LOG_MODE in (1, 2):
        logger.info(f"[{cmd2_cn}] CMD UDP socket bound to port: {udp_port}")
    
    gcs_socket = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    gcs_socket.setblocking(False)
    gcs_socket.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 65536)
    gcs_socket.bind(("", 0))
    
    if LOG_MODE in (1, 2):
        logger.info(f"[{cmd2_cn}] UDP socket bound to port: {gcs_socket.getsockname()[1]} for GCS connections")
    
    # Create MAVLink parser
    global mav
    mav = mavutil.mavlink_connection('udp:127.0.0.1:14500', source_system=255)
    
    threading.Thread(target=session_key_monitor, daemon=True).start()
    threading.Thread(target=cleanup_pending_dh, daemon=True).start()
    threading.Thread(target=send_heartbeat, daemon=True).start()
    threading.Thread(target=credential_expiry_monitor, daemon=True).start()
    #threading.Thread(target=monitor_threads, daemon=True).start()
    
    # Create GUI
    root.deiconify()
    root.title("2CMD Drone Tracker")
    
    

    canvas = tk.Canvas(root)
    
    # Left side frame for network diagram
    network_frame = tk.Frame(root)
    network_frame.pack(side=tk.LEFT, fill=tk.Y)

    network_label = tk.Label(network_frame, text="Network Mapping", font=("Arial", 12, "bold"))
    network_label.pack(anchor='w')

    network_text = tk.Text(network_frame, width=20, height=30, font=("Courier", 10))
    network_text.pack(fill=tk.BOTH, expand=True)
    network_text.configure(state='disabled')
    
    canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
    canvas.bind('<Configure>', resize_map_and_redraw)
    
    # Sidebar (no buttons)
    sidebar = tk.Frame(root, bd=1, relief=tk.SOLID)
    sidebar.pack(side=tk.RIGHT, fill=tk.Y, padx=5, pady=5)
    global send_button
    send_button = tk.Button(sidebar, text="Send Waypoint Mission", command=send_waypoint_wrapper)
    send_button.pack(pady=10)
    
    # Notebook frame
    notebook_frame = ttk.Frame(root)
    notebook_frame.pack(fill=tk.BOTH, expand=True)
    
    # Start mTLS server
    threading.Thread(target=mtls_server, args=(mtls_port,), daemon=True).start()
    
    # Start UDP handling threads
    threading.Thread(target=handle_cmd_udp, daemon=True).start()
    threading.Thread(target=handle_gcs_udp, daemon=True).start()
    
    root.after(10, process_popups)
    root.after(1000, check_gcs_timeouts)
    root.after(5000, send_network_map_to_cmd)
    root.after(100, update_gui)
    try:
        root.mainloop()
    except KeyboardInterrupt:
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] Shutting down...")
    finally:
        global running
        running = False
        def _format_msg_type(msg_type):
            return "Unknown" if msg_type is None else f"0x{msg_type:02X}"

        if message_lenght_received:
            for node_cn, records in message_lenght_received.items():
                if not records:
                    continue
                type_totals = {}
                total_length = 0
                total_count = 0
                for record in records:
                    if isinstance(record, tuple) and len(record) == 2:
                        msg_type, length = record
                    else:
                        msg_type, length = None, record
                    total_length += length
                    total_count += 1
                    entry = type_totals.setdefault(msg_type, {"count": 0, "total_length": 0})
                    entry["count"] += 1
                    entry["total_length"] += length

                print(f"[{cmd2_cn}] Message statistics for {node_cn} receiving:")
                for msg_type, stats in sorted(type_totals.items(), key=lambda item: (-1 if item[0] is None else item[0])):
                    avg_type_length = stats["total_length"] / stats["count"]
                    print(f"[{cmd2_cn}] Type {_format_msg_type(msg_type)}: Average length {avg_type_length:.2f} bytes over {stats['count']} messages (Total: {stats['total_length']} bytes)")
                overall_avg = total_length / total_count if total_count else 0
                print(f"[{cmd2_cn}] Total messages received: {total_count}, Average length: {overall_avg:.2f} bytes (Total: {total_length} bytes)")

        if message_lenght_sent:
            for node_cn, records in message_lenght_sent.items():
                if not records:
                    continue
                type_totals = {}
                total_length = 0
                total_count = 0
                for record in records:
                    if isinstance(record, tuple) and len(record) == 2:
                        msg_type, length = record
                    else:
                        msg_type, length = None, record
                    total_length += length
                    total_count += 1
                    entry = type_totals.setdefault(msg_type, {"count": 0, "total_length": 0})
                    entry["count"] += 1
                    entry["total_length"] += length

                print(f"[{cmd2_cn}] Message statistics for {node_cn} sending:")
                for msg_type, stats in sorted(type_totals.items(), key=lambda item: (-1 if item[0] is None else item[0])):
                    avg_type_length = stats["total_length"] / stats["count"]
                    print(f"[{cmd2_cn}] Type {_format_msg_type(msg_type)}: Average length {avg_type_length:.2f} bytes over {stats['count']} messages (Total: {stats['total_length']} bytes)")
                overall_avg = total_length / total_count if total_count else 0
                print(f"[{cmd2_cn}] Total messages sent: {total_count}, Average length: {overall_avg:.2f} bytes (Total: {total_length} bytes)")
            
        if message_processing_time:
            avg_processing_time = sum(message_processing_time) / len(message_processing_time)
            print(f"[{cmd2_cn}] Average message processing time: {avg_processing_time:.2f} μs for {len(message_processing_time)} messages")
        
        
        if offset_per_node:
            # Calculate and print the average for each specific node
            for node, times in offset_per_node.items():
                if not times:
                    continue
                # Use the corrected variables and a more accurate description in the print statement.
                print(f"[{cmd2_cn}] offset {node}: {times} μs")
        
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
                print(f"[{cmd2_cn}] Average connection establishment time for {node}: {node_avg_time:.2f} μs over {node_connection_count} connection(s)")
                
                # Add the node's totals to the overall counters
                overall_total_time += node_total_time
                overall_total_count += node_connection_count

            # Calculate and print the overall average after the loop
            if overall_total_count > 0:
                overall_avg_time = overall_total_time / overall_total_count
                print(f"[{cmd2_cn}] Overall average connection establishment time: {overall_avg_time:.2f} μs over {overall_total_count} total connection(s)")

        print(f"[{cmd2_cn}] Number of messages dropped due to gap:{number_gap_drop}")
        with gap_values_lock:
            overall_total_gap = 0
            overall_total_count = 0

            for node_cn, records in gap_values_per_connection.items():
                if not records:
                    print(f"[{cmd2_cn}] No gap values recorded for {node_cn}")
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

                print(f"[{cmd2_cn}] Gap statistics for {node_cn}:")
                for msg_type, stats in sorted(type_totals.items(), key=lambda item: item[0]):
                    avg_type_gap = stats["total_gap"] / stats["count"]
                    print(f"[{cmd2_cn}] Type {msg_type}: Average gap {avg_type_gap:.2f} μs over {stats['count']} message(s)")

                node_avg_gap = node_total_gap / node_total_count if node_total_count else 0
                print(f"[{cmd2_cn}] Total messages: {node_total_count}, Average gap: {node_avg_gap:.2f} μs")

                overall_total_gap += node_total_gap
                overall_total_count += node_total_count

            if overall_total_count:
                overall_avg_gap = overall_total_gap / overall_total_count
                print(f"[{cmd2_cn}] Overall average gap across all nodes: {overall_avg_gap:.2f} μs over {overall_total_count} message(s)")
            else:
                if not gap_values_per_connection:
                    print(f"[{cmd2_cn}] No gap values recorded for any node")
                else:
                    print(f"[{cmd2_cn}] No gap values recorded across all nodes")
        send_disconnection()
        cmd_socket.close()
        gcs_socket.close()
        root.destroy()
        try:
            if listener is not None:
                listener.stop()
        except Exception:
            pass
        if LOG_MODE in (1, 2):
            logger.info(f"[{cmd2_cn}] Shut down")

def main():
    global logger, log_queue, queue_handler, file_handler, console_handler, listener, LOG_MODE
    if len(sys.argv) != 5 :
        print("Usage: 2CMD_terminal.py <CMD2_NAME> <mtls_port> <udp_port>")
        exit(1)
    try:
        cmd2_name = sys.argv[1]
        mtls_port = int(sys.argv[2])
        udp_port = int(sys.argv[3])
        LOG_MODE = sys.argv[4]
        if mtls_port <= 0 or udp_port <= 0:
            raise ValueError("Ports must be positive integers")
    except ValueError as e:
        print(f"Invalid port numbers: {e}")
        exit(1)

    # Load configuration
    load_config(cmd2_name)

    if LOG_MODE not in ('0', '1', '2'):
        print(f"Invalid LOG_MODE: {LOG_MODE}. Must be 0, 1 or 2.")
        sys.exit(1)
    LOG_MODE = int(LOG_MODE)

    # Prepare log file path
    log_path = os.path.join(CERT_DIR, f"{cmd2_cn}_log.txt")
    os.makedirs(CERT_DIR, exist_ok=True)

    # Root logger
    logger = logging.getLogger()
    logger.setLevel(logging.DEBUG)
    logger.handlers.clear()

    # Common formatter
    formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')

    # Setup async logging based on mode
    if LOG_MODE == 0:
        # completely silent
        pass

    elif LOG_MODE in (1, 2):
        log_queue  = queue.Queue()
        queue_handler = QueueHandler(log_queue)
        logger.addHandler(queue_handler)

        listener_handlers = []

        # Console handler
        console = logging.StreamHandler(sys.stdout)
        console.setLevel(logging.INFO)
        console.setFormatter(formatter)
        listener_handlers.append(console)

        # File handler only in mode 2
        if LOG_MODE == 2:
            file_handler = logging.FileHandler(log_path, mode='w', encoding='utf-8')
            file_handler.setLevel(logging.DEBUG)
            file_handler.setFormatter(formatter)
            listener_handlers.append(file_handler)

        # Start background listener
        listener = QueueListener(log_queue, *listener_handlers)
        listener.start()

        # Redirect print()/stderr into logger
        class StreamToLogger:
            def __init__(self, log_func):
                self.log_func = log_func
            def write(self, msg):
                for line in msg.rstrip().splitlines():
                    self.log_func(line)
            def flush(self):
                pass

        if LOG_MODE in (0, 1, 2):
            sys.stdout = StreamToLogger(logger.info)
            sys.stderr = StreamToLogger(logger.error)

    # Initial log messages
    if LOG_MODE in (1, 2):
        logger.info(f"[{cmd2_cn}] Logging initialized (mode={LOG_MODE})")
        logger.info(f"[{cmd2_cn}] PID: {os.getpid()}")

    # Now load CRL, credentials, and cert CRL
    global current_crl, credentials, current_cert_crl
    current_crl = load_crl()
    credentials = load_credentials(CREDENTIAL_DIR, PUcmd)
    current_cert_crl = load_latest_cert_crl(CRL_CERT_DIR)
    global gcs_permissions_sending, gcs_permissions_receiving, cmd_permissions_sending, cmd_permissions_receiving
    gcs_permissions_sending, gcs_permissions_receiving, cmd_permissions_sending, cmd_permissions_receiving = load_policies(POLICY_FILE)
    setup_mavlink_and_gui(mtls_port, udp_port, listener)

if __name__ == "__main__":
    main()