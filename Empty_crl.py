import os
import time
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.backends import default_backend

# Paths and constants (same as original script)
CERT_DIR = r"C:\Users\Admin\Desktop\tecnico\tese\NC2S Repository\NC2S-Repository\cert1\cmd"
CMD_KEY = os.path.join(CERT_DIR, "cmd.key")
CRL_DIR = os.path.join(CERT_DIR, "crl")
CRL_LIFETIME_SECONDS = 365 * 24 * 60 * 60  # 1 year
#CRL_LIFETIME_SECONDS = 4 * 60  # 1 year
# Ensure CRL_DIR exists (same as original)
os.makedirs(CRL_DIR, exist_ok=True)

# Load PRcmd (CMD private key, same as original)
with open(CMD_KEY, 'rb') as f:
    PRcmd = serialization.load_pem_private_key(f.read(), None, default_backend())

# CRL creation function (identical to original script)
def create_crl(revoked_hashes, prcmd):
    timestamp = time.time()
    lifetime = CRL_LIFETIME_SECONDS  
    lt_bytes = int(lifetime* 1e6).to_bytes(8, 'big')
    ts_bytes = int(timestamp * 1e6).to_bytes(8, 'big')
    payload = ts_bytes + lt_bytes
    for h in revoked_hashes:
        payload += h
    
    signature = prcmd.sign(payload, ec.ECDSA(hashes.SHA256()))
    sig_len = len(signature).to_bytes(2, 'big')

    return payload + signature + sig_len, timestamp, payload

# Create empty CRL (revoked_hashes = [])
empty_crl_bytes, creation_timestamp, empty_crl_payload = create_crl([], PRcmd)

# Save to file in CRL_DIR (filename includes timestamp for uniqueness)
filename = os.path.join(CRL_DIR, f"crl_{int(creation_timestamp*1e6)}.crl")
with open(filename, 'wb') as f:
    f.write(empty_crl_bytes)

# Output confirmation
print(f"Empty custom CRL created successfully.")
print(f" - Timestamp (microseconds): {int(creation_timestamp * 1e6)}")
print(f" - Lifetime (microseconds): {int(CRL_LIFETIME_SECONDS* 1e6)} ")
print(f" - Revoked hashes: None (empty)")
print(f" - Total size: {len(empty_crl_bytes)} bytes")
print(f" - Payload size: {len(empty_crl_payload)} bytes")
print(f" - Saved to: {filename}")