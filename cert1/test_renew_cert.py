import os
import subprocess
import time
import argparse
from datetime import datetime, timezone, timedelta
from zoneinfo import ZoneInfo
from cryptography import x509
from cryptography.hazmat.backends import default_backend
import glob
# ========= CONFIG (adjust if your paths differ) =========
CERT_DIR       = r"C:\Users\Admin\Desktop\tecnico\tese\tese\cert1\cmd"  # folder containing *.crt/*.key/*.conf
OPENSSL_PATH   = r"C:\Program Files\OpenSSL-Win64\bin\openssl.exe"      # openssl executable
CA_CONF_PATH   = r"C:\Users\Admin\Desktop\tecnico\tese\tese\cert1\ca\ca.conf"  # CA config
RENEW_THRESHOLD_SEC = 120   # renew when time-to-expiry <= 2 minutes
CHECK_EVERY_SEC     = 10    # scan period
DEFAULT_DAYS        = "365" # CA -days value (match your current practice)
EXT_SECTION         = "v3_req"  # extension section used when signing
LOCAL_TZ            = ZoneInfo("Europe/Lisbon")
# ========================================================

cert_expirations = {}  # CN -> datetime (UTC)

def load_cert_expirations():
    """(Re)load CN -> expiry from .crt files in CERT_DIR."""
    new_map = {}
    for fname in os.listdir(CERT_DIR):
        if not fname.endswith(".crt"):
            continue
        if fname.lower() == "ca.crt":
            # skip CA cert
            continue
        crt_path = os.path.join(CERT_DIR, fname)
        try:
            with open(crt_path, "rb") as f:
                cert = x509.load_pem_x509_certificate(f.read(), default_backend())
            # Use the modern utc property to avoid deprecation warnings
            expiry_utc = cert.not_valid_after_utc  # cryptography >= 41 provides *_utc
            # CN from subject
            cn_attr = cert.subject.get_attributes_for_oid(x509.NameOID.COMMON_NAME)[0]
            cn = cn_attr.value
            new_map[cn] = expiry_utc
            expiry_local = expiry_utc.astimezone(LOCAL_TZ)
            print(f"[SCAN] {cn}: expires {expiry_utc.isoformat()} (UTC) | {expiry_local.isoformat()} ({LOCAL_TZ.key})")
        except Exception as e:
            print(f"[WARN] Skipping {fname}: {e}")
    cert_expirations.clear()
    cert_expirations.update(new_map)

def tte_seconds(dt_utc):
    """Return time-to-expiry in seconds (can be negative)."""
    now = datetime.now(timezone.utc)
    return (dt_utc - now).total_seconds()

def run(cmd_args):
    """Run a subprocess, raise if non-zero."""
    # For readability in logs:
    pretty = " ".join([f'"{a}"' if " " in a and not a.startswith("-") else a for a in cmd_args])
    print(f"[CMD] {pretty}")
    subprocess.run(cmd_args, check=True)

def renew_certificate(cn):
    """
    Renew a node certificate:
      1) generate a new CSR using the SAME key and node .conf
      2) have the CA sign it into CN.crt (overwrites existing after backup)
    """
    key_path  = os.path.join(CERT_DIR, f"{cn}.key")
    conf_path = os.path.join(CERT_DIR, f"{cn}.conf")
    csr_path  = os.path.join(CERT_DIR, f"{cn}.csr")
    crt_path  = os.path.join(CERT_DIR, f"{cn}.crt")

    if not os.path.exists(key_path):
        raise FileNotFoundError(f"Missing key: {key_path}")
    if not os.path.exists(conf_path):
        raise FileNotFoundError(f"Missing conf: {conf_path}")
    if not os.path.exists(CA_CONF_PATH):
        raise FileNotFoundError(f"Missing CA conf: {CA_CONF_PATH}")

    # 0) backup current cert (optional but handy)
    if os.path.exists(crt_path):
        ts = int(time.time())
        backup = os.path.join(CERT_DIR, f"{cn}_{ts}.bak.crt")
        try:
            os.replace(crt_path, backup)
            print(f"[BACKUP] Moved old cert to: {backup}")
        except Exception as e:
            print(f"[WARN] Could not backup old cert: {e}")

    # 1) New CSR (same key + same node conf)
    run([
        OPENSSL_PATH, "req",
        "-new",
        "-key", key_path,
        "-out", csr_path,
        "-config", conf_path
    ])

    # 2) CA signs CSR into a fresh CRT using the node's conf for -extfile
    run([
        OPENSSL_PATH, "ca",
        "-config", CA_CONF_PATH,
        "-in", csr_path,
        "-out", crt_path,
        "-days", DEFAULT_DAYS,
        "-extensions", EXT_SECTION,
        "-extfile", conf_path,
        "-batch"  # non-interactive
    ])

    # Reload this CN’s expiry and update cache
    try:
        with open(crt_path, "rb") as f:
            cert = x509.load_pem_x509_certificate(f.read(), default_backend())
        new_expiry = cert.not_valid_after_utc
        cert_expirations[cn] = new_expiry
        print(f"[RENEWED] {cn} new expiry: {new_expiry.isoformat()} (UTC) | {new_expiry.astimezone(LOCAL_TZ).isoformat()} ({LOCAL_TZ.key})")
        purge_old_backups(cn)   
    except Exception as e:
        print(f"[ERROR] Renewed but failed to parse new cert for {cn}: {e}")

def human_secs(s):
    s = int(s)
    sign = "-" if s < 0 else ""
    s = abs(s)
    h, r = divmod(s, 3600); m, r = divmod(r, 60)
    return f"{sign}{h:02d}:{m:02d}:{r:02d}"

BACKUP_KEEP_LAST = 0

def purge_old_backups(cn: str, keep_last: int = BACKUP_KEEP_LAST):
    """
    Delete old backup certs for this CN from the node CERT_DIR.
    We consider backups named either *.crt.bak or *.bak.crt.
    """
    patterns = [
        os.path.join(CERT_DIR, f"{cn}_*.crt.bak"),
        os.path.join(CERT_DIR, f"{cn}_*.bak.crt"),
    ]
    files = []
    for pat in patterns:
        files.extend(glob.glob(pat))

    # newest first by mtime
    files.sort(key=lambda p: os.path.getmtime(p), reverse=True)

    for f in files[keep_last:]:
        try:
            os.remove(f)
            print(f"[CLEAN] Deleted backup: {f}")
        except Exception as e:
            print(f"[CLEAN-ERROR] {f}: {e}")

def delete_leftover_csr(cn: str):
    csr = os.path.join(CERT_DIR, f"{cn}.csr")
    if os.path.exists(csr):
        try:
            os.remove(csr)
            print(f"[CLEAN] Deleted CSR: {csr}")
        except Exception as e:
            print(f"[CLEAN-ERROR] {csr}: {e}")

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--force-renew",
        nargs="*",
        default=[],
        dest="force_renew",
        help="CNs to renew immediately (testing). Example: --force-renew GCS2 CMD"
    )
    args = parser.parse_args()

    print("[INIT] Loading current certificate expirations…")
    load_cert_expirations()

    # Simple loop: check every CHECK_EVERY_SEC
    while True:
        try:
            now_utc = datetime.now(timezone.utc)
            now_local = now_utc.astimezone(LOCAL_TZ)
            print(f"[LOOP] now: {now_utc.isoformat()} (UTC) | {now_local.isoformat()} ({LOCAL_TZ.key}) | threshold={RENEW_THRESHOLD_SEC}s")

            # Scan for any new/changed certs each cycle to stay in sync
            load_cert_expirations()

            for cn, expiry in list(cert_expirations.items()):
                # Force mode: renew immediately for testing
                if cn in args.force_renew:
                    print(f"[TEST] Forcing renewal for {cn}")
                    try:
                        renew_certificate(cn)
                    except subprocess.CalledProcessError as e:
                        print(f"[OPENSSL-ERROR] Force renewal for {cn} failed: {e}")
                    except Exception as e:
                        print(f"[ERROR] Force renewal for {cn} failed: {e}")
                    continue

                secs = tte_seconds(expiry)

                # Informative countdown up to 24h
                if secs <= 86400:
                    exp_local = expiry.astimezone(LOCAL_TZ)
                    print(f"[TTE] {cn}: {human_secs(secs)} left | expires {expiry.isoformat()} (UTC) / {exp_local.isoformat()} ({LOCAL_TZ.key})")

                # Renew if within threshold
                if secs <= RENEW_THRESHOLD_SEC:
                    if secs <= 0:
                        print(f"[ALERT] {cn} EXPIRED {human_secs(secs)} ago — renewing…")
                    else:
                        print(f"[INFO] {cn} expiring in {human_secs(secs)} (≤ {RENEW_THRESHOLD_SEC}s) — renewing…")
                    try:
                        renew_certificate(cn)
                    except subprocess.CalledProcessError as e:
                        print(f"[OPENSSL-ERROR] Renewal for {cn} failed: {e}")
                    except Exception as e:
                        print(f"[ERROR] Renewal for {cn} failed: {e}")

        except KeyboardInterrupt:
            print("\n[EXIT] Stopping renewal monitor.")
            break
        except Exception as e:
            print(f"[LOOP-ERROR] {e}")

        time.sleep(CHECK_EVERY_SEC)

if __name__ == "__main__":
    main()
