# =====================================================================================
#  SECURE MEDICAL REPORT ARCHIVE   (Doctor / Staff / Auditor)
#    Doctor : AES-256 encrypt the report text; for each keyword store HMAC(index_key,kw)
#             linked to the Report ID; SHA-256 hash + RSA sign; store (keys persisted).
#    Staff  : search by keyword token -> Report IDs; to OPEN a report, verify hash+sig,
#             THEN check this staff is AUTHORIZED for that patient, and only then decrypt.
#             (A valid signature proves integrity; it does NOT grant read permission.)
#    Auditor: verify hash+sig; if either fails show "tampered"; if valid, decrypt and
#             show the bytes as a HEX DUMP.
#
#  python prac10.py        -> menu-driven
#  python prac10.py test   -> self-test (ALL PASSED)
# =====================================================================================
import math, time, json, sys, hmac, os, hashlib
from Crypto.Cipher import AES
from Crypto.Random import get_random_bytes
from Crypto.Util.number import getPrime
from Crypto.Util.Padding import pad, unpad

STORE = "reports.json"
KEYS = "report_keys.json"


# =====================================================================================
# HELPERS
# =====================================================================================
def sha256(data):
    return hashlib.sha256(data).hexdigest()


def timestamp():
    return time.strftime("%Y-%m-%d %H:%M:%S")


def aes256_encrypt(key, data):                    # key = 32 bytes -> AES-256
    iv = get_random_bytes(16)
    return iv, AES.new(key, AES.MODE_CBC, iv).encrypt(pad(data, 16))


def aes256_decrypt(key, iv, ct):
    return unpad(AES.new(key, AES.MODE_CBC, iv).decrypt(ct), 16)


def rsa_keygen(bits=1024, e=65537):
    while True:
        p, q = getPrime(bits // 2), getPrime(bits // 2)
        if p != q and math.gcd(e, (p - 1) * (q - 1)) == 1:
            break
    n = p * q
    return (n, e), (n, pow(e, -1, (p - 1) * (q - 1)))      # (pub, priv)


def rsa_sign(message, priv):                      # message bytes
    n, d = priv
    return pow(int(sha256(message), 16) % n, d, n)


def rsa_verify(message, sig, pub):
    n, e = pub
    return pow(sig, e, n) == int(sha256(message), 16) % n


def kw_token(index_key, keyword):                 # deterministic HMAC token (normalize = lower+strip)
    return hmac.new(index_key, keyword.strip().lower().encode(), hashlib.sha256).hexdigest()


# =====================================================================================
# RBAC + AUTHORIZATION
#   RBAC = which role may do what.  AUTHORIZATION = which staff may read which patient.
#   The spec's key point: a valid signature proves integrity, NOT permission -> we check
#   authorization SEPARATELY, after verification, before decrypting.
# =====================================================================================
USER_ROLES = {"doc": "doctor", "stf": "staff", "aud": "auditor"}
ROLE_PERMS = {"doctor": {"add", "view"}, "staff": {"search", "open"}, "auditor": {"audit"}}
# patient access list: which patient IDs each staff user may read
STAFF_PATIENTS = {"stf": {"P1"}}                  # stf can read P1's reports, NOT P2's


def can(user, perm):
    return perm in ROLE_PERMS.get(USER_ROLES.get(user), set())


def authorized_for(user, pid):
    return pid in STAFF_PATIENTS.get(user, set())


# =====================================================================================
# STORE + KEYS
# =====================================================================================
def load_store():
    if not os.path.exists(STORE):
        return []
    with open(STORE, "r", encoding="utf-8") as f:
        return json.load(f)


def save_store(records):
    with open(STORE, "w", encoding="utf-8") as f:
        json.dump(records, f, indent=2)


def load_or_create_keys():
    if os.path.exists(KEYS):
        with open(KEYS) as f:
            k = json.load(f)
        return bytes.fromhex(k["aes"]), bytes.fromhex(k["index_key"]), tuple(k["rsa_pub"]), tuple(k["rsa_priv"])
    aes_key = get_random_bytes(32)                # AES-256
    index_key = get_random_bytes(16)
    rsa_pub, rsa_priv = rsa_keygen(1024)          # FIX: unpack the two pairs correctly
    with open(KEYS, "w") as f:
        json.dump({"aes": aes_key.hex(), "index_key": index_key.hex(),
                   "rsa_pub": list(rsa_pub), "rsa_priv": list(rsa_priv)}, f)   # FIX: save/load with the SAME names
    return aes_key, index_key, rsa_pub, rsa_priv


# what gets hashed/signed (rebuilt identically at verify time)
def payload(rec):
    return f"{rec['rid']}|{rec['pid']}|{rec['text']}|{rec['iv']}|{rec['tokens']}|{rec['timestamp']}".encode()


# =====================================================================================
# ROLE ACTIONS
# =====================================================================================
def doctor_add(user, rid, pid, text, keywords, aes_key, index_key, rsa_priv):
    if not can(user, "add"):
        raise PermissionError("not allowed")
    iv, ct = aes256_encrypt(aes_key, text.encode())
    tokens = [kw_token(index_key, kw) for kw in keywords]          # one HMAC token per keyword
    rec = {"rid": rid, "pid": pid, "text": ct.hex(), "iv": iv.hex(),
           "tokens": tokens, "timestamp": timestamp()}
    rec["hash"] = sha256(payload(rec))
    rec["sign"] = rsa_sign(payload(rec), rsa_priv)
    recs = load_store(); recs.append(rec); save_store(recs)
    print(f"[STORED] report {rid} (patient {pid}), {len(tokens)} keyword(s)")
    return rec


def doctor_view(user):
    if not can(user, "view"):
        raise PermissionError("not allowed")
    recs = load_store()
    print(f"{len(recs)} report(s):")
    for r in recs:
        print(f"  rid={r['rid']}  patient={r['pid']}  text=<AES>  hash={r['hash'][:12]}...  {r['timestamp']}")


def _verify(rec, rsa_pub):
    pl = payload(rec)
    return sha256(pl) == rec["hash"], rsa_verify(pl, rec["sign"], rsa_pub)


def staff_search(user, keyword, index_key):
    if not can(user, "search"):
        raise PermissionError("not allowed")
    tok = kw_token(index_key, keyword)
    hits = [r["rid"] for r in load_store() if tok in r["tokens"]]   # no need to store the keyword
    print(f"  keyword '{keyword}' -> reports {hits}")
    return hits


def staff_open(user, rid, aes_key, rsa_pub):
    if not can(user, "open"):
        raise PermissionError("not allowed")
    rec = next((r for r in load_store() if r["rid"] == rid), None)
    if not rec:
        print("  no such report"); return None
    # 1) verify integrity + authenticity
    hash_ok, sig_ok = _verify(rec, rsa_pub)
    print(f"  integrity={'PASS' if hash_ok else 'FAIL'}  signature={'VALID' if sig_ok else 'INVALID'}")
    if not (hash_ok and sig_ok):
        print("  -> verification failed, not decrypting"); return None
    # 2) SEPARATE authorization check (a valid signature does NOT grant read permission)
    if not authorized_for(user, rec["pid"]):
        print(f"  -> {user} is NOT authorized to read patient {rec['pid']}'s report"); return None
    # 3) only now decrypt
    text = aes256_decrypt(aes_key, bytes.fromhex(rec["iv"]), bytes.fromhex(rec["text"]))
    print("  report text:", text.decode())
    return text.decode()


def auditor_check(user, rid, aes_key, rsa_pub):
    if not can(user, "audit"):
        raise PermissionError("not allowed")
    rec = next((r for r in load_store() if r["rid"] == rid), None)
    if not rec:
        print("  no such report"); return
    hash_ok, sig_ok = _verify(rec, rsa_pub)
    if not (hash_ok and sig_ok):
        print(f"  report {rid}: TAMPERED / verification failed -> not shown"); return
    text = aes256_decrypt(aes_key, bytes.fromhex(rec["iv"]), bytes.fromhex(rec["text"]))
    print(f"  report {rid}: VALID -> hex dump: {text.hex()}")        # spec: show bytes in hexadecimal
    return text.hex()


def tamper(rid):
    recs = load_store()
    for rec in recs:
        if rec["rid"] == rid:
            ct = bytearray(bytes.fromhex(rec["text"])); ct[0] ^= 0xFF
            rec["text"] = bytes(ct).hex()
    save_store(recs)
    print(f"[TAMPERED] flipped a byte in report {rid}")


# =====================================================================================
# MENU-DRIVEN
# =====================================================================================
def menu():
    aes_key, index_key, rsa_pub, rsa_priv = load_or_create_keys()
    print("Medical Report Archive. Users: doc (doctor), stf (staff), aud (auditor)")
    while True:
        user = input("\nlogin as (doc/stf/aud, or 'quit'): ").strip()
        if user == "quit":
            break
        role = USER_ROLES.get(user)
        if role is None:
            print("unknown user"); continue
        print(f"--- {user} : {role} ---")

        if role == "doctor":
            while True:
                print("1. add report   2. view all   3. tamper a report   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    rid = input("Report ID: ")
                    pid = input("Patient ID: ")
                    text = input("Report text: ")
                    kws = [w for w in input("Keywords (comma separated): ").split(",") if w.strip()]
                    doctor_add(user, rid, pid, text, kws, aes_key, index_key, rsa_priv)
                elif c == "2":
                    doctor_view(user)
                elif c == "3":
                    tamper(input("Report ID to tamper: "))

        elif role == "staff":
            while True:
                print("1. search keyword   2. open a report (verify + authorize + decrypt)   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    staff_search(user, input("Keyword: "), index_key)
                elif c == "2":
                    staff_open(user, input("Report ID: "), aes_key, rsa_pub)

        elif role == "auditor":
            while True:
                print("1. audit a report (verify + hex dump if valid)   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    auditor_check(user, input("Report ID: "), aes_key, rsa_pub)


# =====================================================================================
# SELF-TEST
# =====================================================================================
def self_test():
    global STORE, KEYS
    STORE, KEYS = "._rep_test.json", "._repk_test.json"
    for f in (STORE, KEYS):
        if os.path.exists(f):
            os.remove(f)
    aes_key, index_key, rsa_pub, rsa_priv = load_or_create_keys()

    doctor_add("doc", "R1", "P1", "fever and cough", ["fever", "cough"], aes_key, index_key, rsa_priv)
    doctor_add("doc", "R2", "P2", "diabetes type 2", ["diabetes"], aes_key, index_key, rsa_priv)

    assert all(all(_verify(r, rsa_pub)) for r in load_store())
    # search by keyword token
    assert staff_search("stf", "fever", index_key) == ["R1"]
    assert staff_search("stf", "diabetes", index_key) == ["R2"]

    # staff opens R1 (P1 -> authorized) -> gets text
    assert staff_open("stf", "R1", aes_key, rsa_pub) == "fever and cough"
    # staff opens R2 (P2 -> NOT authorized) -> refused even though signature is valid
    assert staff_open("stf", "R2", aes_key, rsa_pub) is None

    # auditor hex dump of a valid report
    assert auditor_check("aud", "R1", aes_key, rsa_pub) == b"fever and cough".hex()

    # RBAC: staff cannot audit, doctor cannot open
    for bad in [lambda: auditor_check("stf", "R1", aes_key, rsa_pub),
                lambda: staff_open("doc", "R1", aes_key, rsa_pub)]:
        try:
            bad(); raise AssertionError("RBAC not enforced")
        except PermissionError:
            pass

    # tamper R1 -> verify fails, auditor reports tampered (returns None)
    tamper("R1")
    assert _verify(load_store()[0], rsa_pub) == (False, False)
    assert auditor_check("aud", "R1", aes_key, rsa_pub) is None

    # keys persist
    aes2, ik2, rp2, rpr2 = load_or_create_keys()
    assert aes2 == aes_key and _verify(load_store()[1], rp2) == (True, True)

    for f in (STORE, KEYS):
        os.remove(f)
    print("ALL PASSED")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "test":
        self_test()
    else:
        menu()
