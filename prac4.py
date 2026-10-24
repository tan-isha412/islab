# =====================================================================================
#  SECURE HEALTH DATA EXCHANGE   (Hospital / Researcher / Auditor)
#
#  Hospital  : DH session key (Lab 3) -> AES-256-CBC note (Lab 2), Paillier cost (Lab 7),
#              HMAC diagnosis token (Lab 8), SHA-256 hash (Lab 5), RSA sign (Lab 6) -> store.
#  Researcher: verify RSA sig + SHA-256, search by diagnosis token, homomorphically
#              total the Paillier costs for a diagnosis, decrypt ONLY the total.
#  Auditor   : verify sig + hash, Bell-LaPadula read check (Lab 4), revoke/renew the
#              hospital key, audit log. NEVER decrypts notes or costs.
#
#  python prac4.py        -> menu-driven
#  python prac4.py test   -> self-test (ALL PASSED)
# =====================================================================================
import time, json, os, sys, math, secrets, random, hashlib, hmac
from Crypto.Cipher import AES
from Crypto.Random import get_random_bytes
from Crypto.Util.number import getPrime, GCD
from Crypto.Util.Padding import pad, unpad
from Crypto.Protocol.KDF import PBKDF2
from Crypto.Hash import SHA256 as _SHA256

STORE = "health.json"
KEYS = "health_keys.json"
AUDIT = "health_audit.log"


# =====================================================================================
# HELPERS
# =====================================================================================
def timestamp():
    return time.strftime("%Y-%m-%d %H:%M:%S")


def sha256(data):                                  # bytes -> hex
    return hashlib.sha256(data).hexdigest()


# ---- Lab 3: Diffie-Hellman session key (hospital <-> exchange) ----
def dh_params(bits=256):
    return getPrime(bits), 2


def dh_keypair(p, g):
    a = random.randint(2, p - 2)
    return a, pow(g, a, p)


def dh_shared(their_pub, my_priv, p):
    return pow(their_pub, my_priv, p)


# ---- Lab 2: AES-256-CBC ----
def aes256_encrypt(key, data):
    iv = get_random_bytes(16)
    return iv, AES.new(key, AES.MODE_CBC, iv).encrypt(pad(data, 16))


def aes256_decrypt(key, iv, ct):
    return unpad(AES.new(key, AES.MODE_CBC, iv).decrypt(ct), 16)


# ---- Lab 7: Paillier ----
def L(u, n):
    return (u - 1) // n


def paillier_keygen(bits=512):
    while True:
        p, q = getPrime(bits // 2), getPrime(bits // 2)
        if p != q and GCD(p * q, (p - 1) * (q - 1)) == 1:
            break
    n = p * q
    lam = (p - 1) * (q - 1) // math.gcd(p - 1, q - 1)
    g = n + 1
    mu = pow(L(pow(g, lam, n * n), n), -1, n)
    return (n, g), (lam, mu, n)


def paillier_encrypt(m, pub):
    n, g = pub
    m %= n
    while True:
        r = secrets.randbelow(n - 1) + 1
        if math.gcd(r, n) == 1:
            break
    return (pow(g, m, n * n) * pow(r, n, n * n)) % (n * n)


def paillier_decrypt(c, priv):
    lam, mu, n = priv
    return (L(pow(c, lam, n * n), n) * mu) % n


def paillier_add(c1, c2, pub):
    n, _ = pub
    return (c1 * c2) % (n * n)


# ---- Lab 6: RSA signature ----
def rsa_keygen(bits=1024, e=65537):
    while True:
        p, q = getPrime(bits // 2), getPrime(bits // 2)
        if p != q and math.gcd(e, (p - 1) * (q - 1)) == 1:
            break
    n = p * q
    return (n, e), (n, pow(e, -1, (p - 1) * (q - 1)))


def rsa_sign(message, priv):                       # message bytes
    n, d = priv
    h = int(sha256(message), 16) % n
    return pow(h, d, n)


def rsa_verify(message, sig, pub):
    n, e = pub
    h = int(sha256(message), 16) % n
    return pow(sig, e, n) == h


# ---- Lab 8: deterministic diagnosis token ----
def diag_token(index_key, word):
    return hmac.new(index_key, word.lower().encode(), hashlib.sha256).hexdigest()


# ---- Lab 4: Bell-LaPadula ----
LEVELS = {"PUBLIC": 0, "CONFIDENTIAL": 1, "SECRET": 2, "TOPSECRET": 3}


def blp_can_read(subject_level, object_level):     # no read up: S >= O
    return LEVELS[subject_level] >= LEVELS[object_level]


# =====================================================================================
# WHAT GETS HASHED / SIGNED
# =====================================================================================
def record_payload(rec):
    return (f"{rec['id']}|{rec['patient']}|{rec['note']}|{rec['iv']}|{rec['cost']}|"
            f"{rec['diag_token']}|{rec['level']}|{rec['timestamp']}").encode()


# =====================================================================================
# RBAC
# =====================================================================================
USER_ROLES = {"hos": "hospital", "res": "researcher", "aud": "auditor"}
USER_CLEARANCE = {"hos": "SECRET", "res": "SECRET", "aud": "CONFIDENTIAL"}   # for BLP demo
ROLE_PERMS = {
    "hospital":   {"add", "view"},
    "researcher": {"verify", "search", "aggregate"},
    "auditor":    {"verify", "revoke", "renew", "blp"},        # never 'decrypt'
}


def can(user, perm):
    return perm in ROLE_PERMS.get(USER_ROLES.get(user), set())


# =====================================================================================
# PERSISTENT STORE + KEYS + AUDIT
# =====================================================================================
def load_records():
    if not os.path.exists(STORE):
        return []
    with open(STORE, "r", encoding="utf-8") as f:
        return json.load(f)


def save_records(records):
    with open(STORE, "w", encoding="utf-8") as f:
        json.dump(records, f, indent=2)


def audit(action, result):
    line = f"{timestamp()} | {action} | {result}"
    with open(AUDIT, "a", encoding="utf-8") as f:
        f.write(line + "\n")
    print("[AUDIT]", line)


def load_or_create_keys():
    if os.path.exists(KEYS):
        with open(KEYS) as f:
            k = json.load(f)
        return (bytes.fromhex(k["session"]), bytes.fromhex(k["index_key"]),
                tuple(k["paill_pub"]), tuple(k["paill_priv"]),
                tuple(k["rsa_pub"]), tuple(k["rsa_priv"]), k["revoked"])
    # Lab 3: establish the DH session key between hospital and exchange
    p, g = dh_params(256)
    a, A = dh_keypair(p, g)                         # hospital side
    b, B = dh_keypair(p, g)                         # exchange side
    shared = dh_shared(B, a, p)                     # == dh_shared(A, b, p)
    session_key = PBKDF2(str(shared), b"health-salt", 32, count=100000, hmac_hash_module=_SHA256)
    index_key = get_random_bytes(16)
    paill_pub, paill_priv = paillier_keygen(512)
    rsa_pub, rsa_priv = rsa_keygen(1024)
    _save_keys(session_key, index_key, paill_pub, paill_priv, rsa_pub, rsa_priv, False)
    return session_key, index_key, paill_pub, paill_priv, rsa_pub, rsa_priv, False


def _save_keys(session_key, index_key, paill_pub, paill_priv, rsa_pub, rsa_priv, revoked):
    with open(KEYS, "w") as f:
        json.dump({"session": session_key.hex(), "index_key": index_key.hex(),
                   "paill_pub": list(paill_pub), "paill_priv": list(paill_priv),
                   "rsa_pub": list(rsa_pub), "rsa_priv": list(rsa_priv),
                   "revoked": revoked}, f)


# =====================================================================================
# ROLE ACTIONS
# =====================================================================================
def hospital_add(user, patient, note, diagnosis, cost, level, keys):
    if not can(user, "add"):
        raise PermissionError(f"{user} may not add records")
    session_key, index_key, paill_pub, _, _, rsa_priv, revoked = keys
    if revoked:
        raise PermissionError("hospital key is revoked -- cannot submit")
    iv, ct = aes256_encrypt(session_key, note.encode())                 # Lab 2
    rec = {"id": len(load_records()) + 1, "patient": patient,
           "note": ct.hex(), "iv": iv.hex(),
           "cost": str(paillier_encrypt(cost, paill_pub)),              # Lab 7
           "diag_token": diag_token(index_key, diagnosis),             # Lab 8
           "level": level, "timestamp": timestamp()}
    payload = record_payload(rec)
    rec["hash"] = sha256(payload)                                       # Lab 5
    rec["sign"] = rsa_sign(payload, rsa_priv)                           # Lab 6
    records = load_records(); records.append(rec); save_records(records)
    print(f"[STORED] record {rec['id']} patient={patient} level={level} "
          f"diag_token={rec['diag_token'][:12]}... {rec['timestamp']}")
    return rec


def hospital_view(user):
    if not can(user, "view"):
        raise PermissionError(f"{user} may not view")
    recs = load_records()
    print(f"{len(recs)} record(s):")
    for r in recs:
        print(f"  id={r['id']} patient={r['patient']} note=<AES> cost=<Paillier> "
              f"level={r['level']} {r['timestamp']}")


def _verify(rec, rsa_pub):
    payload = record_payload(rec)
    hash_ok = sha256(payload) == rec["hash"]
    sig_ok = rsa_verify(payload, rec["sign"], rsa_pub)
    return hash_ok, sig_ok


def researcher_verify(user, rec_id, keys):
    if not can(user, "verify"):
        raise PermissionError(f"{user} may not verify")
    rsa_pub = keys[4]
    rec = next((r for r in load_records() if r["id"] == rec_id), None)
    if not rec:
        print("  no such record"); return
    hash_ok, sig_ok = _verify(rec, rsa_pub)
    print(f"  record {rec_id}: integrity={'PASS' if hash_ok else 'FAIL'}, "
          f"signature={'VALID' if sig_ok else 'INVALID'}")
    return hash_ok and sig_ok


def researcher_search(user, diagnosis, keys):
    if not can(user, "search"):
        raise PermissionError(f"{user} may not search")
    tok = diag_token(keys[1], diagnosis)
    hits = [r["id"] for r in load_records() if r["diag_token"] == tok]
    print(f"  diagnosis '{diagnosis}' -> record ids {hits} (contents stay encrypted)")
    return hits


def researcher_aggregate(user, diagnosis, keys):
    if not can(user, "aggregate"):
        raise PermissionError(f"{user} may not aggregate")
    _, index_key, paill_pub, paill_priv, rsa_pub, _, _ = keys
    tok = diag_token(index_key, diagnosis)
    enc_total, used = None, []
    for rec in load_records():
        if rec["diag_token"] != tok:
            continue
        if not all(_verify(rec, rsa_pub)):                    # verify before using
            print(f"  record {rec['id']} TAMPERED, skipping"); continue
        c = int(rec["cost"])
        enc_total = c if enc_total is None else paillier_add(enc_total, c, paill_pub)
        used.append(rec["id"])
    if enc_total is None:
        print(f"  no valid records for '{diagnosis}'"); return None
    total = paillier_decrypt(enc_total, paill_priv)           # decrypt ONLY the total
    print(f"  diagnosis '{diagnosis}' records {used} -> TOTAL treatment cost = {total}")
    return total


def auditor_verify_all(user, keys):
    if not can(user, "verify"):
        raise PermissionError(f"{user} may not audit")
    rsa_pub = keys[4]
    for rec in load_records():
        hash_ok, sig_ok = _verify(rec, rsa_pub)
        verdict = "VALID" if (hash_ok and sig_ok) else "INVALID"
        audit(f"VERIFY record {rec['id']}", verdict)


def auditor_blp_check(user, rec_id):
    """Bell-LaPadula read check (no read up). Does NOT decrypt -- only a policy decision."""
    if not can(user, "blp"):
        raise PermissionError(f"{user} may not run access checks")
    rec = next((r for r in load_records() if r["id"] == rec_id), None)
    if not rec:
        print("  no such record"); return
    for who, clr in USER_CLEARANCE.items():
        allowed = blp_can_read(clr, rec["level"])
        print(f"  {who} ({clr}) read record {rec_id} ({rec['level']}): "
              f"{'ALLOWED' if allowed else 'DENIED (no read up)'}")


def auditor_revoke(user, keys):
    if not can(user, "revoke"):
        raise PermissionError(f"{user} may not revoke")
    sk, ik, pp, ppr, rp, rpr, _ = keys
    _save_keys(sk, ik, pp, ppr, rp, rpr, True)
    audit("REVOKE hospital key", "revoked")
    return load_or_create_keys()


def auditor_renew(user, keys):
    if not can(user, "renew"):
        raise PermissionError(f"{user} may not renew")
    sk, ik, pp, ppr, _, _, _ = keys
    rp, rpr = rsa_keygen(1024)                                # fresh signing key, un-revoke
    _save_keys(sk, ik, pp, ppr, rp, rpr, False)
    audit("RENEW hospital key", "new RSA key issued")
    return load_or_create_keys()


def tamper(rec_id):
    records = load_records()
    for rec in records:
        if rec["id"] == rec_id:
            ct = bytearray(bytes.fromhex(rec["note"])); ct[0] ^= 0xFF
            rec["note"] = bytes(ct).hex()
    save_records(records)
    print(f"[TAMPERED] flipped a byte in record {rec_id}")


# =====================================================================================
# MENU-DRIVEN
# =====================================================================================
def menu():
    keys = load_or_create_keys()
    print("Health Exchange. Users: hos (hospital), res (researcher), aud (auditor)")
    while True:
        user = input("\nlogin as (hos/res/aud, or 'quit'): ").strip()
        if user == "quit":
            break
        role = USER_ROLES.get(user)
        if role is None:
            print("unknown user"); continue
        print(f"--- {user} : {role} ---")

        if role == "hospital":
            while True:
                print("1. add record   2. view all   3. tamper a record   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    patient = input("Patient ID: ")
                    note = input("Clinical note: ")
                    diag = input("Diagnosis keyword: ")
                    cost = int(input("Treatment cost: "))
                    level = input("Classification (PUBLIC/CONFIDENTIAL/SECRET/TOPSECRET): ").strip().upper() or "SECRET"
                    try:
                        hospital_add(user, patient, note, diag, cost, level, keys)
                    except PermissionError as e:
                        print("ERROR:", e)
                elif c == "2":
                    hospital_view(user)
                elif c == "3":
                    tamper(int(input("record id: ")))

        elif role == "researcher":
            while True:
                print("1. verify a record   2. search by diagnosis   3. total cost by diagnosis   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    researcher_verify(user, int(input("record id: ")), keys)
                elif c == "2":
                    researcher_search(user, input("diagnosis: "), keys)
                elif c == "3":
                    researcher_aggregate(user, input("diagnosis: "), keys)

        elif role == "auditor":
            while True:
                print("1. verify all   2. Bell-LaPadula read check   3. revoke hospital key   "
                      "4. renew hospital key   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    auditor_verify_all(user, keys)
                elif c == "2":
                    auditor_blp_check(user, int(input("record id: ")))
                elif c == "3":
                    keys = auditor_revoke(user, keys)
                elif c == "4":
                    keys = auditor_renew(user, keys)


# =====================================================================================
# SELF-TEST
# =====================================================================================
def self_test():
    global STORE, KEYS, AUDIT
    STORE, KEYS, AUDIT = "._h.json", "._hk.json", "._ha.log"
    for f in (STORE, KEYS, AUDIT):
        if os.path.exists(f):
            os.remove(f)
    keys = load_or_create_keys()

    hospital_add("hos", "P001", "high blood sugar", "diabetes", 5000, "SECRET", keys)
    hospital_add("hos", "P002", "chest pain", "cardiac", 8000, "SECRET", keys)
    hospital_add("hos", "P003", "insulin therapy", "diabetes", 3000, "CONFIDENTIAL", keys)

    rsa_pub = keys[4]
    assert all(all(_verify(r, rsa_pub)) for r in load_records())        # all genuine

    # search + homomorphic total by diagnosis (diabetes = 5000 + 3000 = 8000)
    assert researcher_search("res", "diabetes", keys) == [1, 3]
    assert researcher_aggregate("res", "diabetes", keys) == 8000
    assert researcher_aggregate("res", "cardiac", keys) == 8000

    # RBAC: auditor cannot aggregate, hospital cannot verify-search
    for bad in [lambda: researcher_aggregate("aud", "diabetes", keys),
                lambda: researcher_search("hos", "diabetes", keys)]:
        try:
            bad(); raise AssertionError("RBAC not enforced")
        except PermissionError:
            pass

    # Bell-LaPadula: aud (CONFIDENTIAL) cannot read a SECRET record (no read up)
    assert blp_can_read("SECRET", "SECRET") and not blp_can_read("CONFIDENTIAL", "SECRET")

    # tamper record 1 -> excluded -> diabetes total drops to 3000
    tamper(1)
    assert not all(_verify(load_records()[0], rsa_pub))
    assert researcher_aggregate("res", "diabetes", keys) == 3000

    # revoke -> hospital cannot submit; renew -> can again (new RSA key)
    keys = auditor_revoke("aud", keys)
    try:
        hospital_add("hos", "P004", "x", "flu", 100, "PUBLIC", keys)
        raise AssertionError("revoked key still worked")
    except PermissionError:
        pass
    keys = auditor_renew("aud", keys)
    hospital_add("hos", "P004", "fever", "flu", 100, "PUBLIC", keys)
    assert researcher_aggregate("res", "flu", keys) == 100

    for f in (STORE, KEYS, AUDIT):
        os.remove(f)
    print("ALL PASSED")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "test":
        self_test()
    else:
        menu()
