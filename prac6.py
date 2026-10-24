# =====================================================================================
#  SECURE EXAM RESULT PORTAL   (Faculty / Exam Coordinator / Controller)
#    Faculty    : AES-256 encrypt Subject, Paillier encrypt Marks, HMAC subject token,
#                 MD5 hash, RSA sign -> store. Can view all records.
#    ExamCoord  : verify RSA sig + MD5, view the AES-256-decrypted Subject.
#    Controller : group by subject token, homomorphically total the Marks per subject,
#                 decrypt ONLY each subject's total, and compute the subject-wise average.
#
#  python prac6.py        -> menu-driven
#  python prac6.py test   -> self-test (ALL PASSED)
# =====================================================================================
import time, json, os, sys, random, hashlib, hmac, math, secrets
from Crypto.Cipher import AES
from Crypto.Random import get_random_bytes
from Crypto.Util.number import getPrime, GCD        # FIX 1: GCD was used in paillier_keygen but never imported
from Crypto.Util.Padding import pad, unpad

STORE = "studs.json"
KEYS = "studs_keys.json"                             # FIX 10: keys persisted so old records stay verifiable after restart


# =====================================================================================
# CRYPTO HELPERS  (unchanged -- these were correct)
# =====================================================================================
def timestamp():
    return time.strftime("%Y-%m-%d %H:%M:%S")


def md5(data):                                       # data must be BYTES
    return hashlib.md5(data).hexdigest()


def aes256_encrypt(key, data):
    iv = get_random_bytes(16)
    return iv, AES.new(key, AES.MODE_CBC, iv).encrypt(pad(data, 16))


def aes256_decrypt(key, iv, ct):
    return unpad(AES.new(key, AES.MODE_CBC, iv).decrypt(ct), 16)


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


def paillier_add(c1, c2, pub):                       # E(a)*E(b) -> E(a+b)
    n, _ = pub
    return (c1 * c2) % (n * n)


def rsa_keygen(bits=1024, e=65537):
    while True:
        p, q = getPrime(bits // 2), getPrime(bits // 2)
        if p != q and math.gcd(e, (p - 1) * (q - 1)) == 1:
            break
    n = p * q
    return (n, e), (n, pow(e, -1, (p - 1) * (q - 1)))    # FIX: return only pub, priv (menu unpacked 3 values -> keep 2 here)


def rsa_sign_manual(message, priv):                  # message is BYTES
    n, d = priv
    return pow(int(hashlib.sha256(message).hexdigest(), 16) % n, d, n)


def rsa_verify_manual(message, sig, pub):
    n, e = pub
    return pow(sig, e, n) == int(hashlib.sha256(message).hexdigest(), 16) % n


# FIX 5: the SSE "token" you were missing -- a DETERMINISTIC HMAC of the subject so the
#        controller can GROUP records by subject (AES ciphertext is random, can't group on it)
def subject_token(index_key, subject):
    return hmac.new(index_key, subject.lower().encode(), hashlib.sha256).hexdigest()


# FIX 4: payload now includes the subject_token too, so tampering with it is also caught
def record_payload(rec):
    return (f"{rec['id']}|{rec['subject-name']}|{rec['iv']}|{rec['marks']}|"
            f"{rec['subject_token']}|{rec['timestamp']}").encode()


# FIX 9: removed the broken sse_setup/_aes_enc/sse_build_index/sse_search --
#        grouping is done by the plaintext subject_token above (no AES-on-index needed).


# =====================================================================================
# RBAC
# =====================================================================================
USER_ROLES = {"fac": "faculty", "examcoord": "exam_coordinator", "con": "controller"}
ROLE_PERMS = {
    "faculty":          {"add", "view"},             # FIX 2: key was "student" -> faculty had NO perms
    "exam_coordinator": {"verify", "viewsub"},
    "controller":       {"verify", "calc"},
}


def can(user, perm):
    return perm in ROLE_PERMS.get(USER_ROLES.get(user), set())


# =====================================================================================
# STORE + KEYS
# =====================================================================================
def load_records():
    if not os.path.exists(STORE):
        return []
    with open(STORE, "r", encoding="utf-8") as f:
        return json.load(f)


def save_records(records):
    with open(STORE, "w", encoding="utf-8") as f:
        json.dump(records, f, indent=2)


def load_or_create_keys():                           # FIX 10: persistence
    if os.path.exists(KEYS):
        with open(KEYS) as f:
            k = json.load(f)
        return (bytes.fromhex(k["aes"]), bytes.fromhex(k["index_key"]),
                tuple(k["paill_pub"]), tuple(k["paill_priv"]),
                tuple(k["rsa_pub"]), tuple(k["rsa_priv"]))
    aes_key = get_random_bytes(32)                   # AES-256
    index_key = get_random_bytes(16)
    paill_pub, paill_priv = paillier_keygen(512)
    rsa_pub, rsa_priv = rsa_keygen(1024)
    with open(KEYS, "w") as f:
        json.dump({"aes": aes_key.hex(), "index_key": index_key.hex(),
                   "paill_pub": list(paill_pub), "paill_priv": list(paill_priv),
                   "rsa_pub": list(rsa_pub), "rsa_priv": list(rsa_priv)}, f)
    return aes_key, index_key, paill_pub, paill_priv, rsa_pub, rsa_priv


# =====================================================================================
# ROLE ACTIONS
# =====================================================================================
def faculty_add(user, sid, subname, marks, aes_key, index_key, paill_pub, rsa_priv):
    if not can(user, "add"):
        raise PermissionError(f"{user} may not add records")
    iv, ct = aes256_encrypt(aes_key, subname.encode())      # FIX 3: encrypt BYTES (subname.encode())
    enc_marks = paillier_encrypt(marks, paill_pub)
    rec = {"id": sid, "subject-name": ct.hex(), "iv": iv.hex(),
           "marks": str(enc_marks),                         # FIX 3: store the Paillier int as str (JSON-safe)
           "subject_token": subject_token(index_key, subname), "timestamp": timestamp()}
    payload = record_payload(rec)
    rec["hash"] = md5(payload)                              # FIX 3: md5 of the PAYLOAD BYTES (old md5(rec) on a dict crashed)
    rec["sign"] = rsa_sign_manual(payload, rsa_priv)        # FIX 3: sign the payload bytes (old rsa_sign_manual(h,..) crashed)
    records = load_records(); records.append(rec); save_records(records)
    # FIX 3: removed the old print's {r % 10000},{s % 10000} (ElGamal leftover; RSA sign is one int)
    print(f"[STORED] id={sid}  hash={rec['hash'][:16]}...  {rec['timestamp']}")
    return rec


def fac_view(user):
    if not can(user, "view"):
        raise PermissionError(f"{user} may not view records")
    records = load_records()
    if not records:
        print("No records found."); return
    print(f"Found {len(records)} records:")
    for rec in records:
        print(f"  id={rec['id']}  subject=<AES>  marks=<Paillier>  hash={rec['hash'][:12]}...  {rec['timestamp']}")


# FIX 6: _verify takes the RECORD and rebuilds the payload (callers wrongly passed record_payload(rec))
def _verify(rec, rsa_pub):
    payload = record_payload(rec)
    hash_ok = md5(payload) == rec["hash"]
    sig_ok = rsa_verify_manual(payload, rec["sign"], rsa_pub)
    return hash_ok, sig_ok


def exam_coordinator_verify(user, rec, rsa_pub):
    if not can(user, "verify"):                            # FIX 6: perm is "verify", not "decrypt"
        raise PermissionError(f"{user} may not verify")
    hash_ok, sig_ok = _verify(rec, rsa_pub)                # FIX 6: pass rec, not record_payload(rec)
    print(f"  integrity={'PASS' if hash_ok else 'FAIL'}  signature={'VALID' if sig_ok else 'INVALID'}")
    return hash_ok and sig_ok


def exam_coordinator_viewsub(user, rec, aes_key, rsa_pub):  # FIX 7: now receives rsa_pub (was using undefined `pub`)
    if not can(user, "viewsub"):
        raise PermissionError(f"{user} may not view subjects")
    hash_ok, sig_ok = _verify(rec, rsa_pub)
    print(f"  integrity={'PASS' if hash_ok else 'FAIL'}  signature={'VALID' if sig_ok else 'INVALID'}")
    if not (hash_ok and sig_ok):
        print("  -> verification FAILED, refusing to decrypt"); return ""
    # FIX 7: bytes.fromhex on iv + ciphertext before decrypting
    return aes256_decrypt(aes_key, bytes.fromhex(rec["iv"]), bytes.fromhex(rec["subject-name"])).decode()


# FIX 8: controller_calc fully rewritten -- group by subject_token, Paillier-add each
#        group's marks, decrypt only the group total, and compute total + average per subject.
def controller_calc(user, aes_key, rsa_pub, paill_pub, paill_priv):
    if not can(user, "calc"):                             # FIX 8: perm is "calc", not "sum"
        raise PermissionError(f"{user} may not compute totals")
    groups = {}
    for rec in load_records():
        hash_ok, sig_ok = _verify(rec, rsa_pub)           # verify before using
        if not (hash_ok and sig_ok):
            print(f"  record {rec['id']} TAMPERED, skipping"); continue
        tok = rec["subject_token"]
        c = int(rec["marks"])
        if tok not in groups:
            groups[tok] = {"enc": c, "count": 1, "sample": rec}
        else:
            groups[tok]["enc"] = paillier_add(groups[tok]["enc"], c, paill_pub)
            groups[tok]["count"] += 1
    if not groups:
        print("  no valid records"); return {}
    results = {}
    for info in groups.values():
        total = paillier_decrypt(info["enc"], paill_priv)             # decrypt ONLY the subject total
        count = info["count"]
        subject = aes256_decrypt(aes_key, bytes.fromhex(info["sample"]["iv"]),
                                 bytes.fromhex(info["sample"]["subject-name"])).decode()
        results[subject] = {"total": total, "average": total / count, "count": count}
        print(f"  {subject}: total={total}  average={total / count:.2f}  ({count} students)")
    return results


def tamper(rec_id):
    records = load_records()
    for rec in records:
        if str(rec["id"]) == str(rec_id):                 # FIX 11: compare as str (id is stored as the typed string)
            ct = bytearray(bytes.fromhex(rec["subject-name"])); ct[0] ^= 0xFF
            rec["subject-name"] = bytes(ct).hex()
    save_records(records)
    print(f"[TAMPERED] flipped a byte in record {rec_id}")


# =====================================================================================
# MENU-DRIVEN
# =====================================================================================
def menu():
    aes_key, index_key, paill_pub, paill_priv, rsa_pub, rsa_priv = load_or_create_keys()
    print("Exam Result Portal. Users: fac (faculty), examcoord (exam coordinator), con (controller)")
    while True:
        user = input("\nlogin as (fac/examcoord/con, or 'quit'): ").strip()
        if user == "quit":
            break
        role = USER_ROLES.get(user)
        if role is None:
            print("unknown user"); continue
        print(f"--- {user} : {role} ---")

        if role == "faculty":
            while True:
                print("1. add marks   2. view all   3. tamper a record   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    sid = input("student id: ")
                    sub = input("subject name: ")
                    marks = int(input("marks: "))
                    faculty_add(user, sid, sub, marks, aes_key, index_key, paill_pub, rsa_priv)
                elif c == "2":
                    fac_view(user)
                elif c == "3":
                    tamper(input("record id to tamper: "))

        elif role == "exam_coordinator":
            while True:
                print("1. verify signature   2. view decrypted subject   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    rid = input("record id: ")
                    rec = next((r for r in load_records() if str(r["id"]) == rid), None)
                    if rec:
                        print("VALID" if exam_coordinator_verify(user, rec, rsa_pub) else "INVALID")
                    else:
                        print("no such record")
                elif c == "2":
                    rid = input("record id: ")
                    rec = next((r for r in load_records() if str(r["id"]) == rid), None)
                    if rec:
                        sub = exam_coordinator_viewsub(user, rec, aes_key, rsa_pub)
                        print("subject:", sub if sub else "(refused)")
                    else:
                        print("no such record")

        elif role == "controller":
            while True:
                print("1. subject-wise total + average   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    controller_calc(user, aes_key, rsa_pub, paill_pub, paill_priv)


if __name__ == "__main__":
    menu()
