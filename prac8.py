# =====================================================================================
#  SECURE DOCUMENT ARCHIVE   (Clerk / Lawyer / Compliance Officer)
#    Clerk     : AES-192 encrypt body, HMAC search token, SHA-256 hash, ElGamal sign -> store.
#    Lawyer    : search by keyword token, verify signature + hash, then decrypt the body.
#    Compliance: verify signatures + hashes, report VALID/INVALID, NEVER decrypt.
#
#  python prac8.py        -> menu-driven
#  python prac8.py test   -> self-test (ALL PASSED)
# =====================================================================================
import math, time, json, sys, hmac, os, random, hashlib        # FIX 1: added random (used by ElGamal)
from Crypto.Cipher import AES
from Crypto.Random import get_random_bytes
from Crypto.Util.number import getPrime                         # FIX 1: getPrime was used but never imported
from Crypto.Util.Padding import pad, unpad

path = "cases.json"
KEYS = "cases_keys.json"                                        # FIX 7: keys persisted so records stay verifiable after restart


# =====================================================================================
# HELPERS
# =====================================================================================
def sha256(data):                                              # data is bytes
    return hashlib.sha256(data).hexdigest()


def _hash_int(message, mod):                                   # FIX 2: this was used but never defined
    return int(sha256(message), 16) % mod


def timestamp():
    return time.strftime("%Y-%m-%d %H:%M:%S")


def load_store():
    if not os.path.exists(path):
        return []
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def save_store(records):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(records, f, indent=2)


def aes192_encrypt(key, data):                                # key = 24 bytes -> AES-192
    iv = get_random_bytes(16)
    return iv, AES.new(key, AES.MODE_CBC, iv).encrypt(pad(data, 16))   # FIX 3: block size is 16, not 14


def aes192_decrypt(key, iv, ct):
    return unpad(AES.new(key, AES.MODE_CBC, iv).decrypt(ct), 16)       # FIX 3: block size is 16, not 14


# ---- ElGamal digital signature ----
def elgamal_keygen(bits=256):
    p = getPrime(bits)
    g = 2
    x = random.randint(2, p - 2)
    return (p, g, pow(g, x, p)), x                             # public (p,g,y), private x


def elgamal_sign(message, p, g, x):
    while True:
        k = random.randint(2, p - 2)
        if math.gcd(k, p - 1) == 1:
            break
    r = pow(g, k, p)
    h = _hash_int(message, p)
    s = ((h - x * r) * pow(k, -1, p - 1)) % (p - 1)
    return r, s


def elgamal_verify(message, sig, p, g, y):
    r, s = sig
    if not 0 < r < p:
        return False
    h = _hash_int(message, p)
    return pow(g, h, p) == (pow(y, r, p) * pow(r, s, p)) % p


def sse_token(index_key, keyword):                            # deterministic search token
    return hmac.new(index_key, keyword.lower().encode(), hashlib.sha256).hexdigest()


# =====================================================================================
# RBAC
# =====================================================================================
ROLES = {"crk": "clerk", "lwyr": "lawyer", "comp": "compliance"}
PERMS = {
    "clerk":      {"add", "view"},                            # FIX 4: clerk also needs "view" (question: clerk views all)
    "lawyer":     {"search", "open"},
    "compliance": {"audit"},
}


def can(user, perm):
    return perm in PERMS.get(ROLES.get(user), set())


def payload(rec):                                             # FIX: renamed from t4_payload for clarity
    return f"{rec['id']}|{rec['body']}|{rec['iv']}|{rec['token']}|{rec['timestamp']}".encode()


# =====================================================================================
# KEYS (persistent)
# =====================================================================================
def load_or_create_keys():                                   # FIX 7
    if os.path.exists(KEYS):
        with open(KEYS) as f:
            k = json.load(f)
        return bytes.fromhex(k["aes"]), bytes.fromhex(k["index_key"]), tuple(k["eg_pub"]), k["eg_priv"]
    aes_key = get_random_bytes(24)                            # AES-192
    index_key = get_random_bytes(16)
    eg_pub, eg_priv = elgamal_keygen(256)
    with open(KEYS, "w") as f:
        json.dump({"aes": aes_key.hex(), "index_key": index_key.hex(),
                   "eg_pub": list(eg_pub), "eg_priv": eg_priv}, f)
    return aes_key, index_key, eg_pub, eg_priv


# =====================================================================================
# ROLE ACTIONS
# =====================================================================================
def clerk_add(user, doc_id, keyword, body, aes_key, index_key, eg_pub, eg_priv):
    if not can(user, "add"):
        raise PermissionError("not allowed")
    p, g, _ = eg_pub
    iv, ct = aes192_encrypt(aes_key, body.encode())
    rec = {"id": doc_id, "body": ct.hex(), "iv": iv.hex(),     # FIX 5: use the entered Document ID (was ignoring it)
           "token": sse_token(index_key, keyword), "timestamp": timestamp()}
    rec["hash"] = sha256(payload(rec))
    rec["sign"] = elgamal_sign(payload(rec), p, g, eg_priv)
    recs = load_store(); recs.append(rec); save_store(recs)
    print(f"[STORED] record {rec['id']}")
    return rec


def clerk_view(user):
    if not can(user, "view"):
        raise PermissionError("not allowed")
    records = load_store()
    if not records:
        print("No records found."); return
    print(f"Found {len(records)} records:")
    for rec in records:
        print(f"  id={rec['id']}  body=<AES>  token=<HMAC>  hash={rec['hash'][:12]}...  {rec['timestamp']}")


def _verify(rec, eg_pub):
    p, g, y = eg_pub
    pl = payload(rec)
    return sha256(pl) == rec["hash"], elgamal_verify(pl, tuple(rec["sign"]), p, g, y)


# FIX 6: merged the empty lawyer_search stub and the broken t4_search into ONE function;
#        fixed load_store() (no arg), _verify (was t4_verify), aes192_decrypt (was aes_decrypt).
def lawyer_search(user, keyword, index_key, aes_key, eg_pub):
    if not can(user, "search"):
        raise PermissionError("not allowed")
    tok = sse_token(index_key, keyword)
    found = False
    for rec in load_store():
        if rec["token"] == tok:
            found = True
            hash_ok, sig_ok = _verify(rec, eg_pub)
            print(f"  match id={rec['id']}  verify={'OK' if hash_ok and sig_ok else 'FAIL'}")
            if hash_ok and sig_ok:
                body = aes192_decrypt(aes_key, bytes.fromhex(rec["iv"]), bytes.fromhex(rec["body"]))
                print("    body:", body.decode())
            else:
                print("    verification failed -> not decrypting")
    if not found:
        print(f"  no documents match '{keyword}'")


def compliance_audit(user, eg_pub):
    if not can(user, "audit"):
        raise PermissionError("not allowed")
    for rec in load_store():                                  # verify only, NEVER decrypt
        hash_ok, sig_ok = _verify(rec, eg_pub)
        print(f"  record {rec['id']}: {'VALID' if hash_ok and sig_ok else 'INVALID'}  ({timestamp()})")


def tamper(doc_id):
    records = load_store()
    for rec in records:
        if str(rec["id"]) == str(doc_id):
            ct = bytearray(bytes.fromhex(rec["body"])); ct[0] ^= 0xFF
            rec["body"] = bytes(ct).hex()
    save_store(records)
    print(f"[TAMPERED] flipped a byte in record {doc_id}")


# =====================================================================================
# MENU-DRIVEN  (FIX 8: the question requires a menu -- this was missing)
# =====================================================================================
def menu():
    aes_key, index_key, eg_pub, eg_priv = load_or_create_keys()
    print("Document Archive. Users: crk (clerk), lwyr (lawyer), comp (compliance officer)")
    while True:
        user = input("\nlogin as (crk/lwyr/comp, or 'quit'): ").strip()
        if user == "quit":
            break
        role = ROLES.get(user)
        if role is None:
            print("unknown user"); continue
        print(f"--- {user} : {role} ---")

        if role == "clerk":
            while True:
                print("1. add document   2. view all   3. tamper a record   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    did = input("Document ID: ")
                    kw = input("Keyword: ")
                    body = input("Document body: ")
                    clerk_add(user, did, kw, body, aes_key, index_key, eg_pub, eg_priv)
                elif c == "2":
                    clerk_view(user)
                elif c == "3":
                    tamper(input("Document ID to tamper: "))

        elif role == "lawyer":
            while True:
                print("1. search keyword (verify + decrypt matches)   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    lawyer_search(user, input("Keyword: "), index_key, aes_key, eg_pub)

        elif role == "compliance":
            while True:
                print("1. audit all documents (verify only)   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    compliance_audit(user, eg_pub)


# =====================================================================================
# SELF-TEST
# =====================================================================================
def self_test():
    global path, KEYS
    path, KEYS = "._cases_test.json", "._ck_test.json"
    for f in (path, KEYS):
        if os.path.exists(f):
            os.remove(f)
    aes_key, index_key, eg_pub, eg_priv = load_or_create_keys()

    clerk_add("crk", "D1", "contract", "body one", aes_key, index_key, eg_pub, eg_priv)
    clerk_add("crk", "D2", "lease", "body two", aes_key, index_key, eg_pub, eg_priv)
    clerk_add("crk", "D3", "contract", "body three", aes_key, index_key, eg_pub, eg_priv)

    # all genuine
    assert all(all(_verify(r, eg_pub)) for r in load_store())
    # search 'contract' matches D1 and D3
    matches = [r for r in load_store() if r["token"] == sse_token(index_key, "contract")]
    assert {r["id"] for r in matches} == {"D1", "D3"}
    # a matching body decrypts
    assert aes192_decrypt(aes_key, bytes.fromhex(matches[0]["iv"]), bytes.fromhex(matches[0]["body"])) == b"body one"

    # RBAC: lawyer cannot audit, compliance cannot search
    try:
        compliance_audit("lwyr", eg_pub); raise AssertionError
    except PermissionError:
        pass
    try:
        lawyer_search("comp", "contract", index_key, aes_key, eg_pub); raise AssertionError
    except PermissionError:
        pass

    # tamper D1 -> verify fails
    tamper("D1")
    assert _verify(load_store()[0], eg_pub) == (False, False)

    # keys persist
    aes2, ik2, ep2, epr2 = load_or_create_keys()
    assert aes2 == aes_key and _verify(load_store()[1], ep2) == (True, True)

    for f in (path, KEYS):
        os.remove(f)
    print("ALL PASSED")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "test":
        self_test()
    else:
        menu()
