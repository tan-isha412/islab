# =====================================================================================
#  EvidenceChain  --  3-role secure digital-evidence system
#    Investigator : encrypt (AES-256-CBC) -> SHA-256(ciphertext) -> ElGamal-sign -> store
#    Prosecutor   : verify hash + signature -> ONLY THEN decrypt and show plaintext
#    Auditor      : verify hash + signature -> print VALID/INVALID -> NEVER decrypt
#
#  python evidencechain.py        -> menu-driven
#  python evidencechain.py test   -> self-test (ALL PASSED)
# =====================================================================================
import time, json, os, sys, random, hashlib
from Crypto.Cipher import AES
from Crypto.Random import get_random_bytes
from Crypto.Util.number import getPrime
from Crypto.Util.Padding import pad, unpad

STORE = "grant.json"


# =====================================================================================
# CRYPTO HELPERS  (module-level functions -- NOT inside any class)
# =====================================================================================
def timestamp():
    return time.strftime("%Y-%m-%d %H:%M:%S")


def md5(data):
    return hashlib.md5(data).hexdigest()


def _hash_int(message, mod):                       # hash bytes to an int < mod (for signing)
    return int(hashlib.sha256(message).hexdigest(), 16) % mod


def aes256_encrypt(key, data):                     # AES-256-CBC, random IV. key = 32 bytes
    iv = get_random_bytes(16)
    return iv, AES.new(key, AES.MODE_CBC, iv).encrypt(pad(data, 16))


def aes256_decrypt(key, iv, ct):
    return unpad(AES.new(key, AES.MODE_CBC, iv).decrypt(ct), 16)

def L(u, n):
    return (u - 1) // n


def paillier_keygen(bits=512):
    while True:
        p, q = getPrime(bits // 2), getPrime(bits // 2)
        if p != q and GCD(p * q, (p - 1) * (q - 1)) == 1:   # ensures n and phi are coprime
            break
    n = p * q
    nsq = n * n
    lam = (p - 1) * (q - 1) // math.gcd(p - 1, q - 1)       # lcm(p-1, q-1)
    g = n + 1                                                # standard simple choice
    mu = pow(L(pow(g, lam, nsq), n), -1, n)
    return (n, g), (lam, mu, n)                              # public (n, g), private (lam, mu, n)


def paillier_encrypt(m, pub):
    n, g = pub
    nsq = n * n
    m %= n
    while True:
        r = secrets.randbelow(n - 1) + 1
        if math.gcd(r, n) == 1:
            break
    return (pow(g, m, nsq) * pow(r, n, nsq)) % nsq


def paillier_decrypt(c, priv):
    lam, mu, n = priv
    return (L(pow(c, lam, n * n), n) * mu) % n


def paillier_add(c1, c2, pub):                 # E(m1)*E(m2) -> E(m1+m2)
    n, _ = pub
    return (c1 * c2) % (n * n)


def paillier_add_const(c, k, pub):             # E(m)*g^k -> E(m+k)
    n, g = pub
    return (c * pow(g, k, n * n)) % (n * n)


def paillier_mul_const(c, k, pub):             # E(m)^k -> E(k*m)
    n, _ = pub
    return pow(c, k, n * n)

def rsa_keygen(bits=1024, e=65537):
    while True:
        p, q = getPrime(bits // 2), getPrime(bits // 2)
        if p != q and math.gcd(e, (p - 1) * (q - 1)) == 1:
            break
    n = p * q
    d = pow(e, -1, (p - 1) * (q - 1))
    return (n, e), (n, d), (p, q)

def rsa_sign_manual(message, priv):              # priv = (n, d)
    n, d = priv
    h = int(hashlib.sha256(message).hexdigest(), 16) % n
    return pow(h, d, n)


def rsa_verify_manual(message, sig, pub):        # pub = (n, e)
    n, e = pub
    h = int(hashlib.sha256(message).hexdigest(), 16) % n
    return pow(sig, e, n) == h

def sse_setup():
    """two independent keys: one for the search tokens, one for encrypting data"""
    return {"index_key": get_random_bytes(16), "data_key": get_random_bytes(16)}


def _aes_enc(key, data):
    iv = get_random_bytes(16)
    return iv.hex() + AES.new(key, AES.MODE_CBC, iv).encrypt(pad(data, 16)).hex()


def _aes_dec(key, blob):
    raw = bytes.fromhex(blob)
    iv, ct = raw[:16], raw[16:]
    return unpad(AES.new(key, AES.MODE_CBC, iv).decrypt(ct), 16)


def sse_token(index_key, word):
    """DETERMINISTIC: same word -> same token. This is the fix for the manual's bug."""
    return hmac.new(index_key, word.lower().encode(), hashlib.sha256).hexdigest()


def sse_build_index(grantid, keys):
    """documents = {doc_id: text}. Returns (encrypted_index, encrypted_docs)."""
    index = {}
    records=load_records()
    for i,record in enumerate(records,1):
        index.setdefault(sse_token(keys["index_key"],record["id"]),[]).append(record["grant_desc"])

    enc_docs = {"Id": _aes_enc(keys["data_key"], record["id"].encode())
                for i, record in enumerate(records,1)}
    return index, enc_docs


def sse_search(index, query, keys):
    """return the list of doc ids whose token matches the query token"""
    tok = sse_token(keys["index_key"], query)
    return [_aes_dec(keys["data_key"], d).decode() for d in index.get(tok, [])]
# =====================================================================================
# RBAC  (user -> role -> allowed actions)
# =====================================================================================
USER_ROLES = {"res": "researcher", "rev": "reviewer", "finoff": "financialofficer"}
ROLE_PERMS = {
    "researcher": {"add"},                       # create + sign + store
    "reviewer":   {"verify", "search"},         # verify then decrypt
    "financialofficer":      {"verify","decrypt"},                     # verify only, never decrypt
}


def can(user, perm):
    return perm in ROLE_PERMS.get(USER_ROLES.get(user), set())


# =====================================================================================
# STORE
# =====================================================================================
def load_records():
    if not os.path.exists(STORE):
        return []
    with open(STORE, "r", encoding="utf-8") as f:
        return json.load(f)


def save_records(records):
    with open(STORE, "w", encoding="utf-8") as f:
        json.dump(records, f, indent=2)


# =====================================================================================
# ROLE ACTIONS  (each checks `can(...)` first -> RBAC enforced here)
# =====================================================================================
def researcher_add(user, data, aes_key, paill_pub,rsa_priv):
    if not can(user, "add"):
        raise PermissionError(f"{user} ({USER_ROLES.get(user)}) may not add evidence")
    iv, ct = aes256_encrypt(aes_key, data["grantdesc"].encode())
    ct2=paillier_encrypt(data["grantamt"],paill_pub)
    rec = {"id": len(load_records()) + 1, "grant_desc": ct.hex(), "grant_amt":ct2, "iv": iv.hex(),
           "timestamp": timestamp()}
    h=md5(rec)
    rec["hash"]=h
    sign=rsa_sign_manual(h,rsa_priv)
    rec["sign"]=sign
    records = load_records(); records.append(rec); save_records(records)
    print(f"[STORED] id={rec['id']}  hash={h[:24]}...  sig=({r % 10000}..,{s % 10000}..)  {rec['timestamp']}")
    return rec

def researcher_view(user):
    if not can(user, "add"):
        raise PermissionError(f"{user} ({USER_ROLES.get(user)}) may not add evidence")
    records = load_records()
    if not records:
        print("📁 No records found or the file is empty.")
        return
    print(f"📋 Found {len(records)} records:\n" + "=" * 40)
    for index, record in enumerate(records, 1):
        print(f"🔹 [Record #{index}]")
        # Pretty-print the individual dictionary object
        print(json.dumps(record, indent=4, ensure_ascii=False))
        print("-" * 40)


def _verify(rec, pub):
    ct = bytes.fromhex(rec["ciphertext"])
    hash_ok = md5(ct) == rec["hash"]
    sig_ok = rsa_verify_manual(ct, (rec["sign"]), pub)
    return hash_ok, sig_ok


def reviewer_verify(user,rec, pub):
    if not can(user, "decrypt"):
        raise PermissionError(f"{user} ({USER_ROLES.get(user)}) may not decrypt")
    hash_ok, sig_ok = _verify(rec, pub)
    print(f"  integrity (hash) : {'PASS' if hash_ok else 'FAIL'}")
    print(f"  authenticity(sig): {'PASS' if sig_ok else 'FAIL'}")
    if not (hash_ok and sig_ok):
        print("  -> verification FAILED, refusing to decrypt")
        return None
    print("  -> Verification approved!!")
    return None

def financialofficer_verify(user,rec, pub):
    if not can(user, "decrypt"):
        raise PermissionError(f"{user} ({USER_ROLES.get(user)}) may not decrypt")
    hash_ok, sig_ok = _verify(rec, pub)
    print(f"  integrity (hash) : {'PASS' if hash_ok else 'FAIL'}")
    print(f"  authenticity(sig): {'PASS' if sig_ok else 'FAIL'}")
    if not (hash_ok and sig_ok):
        print("  -> verification FAILED, refusing to decrypt")
        return None
    print("  -> Verification approved!!")
    return None


def auditor_check(user, rec, p, g, y):
    if not can(user, "verify"):
        raise PermissionError(f"{user} may not audit")
    hash_ok, sig_ok = _verify(rec, p, g, y)
    verdict = "VALID" if (hash_ok and sig_ok) else "INVALID"
    print(f"  AUDIT id={rec['id']}: integrity={'PASS' if hash_ok else 'FAIL'}, "
          f"signature={'VALID' if sig_ok else 'INVALID'} -> {verdict}  ({timestamp()})")
    # auditor NEVER decrypts
    return verdict


def tamper(rec_id):
    """flip one byte of a stored ciphertext -> to demonstrate detection"""
    records = load_records()
    for rec in records:
        if rec["id"] == rec_id:
            ct = bytearray(bytes.fromhex(rec["ciphertext"]))
            ct[0] ^= 0xFF
            rec["ciphertext"] = bytes(ct).hex()
    save_records(records)
    print(f"[TAMPERED] flipped a byte in record {rec_id}")


# =====================================================================================
# MENU-DRIVEN
# =====================================================================================
def menu():
    # one shared AES-256 key and one investigator ElGamal keypair for the session
    aes_key = get_random_bytes(32)
    paill_pub,paill_priv=paillier_keygen(512)
    rsa_pub,rsa_priv,(p,q)=rsa_keygen()
    sse_setup()
    print("EvidenceChain ready. Users: inv1 (investigator), pros1 (prosecutor), aud1 (auditor)")

    while True:
        user = input("\nlogin as (inv1/pros1/aud1, or 'quit'): ").strip()
        if user == "quit":
            break
        role = USER_ROLES.get(user)
        if role is None:
            print("unknown user"); continue
        print(f"--- {user} : {role} ---")

        if role == "":
            print("1. add grant   2. tamper a record   0. logout")
            while True:
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    desc=input("grant description: ")
                    amt=int(input("grant amount: "))
                    data={"grantdesc":desc,"grantamt":amt}
                    researcher_add(user, data, aes_key,paill_pub,rsa_priv)
                elif c == "2":
                    tamper(int(input("record id: ")))

        elif role == "reviewer":
            print("1. verify sign  2. searches a record   0. logout")
            while True:
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    recs = load_records()
                    for r in recs:
                        print(f"  id={r['id']} time={r['timestamp']}")
                    rid = int(input("record id: "))
                    rec = next((r for r in recs if r["id"] == rid), None)
                    if rec:
                        reviewer_verify(user, rec, rsa_pub)
                elif c=="2":


        elif role == "financialofficer":
            print("1. verify 2.decrypt the amount and the record   0. logout")
            while True:
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    for rec in load_records():
                        financialofficer_verify(user,rec,rsa_pub)
                elif c=="2":



