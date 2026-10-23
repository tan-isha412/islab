# =====================================================================================
#  EXAM TEMPLATE BANK
#  Each TEMPLATE has: a short question (4-5 lines) + a ready menu-driven multi-role
#  program with GENERIC role names (role1/role2/role3) -> rename them to whatever the
#  question asks (Patient/Doctor/Auditor, Bank/Officer/Regulator, ...) and tweak the
#  fields. All share the TOOLKIT below.
#
#  HOW TO USE IN THE EXAM:
#    1. Copy the TOOLKIT section once.
#    2. Copy the TEMPLATE closest to your question.
#    3. Rename role1/role2/role3, change the input fields, swap the cipher if needed.
#
#  RUN:
#    python templates.py          -> pick a template number, run its menu
#    python templates.py test     -> runs every template's logic non-interactively
#
#  WHICH TEMPLATE FOR WHICH QUESTION
#    T1  3-role secure record         : AES-256-CBC + SHA-256 + RSA sign      [EASY-MED]
#    T2  homomorphic aggregation      : AES-192 + Paillier + MD5 + RSA sign   [MED]
#    T3  DH + classical gate (sockets): Diffie-Hellman + Vigenere + gate      [MED]
#    T4  searchable + signatures      : AES + SSE token + SHA + ElGamal sign  [MED-HARD]
#    T5  full combo                   : hybrid RSA+AES + sign + Paillier + SSE
#                                       + replay-nonce + RBAC + tamper        [HARD]
#    CS  standalone client/server pair (sockets)                              [reference]
# =====================================================================================
import time, json, os, sys, math, secrets, random, hashlib, hmac, socket
from Crypto.Cipher import AES, DES, DES3, PKCS1_OAEP
from Crypto.PublicKey import RSA, ECC
from Crypto.Signature import DSS
from Crypto.Random import get_random_bytes
from Crypto.Util.number import getPrime, isPrime, GCD, bytes_to_long, long_to_bytes
from Crypto.Util.Padding import pad, unpad
from Crypto.Protocol.KDF import PBKDF2
from Crypto.Hash import SHA256


# #####################################################################################
#  TOOLKIT  (copy this whole block, then copy the template you need)
# #####################################################################################
def timestamp():
    return time.strftime("%Y-%m-%d %H:%M:%S")


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def md5(data):
    return hashlib.md5(data).hexdigest()


# ---- symmetric: AES (key size picks 128/192/256) and DES ----
def key_from_text(text, size):                 # user word/hex -> size bytes
    try:
        b = bytes.fromhex(text)
        if len(b) == size:
            return b
    except ValueError:
        pass
    return hashlib.sha256(text.encode()).digest()[:size]


def aes_encrypt(key, data):                    # CBC, random IV
    iv = get_random_bytes(16)
    return iv, AES.new(key, AES.MODE_CBC, iv).encrypt(pad(data, 16))


def aes_decrypt(key, iv, ct):
    return unpad(AES.new(key, AES.MODE_CBC, iv).decrypt(ct), 16)


def aes_encrypt_iv(key, data, iv):             # CBC with a given IV
    return AES.new(key, AES.MODE_CBC, iv).encrypt(pad(data, 16))


def aes_decrypt_iv(key, ct, iv):
    return unpad(AES.new(key, AES.MODE_CBC, iv).decrypt(ct), 16)


def des_cbc_encrypt(key, data, iv):            # 8-byte key/iv
    return DES.new(key, DES.MODE_CBC, iv).encrypt(pad(data, 8))


def des_cbc_decrypt(key, ct, iv):
    return unpad(DES.new(key, DES.MODE_CBC, iv).decrypt(ct), 8)


# ---- classical (Lab 1) ----
def letters_only(t):
    return "".join(c for c in t.upper() if c.isalpha())


def vigenere(text, key, enc=True):
    t, k = letters_only(text), letters_only(key)
    s = 1 if enc else -1
    return "".join(chr((ord(t[i]) - 65 + s * (ord(k[i % len(k)]) - 65)) % 26 + 65) for i in range(len(t)))


def affine(text, a, b, enc=True):
    t = letters_only(text)
    if enc:
        return "".join(chr((a * (ord(c) - 65) + b) % 26 + 65) for c in t)
    ai = pow(a, -1, 26)
    return "".join(chr((ai * (ord(c) - 65 - b)) % 26 + 65) for c in t)


# ---- Diffie-Hellman (Lab 3) ----
def dh_params(bits=256):
    return getPrime(bits), 2


def dh_keypair(p, g):
    a = random.randint(2, p - 2)
    return a, pow(g, a, p)


def dh_shared(their_pub, my_priv, p):
    return pow(their_pub, my_priv, p)


def kdf(secret, salt=b"salt", size=32):
    return PBKDF2(str(secret), salt, size, count=100000, hmac_hash_module=SHA256)


# ---- RSA (Lab 3/6): encrypt, hybrid, sign ----
def rsa_keygen(bits=1024, e=65537):
    while True:
        p, q = getPrime(bits // 2), getPrime(bits // 2)
        if p != q and math.gcd(e, (p - 1) * (q - 1)) == 1:
            break
    n = p * q
    return (n, e), (n, pow(e, -1, (p - 1) * (q - 1)))


def rsa_sign(message, priv):
    n, d = priv
    return pow(int(sha256(message), 16) % n, d, n)


def rsa_verify(message, sig, pub):
    n, e = pub
    return pow(sig, e, n) == int(sha256(message), 16) % n


def rsa_lib_keys(bits=2048):
    k = RSA.generate(bits)
    return k.publickey(), k


def rsa_hybrid_encrypt(pub_key, data):         # RSA-OAEP wraps a random AES key
    ak = get_random_bytes(16)
    iv, ct = aes_encrypt(ak, data)
    return PKCS1_OAEP.new(pub_key).encrypt(ak), iv, ct


def rsa_hybrid_decrypt(priv_key, enc_key, iv, ct):
    return aes_decrypt(PKCS1_OAEP.new(priv_key).decrypt(enc_key), iv, ct)


# ---- ElGamal signature (Lab 6) ----
def elgamal_keygen(bits=256):
    p = getPrime(bits)
    g = 2
    x = random.randint(2, p - 2)
    return (p, g, pow(g, x, p)), x


def _hi(message, mod):
    return int(sha256(message), 16) % mod


def elgamal_sign(message, p, g, x):
    while True:
        k = random.randint(2, p - 2)
        if math.gcd(k, p - 1) == 1:
            break
    r = pow(g, k, p)
    s = ((_hi(message, p) - x * r) * pow(k, -1, p - 1)) % (p - 1)
    return r, s


def elgamal_verify(message, sig, p, g, y):
    r, s = sig
    if not 0 < r < p:
        return False
    return pow(g, _hi(message, p), p) == (pow(y, r, p) * pow(r, s, p)) % p


# ---- Paillier (Lab 7): additive homomorphic ----
def _L(u, n):
    return (u - 1) // n


def paillier_keygen(bits=512):
    while True:
        p, q = getPrime(bits // 2), getPrime(bits // 2)
        if p != q and GCD(p * q, (p - 1) * (q - 1)) == 1:
            break
    n = p * q
    lam = (p - 1) * (q - 1) // math.gcd(p - 1, q - 1)
    g = n + 1
    mu = pow(_L(pow(g, lam, n * n), n), -1, n)
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
    return (_L(pow(c, lam, n * n), n) * mu) % n


def paillier_add(c1, c2, pub):                 # E(a)*E(b) -> E(a+b)
    return (c1 * c2) % (pub[0] ** 2)


def paillier_mul_const(c, k, pub):             # E(m)^k -> E(k*m)
    return pow(c, k, pub[0] ** 2)


# ---- 3DES (Lab 2) ----
def des3_make_key():
    while True:
        try:
            k = DES3.adjust_key_parity(get_random_bytes(24))
            DES3.new(k, DES3.MODE_ECB); return k
        except ValueError:
            pass


def des3_cbc_encrypt(key, data, iv):
    return DES3.new(key, DES3.MODE_CBC, iv).encrypt(pad(data, 8))


def des3_cbc_decrypt(key, ct, iv):
    return unpad(DES3.new(key, DES3.MODE_CBC, iv).decrypt(ct), 8)


# ---- ElGamal ENCRYPTION (Lab 3; multiplicative homomorphic in Lab 7) ----
def elgamal_enc_keygen(bits=256):
    p = getPrime(bits); g = 2
    x = random.randint(2, p - 2)
    return (p, g, pow(g, x, p)), x                 # public (p,g,y), private x


def elgamal_encrypt(m, pub, k=None):
    p, g, y = pub
    k = k or random.randint(2, p - 2)
    return pow(g, k, p), (m % p) * pow(y, k, p) % p     # (c1, c2)


def elgamal_decrypt(ct, x, p):
    c1, c2 = ct
    return (c2 * pow(pow(c1, x, p), -1, p)) % p


def elgamal_enc_text(text, pub):               # whole message as one int (needs big p)
    return elgamal_encrypt(bytes_to_long(text.encode()), pub)


def elgamal_dec_text(ct, x, p):
    return long_to_bytes(elgamal_decrypt(ct, x, p)).decode()


def elgamal_mul(ct1, ct2, p):                  # homomorphic multiply: E(a)*E(b) -> E(a*b)
    return (ct1[0] * ct2[0]) % p, (ct1[1] * ct2[1]) % p


# ---- ECC: ECIES encryption + ECDSA signature (Lab 3 / 6) ----
def ecc_keygen(curve="P-256"):
    k = ECC.generate(curve=curve)
    return k.public_key(), k


def ecies_encrypt(recipient_pub, data):        # ECC "encryption" = ECDH + AES
    eph = ECC.generate(curve=recipient_pub.curve)
    key = kdf(int((recipient_pub.pointQ * eph.d).x), b"ecies", 16)
    iv, ct = aes_encrypt(key, data)
    return eph.public_key().export_key(format="PEM"), iv, ct


def ecies_decrypt(priv_key, eph_pem, iv, ct):
    eph = ECC.import_key(eph_pem)
    key = kdf(int((eph.pointQ * priv_key.d).x), b"ecies", 16)
    return aes_decrypt(key, iv, ct)


def ecdsa_sign(message, priv_key):
    return DSS.new(priv_key, "fips-186-3").sign(SHA256.new(message))


def ecdsa_verify(message, sig, pub_key):
    try:
        DSS.new(pub_key, "fips-186-3").verify(SHA256.new(message), sig)
        return True
    except (ValueError, TypeError):
        return False


# ---- Schnorr signature (Lab 6) ----
def schnorr_params(bits=256):
    while True:
        q = getPrime(bits)
        for k in range(2, 4000):
            p = k * q + 1
            if isPrime(p):
                g = pow(2, (p - 1) // q, p)
                if g != 1:
                    return p, q, g


def schnorr_keygen(params):
    p, q, g = params
    x = random.randint(1, q - 1)
    return x, pow(g, x, p)


def schnorr_sign(message, params, x):
    p, q, g = params
    k = random.randint(1, q - 1)
    r = pow(g, k, p)
    e = int(sha256(long_to_bytes(r) + message), 16) % q
    return e, (k + x * e) % q


def schnorr_verify(message, sig, params, y):
    p, q, g = params
    e, s = sig
    rv = (pow(g, s, p) * pow(y, (-e) % q, p)) % p
    return e == int(sha256(long_to_bytes(rv) + message), 16) % q


# ---- Rabin (Lab 4) ----
RABIN_MARK = b"##"


def rabin_keygen(bits=512):
    def prime_3mod4(b):
        while True:
            x = getPrime(b)
            if x % 4 == 3:
                return x
    p = prime_3mod4(bits // 2); q = prime_3mod4(bits // 2)
    while q == p:
        q = prime_3mod4(bits // 2)
    return p * q, (p, q)


def rabin_encrypt_text(text, n):
    return pow(bytes_to_long(text.encode() + RABIN_MARK), 2, n)


def _egcd(a, b):
    if b == 0:
        return a, 1, 0
    g, x, y = _egcd(b, a % b)
    return g, y, x - (a // b) * y


def rabin_decrypt_text(c, p, q):
    n = p * q
    mp = pow(c, (p + 1) // 4, p); mq = pow(c, (q + 1) // 4, q)
    _, yp, yq = _egcd(p, q)
    r1 = (yp * p * mq + yq * q * mp) % n
    r3 = (yp * p * mq - yq * q * mp) % n
    for r in (r1, n - r1, r3, n - r3):
        b = long_to_bytes(r)
        if b.endswith(RABIN_MARK):
            return b[:-len(RABIN_MARK)].decode()
    raise ValueError("no root matched")


# ---- weak-key attacks (Lab 4) ----
def fermat_factor(n, steps=10_000_000):        # primes too close
    a = math.isqrt(n)
    if a * a < n:
        a += 1
    for _ in range(steps):
        b2 = a * a - n; b = math.isqrt(b2)
        if b * b == b2:
            return a - b, a + b
        a += 1
    raise ValueError("Fermat failed")


def common_factor_attack(n1, n2):              # shared prime
    p = math.gcd(n1, n2)
    if p in (1, n1):
        raise ValueError("no shared factor")
    return p, n1 // p, n2 // p


# ---- searchable (Lab 8) ----
def sse_token(index_key, word):                # deterministic keyed hash
    return hmac.new(index_key, word.lower().encode(), hashlib.sha256).hexdigest()


# ---- persistence + RBAC + sockets ----
def load_store(path):
    if not os.path.exists(path):
        return []
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def save_store(path, records):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(records, f, indent=2)


def recv_exact(sock, n):
    buf = b""
    while len(buf) < n:
        part = sock.recv(n - len(buf))
        if not part:
            raise ConnectionError("closed")
        buf += part
    return buf


def send_msg(sock, obj):
    data = json.dumps(obj).encode()
    sock.sendall(len(data).to_bytes(4, "big") + data)


def recv_msg(sock):
    n = int.from_bytes(recv_exact(sock, 4), "big")
    return json.loads(recv_exact(sock, n).decode())


# #####################################################################################
#  TEMPLATE 1 -- 3-ROLE SECURE RECORD                                       [EASY-MED]
#  Q: A system stores confidential records. role1 enters a record, encrypts it with
#     AES-256-CBC, computes its SHA-256 hash and signs the hash with RSA, then stores
#     it. role2 verifies the signature and hash, and only then decrypts and shows the
#     record. role3 verifies only (integrity + authenticity) and never decrypts.
# #####################################################################################
T1_STORE = "t1.json"
T1_ROLES = {"1": "role1", "2": "role2", "3": "role3"}        # RENAME these
T1_PERMS = {"role1": {"add", "view"}, "role2": {"open"}, "role3": {"audit"}}


def t1_can(user, perm):
    return perm in T1_PERMS.get(T1_ROLES.get(user), set())


def t1_payload(rec):
    return f"{rec['id']}|{rec['data']}|{rec['iv']}|{rec['timestamp']}".encode()


def t1_add(user, text, aes_key, rsa_priv):
    if not t1_can(user, "add"):
        raise PermissionError("not allowed")
    iv, ct = aes_encrypt(aes_key, text.encode())
    rec = {"id": len(load_store(T1_STORE)) + 1, "data": ct.hex(), "iv": iv.hex(), "timestamp": timestamp()}
    rec["hash"] = sha256(t1_payload(rec))
    rec["sign"] = rsa_sign(t1_payload(rec), rsa_priv)
    recs = load_store(T1_STORE); recs.append(rec); save_store(T1_STORE, recs)
    print(f"[STORED] record {rec['id']}")
    return rec


def t1_verify(rec, rsa_pub):
    p = t1_payload(rec)
    return sha256(p) == rec["hash"], rsa_verify(p, rec["sign"], rsa_pub)


def t1_open(user, rid, aes_key, rsa_pub):
    if not t1_can(user, "open"):
        raise PermissionError("not allowed")
    rec = next((r for r in load_store(T1_STORE) if r["id"] == rid), None)
    if not rec:
        print("no such record"); return
    h, s = t1_verify(rec, rsa_pub)
    print(f"  integrity={'PASS' if h else 'FAIL'} signature={'VALID' if s else 'INVALID'}")
    if h and s:
        print("  record:", aes_decrypt(aes_key, bytes.fromhex(rec["iv"]), bytes.fromhex(rec["data"])).decode())
    else:
        print("  verification failed -> not decrypting")


def t1_audit(user, rsa_pub):
    if not t1_can(user, "audit"):
        raise PermissionError("not allowed")
    for rec in load_store(T1_STORE):
        h, s = t1_verify(rec, rsa_pub)
        print(f"  record {rec['id']}: {'VALID' if h and s else 'INVALID'}")


def t1_menu():
    aes_key = get_random_bytes(32)
    rsa_pub, rsa_priv = rsa_keygen(1024)
    while True:
        u = input("\nlogin (1/2/3, quit): ").strip()
        if u == "quit":
            return
        role = T1_ROLES.get(u)
        if not role:
            print("unknown"); continue
        while True:
            print(f"[{role}] 1.add 2.view 3.open(verify+decrypt) 4.audit 0.logout")
            c = input("choice: ").strip()
            if c == "0":
                break
            try:
                if c == "1":
                    t1_add(u, input("record text: "), aes_key, rsa_priv)
                elif c == "2":
                    for r in load_store(T1_STORE):
                        print(f"  id={r['id']} {r['timestamp']}")
                elif c == "3":
                    t1_open(u, int(input("id: ")), aes_key, rsa_pub)
                elif c == "4":
                    t1_audit(u, rsa_pub)
            except PermissionError as e:
                print("DENIED:", e)


def t1_demo():
    global T1_STORE
    T1_STORE = "._t1.json"
    open(T1_STORE, "w").write("[]")
    aes_key = get_random_bytes(32)
    rsa_pub, rsa_priv = rsa_keygen(1024)
    t1_add("1", "secret record A", aes_key, rsa_priv)
    assert all(t1_verify(r, rsa_pub) == (True, True) for r in load_store(T1_STORE))
    os.remove(T1_STORE)
    print("T1 ok")


# #####################################################################################
#  TEMPLATE 2 -- HOMOMORPHIC AGGREGATION                                         [MED]
#  Q: role1 submits a record with a description and an amount. The description is AES-192
#     encrypted, the amount is Paillier encrypted, the record is MD5-hashed and RSA-signed,
#     then stored. role2 verifies and can view a decrypted description. role3 (finance)
#     homomorphically adds the amounts of selected records and decrypts only the total.
# #####################################################################################
T2_STORE = "t2.json"
T2_ROLES = {"1": "role1", "2": "role2", "3": "role3"}
T2_PERMS = {"role1": {"add", "view"}, "role2": {"verify", "viewdesc"}, "role3": {"aggregate"}}


def t2_can(user, perm):
    return perm in T2_PERMS.get(T2_ROLES.get(user), set())


def t2_payload(rec):
    return f"{rec['id']}|{rec['desc']}|{rec['iv']}|{rec['amount']}|{rec['timestamp']}".encode()


def t2_add(user, desc, amount, aes_key, paill_pub, rsa_priv):
    if not t2_can(user, "add"):
        raise PermissionError("not allowed")
    iv, ct = aes_encrypt(aes_key, desc.encode())                # aes_key is 24 bytes -> AES-192
    rec = {"id": len(load_store(T2_STORE)) + 1, "desc": ct.hex(), "iv": iv.hex(),
           "amount": str(paillier_encrypt(amount, paill_pub)), "timestamp": timestamp()}
    rec["hash"] = md5(t2_payload(rec))
    rec["sign"] = rsa_sign(t2_payload(rec), rsa_priv)
    recs = load_store(T2_STORE); recs.append(rec); save_store(T2_STORE, recs)
    print(f"[STORED] record {rec['id']}")
    return rec


def t2_verify(rec, rsa_pub):
    p = t2_payload(rec)
    return md5(p) == rec["hash"], rsa_verify(p, rec["sign"], rsa_pub)


def t2_aggregate(user, ids, paill_pub, paill_priv, rsa_pub):
    if not t2_can(user, "aggregate"):
        raise PermissionError("not allowed")
    recs = {r["id"]: r for r in load_store(T2_STORE)}
    total, used = None, []
    for i in ids:
        rec = recs.get(i)
        if not rec or not all(t2_verify(rec, rsa_pub)):
            print(f"  record {i} missing/tampered, skipping"); continue
        c = int(rec["amount"])
        total = c if total is None else paillier_add(total, c, paill_pub)
        used.append(i)
    if total is None:
        print("  nothing to total"); return None
    t = paillier_decrypt(total, paill_priv)
    print(f"  records {used} -> TOTAL = {t}")
    return t


def t2_viewdesc(user, rid, aes_key, rsa_pub):
    if not t2_can(user, "viewdesc"):
        raise PermissionError("not allowed")
    rec = next((r for r in load_store(T2_STORE) if r["id"] == rid), None)
    if not rec:
        print("no such record"); return
    h, s = t2_verify(rec, rsa_pub)
    print(f"  integrity={'PASS' if h else 'FAIL'} signature={'VALID' if s else 'INVALID'}")
    if h and s:
        print("  description:", aes_decrypt(aes_key, bytes.fromhex(rec["iv"]), bytes.fromhex(rec["desc"])).decode())


def t2_menu():
    aes_key = get_random_bytes(24)                              # AES-192
    paill_pub, paill_priv = paillier_keygen(512)
    rsa_pub, rsa_priv = rsa_keygen(1024)
    while True:
        u = input("\nlogin (1/2/3, quit): ").strip()
        if u == "quit":
            return
        role = T2_ROLES.get(u)
        if not role:
            print("unknown"); continue
        while True:
            print(f"[{role}] 1.add 2.view 3.verify+viewdesc 4.aggregate total 0.logout")
            c = input("choice: ").strip()
            if c == "0":
                break
            try:
                if c == "1":
                    desc = input("description: "); amt = int(input("amount: "))
                    t2_add(u, desc, amt, aes_key, paill_pub, rsa_priv)
                elif c == "2":
                    for r in load_store(T2_STORE):
                        print(f"  id={r['id']} {r['timestamp']}")
                elif c == "3":
                    t2_viewdesc(u, int(input("id: ")), aes_key, rsa_pub)
                elif c == "4":
                    ids = [int(i) for i in input("ids (comma): ").split(",")]
                    t2_aggregate(u, ids, paill_pub, paill_priv, rsa_pub)
            except PermissionError as e:
                print("DENIED:", e)


def t2_demo():
    global T2_STORE
    T2_STORE = "._t2.json"
    open(T2_STORE, "w").write("[]")
    aes_key = get_random_bytes(24)                              # AES-192
    paill_pub, paill_priv = paillier_keygen(512)
    rsa_pub, rsa_priv = rsa_keygen(1024)
    t2_add("1", "item A", 500, aes_key, paill_pub, rsa_priv)
    t2_add("1", "item B", 300, aes_key, paill_pub, rsa_priv)
    assert t2_aggregate("3", [1, 2], paill_pub, paill_priv, rsa_pub) == 800
    os.remove(T2_STORE)
    print("T2 ok")


# #####################################################################################
#  TEMPLATE 3 -- DIFFIE-HELLMAN + CLASSICAL GATE (CLIENT/SERVER)                 [MED]
#  Q: A sender and receiver establish a shared key K with Diffie-Hellman (params given).
#     The message is cleaned to letters only. If K mod 10 == <checkpoint>, derive a
#     Vigenere keyword from K's digits and encrypt; else refuse. The receiver recomputes
#     K, checks the same gate, rebuilds the keyword and decrypts. Runs over sockets.
# #####################################################################################
T3_CHECKPOINT = 7


def t3_keyword(K):                             # each digit -> a letter
    return "".join(chr(65 + int(d) % 26) for d in str(K))


def t3_server(host="127.0.0.1", port=7000):
    p, g = 2087, 5                             # given params (same on both sides)
    b, B = dh_keypair(p, g)
    with socket.socket() as srv:
        srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        srv.bind((host, port)); srv.listen(1)
        print(f"server on {host}:{port}")
        conn, _ = srv.accept()
        with conn:
            A = recv_msg(conn)["A"]
            send_msg(conn, {"B": B})
            K = dh_shared(A, b, p)
            pkt = recv_msg(conn)
            if K % 10 != T3_CHECKPOINT:
                send_msg(conn, {"status": "FAIL", "reason": "gate failed"})
            else:
                send_msg(conn, {"status": "OK", "message": vigenere(pkt["ct"], t3_keyword(K), enc=False)})


def t3_client(host="127.0.0.1", port=7000, message="attack at dawn"):
    p, g = 2087, 5
    a, A = dh_keypair(p, g)
    with socket.socket() as s:
        s.connect((host, port))
        send_msg(s, {"A": A})
        B = recv_msg(s)["B"]
        K = dh_shared(B, a, p)
        if K % 10 != T3_CHECKPOINT:
            print("gate failed, not sending"); return
        ct = vigenere(message, t3_keyword(K))
        send_msg(s, {"ct": ct})
        print("server reply:", recv_msg(s))


def t3_demo():                                 # in-process (no sockets) to verify the logic
    p, g = 2087, 5
    a, A = dh_keypair(p, g); b, B = dh_keypair(p, g)
    Ka, Kb = dh_shared(B, a, p), dh_shared(A, b, p)
    assert Ka == Kb
    kw = t3_keyword(Ka)
    ct = vigenere("hello world", kw)
    assert vigenere(ct, kw, enc=False) == "HELLOWORLD"
    print("T3 ok")


# #####################################################################################
#  TEMPLATE 4 -- SEARCHABLE + SIGNATURES                                     [MED-HARD]
#  Q: role1 submits a record with a keyword and a body. The body is AES encrypted, a
#     deterministic HMAC token is built for the keyword, the record is SHA-256 hashed and
#     ElGamal-signed. role2 searches by keyword token (contents stay encrypted), verifies
#     the signature, and decrypts matching bodies. role3 verifies only, never decrypts.
# #####################################################################################
T4_STORE = "t4.json"
T4_ROLES = {"1": "role1", "2": "role2", "3": "role3"}
T4_PERMS = {"role1": {"add"}, "role2": {"search", "open"}, "role3": {"audit"}}


def t4_can(user, perm):
    return perm in T4_PERMS.get(T4_ROLES.get(user), set())


def t4_payload(rec):
    return f"{rec['id']}|{rec['body']}|{rec['iv']}|{rec['token']}|{rec['timestamp']}".encode()


def t4_add(user, keyword, body, aes_key, index_key, eg_pub, eg_priv):
    if not t4_can(user, "add"):
        raise PermissionError("not allowed")
    p, g, _ = eg_pub
    iv, ct = aes_encrypt(aes_key, body.encode())
    rec = {"id": len(load_store(T4_STORE)) + 1, "body": ct.hex(), "iv": iv.hex(),
           "token": sse_token(index_key, keyword), "timestamp": timestamp()}
    rec["hash"] = sha256(t4_payload(rec))
    rec["sign"] = elgamal_sign(t4_payload(rec), p, g, eg_priv)
    recs = load_store(T4_STORE); recs.append(rec); save_store(T4_STORE, recs)
    print(f"[STORED] record {rec['id']}")
    return rec


def t4_verify(rec, eg_pub):
    p, g, y = eg_pub
    pl = t4_payload(rec)
    return sha256(pl) == rec["hash"], elgamal_verify(pl, tuple(rec["sign"]), p, g, y)


def t4_search(user, keyword, index_key, aes_key, eg_pub):
    if not t4_can(user, "search"):
        raise PermissionError("not allowed")
    tok = sse_token(index_key, keyword)
    for rec in load_store(T4_STORE):
        if rec["token"] == tok:
            h, s = t4_verify(rec, eg_pub)
            print(f"  match id={rec['id']} verify={'OK' if h and s else 'FAIL'}", end="")
            if h and s:
                print("  body:", aes_decrypt(aes_key, bytes.fromhex(rec["iv"]), bytes.fromhex(rec["body"])).decode())
            else:
                print()


def t4_audit(user, eg_pub):
    if not t4_can(user, "audit"):
        raise PermissionError("not allowed")
    for rec in load_store(T4_STORE):
        h, s = t4_verify(rec, eg_pub)
        print(f"  record {rec['id']}: {'VALID' if h and s else 'INVALID'}")


def t4_menu():
    aes_key, index_key = get_random_bytes(16), get_random_bytes(16)
    eg_pub, eg_priv = elgamal_keygen(256)
    while True:
        u = input("\nlogin (1/2/3, quit): ").strip()
        if u == "quit":
            return
        role = T4_ROLES.get(u)
        if not role:
            print("unknown"); continue
        while True:
            print(f"[{role}] 1.add 2.search+decrypt 3.audit(verify only) 0.logout")
            c = input("choice: ").strip()
            if c == "0":
                break
            try:
                if c == "1":
                    kw = input("keyword: "); body = input("body: ")
                    t4_add(u, kw, body, aes_key, index_key, eg_pub, eg_priv)
                elif c == "2":
                    t4_search(u, input("keyword: "), index_key, aes_key, eg_pub)
                elif c == "3":
                    t4_audit(u, eg_pub)
            except PermissionError as e:
                print("DENIED:", e)


def t4_demo():
    global T4_STORE
    T4_STORE = "._t4.json"
    open(T4_STORE, "w").write("[]")
    aes_key, index_key = get_random_bytes(16), get_random_bytes(16)
    eg_pub, eg_priv = elgamal_keygen(256)
    t4_add("1", "alpha", "body one", aes_key, index_key, eg_pub, eg_priv)
    t4_add("1", "beta", "body two", aes_key, index_key, eg_pub, eg_priv)
    t4_add("1", "alpha", "body three", aes_key, index_key, eg_pub, eg_priv)
    hits = [r for r in load_store(T4_STORE) if r["token"] == sse_token(index_key, "alpha")]
    assert len(hits) == 2 and all(all(t4_verify(r, eg_pub)) for r in hits)
    os.remove(T4_STORE)
    print("T4 ok")


# #####################################################################################
#  TEMPLATE 5 -- FULL COMBO                                                     [HARD]
#  Q: role1 submits a record: body hybrid-encrypted (RSA-OAEP wraps an AES key), a numeric
#     amount Paillier-encrypted, a keyword token, a fresh nonce + timestamp, SHA-256 hash,
#     RSA signature. role2 verifies + rejects replays (seen nonce / old timestamp), totals
#     the amounts homomorphically, decrypts only the total, and can search by keyword.
#     role3 verifies only, never decrypts. Tampered/replayed records are refused.
# #####################################################################################
T5_STORE = "t5.json"
T5_ROLES = {"1": "role1", "2": "role2", "3": "role3"}
T5_PERMS = {"role1": {"add"}, "role2": {"verify", "aggregate", "search"}, "role3": {"audit"}}
T5_SEEN_NONCES = set()


def t5_can(user, perm):
    return perm in T5_PERMS.get(T5_ROLES.get(user), set())


def t5_payload(rec):
    return (f"{rec['id']}|{rec['enc_key']}|{rec['iv']}|{rec['body']}|{rec['amount']}|"
            f"{rec['token']}|{rec['nonce']}|{rec['timestamp']}").encode()


def t5_add(user, keyword, body, amount, rsa_body_pub, index_key, paill_pub, rsa_sign_priv):
    if not t5_can(user, "add"):
        raise PermissionError("not allowed")
    enc_key, iv, ct = rsa_hybrid_encrypt(rsa_body_pub, body.encode())
    rec = {"id": len(load_store(T5_STORE)) + 1, "enc_key": enc_key.hex(), "iv": iv.hex(),
           "body": ct.hex(), "amount": str(paillier_encrypt(amount, paill_pub)),
           "token": sse_token(index_key, keyword), "nonce": secrets.token_hex(8),
           "timestamp": timestamp()}
    rec["hash"] = sha256(t5_payload(rec))
    rec["sign"] = rsa_sign(t5_payload(rec), rsa_sign_priv)
    recs = load_store(T5_STORE); recs.append(rec); save_store(T5_STORE, recs)
    print(f"[STORED] record {rec['id']} nonce={rec['nonce']}")
    return rec


def t5_verify(rec, rsa_sign_pub):
    p = t5_payload(rec)
    return sha256(p) == rec["hash"], rsa_verify(p, rec["sign"], rsa_sign_pub)


def t5_check_replay(rec):
    if rec["nonce"] in T5_SEEN_NONCES:
        return False
    T5_SEEN_NONCES.add(rec["nonce"])
    return True


def t5_aggregate(user, paill_pub, paill_priv, rsa_sign_pub):
    if not t5_can(user, "aggregate"):
        raise PermissionError("not allowed")
    total, used = None, []
    for rec in load_store(T5_STORE):
        if not all(t5_verify(rec, rsa_sign_pub)):
            print(f"  record {rec['id']} tampered, skip"); continue
        c = int(rec["amount"])
        total = c if total is None else paillier_add(total, c, paill_pub)
        used.append(rec["id"])
    if total is None:
        return None
    t = paillier_decrypt(total, paill_priv)
    print(f"  records {used} -> TOTAL = {t}")
    return t


def t5_search(user, keyword, index_key):
    if not t5_can(user, "search"):
        raise PermissionError("not allowed")
    tok = sse_token(index_key, keyword)
    hits = [r["id"] for r in load_store(T5_STORE) if r["token"] == tok]
    print(f"  keyword '{keyword}' -> ids {hits}")


def t5_audit(user, rsa_sign_pub):
    if not t5_can(user, "audit"):
        raise PermissionError("not allowed")
    for rec in load_store(T5_STORE):
        h, s = t5_verify(rec, rsa_sign_pub)
        print(f"  record {rec['id']}: {'VALID' if h and s else 'INVALID'}")


def t5_menu():
    global T5_SEEN_NONCES
    T5_SEEN_NONCES = set()
    body_pub, body_priv = rsa_lib_keys(1024)            # hybrid body encryption
    sign_pub, sign_priv = rsa_keygen(1024)              # signatures
    index_key = get_random_bytes(16)
    paill_pub, paill_priv = paillier_keygen(512)
    while True:
        u = input("\nlogin (1/2/3, quit): ").strip()
        if u == "quit":
            return
        role = T5_ROLES.get(u)
        if not role:
            print("unknown"); continue
        while True:
            print(f"[{role}] 1.add 2.aggregate total 3.search 4.audit(verify only) 0.logout")
            c = input("choice: ").strip()
            if c == "0":
                break
            try:
                if c == "1":
                    kw = input("keyword: "); body = input("body: "); amt = int(input("amount: "))
                    t5_add(u, kw, body, amt, body_pub, index_key, paill_pub, sign_priv)
                elif c == "2":
                    t5_aggregate(u, paill_pub, paill_priv, sign_pub)
                elif c == "3":
                    t5_search(u, input("keyword: "), index_key)
                elif c == "4":
                    t5_audit(u, sign_pub)
            except PermissionError as e:
                print("DENIED:", e)


def t5_demo():
    global T5_STORE, T5_SEEN_NONCES
    T5_STORE = "._t5.json"; T5_SEEN_NONCES = set()
    open(T5_STORE, "w").write("[]")
    body_pub, body_priv = rsa_lib_keys(1024)            # for hybrid body encryption
    sign_pub, sign_priv = rsa_keygen(1024)              # for signatures
    index_key = get_random_bytes(16)
    paill_pub, paill_priv = paillier_keygen(512)
    r1 = t5_add("1", "x", "body1", 100, body_pub, index_key, paill_pub, sign_priv)
    r2 = t5_add("1", "y", "body2", 250, body_pub, index_key, paill_pub, sign_priv)
    assert t5_aggregate("2", paill_pub, paill_priv, sign_pub) == 350
    # body decrypts via the hybrid private key
    assert rsa_hybrid_decrypt(body_priv, bytes.fromhex(r1["enc_key"]),
                              bytes.fromhex(r1["iv"]), bytes.fromhex(r1["body"])) == b"body1"
    # replay check: first time ok, second time rejected
    assert t5_check_replay(r1) and not t5_check_replay(r1)
    os.remove(T5_STORE)
    print("T5 ok")


# #####################################################################################
#  TEMPLATE 6 -- ECC VARIANT (ECIES encryption + ECDSA signature)          [MED-HARD]
#  Q: role1 submits a record. The body is encrypted with ECC (ECIES = ECDH + AES) using
#     the exchange's ECC public key, and the record is signed with ECDSA (role1's ECC key).
#     role2 verifies the ECDSA signature and decrypts the body with the ECC private key.
#     role3 verifies only, never decrypts. (Use when the question says ECC / elliptic curve.)
# #####################################################################################
T6_STORE = "t6.json"
T6_ROLES = {"1": "role1", "2": "role2", "3": "role3"}
T6_PERMS = {"role1": {"add"}, "role2": {"open"}, "role3": {"audit"}}


def t6_can(user, perm):
    return perm in T6_PERMS.get(T6_ROLES.get(user), set())


def t6_add(user, body, enc_pub, sign_priv):
    if not t6_can(user, "add"):
        raise PermissionError("not allowed")
    eph_pem, iv, ct = ecies_encrypt(enc_pub, body.encode())      # ECIES body encryption
    rec = {"id": len(load_store(T6_STORE)) + 1, "eph": eph_pem, "iv": iv.hex(),
           "body": ct.hex(), "timestamp": timestamp()}
    payload = f"{rec['id']}|{rec['eph']}|{rec['iv']}|{rec['body']}|{rec['timestamp']}".encode()
    rec["sign"] = ecdsa_sign(payload, sign_priv).hex()           # ECDSA signature
    recs = load_store(T6_STORE); recs.append(rec); save_store(T6_STORE, recs)
    print(f"[STORED] record {rec['id']}")
    return rec


def t6_verify(rec, sign_pub):
    payload = f"{rec['id']}|{rec['eph']}|{rec['iv']}|{rec['body']}|{rec['timestamp']}".encode()
    return ecdsa_verify(payload, bytes.fromhex(rec["sign"]), sign_pub)


def t6_open(user, rid, enc_priv, sign_pub):
    if not t6_can(user, "open"):
        raise PermissionError("not allowed")
    rec = next((r for r in load_store(T6_STORE) if r["id"] == rid), None)
    if not rec:
        print("no such record"); return
    if not t6_verify(rec, sign_pub):
        print("  ECDSA verify FAILED -> not decrypting"); return
    body = ecies_decrypt(enc_priv, rec["eph"], bytes.fromhex(rec["iv"]), bytes.fromhex(rec["body"]))
    print("  verified; body:", body.decode())


def t6_menu():
    enc_pub, enc_priv = ecc_keygen()               # exchange ECC key (for ECIES)
    sign_pub, sign_priv = ecc_keygen()             # submitter ECC key (for ECDSA)
    while True:
        u = input("\nlogin (1/2/3, quit): ").strip()
        if u == "quit":
            return
        if u not in T6_ROLES:
            print("unknown"); continue
        while True:
            print(f"[{T6_ROLES[u]}] 1.add 2.open(verify+decrypt) 3.audit 0.logout")
            c = input("choice: ").strip()
            if c == "0":
                break
            try:
                if c == "1":
                    t6_add(u, input("body: "), enc_pub, sign_priv)
                elif c == "2":
                    t6_open(u, int(input("id: ")), enc_priv, sign_pub)
                elif c == "3":
                    for r in load_store(T6_STORE):
                        print(f"  record {r['id']}: {'VALID' if t6_verify(r, sign_pub) else 'INVALID'}")
            except PermissionError as e:
                print("DENIED:", e)


def t6_demo():
    global T6_STORE
    T6_STORE = "._t6.json"; open(T6_STORE, "w").write("[]")
    enc_pub, enc_priv = ecc_keygen(); sign_pub, sign_priv = ecc_keygen()
    r = t6_add("1", "ecc secret body", enc_pub, sign_priv)
    assert t6_verify(r, sign_pub)
    assert ecies_decrypt(enc_priv, r["eph"], bytes.fromhex(r["iv"]), bytes.fromhex(r["body"])) == b"ecc secret body"
    os.remove(T6_STORE)
    print("T6 ok")


# #####################################################################################
#  TEMPLATE 7 -- ELGAMAL VARIANT (ElGamal encryption + ElGamal signature)  [MED-HARD]
#  Q: role1 submits a short record. The body is encrypted with ElGamal (whole message as
#     one integer; needs a large p), and the record is signed with an ElGamal signature.
#     role2 verifies the signature and decrypts the body. role3 verifies only.
#     (Use when the question says ElGamal for BOTH encryption and signing.)
# #####################################################################################
T7_STORE = "t7.json"
T7_ROLES = {"1": "role1", "2": "role2", "3": "role3"}
T7_PERMS = {"role1": {"add"}, "role2": {"open"}, "role3": {"audit"}}


def t7_can(user, perm):
    return perm in T7_PERMS.get(T7_ROLES.get(user), set())


def t7_add(user, body, enc_pub, sign_pub, sign_priv):
    if not t7_can(user, "add"):
        raise PermissionError("not allowed")
    c1, c2 = elgamal_enc_text(body, enc_pub)                     # ElGamal encryption
    sp, sg, _ = sign_pub
    rec = {"id": len(load_store(T7_STORE)) + 1, "c1": str(c1), "c2": str(c2), "timestamp": timestamp()}
    payload = f"{rec['id']}|{rec['c1']}|{rec['c2']}|{rec['timestamp']}".encode()
    rec["sign"] = elgamal_sign(payload, sp, sg, sign_priv)       # ElGamal signature (r, s)
    recs = load_store(T7_STORE); recs.append(rec); save_store(T7_STORE, recs)
    print(f"[STORED] record {rec['id']}")
    return rec


def t7_verify(rec, sign_pub):
    sp, sg, sy = sign_pub
    payload = f"{rec['id']}|{rec['c1']}|{rec['c2']}|{rec['timestamp']}".encode()
    return elgamal_verify(payload, tuple(rec["sign"]), sp, sg, sy)


def t7_open(user, rid, enc_priv, enc_p, sign_pub):
    if not t7_can(user, "open"):
        raise PermissionError("not allowed")
    rec = next((r for r in load_store(T7_STORE) if r["id"] == rid), None)
    if not rec:
        print("no such record"); return
    if not t7_verify(rec, sign_pub):
        print("  ElGamal verify FAILED -> not decrypting"); return
    body = elgamal_dec_text((int(rec["c1"]), int(rec["c2"])), enc_priv, enc_p)
    print("  verified; body:", body)


def t7_menu():
    enc_pub, enc_priv = elgamal_enc_keygen(512)    # big p so a short message fits in one int
    sign_pub, sign_priv = elgamal_enc_keygen(256)
    while True:
        u = input("\nlogin (1/2/3, quit): ").strip()
        if u == "quit":
            return
        if u not in T7_ROLES:
            print("unknown"); continue
        while True:
            print(f"[{T7_ROLES[u]}] 1.add 2.open(verify+decrypt) 3.audit 0.logout")
            c = input("choice: ").strip()
            if c == "0":
                break
            try:
                if c == "1":
                    t7_add(u, input("short body: "), enc_pub, sign_pub, sign_priv)
                elif c == "2":
                    t7_open(u, int(input("id: ")), enc_priv, enc_pub[0], sign_pub)
                elif c == "3":
                    for r in load_store(T7_STORE):
                        print(f"  record {r['id']}: {'VALID' if t7_verify(r, sign_pub) else 'INVALID'}")
            except PermissionError as e:
                print("DENIED:", e)


def t7_demo():
    global T7_STORE
    T7_STORE = "._t7.json"; open(T7_STORE, "w").write("[]")
    enc_pub, enc_priv = elgamal_enc_keygen(512)
    sign_pub, sign_priv = elgamal_enc_keygen(256)
    r = t7_add("1", "elgamal body", enc_pub, sign_pub, sign_priv)
    assert t7_verify(r, sign_pub)
    assert elgamal_dec_text((int(r["c1"]), int(r["c2"])), enc_priv, enc_pub[0]) == "elgamal body"
    os.remove(T7_STORE)
    print("T7 ok")


# #####################################################################################
#  CS -- STANDALONE CLIENT / SERVER (reference for any sockets question)
#  Client hybrid-encrypts a message for the server and sends it; server decrypts with
#  its private key and replies. Run: `python templates.py server` then `... client`.
# #####################################################################################
def cs_server(host="127.0.0.1", port=7001):
    pub, priv = rsa_lib_keys(2048)
    with open("cs_pub.pem", "wb") as f:
        f.write(pub.export_key())
    with socket.socket() as srv:
        srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        srv.bind((host, port)); srv.listen(1)
        print(f"server on {host}:{port} (public key in cs_pub.pem)")
        conn, _ = srv.accept()
        with conn:
            pkt = recv_msg(conn)
            msg = rsa_hybrid_decrypt(priv, bytes.fromhex(pkt["k"]), bytes.fromhex(pkt["iv"]), bytes.fromhex(pkt["ct"]))
            print("decrypted:", msg.decode())
            send_msg(conn, {"status": "OK", "got": msg.decode()})


def cs_client(host="127.0.0.1", port=7001, message="hello server"):
    pub = RSA.import_key(open("cs_pub.pem", "rb").read())
    k, iv, ct = rsa_hybrid_encrypt(pub, message.encode())
    with socket.socket() as s:
        s.connect((host, port))
        send_msg(s, {"k": k.hex(), "iv": iv.hex(), "ct": ct.hex()})
        print("reply:", recv_msg(s))


# #####################################################################################
#  DISPATCHER
# #####################################################################################
def run_all_tests():
    t1_demo(); t2_demo(); t3_demo(); t4_demo(); t5_demo(); t6_demo(); t7_demo()
    print("ALL TEMPLATES OK")


if __name__ == "__main__":
    arg = sys.argv[1] if len(sys.argv) > 1 else ""
    if arg == "test":
        run_all_tests()
    elif arg == "server":
        cs_server()
    elif arg == "client":
        cs_client()
    else:
        print("Templates:")
        print("  1 = T1 secure-record (AES+SHA+RSA)   2 = T2 homomorphic (AES+Paillier+RSA)")
        print("  4 = T4 searchable (AES+SSE+ElGamal)  5 = T5 full combo")
        print("  6 = T6 ECC (ECIES + ECDSA)           7 = T7 ElGamal (encrypt + sign)")
        print("  (T3 DH+classical and CS are client/server: run them with the server/client args)")
        pick = input("run which menu? (1/2/4/5/6/7): ").strip()
        menus = {"1": t1_menu, "2": t2_menu, "4": t4_menu, "5": t5_menu, "6": t6_menu, "7": t7_menu}
        if pick in menus:
            menus[pick]()
        else:
            print("For T3: `python templates.py` can't do sockets inline -- call t3_server()/t3_client(),")
            print("or use CS: `python templates.py server` then `python templates.py client`.")
