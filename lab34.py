# =====================================================================================
#  LAB 3 + LAB 4  --  RSA, ElGamal, ECC, Diffie-Hellman, Rabin
#                     + Key Management + Access Control + attacks + client/server
# =====================================================================================
#  HOW TO RUN
#    python lab34.py            -> demos of every algorithm + manual exercise answers
#    python lab34.py test       -> self-test (should print ALL PASSED)
#    python lab34.py server     -> hospital receiver (decrypts with its private key)
#    python lab34.py client     -> hospital sender (encrypts with receiver public key)
#
#  BIG PICTURE
#    Asymmetric crypto uses a KEY PAIR: a public key (shareable) and a private key (secret).
#    Encrypt with the recipient's PUBLIC key -> only their PRIVATE key decrypts.
#    Sign with YOUR private key -> anyone verifies with your public key (that is Lab 6).
#    Security rests on a hard math problem:
#       RSA / Rabin -> factoring a big n = p*q
#       ElGamal / DH -> discrete log (find x given g^x mod p)
#       ECC          -> discrete log on an elliptic curve (smaller keys, same strength)
#
#  INDEX
#    [A] number helpers           [F] Rabin (4 roots)            [bonus] Rabin vs RSA
#    [B] RSA                       [G] attacks (Fermat, rho, shared prime, small e, k reuse)
#    [C] ElGamal                   [H] key management (entropy/KDF/rotation/expiry + KMS)
#    [D] Diffie-Hellman            [I] access control (RBAC/ABAC/BLP/MAC/DAC/time)
#    [E] ECC (ECDH + ECIES)        [J] sockets + hospital client/server
#    [K] demos / manual answers / self-test
# =====================================================================================
import math, time, json, socket, sys, random
from Crypto.PublicKey import RSA, ECC
from Crypto.Cipher import AES, PKCS1_OAEP
from Crypto.Random import get_random_bytes
from Crypto.Util.number import getPrime, isPrime, inverse, bytes_to_long, long_to_bytes
from Crypto.Util.Padding import pad, unpad
from Crypto.Protocol.KDF import PBKDF2
from Crypto.Hash import SHA256
import os


# =====================================================================================
# [EX] EXAM EXTRAS -- menu-driven RBAC runner + JSON record store + timestamp
#   The skeleton every 3-role question (Client/Lawyer/Officer, Doctor/Nurse/Admin...) wants.
# =====================================================================================
def timestamp():
    return time.strftime("%Y-%m-%d %H:%M:%S")


def run_menu(role, actions):
    """actions = {"1": ("Encrypt", func), ...}. Shows only this role's options, loops."""
    print(f"\n--- logged in as: {role} ---")
    while True:
        print()
        for key, (label, _) in actions.items():
            print(f"  {key}. {label}")
        print("  0. Logout")
        choice = input("choice: ").strip()
        if choice == "0":
            print("bye"); return
        if choice in actions:
            try:
                actions[choice][1]()
            except Exception as e:
                print("ERROR:", e)
        else:
            print("not allowed / invalid option")


def require(condition, message):
    """gate helper: raise with a clear message when a validation fails"""
    if not condition:
        raise PermissionError(message)


def save_record(path, record):
    """append one dict to a JSON-list file (bytes must already be .hex() strings)"""
    records = load_records(path)
    records.append(record)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(records, f, indent=2)


def load_records(path):
    if not os.path.exists(path):
        return []
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


# =====================================================================================
# [A] NUMBER HELPERS
#   pow(base, exp, mod)   -> fast modular exponentiation (base^exp mod mod)
#   pow(a, -1, m)         -> modular inverse (a * result = 1 mod m); needs gcd(a,m)=1
#   bytes_to_long / long_to_bytes -> turn text into one big integer and back, because
#   these ciphers operate on NUMBERS, not strings.
# =====================================================================================
def egcd(a, b):                                  # extended gcd: returns g, x, y: ax+by=g
    if b == 0:
        return a, 1, 0
    g, x, y = egcd(b, a % b)
    return g, y, x - (a // b) * y


def text_to_int(s):
    return bytes_to_long(s.encode())


def int_to_text(n):
    return long_to_bytes(n).decode()


# =====================================================================================
# [B] RSA
#   keygen : pick primes p, q -> n = p*q, phi = (p-1)(q-1), pick e with gcd(e,phi)=1,
#            d = e^-1 mod phi.  public (n,e), private (n,d)
#   encrypt: c = m^e mod n          decrypt: m = c^d mod n       (needs 0 <= m < n)
#   Why it works: m^(ed) = m mod n because ed = 1 mod phi (Euler's theorem).
#   Security: recovering d needs phi, which needs the factors p, q of n.
# =====================================================================================
def rsa_keygen(bits=1024, e=65537):
    while True:
        p, q = getPrime(bits // 2), getPrime(bits // 2)
        if p != q and math.gcd(e, (p - 1) * (q - 1)) == 1:
            break
    n = p * q
    d = pow(e, -1, (p - 1) * (q - 1))
    return (n, e), (n, d), (p, q)


def rsa_encrypt_int(m, pub):
    n, e = pub
    if not 0 <= m < n:
        raise ValueError("message integer must be < n (use chunks or hybrid encryption)")
    return pow(m, e, n)


def rsa_decrypt_int(c, priv):
    n, d = priv
    return pow(c, d, n)


def rsa_encrypt_text(text, pub):                 # whole message as one integer (needs small msg, big n)
    return rsa_encrypt_int(text_to_int(text), pub)


def rsa_decrypt_text(c, priv):
    return int_to_text(rsa_decrypt_int(c, priv))


def rsa_encrypt_chars(text, pub):                # tiny n (e.g. 323): one char at a time
    return [rsa_encrypt_int(ord(ch), pub) for ch in text]


def rsa_decrypt_chars(cs, priv):
    return "".join(chr(rsa_decrypt_int(c, priv)) for c in cs)


# library RSA with OAEP padding (what you use in practice: randomized + safe)
def rsa_lib_keys(bits=2048):
    k = RSA.generate(bits)
    return k.publickey(), k


def rsa_oaep_encrypt(pub_key, data):             # max ~ bits/8 - 42 bytes (190 B at 2048)
    return PKCS1_OAEP.new(pub_key).encrypt(data)


def rsa_oaep_decrypt(priv_key, ct):
    return PKCS1_OAEP.new(priv_key).decrypt(ct)


# RSA is slow and size-limited, so for real data use HYBRID: RSA wraps a random AES key
def rsa_hybrid_encrypt(pub_key, data):
    aes_key = get_random_bytes(16)
    iv = get_random_bytes(16)
    ct = AES.new(aes_key, AES.MODE_CBC, iv).encrypt(pad(data, 16))
    return rsa_oaep_encrypt(pub_key, aes_key), iv, ct


def rsa_hybrid_decrypt(priv_key, enc_key, iv, ct):
    aes_key = rsa_oaep_decrypt(priv_key, enc_key)
    return unpad(AES.new(aes_key, AES.MODE_CBC, iv).decrypt(ct), 16)


# =====================================================================================
# [C] ELGAMAL  (based on the discrete log problem)
#   public (p, g, y) with y = g^x mod p; private x
#   encrypt: pick random k -> c1 = g^k mod p, c2 = m * y^k mod p -> (c1, c2)
#   decrypt: s = c1^x mod p, m = c2 * s^-1 mod p
#   CRUCIAL: a fresh random k EVERY message. Reusing k leaks messages (see [G]).
# =====================================================================================
def elgamal_keygen(bits=256):
    p = getPrime(bits)
    g = 2
    x = random.randint(2, p - 2)
    y = pow(g, x, p)
    return (p, g, y), x


def elgamal_encrypt_int(m, pub, k=None):
    p, g, y = pub
    if not 0 <= m < p:
        raise ValueError("m must be < p")
    k = k or random.randint(2, p - 2)
    return pow(g, k, p), (m * pow(y, k, p)) % p


def elgamal_decrypt_int(ct, x, p):
    c1, c2 = ct
    return (c2 * pow(pow(c1, x, p), -1, p)) % p


def elgamal_encrypt_text(text, pub):
    return elgamal_encrypt_int(text_to_int(text), pub)


def elgamal_decrypt_text(ct, x, p):
    return int_to_text(elgamal_decrypt_int(ct, x, p))


def elgamal_encrypt_chars(text, pub):            # small p: char by char
    return [elgamal_encrypt_int(ord(ch), pub) for ch in text]


def elgamal_decrypt_chars(cts, x, p):
    return "".join(chr(elgamal_decrypt_int(ct, x, p)) for ct in cts)


# =====================================================================================
# [D] DIFFIE-HELLMAN  (agree on a shared secret over a public channel)
#   public p, g.  Alice: a secret, A = g^a mod p.  Bob: b secret, B = g^b mod p.
#   They swap A and B.  Shared = B^a = A^b = g^(ab) mod p.  An eavesdropper sees A, B
#   but needs the discrete log to get a or b.  (Plain DH has no authentication, so it
#   is open to a man-in-the-middle unless each public value is signed -- Lab 6.)
# =====================================================================================
def dh_params(bits=512):
    return getPrime(bits), 2


def dh_keypair(p, g):
    a = random.randint(2, p - 2)
    return a, pow(g, a, p)                        # private a, public A


def dh_shared(their_public, my_private, p):
    return pow(their_public, my_private, p)


def secret_to_aes_key(secret, size=16, salt=b"dh-salt"):
    """turn a DH / ECDH number into an AES key with a KDF"""
    return PBKDF2(str(secret), salt, size, count=100000, hmac_hash_module=SHA256)


# =====================================================================================
# [E] ECC  --  same security as RSA with much smaller keys
#   curve: y^2 = x^3 + ax + b (mod p). Public key Q = d*G (G = base point, d = private).
#   ECDH: shared = d_A * Q_B = d_B * Q_A.  ECIES = ECC "encryption" = ECDH + AES (hybrid).
# =====================================================================================
def ecc_keygen(curve="P-256"):                   # P-256 == secp256r1 == prime256v1
    k = ECC.generate(curve=curve)
    return k.public_key(), k                      # k.d private int, k.pointQ public point


def ecdh_shared(my_priv, their_pub):
    return int((their_pub.pointQ * my_priv.d).x)


def ecies_encrypt(recipient_pub, data):
    """ephemeral key r, shared = r*Q, AES-CBC under it; send R = r*G + iv + ct"""
    eph = ECC.generate(curve=recipient_pub.curve)
    key = secret_to_aes_key(int((recipient_pub.pointQ * eph.d).x))
    iv = get_random_bytes(16)
    ct = AES.new(key, AES.MODE_CBC, iv).encrypt(pad(data, 16))
    return eph.public_key().export_key(format="PEM"), iv, ct


def ecies_decrypt(priv_key, eph_pem, iv, ct):
    eph = ECC.import_key(eph_pem)
    key = secret_to_aes_key(int((eph.pointQ * priv_key.d).x))   # d*R = d*r*G = r*Q
    return unpad(AES.new(key, AES.MODE_CBC, iv).decrypt(ct), 16)


# tiny textbook curve for by-hand questions: point add / scalar multiply
def ec_add(P, Q, a, p):
    if P is None:
        return Q
    if Q is None:
        return P
    (x1, y1), (x2, y2) = P, Q
    if x1 == x2 and (y1 + y2) % p == 0:
        return None
    lam = ((3 * x1 * x1 + a) * pow(2 * y1, -1, p) if P == Q
           else (y2 - y1) * pow(x2 - x1, -1, p)) % p
    x3 = (lam * lam - x1 - x2) % p
    return x3, (lam * (x1 - x3) - y1) % p


def ec_mul(k, P, a, p):
    R = None
    while k:
        if k & 1:
            R = ec_add(R, P, a, p)
        P = ec_add(P, P, a, p)
        k >>= 1
    return R


# =====================================================================================
# [F] RABIN  (security = factoring; decryption gives FOUR roots)
#   keygen: primes p = q = 3 (mod 4), n = p*q.  encrypt: c = m^2 mod n.
#   decrypt: mp = c^((p+1)/4) mod p, mq = c^((q+1)/4) mod q, combine with CRT -> 4 roots.
#   Problem: which of the 4 is the message? -> add a known marker (redundancy) and keep
#   the root that ends with it.
# =====================================================================================
REDUNDANCY = b"##"


def rabin_keygen(bits=512):
    def prime_3mod4(b):
        while True:
            x = getPrime(b)
            if x % 4 == 3:
                return x
    p = prime_3mod4(bits // 2)
    q = prime_3mod4(bits // 2)
    while q == p:
        q = prime_3mod4(bits // 2)
    return p * q, (p, q)


def rabin_encrypt_int(m, n):
    return pow(m, 2, n)


def rabin_roots(c, p, q):
    n = p * q
    mp = pow(c, (p + 1) // 4, p)
    mq = pow(c, (q + 1) // 4, q)
    _, yp, yq = egcd(p, q)                        # yp*p + yq*q = 1
    r1 = (yp * p * mq + yq * q * mp) % n
    r3 = (yp * p * mq - yq * q * mp) % n
    return [r1, n - r1, r3, n - r3]


def rabin_encrypt_text(text, n):
    return rabin_encrypt_int(bytes_to_long(text.encode() + REDUNDANCY), n)


def rabin_decrypt_text(c, p, q):
    for r in rabin_roots(c, p, q):
        b = long_to_bytes(r)
        if b.endswith(REDUNDANCY):
            return b[:-len(REDUNDANCY)].decode()
    raise ValueError("no root carried the redundancy marker")


# =====================================================================================
# [G] ATTACKS  (each one exploits a MISTAKE in how the scheme was used)
# =====================================================================================
def fermat_factor(n, max_steps=10_000_000):
    """p and q too CLOSE: n = a^2 - b^2 = (a-b)(a+b). Start a at ceil(sqrt(n))."""
    a = math.isqrt(n)
    if a * a < n:
        a += 1
    for _ in range(max_steps):
        b2 = a * a - n
        b = math.isqrt(b2)
        if b * b == b2:
            return a - b, a + b
        a += 1
    raise ValueError("Fermat failed (primes not close enough)")


def pollard_rho(n):
    """one prime factor SMALL"""
    if n % 2 == 0:
        return 2
    while True:
        x = y = random.randint(2, n - 1)
        c = random.randint(1, n - 1)
        d = 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = math.gcd(abs(x - y), n)
        if d != n:
            return d


def common_factor_attack(n1, n2):
    """two keys SHARE a prime (bad randomness): gcd(n1,n2) reveals it"""
    p = math.gcd(n1, n2)
    if p in (1, n1):
        raise ValueError("no shared factor")
    return p, n1 // p, n2 // p


def rsa_private_from_factors(p, q, e):
    return pow(e, -1, (p - 1) * (q - 1))


def rsa_break(n, e, c, method="fermat"):
    p, q = fermat_factor(n) if method == "fermat" else (lambda f: (f, n // f))(pollard_rho(n))
    d = rsa_private_from_factors(p, q, e)
    return p, q, d, pow(c, d, n)


def integer_root(x, k):
    lo, hi = 0, 1 << (x.bit_length() // k + 1)
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid ** k <= x:
            lo = mid
        else:
            hi = mid - 1
    return lo


def small_e_attack(c, e=3):
    """no padding + small e + m^e < n: c is NOT reduced, so m = integer e-th root of c"""
    m = integer_root(c, e)
    if m ** e != c:
        raise ValueError("m^e wrapped around n; attack does not apply")
    return m


def elgamal_k_reuse(ct1, ct2, m1, p):
    """same k for two messages -> same c1. s = c2_1 * m1^-1, then m2 = c2_2 * s^-1"""
    if ct1[0] != ct2[0]:
        raise ValueError("c1 values differ: k was not reused")
    s = (ct1[1] * pow(m1, -1, p)) % p
    return (ct2[1] * pow(s, -1, p)) % p


# =====================================================================================
# [H] KEY MANAGEMENT  (Lab 4 formulas + a full KMS class)
# =====================================================================================
def key_entropy(probs):                          # H(K) = -sum p*log2(p)
    return -sum(p * math.log2(p) for p in probs if p > 0)


def uniform_key_entropy(num_keys):               # all keys equally likely
    return math.log2(num_keys)


def derive_key(password, salt=None, iterations=100000, size=32):
    salt = salt or get_random_bytes(16)          # DK = KDF(password, salt, iterations)
    return PBKDF2(password, salt, size, count=iterations, hmac_hash_module=SHA256), salt


def rotation_rate(num_keys, period):             # N / T
    return num_keys / period


def expiry_time(t0, lifetime):                   # Expiry = t0 + L
    return t0 + lifetime


def is_expired(t0, lifetime, now=None):
    return (now if now is not None else time.time()) > expiry_time(t0, lifetime)


class KeyManager:
    """generate / store (encrypted) / distribute / revoke / renew / expire / audit"""

    def __init__(self, master_password, lifetime=3600):
        self.master_key, _ = derive_key(master_password)
        self.lifetime = lifetime
        self.keys = {}
        self.log = []

    def _audit(self, event):
        line = f"{time.strftime('%H:%M:%S')} {event}"
        self.log.append(line)
        print("[AUDIT]", line)

    def _enc(self, data):
        iv = get_random_bytes(16)
        return iv, AES.new(self.master_key, AES.MODE_CBC, iv).encrypt(pad(data, 16))

    def _dec(self, iv, ct):
        return unpad(AES.new(self.master_key, AES.MODE_CBC, iv).decrypt(ct), 16)

    def generate(self, owner, kind="RSA", bits=2048):
        if kind == "RSA":
            k = RSA.generate(bits)
            pub, priv = k.publickey().export_key(), k.export_key()
        elif kind == "RABIN":
            n, (p, q) = rabin_keygen(bits)
            pub, priv = str(n).encode(), json.dumps([p, q]).encode()
        else:
            raise ValueError("kind must be RSA or RABIN")
        self.keys[owner] = {"kind": kind, "public": pub, "private": self._enc(priv),
                            "created": time.time(), "revoked": False}
        self._audit(f"GENERATE {kind} key for {owner}")

    def _check(self, owner):
        rec = self.keys.get(owner)
        if rec is None:
            raise KeyError(f"{owner} has no key")
        if rec["revoked"]:
            raise PermissionError(f"{owner}'s key is revoked")
        if is_expired(rec["created"], self.lifetime):
            raise PermissionError(f"{owner}'s key expired")
        return rec

    def get_public(self, owner):
        rec = self._check(owner)
        self._audit(f"DISTRIBUTE public key of {owner}")
        return rec["public"]

    def get_private(self, owner, requester):
        if requester != owner:
            self._audit(f"DENIED {requester} -> private key of {owner}")
            raise PermissionError("only the owner may use its private key")
        rec = self._check(owner)
        self._audit(f"DISTRIBUTE private key to {owner}")
        return self._dec(*rec["private"])

    def revoke(self, owner):
        self.keys[owner]["revoked"] = True
        self._audit(f"REVOKE {owner}")

    def renew(self, owner):
        self.generate(owner, self.keys[owner]["kind"])
        self._audit(f"RENEW {owner}")


# =====================================================================================
# [I] ACCESS CONTROL MODELS
# =====================================================================================
ROLE_PERMS = {"doctor": {("records", "read"), ("records", "write")},
              "nurse": {("records", "read")},
              "admin": {("keys", "revoke"), ("records", "read")}}
USER_ROLES = {"alice": {"doctor"}, "bob": {"nurse"}, "carol": {"admin"}}


def rbac_access(user, obj, action):              # role-based
    return any((obj, action) in ROLE_PERMS.get(r, set()) for r in USER_ROLES.get(user, set()))


def abac_access(user, obj, env):                 # attribute-based
    return (user["department"] == obj["department"] and user["clearance"] >= obj["sensitivity"]
            and env.get("location") == "on-site")


LEVELS = {"PUBLIC": 0, "CONFIDENTIAL": 1, "SECRET": 2, "TOPSECRET": 3}


def blp_can_read(subj, obj):                     # Bell-LaPadula: no read up (S >= C)
    return LEVELS[subj] >= LEVELS[obj]


def blp_can_write(subj, obj):                    # no write down (S <= C)
    return LEVELS[subj] <= LEVELS[obj]


def mac_access(clearance, classification, policy_ok=True):
    return LEVELS[clearance] >= LEVELS[classification] and policy_ok


ACCESS_MATRIX = {"alice": {"file1": {"read", "write", "own"}}, "bob": {"file1": {"read"}}}


def dac_access(subject, obj, right):
    return right in ACCESS_MATRIX.get(subject, {}).get(obj, set())


def dac_grant(owner, subject, obj, right):
    if not dac_access(owner, obj, "own"):
        raise PermissionError(f"{owner} does not own {obj}")
    ACCESS_MATRIX.setdefault(subject, {}).setdefault(obj, set()).add(right)


def time_access(start_hour, end_hour, now_hour=None):
    h = now_hour if now_hour is not None else time.localtime().tm_hour
    return start_hour <= h < end_hour


# =====================================================================================
# [J] SOCKETS + HOSPITAL CLIENT / SERVER
#   A asks the KMS (here: a shared file) for B's public key, encrypts with hybrid RSA,
#   and sends. B decrypts with its own private key (owner-only). An identity token under
#   a DH shared secret proves "really from A, really to B".
# =====================================================================================
HOST, PORT = "127.0.0.1", 7000


def recv_exact(sock, n):
    buf = b""
    while len(buf) < n:
        part = sock.recv(n - len(buf))
        if not part:
            raise ConnectionError("connection closed")
        buf += part
    return buf


def send_msg(sock, obj):
    data = json.dumps(obj).encode()
    sock.sendall(len(data).to_bytes(4, "big") + data)


def recv_msg(sock):
    n = int.from_bytes(recv_exact(sock, 4), "big")
    return json.loads(recv_exact(sock, n).decode())


def run_server(host=HOST, port=PORT):
    print("Generating RSA-2048 key pair for this hospital...")
    pub, priv = rsa_lib_keys(2048)
    with open("server_pub.pem", "wb") as f:                      # publish the public key
        f.write(pub.export_key())
    print("Public key written to server_pub.pem (give this to senders).")
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as srv:
        srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        srv.bind((host, port))
        srv.listen(1)
        print(f"Server listening on {host}:{port} ...")
        conn, _ = srv.accept()
        with conn:
            pkt = recv_msg(conn)
            print("Received from", pkt["from"])
            data = rsa_hybrid_decrypt(priv, bytes.fromhex(pkt["enc_key"]),
                                      bytes.fromhex(pkt["iv"]), bytes.fromhex(pkt["ct"]))
            print("Decrypted (only this hospital's private key can do this):", data.decode())
            send_msg(conn, {"status": "OK", "received": data.decode()})


def run_client(host=HOST, port=PORT):
    name = input("Sender hospital name: ")
    data = input("Patient data to send: ")
    try:
        pub = RSA.import_key(open("server_pub.pem", "rb").read())
    except FileNotFoundError:
        print("server_pub.pem not found -- start the server first so it publishes its key.")
        return
    enc_key, iv, ct = rsa_hybrid_encrypt(pub, data.encode())
    print("Encrypted with the receiver's PUBLIC key.")
    print("  RSA-wrapped AES key:", enc_key.hex()[:48], "...")
    print("  ciphertext         :", ct.hex())
    pkt = {"from": name, "enc_key": enc_key.hex(), "iv": iv.hex(), "ct": ct.hex()}
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.connect((host, port))
        send_msg(s, pkt)
        print("Server reply:", recv_msg(s))


# =====================================================================================
# [K] DEMOS + SELF-TEST
# =====================================================================================
def demo():
    line = lambda t: print("\n" + "=" * 15, t, "=" * 15)

    line("LAB 3 Q1  RSA 'Asymmetric Encryption' (OAEP, 2048)")
    pub, priv = rsa_lib_keys(2048)
    c = rsa_oaep_encrypt(pub, b"Asymmetric Encryption")
    print(c.hex()[:48], "... ->", rsa_oaep_decrypt(priv, c))

    line("LAB 3 Q2  ECC 'Secure Transactions' (ECIES, P-256)")
    epub, epriv = ecc_keygen()
    packed = ecies_encrypt(epub, b"Secure Transactions")
    print("ct:", packed[2].hex(), "->", ecies_decrypt(epriv, *packed))

    line("LAB 3 Q3  ElGamal 'Confidential Data'")
    pk, x = elgamal_keygen(256)
    ct = elgamal_encrypt_text("Confidential Data", pk)
    print("(c1,c2) first 20 digits:", str(ct[0])[:20], "...  ->", elgamal_decrypt_text(ct, x, pk[0]))

    line("LAB 3 Q5  Diffie-Hellman with timing")
    t0 = time.perf_counter()
    p, g = dh_params(512)
    a, A = dh_keypair(p, g)
    b, B = dh_keypair(p, g)
    t1 = time.perf_counter()
    ka, kb = dh_shared(B, a, p), dh_shared(A, b, p)
    print(f"keygen {1000*(t1-t0):.1f} ms | exchange equal: {ka == kb}")

    line("LAB 3 Additional 1  ElGamal p=7919 g=2 x=2999")
    h = pow(2, 2999, 7919)
    print(f"manual says h=6465, real h={h} (manual is WRONG)")
    cts = elgamal_encrypt_chars("Asymmetric Algorithms", (7919, 2, h))
    print("decrypt:", elgamal_decrypt_chars(cts, 2999, 7919))

    line("LAB 3 Additional 3  RSA n=323 e=5 d=173")
    cs = rsa_encrypt_chars("Cryptographic Protocols", (323, 5))
    print("cipher:", cs[:6], "...  -> plain:", rsa_decrypt_chars(cs, (323, 173)))

    line("LAB 4  Rabin (4 roots, redundancy picks the right one)")
    n, (p, q) = rabin_keygen(512)
    c = rabin_encrypt_text("patient 42", n)
    print("4 roots:", [hex(r)[:14] + "..." for r in rabin_roots(c, p, q)])
    print("chosen by redundancy:", rabin_decrypt_text(c, p, q))

    line("LAB 4  attack: weak RSA with close primes")
    p = getPrime(256)
    q = p + 2
    while not isPrime(q):
        q += 2
    n, e = p * q, 65537
    c = pow(text_to_int("secret plan"), e, n)
    fp, fq, d, m = rsa_break(n, e, c, "fermat")
    print("factored correctly:", {fp, fq} == {p, q}, "| recovered:", long_to_bytes(m))
    print("mitigation: 2048-bit n, independent random primes, |p-q| large, use OAEP")

    line("LAB 4  attack: ElGamal reused k")
    pk, x = elgamal_keygen(128)
    k = 123456789
    ct1 = elgamal_encrypt_int(1111, pk, k)
    ct2 = elgamal_encrypt_int(2222, pk, k)
    print("recovered m2 =", elgamal_k_reuse(ct1, ct2, 1111, pk[0]), "(should be 2222)")

    line("LAB 4  Key Manager")
    km = KeyManager("master-pass", lifetime=3600)
    km.generate("HospitalA", "RSA")
    km.generate("ClinicB", "RABIN", 512)
    km.get_public("HospitalA")
    try:
        km.get_private("HospitalA", "ClinicB")
    except PermissionError as e:
        print("->", e)
    km.revoke("ClinicB")
    try:
        km.get_public("ClinicB")
    except PermissionError as e:
        print("->", e)

    line("LAB 4  access control")
    print("RBAC nurse write records :", rbac_access("bob", "records", "write"))
    print("RBAC doctor write records:", rbac_access("alice", "records", "write"))
    print("BLP SECRET read TOPSECRET:", blp_can_read("SECRET", "TOPSECRET"))
    print("BLP SECRET write PUBLIC  :", blp_can_write("SECRET", "PUBLIC"))
    print("Time access 10h in 9-17  :", time_access(9, 17, 10))

    line("Rabin vs RSA trade-off")
    print("""  Rabin: decryption is a single squaring inverse (fast), but gives 4 candidate
         roots -> needs redundancy to disambiguate; security PROVABLY equals factoring.
  RSA  : one unique plaintext, flexible (sign + encrypt), huge real-world use; security
         'only' believed to equal factoring. Both broken if n is factored.""")


def self_test():
    pub, priv, (p, q) = rsa_keygen(512)
    assert rsa_decrypt_text(rsa_encrypt_text("hi rsa", pub), priv) == "hi rsa"
    assert rsa_decrypt_chars(rsa_encrypt_chars("Cryptographic Protocols", (323, 5)), (323, 173)) \
        == "Cryptographic Protocols"
    rp, rk = rsa_lib_keys(1024)
    assert rsa_oaep_decrypt(rk, rsa_oaep_encrypt(rp, b"hello")) == b"hello"
    assert rsa_hybrid_decrypt(rk, *rsa_hybrid_encrypt(rp, b"x" * 5000)) == b"x" * 5000

    pk, x = elgamal_keygen(256)
    assert elgamal_decrypt_text(elgamal_encrypt_text("hi elgamal", pk), x, pk[0]) == "hi elgamal"
    assert pow(2, 2999, 7919) == 3868
    assert elgamal_decrypt_chars(elgamal_encrypt_chars("Asym", (7919, 2, 3868)), 2999, 7919) == "Asym"

    p2, g = dh_params(256)
    a, A = dh_keypair(p2, g)
    b, B = dh_keypair(p2, g)
    assert dh_shared(B, a, p2) == dh_shared(A, b, p2)
    assert secret_to_aes_key(dh_shared(B, a, p2)) == secret_to_aes_key(dh_shared(A, b, p2))

    e1, d1 = ecc_keygen()
    e2, d2 = ecc_keygen()
    assert ecdh_shared(d1, e2) == ecdh_shared(d2, e1)
    assert ecies_decrypt(d1, *ecies_encrypt(e1, b"ecc data")) == b"ecc data"
    assert ec_add((3, 10), (9, 7), 1, 23) == (17, 20)            # Stallings textbook example
    assert ec_mul(2, (3, 10), 1, 23) == (7, 12)

    n, (rp2, rq2) = rabin_keygen(512)
    assert rp2 % 4 == 3 and rq2 % 4 == 3
    assert rabin_decrypt_text(rabin_encrypt_text("rabin ok", n), rp2, rq2) == "rabin ok"
    assert 99 in rabin_roots(rabin_encrypt_int(99, n), rp2, rq2)

    pp = getPrime(128)
    qq = pp + 2
    while not isPrime(qq):
        qq += 2
    assert sorted(fermat_factor(pp * qq)) == sorted([pp, qq])
    small, big = getPrime(30), getPrime(200)
    assert pollard_rho(small * big) in (small, big)
    s = getPrime(128)
    assert common_factor_attack(s * getPrime(128), s * getPrime(128))[0] == s
    assert small_e_attack(pow(text_to_int("hi"), 3)) == text_to_int("hi")
    pk2, _ = elgamal_keygen(128)
    assert elgamal_k_reuse(elgamal_encrypt_int(1111, pk2, 42), elgamal_encrypt_int(2222, pk2, 42),
                           1111, pk2[0]) == 2222

    assert key_entropy([0.25] * 4) == 2.0 and uniform_key_entropy(2 ** 128) == 128.0
    dk, salt = derive_key("pw")
    assert derive_key("pw", salt)[0] == dk
    assert expiry_time(100, 50) == 150 and is_expired(100, 50, now=151)
    km = KeyManager("mp", lifetime=3600)
    km.generate("A", "RSA", 1024)
    assert km.get_public("A")
    try:
        km.get_private("A", "B")
        raise AssertionError("should deny")
    except PermissionError:
        pass
    km.revoke("A")
    try:
        km.get_public("A")
        raise AssertionError("revoked key served")
    except PermissionError:
        pass
    assert rbac_access("alice", "records", "write") and not rbac_access("bob", "records", "write")
    assert blp_can_read("SECRET", "CONFIDENTIAL") and not blp_can_read("CONFIDENTIAL", "SECRET")
    assert blp_can_write("CONFIDENTIAL", "SECRET") and not blp_can_write("SECRET", "PUBLIC")
    assert abac_access({"department": "icu", "clearance": 3}, {"department": "icu", "sensitivity": 2},
                       {"location": "on-site"})
    assert dac_access("bob", "file1", "read") and not dac_access("bob", "file1", "write")
    assert time_access(9, 17, 12) and not time_access(9, 17, 20)
    # exam extras
    assert len(timestamp()) == 19
    try:
        require(False, "nope"); raise AssertionError
    except PermissionError:
        pass
    save_record("._t34", {"id": 1}); save_record("._t34", {"id": 2})
    assert len(load_records("._t34")) == 2 and load_records("._t34")[1]["id"] == 2
    os.remove("._t34")
    print("ALL PASSED")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "demo"
    if cmd == "test":
        self_test()
    elif cmd == "server":
        run_server()
    elif cmd == "client":
        run_client()
    else:
        demo()
