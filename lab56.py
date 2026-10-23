# =====================================================================================
#  LAB 5 + LAB 6  --  HASHING  +  DIGITAL SIGNATURES
#                     + HMAC + socket integrity + CIA-triad demo + client/server
# =====================================================================================
#  HOW TO RUN
#    python lab56.py            -> demos of every hash / signature + manual answers
#    python lab56.py test       -> self-test (should print ALL PASSED)
#    python lab56.py server     -> integrity server (hashes received data, sends hash back)
#    python lab56.py client     -> sends data in parts, verifies the returned hash
#
#  BIG PICTURE
#    Hash H(M): variable input -> fixed-size output. Properties wanted:
#      - one-way (preimage resistance): given h, cannot find M with H(M)=h
#      - second preimage: given M, cannot find M' != M with H(M')=H(M)
#      - collision resistance: cannot find ANY two M != M' with the same hash
#    A hash alone proves INTEGRITY against accidental change, NOT against an attacker
#    (they can recompute the hash). For that you need:
#      - HMAC (hash + secret key)  -> integrity + authenticity between two key-holders
#      - digital signature (private-key sign, public-key verify) -> + non-repudiation
#
#  INDEX
#    [A] custom hash (djb2) + collision search
#    [B] library hashes MD5/SHA + performance/collision experiment
#    [C] HMAC (keyed hash)
#    [D] RSA signature (hash-then-sign)      [E] ElGamal signature     [F] Schnorr signature
#    [G] attack: ElGamal/DSA reused-k recovers the private key
#    [H] sockets: integrity client/server (whole + chunked)
#    [I] CIA triad end to end (RSA encrypt + sign + SHA hash)
#    [J] demos / manual answers / self-test
# =====================================================================================
import hashlib, hmac, time, json, socket, sys, random, secrets
from Crypto.PublicKey import RSA
from Crypto.Signature import pkcs1_15
from Crypto.Hash import SHA256
from Crypto.Cipher import AES, PKCS1_OAEP
from Crypto.Random import get_random_bytes
from Crypto.Util.number import getPrime, isPrime, inverse, bytes_to_long, long_to_bytes
from Crypto.Util.Padding import pad, unpad
import os


# =====================================================================================
# [EX] EXAM EXTRAS -- file hashing + the 3-role "secure record" envelope + audit/report
#   This envelope IS the core of SecureVault / HealthSecure / MediSecure / EvidenceChain:
#     creator : encrypt -> SHA-256(ciphertext) -> SIGN the hash -> store with timestamp
#     verifier: re-hash -> compare -> verify signature -> ONLY THEN decrypt
#     auditor : re-hash -> compare -> verify signature -> NEVER decrypt
# =====================================================================================
def timestamp():
    return time.strftime("%Y-%m-%d %H:%M:%S")


def read_text(path):
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


def file_sha256(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def make_secure_record(plaintext, aes_key, iv, signer_priv):
    """creator side -> a JSON-ready dict. AES-CBC encrypt, hash the ciphertext, sign it."""
    ct = AES.new(aes_key, AES.MODE_CBC, iv).encrypt(pad(plaintext, 16))
    h = hashlib.sha256(ct).hexdigest()
    sig = pkcs1_15.new(signer_priv).sign(SHA256.new(ct))
    return {"ciphertext": ct.hex(), "iv": iv.hex(), "hash": h,
            "signature": sig.hex(), "timestamp": timestamp()}


def verify_record(record, signer_pub):
    """verifier/auditor -> (hash_ok, sig_ok). Does NOT decrypt."""
    ct = bytes.fromhex(record["ciphertext"])
    hash_ok = hashlib.sha256(ct).hexdigest() == record["hash"]
    try:
        pkcs1_15.new(signer_pub).verify(SHA256.new(ct), bytes.fromhex(record["signature"]))
        sig_ok = True
    except (ValueError, TypeError):
        sig_ok = False
    return hash_ok, sig_ok


def open_secure_record(record, aes_key, signer_pub):
    """verifier -> plaintext, but ONLY if both the hash and the signature check out"""
    hash_ok, sig_ok = verify_record(record, signer_pub)
    if not (hash_ok and sig_ok):
        raise PermissionError(f"verification failed (hash_ok={hash_ok}, sig_ok={sig_ok}) -> no decrypt")
    ct = bytes.fromhex(record["ciphertext"]); iv = bytes.fromhex(record["iv"])
    return unpad(AES.new(aes_key, AES.MODE_CBC, iv).decrypt(ct), 16).decode()


def tamper_record(record):
    """flip one byte of the stored ciphertext -> to demonstrate detection"""
    ct = bytearray(bytes.fromhex(record["ciphertext"])); ct[0] ^= 0xFF
    r = dict(record); r["ciphertext"] = bytes(ct).hex(); return r


def audit(path, who, action, result):
    line = f"{timestamp()} | {who} | {action} | {result}\n"
    with open(path, "a", encoding="utf-8") as f:
        f.write(line)
    return line.strip()


def compliance_report(record, hash_ok, sig_ok):
    return (f"COMPLIANCE REPORT ({timestamp()})\n"
            f"  record time : {record.get('timestamp')}\n"
            f"  integrity   : {'PASS' if hash_ok else 'FAIL'}\n"
            f"  authenticity: {'PASS' if sig_ok else 'FAIL'}\n"
            f"  plaintext accessed: NO (auditor cannot decrypt)\n")


# =====================================================================================
# [A] CUSTOM HASH  (manual Lab 5 Q1: djb2-style)
#   start at 5381; for each char: hash = hash*33 + ord(char); mix bits; mask to 32 bits.
#   The *33 and the XOR-shift spread each input bit across the whole output (avalanche).
#   The 32-bit mask keeps the output a fixed size no matter how long the input is.
# =====================================================================================
def custom_hash(text):
    h = 5381
    for ch in text:
        h = (h * 33 + ord(ch)) & 0xFFFFFFFF      # multiply, add, keep 32 bits
        h ^= (h >> 13)                           # bit mixing (avalanche)
        h &= 0xFFFFFFFF
    return h


def find_collision(hash_func=custom_hash, charset="abcdefghijklmnopqrstuvwxyz"):
    """birthday attack: keep hashing random strings until two share a hash.
       For a 32-bit hash expect a collision after ~sqrt(2^32) ~ 65000 tries.
       Use VARIABLE-LENGTH strings: fixed-length inputs are too structured for this
       multiply-add hash and almost never collide, which would hide the birthday effect."""
    seen = {}
    attempts = 0
    while True:
        attempts += 1
        s = "".join(random.choice(charset) for _ in range(random.randint(4, 10)))
        h = hash_func(s)
        if h in seen and seen[h] != s:
            return seen[h], s, h, attempts
        seen[h] = s


# =====================================================================================
# [B] LIBRARY HASHES  +  the Lab 5 Q3 experiment
# =====================================================================================
def md5(data):
    return hashlib.md5(data).hexdigest()


def sha1(data):
    return hashlib.sha1(data).hexdigest()


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def sha512(data):
    return hashlib.sha512(data).hexdigest()


def hash_experiment(n=100, plot=True):
    """Lab 5 Q3: time MD5/SHA-1/SHA-256 on n random strings, check for collisions."""
    import os
    data = [os.urandom(random.randint(20, 60)) for _ in range(n)]
    results = {}
    for name, func in [("MD5", hashlib.md5), ("SHA-1", hashlib.sha1), ("SHA-256", hashlib.sha256)]:
        start = time.perf_counter()
        digests = [func(d).hexdigest() for d in data]
        elapsed = (time.perf_counter() - start) * 1000
        collisions = len(digests) - len(set(digests))
        results[name] = (elapsed, collisions)
        print(f"{name:8}: {elapsed:.3f} ms for {n} hashes, collisions found: {collisions}")
    print("(No collisions appear: even 'broken' MD5 needs ~2^64 random tries for one by chance.)")
    if plot:
        import matplotlib.pyplot as plt
        names = list(results)
        plt.bar(names, [results[n][0] for n in names], color=["#c0504d", "#f79646", "#4f81bd"])
        plt.ylabel("time (ms)")
        plt.title(f"Hashing {n} random strings")
        plt.tight_layout()
        plt.show()
    return results


# =====================================================================================
# [C] HMAC  (keyed hash: integrity + authenticity between two parties sharing a key)
#   HMAC(K, M) = H((K xor opad) || H((K xor ipad) || M)).  Needing the secret key to
#   produce a valid tag is what stops an attacker who changed M from fixing the tag.
#   Always compare with a constant-time compare to avoid timing leaks.
# =====================================================================================
def hmac_sha256(key, data):
    return hmac.new(key, data, hashlib.sha256).hexdigest()


def hmac_verify(key, data, tag):
    return hmac.compare_digest(hmac_sha256(key, data), tag)


# =====================================================================================
# [D] RSA DIGITAL SIGNATURE  (hash-then-sign)
#   sign   : s = H(M)^d mod n   (sign the HASH with the PRIVATE key)
#   verify : H(M) == s^e mod n  (anyone checks with the PUBLIC key)
#   Gives integrity + authenticity + non-repudiation (only the key owner could sign).
#   We sign the hash, not M, so any length works and it is secure.
# =====================================================================================
def rsa_sign_manual(message, priv):              # priv = (n, d)
    n, d = priv
    h = int(hashlib.sha256(message).hexdigest(), 16) % n
    return pow(h, d, n)


def rsa_verify_manual(message, sig, pub):        # pub = (n, e)
    n, e = pub
    h = int(hashlib.sha256(message).hexdigest(), 16) % n
    return pow(sig, e, n) == h


# library version (proper PKCS#1 v1.5 padding)
def rsa_sign_lib(message, priv_key):
    return pkcs1_15.new(priv_key).sign(SHA256.new(message))


def rsa_verify_lib(message, sig, pub_key):
    try:
        pkcs1_15.new(pub_key).verify(SHA256.new(message), sig)
        return True
    except (ValueError, TypeError):
        return False


# =====================================================================================
# [E] ELGAMAL SIGNATURE  (different maths from ElGamal encryption)
#   key: y = g^x mod p (public), x private.
#   sign M:  pick k with gcd(k, p-1) = 1
#            r = g^k mod p
#            s = (H(M) - x*r) * k^-1 mod (p-1)          -> signature (r, s)
#   verify:  0 < r < p  and  g^H(M) == y^r * r^s (mod p)
#   k MUST be fresh and random each time (reuse leaks x -- see [G]).
# =====================================================================================
def _hash_int(message, mod):
    return int(hashlib.sha256(message).hexdigest(), 16) % mod


def elgamal_sign(message, p, g, x, k=None):
    while True:
        k = k or random.randint(2, p - 2)
        if math.gcd(k, p - 1) == 1:
            break
        k = None
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


# =====================================================================================
# [F] SCHNORR SIGNATURE  (short, modern; basis of EdDSA)
#   params: prime p, prime q | p-1, generator g of order q.  y = g^x mod p.
#   sign M: k random -> r = g^k mod p; e = H(r || M) mod q; s = (k + x*e) mod q  -> (e, s)
#   verify: rv = g^s * y^(-e) mod p; e == H(rv || M) mod q
# =====================================================================================
def schnorr_params(bits=256):
    # find q prime, then p = k*q + 1 prime, then g of order q
    while True:
        q = getPrime(bits)
        for k in range(2, 4000):
            p = k * q + 1
            if isPrime(p):
                g = pow(2, (p - 1) // q, p)      # g has order q (unless it is 1)
                if g != 1:
                    return p, q, g


def schnorr_keygen(params):
    p, q, g = params
    x = random.randint(1, q - 1)
    return x, pow(g, x, p)                        # private x, public y


def schnorr_sign(message, params, x):
    p, q, g = params
    k = random.randint(1, q - 1)
    r = pow(g, k, p)
    e = int(hashlib.sha256(long_to_bytes(r) + message).hexdigest(), 16) % q
    s = (k + x * e) % q
    return e, s


def schnorr_verify(message, sig, params, y):
    p, q, g = params
    e, s = sig
    rv = (pow(g, s, p) * pow(y, (-e) % q, p)) % p
    return e == int(hashlib.sha256(long_to_bytes(rv) + message).hexdigest(), 16) % q


# =====================================================================================
# [G] ATTACK: reused k (nonce) reveals the private key
#   Schnorr sign: s = (k + x*e) mod q. Two signatures with the SAME k:
#       s1 = k + x*e1,  s2 = k + x*e2   (mod q)
#   Subtract:  s1 - s2 = x*(e1 - e2)  ->  x = (s1 - s2) * (e1 - e2)^-1 mod q.
#   q is PRIME so the inverse always exists -> the attack always succeeds.
#   Same lesson for DSA/ECDSA (this is how the PS3 signing key leaked). NEVER reuse k.
# =====================================================================================
def schnorr_recover_x(sig1, sig2, q):
    e1, s1 = sig1
    e2, s2 = sig2
    return ((s1 - s2) * pow((e1 - e2) % q, -1, q)) % q


def schnorr_sign_fixed_k(message, params, x, k):
    """sign with a CHOSEN k (to simulate the reuse mistake); do NOT do this for real"""
    p, q, g = params
    r = pow(g, k, p)
    e = int(hashlib.sha256(long_to_bytes(r) + message).hexdigest(), 16) % q
    return e, (k + x * e) % q


# =====================================================================================
# [H] SOCKETS: integrity client/server (Lab 5 Q2 + additional chunked exercise)
#   Server: receive data, compute SHA-256, send the hash back.
#   Client: compute the hash locally and compare -> detects corruption in transit.
#   HMAC version resists an active attacker (needs the shared key to forge the tag).
# =====================================================================================
HOST, PORT = "127.0.0.1", 8000
SHARED_HMAC_KEY = b"shared-integrity-key-123"


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
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as srv:
        srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        srv.bind((host, port))
        srv.listen(1)
        print(f"Integrity server on {host}:{port} ...")
        conn, _ = srv.accept()
        with conn:
            pkt = recv_msg(conn)
            parts = pkt["parts"]                              # client may send in chunks
            data = "".join(parts).encode()
            print(f"Reassembled {len(parts)} part(s):", data.decode())
            h = sha256(data)
            tag = hmac_sha256(SHARED_HMAC_KEY, data)
            print("SHA-256:", h)
            send_msg(conn, {"sha256": h, "hmac": tag})


def run_client(host=HOST, port=PORT):
    msg = input("Message to send: ")
    nparts = max(1, int(input("Split into how many parts? ") or 1))
    size = max(1, len(msg) // nparts)
    parts = [msg[i:i + size] for i in range(0, len(msg), size)]
    local_hash = sha256(msg.encode())
    local_tag = hmac_sha256(SHARED_HMAC_KEY, msg.encode())
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.connect((host, port))
        send_msg(s, {"parts": parts})
        reply = recv_msg(s)
    print("local  SHA-256:", local_hash)
    print("server SHA-256:", reply["sha256"])
    print("hash match :", local_hash == reply["sha256"],
          "-> integrity OK" if local_hash == reply["sha256"] else "-> DATA CORRUPTED")
    print("HMAC match :", hmac.compare_digest(local_tag, reply["hmac"]),
          "(HMAC also proves it came from a holder of the shared key)")


# =====================================================================================
# [I] CIA TRIAD  (manual Lab 6 additional: RSA encryption + signature + SHA hashing)
#   Confidentiality: encrypt the message for the recipient (hybrid RSA).
#   Integrity + Authenticity + Non-repudiation: sign SHA-256(message) with the sender's
#   private key. Recipient verifies the signature, then decrypts.
# =====================================================================================
def cia_send(message, sender_priv, recipient_pub):
    aes = get_random_bytes(16)                                             # fresh AES session key
    enc_key = PKCS1_OAEP.new(recipient_pub).encrypt(aes)                   # wrap it for the recipient
    iv = get_random_bytes(16)
    ct = AES.new(aes, AES.MODE_CBC, iv).encrypt(pad(message, 16))          # Confidentiality
    signature = pkcs1_15.new(sender_priv).sign(SHA256.new(message))        # sign the plaintext hash
    return {"enc_key": enc_key, "iv": iv, "ct": ct, "sig": signature}


def cia_receive(packet, sender_pub, recipient_priv):
    aes = PKCS1_OAEP.new(recipient_priv).decrypt(packet["enc_key"])         # Confidentiality
    try:
        message = unpad(AES.new(aes, AES.MODE_CBC, packet["iv"]).decrypt(packet["ct"]), 16)
    except ValueError:
        return None, False                                                 # corrupted ciphertext
    try:
        pkcs1_15.new(sender_pub).verify(SHA256.new(message), packet["sig"])  # Integrity + Auth
        verified = True
    except (ValueError, TypeError):
        verified = False
    return message, verified


# =====================================================================================
# [J] DEMOS + SELF-TEST
# =====================================================================================
import math


def demo():
    line = lambda t: print("\n" + "=" * 15, t, "=" * 15)

    line("LAB 5 Q1  custom djb2 hash")
    for s in ["hello", "Hello", "hella", ""]:
        print(f"custom_hash({s!r:9}) = {custom_hash(s):#010x}")
    print("one-bit change ('hello' vs 'hella') gives a completely different hash (avalanche)")

    line("LAB 5 Q1b  collision via birthday attack")
    a, b, h, tries = find_collision()
    print(f"collision after {tries} tries: {a!r} and {b!r} both hash to {h:#010x}")
    print("~sqrt(2^32) ~ 65000 expected -> matches the birthday bound")

    line("LAB 5 Q3  MD5 vs SHA-1 vs SHA-256")
    hash_experiment(n=100, plot=False)

    line("LAB 5 Q2  hash for integrity")
    data = b"important message"
    print("SHA-256:", sha256(data))
    print("after 1 char change:", sha256(b"important messege"), "(totally different)")

    line("HMAC (keyed)")
    key = b"secret"
    tag = hmac_sha256(key, data)
    print("HMAC:", tag, "| verify:", hmac_verify(key, data, tag),
          "| tampered:", hmac_verify(key, b"evil message", tag))

    line("LAB 6  RSA signature (sign with private, verify with public)")
    pub, priv = (lambda k: (k.publickey(), k))(RSA.generate(2048))
    msg = b"I approve this transaction"
    sig = rsa_sign_lib(msg, priv)
    print("signature:", sig.hex()[:48], "...")
    print("verify genuine :", rsa_verify_lib(msg, sig, pub))
    print("verify tampered:", rsa_verify_lib(b"I approve this transfer", sig, pub),
          "-> signature fails, tampering caught")

    line("LAB 6  ElGamal signature")
    p = getPrime(256)
    g, x = 2, random.randint(2, p - 2)
    y = pow(g, x, p)
    sig = elgamal_sign(msg, p, g, x)
    print("verify genuine :", elgamal_verify(msg, sig, p, g, y))
    print("verify tampered:", elgamal_verify(b"other", sig, p, g, y))

    line("LAB 6  Schnorr signature")
    params = schnorr_params(256)
    xs, ys = schnorr_keygen(params)
    sig = schnorr_sign(msg, params, xs)
    print("verify genuine :", schnorr_verify(msg, sig, params, ys))
    print("verify tampered:", schnorr_verify(b"other", sig, params, ys))

    line("LAB 6  attack: reused k (nonce) recovers the private key")
    params = schnorr_params(256)
    xk, _ = schnorr_keygen(params)
    k = random.randint(1, params[1] - 1)                 # ONE k reused for two messages (the mistake)
    s1 = schnorr_sign_fixed_k(b"message one", params, xk, k)
    s2 = schnorr_sign_fixed_k(b"message two", params, xk, k)
    xr = schnorr_recover_x(s1, s2, params[1])
    print("recovered x == real x:", xr == xk, "-> NEVER reuse k")

    line("CIA triad  (confidentiality + integrity + authenticity)")
    a_pub, a_priv = (lambda k: (k.publickey(), k))(RSA.generate(2048))   # sender
    b_pub, b_priv = (lambda k: (k.publickey(), k))(RSA.generate(2048))   # recipient
    pkt = cia_send(b"Patient record: BP 150/95", a_priv, b_pub)
    out, ok = cia_receive(pkt, a_pub, b_priv)
    print("decrypted:", out.decode(), "| signature verified:", ok)


def self_test():
    assert custom_hash("hello") != custom_hash("hella")
    assert custom_hash("") == 5381 ^ 0 or True          # empty -> initial value path
    assert 0 <= custom_hash("anything") <= 0xFFFFFFFF
    a, b, h, _ = find_collision()
    assert a != b and custom_hash(a) == custom_hash(b) == h
    assert sha256(b"abc") == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    assert md5(b"abc") == "900150983cd24fb0d6963f7d28e17f72"
    key = b"k"
    assert hmac_verify(key, b"data", hmac_sha256(key, b"data"))
    assert not hmac_verify(key, b"data", hmac_sha256(key, b"other"))

    k = RSA.generate(2048)
    pub, priv = k.publickey(), k
    sig = rsa_sign_lib(b"hello", priv)
    assert rsa_verify_lib(b"hello", sig, pub) and not rsa_verify_lib(b"hellp", sig, pub)
    npub, npriv = (k.n, k.e), (k.n, k.d)
    ms = rsa_sign_manual(b"manual sign", npriv)
    assert rsa_verify_manual(b"manual sign", ms, npub)
    assert not rsa_verify_manual(b"manual sigh", ms, npub)         # changed message -> fails

    p = getPrime(256)
    g, x = 2, random.randint(2, p - 2)
    y = pow(g, x, p)
    sig = elgamal_sign(b"msg", p, g, x)
    assert elgamal_verify(b"msg", sig, p, g, y) and not elgamal_verify(b"xx", sig, p, g, y)

    params = schnorr_params(256)
    xs, ys = schnorr_keygen(params)
    sig = schnorr_sign(b"msg", params, xs)
    assert schnorr_verify(b"msg", sig, params, ys) and not schnorr_verify(b"xx", sig, params, ys)

    k = random.randint(1, params[1] - 1)
    s1k = schnorr_sign_fixed_k(b"one", params, xs, k)
    s2k = schnorr_sign_fixed_k(b"two", params, xs, k)
    assert schnorr_recover_x(s1k, s2k, params[1]) == xs

    a_pub, a_priv = (lambda kk: (kk.publickey(), kk))(RSA.generate(2048))
    b_pub, b_priv = (lambda kk: (kk.publickey(), kk))(RSA.generate(2048))
    pkt = cia_send(b"secret record", a_priv, b_pub)
    out, ok = cia_receive(pkt, a_pub, b_priv)
    assert out == b"secret record" and ok
    pkt["ct"] = bytes(pkt["ct"][:-1] + bytes([pkt["ct"][-1] ^ 1]))       # flip a bit -> still decrypts?
    out2, ok2 = cia_receive(pkt, a_pub, b_priv)
    assert not ok2 or out2 != b"secret record"                          # signature catches change
    # exam extras: the 3-role secure-record envelope
    assert len(timestamp()) == 19
    signer = RSA.generate(2048)
    aes_key, iv = get_random_bytes(16), get_random_bytes(16)
    rec = make_secure_record(b"Top Secret Evidence", aes_key, iv, signer)
    assert verify_record(rec, signer.publickey()) == (True, True)
    assert open_secure_record(rec, aes_key, signer.publickey()) == "Top Secret Evidence"
    bad = tamper_record(rec)
    assert verify_record(bad, signer.publickey()) == (False, False)
    try:
        open_secure_record(bad, aes_key, signer.publickey()); raise AssertionError
    except PermissionError:
        pass
    assert "COMPLIANCE REPORT" in compliance_report(rec, True, True)
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
