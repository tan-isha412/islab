# =====================================================================================
#  LAB 7 + LAB 8  --  PARTIAL HOMOMORPHIC ENCRYPTION  +  SEARCHABLE ENCRYPTION
# =====================================================================================
#  HOW TO RUN
#    python lab78.py            -> demos of every scheme + manual exercise answers
#    python lab78.py test       -> self-test (should print ALL PASSED)
#    python lab78.py server     -> cloud server: stores ciphertexts, computes on them blind
#    python lab78.py client     -> uploads encrypted salaries / searches, never shares the key
#
#  BIG PICTURE
#    Homomorphic encryption = compute on ciphertexts; decrypt gives the result as if you
#    had computed on the plaintexts. The server never sees the data.
#      Paillier  -> ADDITIVE : E(a) * E(b)  decrypts to  a + b     (and E(a)^k -> k*a)
#      RSA/ElGamal -> MULTIPLICATIVE : E(a) * E(b) decrypts to a * b
#    "Partial" (PHE) = supports addition OR multiplication, not both.
#
#    Searchable encryption = search encrypted data without decrypting it. The trick:
#    index words by a DETERMINISTIC token (same word -> same token) so a query token can
#    be matched, while the documents themselves stay encrypted.
#      SSE  (symmetric)  -> token = HMAC(key, word)        fast, one secret key
#      PKSE (public-key) -> token via Paillier "is it zero?" check   flexible, slower
#
#  WHY THE MANUAL'S SAMPLE CODE IS BROKEN (and this file fixes it)
#    - "Paillier" sample actually calls RSA.generate and sets p=n//2: not Paillier at all,
#      never imports math, and decrypt uses an undefined variable. -> real Paillier in [A].
#    - ElGamal "homomorphic_comparison" does not compare anything. -> ElGamal can only
#      MULTIPLY; a true > test needs extra protocols. Shown honestly in [C].
#    - SSE sample encrypts the index with AES-CBC + random IV, so the same word gives a
#      different ciphertext each time and search NEVER matches. -> deterministic HMAC in [D].
#
#  INDEX
#    [A] Paillier (additive HE)        [D] SSE  (symmetric searchable, HMAC index)
#    [B] RSA multiplicative HE         [E] PKSE (Paillier-based searchable)
#    [C] ElGamal multiplicative HE     [F] sockets: blind cloud server + client
#    [G] demos / manual answers / self-test
# =====================================================================================
import math, json, socket, sys, time, hmac, hashlib, secrets
from Crypto.Util.number import getPrime, inverse, bytes_to_long, long_to_bytes, GCD
from Crypto.Cipher import AES
from Crypto.Random import get_random_bytes
from Crypto.Util.Padding import pad, unpad
import os


# =====================================================================================
# [EX] EXAM EXTRAS -- timestamp + JSON store (to persist an encrypted index / documents)
# =====================================================================================
def timestamp():
    return time.strftime("%Y-%m-%d %H:%M:%S")


def save_json(path, obj):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(obj, f, indent=2)


def load_json(path, default=None):
    if not os.path.exists(path):
        return {} if default is None else default
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


# =====================================================================================
# [A] PAILLIER  -- ADDITIVE homomorphic encryption
#   keygen: primes p, q -> n = p*q, lambda = lcm(p-1, q-1), g = n + 1,
#           mu = (L(g^lambda mod n^2))^-1 mod n, where L(u) = (u - 1) // n
#   encrypt m: pick random r in [1, n), c = g^m * r^n mod n^2
#   decrypt c: m = L(c^lambda mod n^2) * mu mod n
#   HOMOMORPHISM (the whole point):
#       E(m1) * E(m2) mod n^2        decrypts to  m1 + m2        (add two secrets)
#       E(m)^k mod n^2               decrypts to  k * m          (scalar multiply)
#       E(m) * g^k  mod n^2          decrypts to  m + k          (add a known constant)
#   The random r makes two encryptions of the same m look different (semantic security),
#   yet multiplying ciphertexts still adds the plaintexts.
# =====================================================================================
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


# =====================================================================================
# [B] RSA  -- MULTIPLICATIVE homomorphic encryption (textbook / unpadded RSA)
#   c1 = m1^e, c2 = m2^e  ->  c1*c2 = (m1*m2)^e mod n  ->  decrypts to m1*m2.
#   This works ONLY for textbook RSA. Real padding (OAEP) destroys the homomorphism
#   (which is good for security but means you cannot compute on OAEP ciphertexts).
# =====================================================================================
def rsa_keygen(bits=512, e=65537):
    while True:
        p, q = getPrime(bits // 2), getPrime(bits // 2)
        if p != q and math.gcd(e, (p - 1) * (q - 1)) == 1:
            break
    n = p * q
    return (n, e), (n, pow(e, -1, (p - 1) * (q - 1)))


def rsa_encrypt(m, pub):
    n, e = pub
    return pow(m % n, e, n)


def rsa_decrypt(c, priv):
    n, d = priv
    return pow(c, d, n)


def rsa_mul(c1, c2, pub):                      # E(m1)*E(m2) -> E(m1*m2)
    n, _ = pub
    return (c1 * c2) % n


# =====================================================================================
# [C] ELGAMAL  -- MULTIPLICATIVE homomorphic encryption
#   E(m1) = (g^k1, m1*y^k1), E(m2) = (g^k2, m2*y^k2).
#   Componentwise product = (g^(k1+k2), (m1*m2)*y^(k1+k2)) = E(m1*m2).
#   NOTE: ElGamal is NOT additively homomorphic, and it CANNOT do a ">" comparison on
#   its own (the manual's homomorphic_comparison is wrong). A real encrypted comparison
#   needs a dedicated protocol (e.g. DGK) or a different scheme.
# =====================================================================================
def elgamal_keygen(bits=256):
    p = getPrime(bits)
    g = 2
    x = secrets.randbelow(p - 3) + 2
    return (p, g, pow(g, x, p)), x


def elgamal_encrypt(m, pub, k=None):
    p, g, y = pub
    k = k or (secrets.randbelow(p - 3) + 2)
    return pow(g, k, p), (m % p) * pow(y, k, p) % p


def elgamal_decrypt(ct, x, p):
    c1, c2 = ct
    return (c2 * pow(pow(c1, x, p), -1, p)) % p


def elgamal_mul(ct1, ct2, p):                  # (c1a*c1b, c2a*c2b) -> E(m1*m2)
    return (ct1[0] * ct2[0]) % p, (ct1[1] * ct2[1]) % p


# =====================================================================================
# [D] SSE  -- Symmetric Searchable Encryption  (Lab 8 Exercise 1, FIXED)
#   Build an inverted index  word -> [doc ids].  The index KEY must be deterministic so a
#   query can match: token = HMAC-SHA256(index_key, word). The document bodies and the
#   doc-id lists are encrypted with AES (random IV is fine there -- we never match on them).
#   To search: client sends only the token; server returns matching encrypted doc ids;
#   client decrypts them. The server learns which encrypted docs matched, never the word.
#   Leakage to discuss: search pattern (same query -> same token) and access pattern.
# =====================================================================================
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


def sse_build_index(documents, keys):
    """documents = {doc_id: text}. Returns (encrypted_index, encrypted_docs)."""
    index = {}
    for doc_id, text in documents.items():
        for word in set(text.lower().split()):
            index.setdefault(sse_token(keys["index_key"], word), []).append(doc_id)
    enc_index = {tok: [_aes_enc(keys["data_key"], d.encode()) for d in ids]
                 for tok, ids in index.items()}
    enc_docs = {doc_id: _aes_enc(keys["data_key"], text.encode())
                for doc_id, text in documents.items()}
    return enc_index, enc_docs


def sse_search(enc_index, query, keys):
    """return the list of doc ids whose token matches the query token"""
    tok = sse_token(keys["index_key"], query)
    return [_aes_dec(keys["data_key"], d).decode() for d in enc_index.get(tok, [])]


# =====================================================================================
# [E] PKSE  -- Public-key searchable encryption (Lab 8 Exercise 2, done properly)
#   Paillier is probabilistic, so E(query) == E(word) is NEVER true -> you cannot compare
#   ciphertexts directly (this is why a naive PKSE "never matches"). Correct approach:
#   the server computes  E(word - query)  homomorphically  (= E(word) * E(query)^-1),
#   then BLINDS it with a random r:  E(r * (word - query)).  The client decrypts: a 0 means
#   word == query (because r*0 = 0); any other value is random, so the client learns only
#   match / no-match, not the word.
# =====================================================================================
def pkse_build_index(documents, pub):
    """index: word-hash -> ([Paillier E(word_int)], [doc ids]). Word hashed to an int < n."""
    n = pub[0]
    index = {}
    for doc_id, text in documents.items():
        for word in set(text.lower().split()):
            w_int = int(hashlib.sha256(word.encode()).hexdigest(), 16) % n
            key = hashlib.sha256(word.encode()).hexdigest()[:16]
            if key not in index:
                index[key] = {"enc_word": paillier_encrypt(w_int, pub), "docs": []}
            index[key]["docs"].append(doc_id)
    return index


def pkse_make_query(query, pub):
    """client encrypts the query word under the public key"""
    n = pub[0]
    q_int = int(hashlib.sha256(query.lower().encode()).hexdigest(), 16) % n
    return paillier_encrypt(q_int, pub)


def pkse_server_match(enc_word, enc_query, pub):
    """server computes E(r*(word - query)) WITHOUT the private key, r random per entry"""
    n, _ = pub
    diff = paillier_add(enc_word, paillier_mul_const(enc_query, n - 1, pub), pub)  # E(word-query)
    r = secrets.randbelow(n - 2) + 2
    return paillier_mul_const(diff, r, pub)                                        # E(r*(word-query))


def pkse_search(index, query, pub, priv):
    """server blinds each entry, client decrypts and keeps the ones that give 0"""
    enc_query = pkse_make_query(query, pub)
    hits = []
    for entry in index.values():
        blinded = pkse_server_match(entry["enc_word"], enc_query, pub)   # server side
        if paillier_decrypt(blinded, priv) == 0:                          # client side
            hits += entry["docs"]
    return hits


# =====================================================================================
# [F] SOCKETS -- blind cloud server + client (Lab 7 "server never sees the data")
#   Clients upload Paillier ciphertexts of their salaries. The server adds them
#   homomorphically and returns the encrypted total. Only the client (with the private
#   key) decrypts it. The server never learns any individual salary or the total.
# =====================================================================================
HOST, PORT = "127.0.0.1", 9000


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
    """stateful: ADD ciphertext to a running encrypted total, or return the total"""
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as srv:
        srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        srv.bind((host, port))
        srv.listen(5)
        print(f"Blind cloud server on {host}:{port} (it never sees plaintext)")
        encrypted_total = None
        count = 0
        while True:
            conn, _ = srv.accept()
            with conn:
                msg = recv_msg(conn)
                if msg["op"] == "add":
                    n = msg["n"]
                    c = int(msg["c"])
                    encrypted_total = c if encrypted_total is None else (encrypted_total * c) % (n * n)
                    count += 1
                    print(f"added entry #{count} (server sees only ciphertext {str(c)[:20]}...)")
                    send_msg(conn, {"status": "added", "count": count})
                elif msg["op"] == "total":
                    send_msg(conn, {"count": count, "encrypted_total": str(encrypted_total)})
                elif msg["op"] == "reset":
                    encrypted_total, count = None, 0
                    send_msg(conn, {"status": "reset"})


def client_upload(value, pub, host=HOST, port=PORT):
    c = paillier_encrypt(value, pub)
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.connect((host, port))
        send_msg(s, {"op": "add", "n": pub[0], "c": str(c)})
        return recv_msg(s)


def client_get_total(host=HOST, port=PORT):
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.connect((host, port))
        send_msg(s, {"op": "total"})
        return recv_msg(s)


def run_client(host=HOST, port=PORT):
    """HR generates the keypair; employees upload encrypted salaries; HR decrypts the sum"""
    pub, priv = paillier_keygen(512)
    print("HR generated a Paillier keypair. The server will get only the PUBLIC key.")
    raw = input("Enter salaries to upload (space separated): ")
    salaries = [int(x) for x in raw.split()]
    for i, sal in enumerate(salaries, 1):
        client_upload(sal, pub, host, port)
        print(f"  uploaded encrypted salary #{i}")
    reply = client_get_total(host, port)
    total = paillier_decrypt(int(reply["encrypted_total"]), priv)
    print(f"server combined {reply['count']} encrypted salaries without decrypting any")
    print(f"HR decrypts the total: {total}  (real sum = {sum(salaries)}, average = {total/len(salaries):.2f})")


# =====================================================================================
# [G] DEMOS + SELF-TEST
# =====================================================================================
def demo():
    line = lambda t: print("\n" + "=" * 15, t, "=" * 15)

    line("LAB 7 Q1  Paillier additive homomorphism")
    pub, priv = paillier_keygen(512)
    ca, cb = paillier_encrypt(15, pub), paillier_encrypt(25, pub)
    print("E(15):", str(ca)[:40], "...")
    print("E(25):", str(cb)[:40], "...")
    csum = paillier_add(ca, cb, pub)
    print("E(15)*E(25) decrypts to:", paillier_decrypt(csum, priv), "(expected 40)")
    print("E(15) scaled by 3 decrypts to:", paillier_decrypt(paillier_mul_const(ca, 3, pub), priv),
          "(expected 45)")
    print("two encryptions of 15 differ:", paillier_encrypt(15, pub) != paillier_encrypt(15, pub),
          "(random r -> semantic security)")

    line("LAB 7 Q2  RSA multiplicative homomorphism")
    rpub, rpriv = rsa_keygen(512)
    c7, c3 = rsa_encrypt(7, rpub), rsa_encrypt(3, rpub)
    print("E(7)*E(3) decrypts to:", rsa_decrypt(rsa_mul(c7, c3, rpub), rpriv), "(expected 21)")

    line("LAB 7 Additional 1a  ElGamal multiplicative homomorphism")
    epub, ex = elgamal_keygen(256)
    e4, e5 = elgamal_encrypt(4, epub), elgamal_encrypt(5, epub)
    print("E(4)*E(5) decrypts to:", elgamal_decrypt(elgamal_mul(e4, e5, epub[0]), ex, epub[0]),
          "(expected 20)")
    print("NOTE: ElGamal cannot ADD or COMPARE -- the manual's comparison code is wrong.")

    line("LAB 7  Secure salary sum (server never sees a salary)")
    salaries = [50000, 65000, 72000, 48000, 90000]
    enc_total = None
    for s in salaries:
        c = paillier_encrypt(s, pub)
        enc_total = c if enc_total is None else paillier_add(enc_total, c, pub)
    print("sum of 5 encrypted salaries decrypts to:", paillier_decrypt(enc_total, priv),
          "(real sum", sum(salaries), ")")

    line("LAB 8 Ex1  SSE -- symmetric searchable encryption")
    docs = {f"doc{i}": t for i, t in enumerate([
        "the patient has diabetes and hypertension",
        "annual report finance and budget",
        "diabetes treatment plan for the patient",
        "network security firewall and encryption",
        "patient records encryption and privacy",
        "budget forecast for finance team",
        "hypertension medication and diabetes care",
        "firewall rules and network monitoring",
        "privacy policy for patient records",
        "encryption keys and security audit"], 1)}
    keys = sse_setup()
    enc_index, enc_docs = sse_build_index(docs, keys)
    for q in ["diabetes", "encryption", "finance", "surgery"]:
        print(f"search {q!r:12} -> {sse_search(enc_index, q, keys)}")
    print("the server stores only tokens + ciphertext, never the words")

    line("LAB 8 Ex2  PKSE -- Paillier searchable encryption")
    ppub, ppriv = paillier_keygen(512)
    index = pkse_build_index(docs, ppub)
    for q in ["diabetes", "firewall", "surgery"]:
        print(f"search {q!r:12} -> {pkse_search(index, q, ppub, ppriv)}")
    print("match found via E(r*(word-query)) == E(0); server never learns the query word")


def self_test():
    pub, priv = paillier_keygen(512)
    assert paillier_decrypt(paillier_encrypt(123, pub), priv) == 123
    assert paillier_decrypt(paillier_add(paillier_encrypt(15, pub), paillier_encrypt(25, pub), pub), priv) == 40
    assert paillier_decrypt(paillier_mul_const(paillier_encrypt(7, pub), 3, pub), priv) == 21
    assert paillier_decrypt(paillier_add_const(paillier_encrypt(10, pub), 5, pub), priv) == 15
    assert paillier_encrypt(15, pub) != paillier_encrypt(15, pub)         # randomized
    total = None
    for v in [50000, 65000, 72000, 48000, 90000]:
        c = paillier_encrypt(v, pub)
        total = c if total is None else paillier_add(total, c, pub)
    assert paillier_decrypt(total, priv) == 325000

    rpub, rpriv = rsa_keygen(512)
    assert rsa_decrypt(rsa_mul(rsa_encrypt(7, rpub), rsa_encrypt(3, rpub), rpub), rpriv) == 21

    epub, ex = elgamal_keygen(256)
    assert elgamal_decrypt(elgamal_mul(elgamal_encrypt(4, epub), elgamal_encrypt(5, epub), epub[0]),
                           ex, epub[0]) == 20

    docs = {f"doc{i}": t for i, t in enumerate([
        "the patient has diabetes", "finance budget report", "diabetes treatment patient",
        "network security firewall", "patient records encryption", "budget finance team",
        "hypertension diabetes care", "firewall network monitoring", "privacy patient records",
        "encryption security audit"], 1)}
    keys = sse_setup()
    enc_index, enc_docs = sse_build_index(docs, keys)
    assert sse_token(keys["index_key"], "Diabetes") == sse_token(keys["index_key"], "diabetes")  # deterministic
    assert set(sse_search(enc_index, "diabetes", keys)) == {"doc1", "doc3", "doc7"}
    assert set(sse_search(enc_index, "patient", keys)) == {"doc1", "doc3", "doc5", "doc9"}
    assert sse_search(enc_index, "surgery", keys) == []
    assert _aes_dec(keys["data_key"], enc_docs["doc1"]).decode() == docs["doc1"]

    ppub, ppriv = paillier_keygen(512)
    index = pkse_build_index(docs, ppub)
    assert set(pkse_search(index, "diabetes", ppub, ppriv)) == {"doc1", "doc3", "doc7"}
    assert set(pkse_search(index, "firewall", ppub, ppriv)) == {"doc4", "doc8"}
    assert pkse_search(index, "surgery", ppub, ppriv) == []
    # exam extras
    assert len(timestamp()) == 19
    save_json("._t78", {"a": 1}); assert load_json("._t78")["a"] == 1; os.remove("._t78")
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
