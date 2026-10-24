# =====================================================================================
#  LAB 1 + LAB 2  --  CLASSICAL CIPHERS  +  DES / 3DES / AES  +  CLIENT / SERVER
# =====================================================================================
#  HOW TO RUN
#    python lab12.py              -> demos of every cipher + manual exercise answers
#    python lab12.py test         -> self-test (should print ALL PASSED)
#    python lab12.py server       -> receiver on port 5000
#    python lab12.py client       -> sender: choose ANY chain of ciphers, sends to server
#
#  EXAM STRATEGY
#    Every function is a separate chunk. Copy the ones the question needs + the
#    SOCKET chunk [K], wire them in main, and PRINT EVERY INTERMEDIATE VALUE.
#
#  INDEX (search for the tag)
#    [A] helpers                    [G] DES / 3DES / AES, all modes
#    [B] additive / mult / affine   [H] AES from scratch (prints every round)
#    [C] vigenere / autokey         [I] integrity: CBC-MAC + corruption detection
#    [D] playfair                   [J] ECB leak, benchmark + plot
#    [E] hill                       [K] sockets + layered client/server
#    [F] transposition + attacks    [L] demos / manual answers / self-test
# =====================================================================================
import math, time, json, socket, sys
from Crypto.Cipher import AES, DES, DES3
from Crypto.Random import get_random_bytes
from Crypto.Util.Padding import pad, unpad
import hashlib


# =====================================================================================
# [EX] EXAM EXTRAS -- timestamps, .txt files, user-typed key/IV, DES-CBC one-liners
#   (used by the role-based record questions: SecureVault, MediSecure, HealthSecure...)
# =====================================================================================
def timestamp():
    """local time 'YYYY-MM-DD HH:MM:SS' for every stored record / log entry"""
    return time.strftime("%Y-%m-%d %H:%M:%S")


def read_text(path):
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


def write_text(path, text):
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)


def read_bytes(path):
    with open(path, "rb") as f:
        return f.read()


def write_bytes(path, data):
    with open(path, "wb") as f:
        f.write(data)


def key_from_text(text, size=16):
    """turn a user-typed string into a `size`-byte key: use it if it's exact hex/ASCII,
    else SHA-256 it and take the first `size` bytes (16=AES128, 24=192, 32=256, 8=DES)."""
    try:
        b = bytes.fromhex(text)
        if len(b) == size:
            return b
    except ValueError:
        pass
    if len(text.encode()) == size:
        return text.encode()
    return hashlib.sha256(text.encode()).digest()[:size]


def aes_cbc_encrypt_iv(key, data, iv):         # AES-CBC with a GIVEN iv (MediSecure style)
    return AES.new(key, AES.MODE_CBC, iv).encrypt(pad(data, 16))


def aes_cbc_decrypt_iv(key, ct, iv):
    return unpad(AES.new(key, AES.MODE_CBC, iv).decrypt(ct), 16)


def des_cbc_encrypt(key, data, iv):            # DES-CBC (SecureVault): key and iv are 8 bytes
    return DES.new(key, DES.MODE_CBC, iv).encrypt(pad(data, 8))


def des_cbc_decrypt(key, ct, iv):
    return unpad(DES.new(key, DES.MODE_CBC, iv).decrypt(ct), 8)


# =====================================================================================
# [A] HELPERS
#   Classical ciphers treat letters as numbers a=0 ... z=25 (the set Z26) and work
#   "mod 26", so results wrap around (z + 1 = a).
# =====================================================================================
def clean(text):
    """lowercase + letters only: 'I am X!' -> 'iamx'  (manual: 'ignore the spaces')"""
    return "".join(ch for ch in text.lower() if ch.isalpha())


def to_nums(text):                       # 'abc' -> [0, 1, 2]
    return [ord(ch) - 97 for ch in clean(text)]


def to_text(nums):                       # [0, 1, 2] -> 'abc'   (% 26 also fixes negatives)
    return "".join(chr(n % 26 + 97) for n in nums)


def key_from(s, size):
    """Exam keys come as text. Work out the bytes:
       '0123456789ABCDEF0123456789ABCDEF' = 32 hex chars  = 16 bytes -> AES-128
       'A1B2C3D4'                          = 8 ASCII chars = 8 bytes  -> DES
    Hex is tried first, then ASCII."""
    try:
        b = bytes.fromhex(s)
        if len(b) == size:
            return b
    except ValueError:
        pass
    if len(s) == size:
        return s.encode()
    raise ValueError(f"key '{s}' is not {size} bytes ({size*2} hex chars or {size} ASCII chars)")


# =====================================================================================
# [B] ADDITIVE (Caesar/shift), MULTIPLICATIVE, AFFINE  -- monoalphabetic substitution
#   monoalphabetic: a plaintext letter ALWAYS becomes the same ciphertext letter, so
#   letter frequencies survive -> breakable by frequency analysis / brute force.
#
#   additive        C = (P + k) mod 26        key space 26
#   multiplicative  C = (P * k) mod 26        k needs an inverse mod 26: gcd(k,26) = 1
#                                             k in {1,3,5,7,9,11,15,17,19,21,23,25} -> 12 keys
#   affine          C = (a*P + b) mod 26      key space 12 * 26 = 312
#   affine decrypt  P = a^-1 * (C - b) mod 26 (a^-1 = pow(a, -1, 26))
# =====================================================================================
def additive_encrypt(text, k):
    return to_text([p + k for p in to_nums(text)])


def additive_decrypt(text, k):
    return to_text([c - k for c in to_nums(text)])


def multiplicative_encrypt(text, k):
    if math.gcd(k, 26) != 1:
        raise ValueError("multiplicative key must be coprime with 26")
    return to_text([p * k for p in to_nums(text)])


def multiplicative_decrypt(text, k):
    k_inv = pow(k, -1, 26)               # modular inverse: k * k_inv = 1 (mod 26)
    return to_text([c * k_inv for c in to_nums(text)])


def affine_encrypt(text, a, b):
    if math.gcd(a, 26) != 1:
        raise ValueError("a must be coprime with 26: 1,3,5,7,9,11,15,17,19,21,23,25")
    return to_text([a * p + b for p in to_nums(text)])


def affine_decrypt(text, a, b):
    a_inv = pow(a, -1, 26)
    return to_text([a_inv * (c - b) for c in to_nums(text)])


def shift_keep_symbols(text, k):
    """shift that keeps case + symbols (for ciphertexts like 'NCJ/AE&Z' in the manual)"""
    out = ""
    for ch in text:
        if ch.isalpha():
            base = 65 if ch.isupper() else 97
            out += chr((ord(ch) - base + k) % 26 + base)
        else:
            out += ch
    return out


# =====================================================================================
# [C] VIGENERE, AUTOKEY  -- polyalphabetic substitution
#   polyalphabetic: the same letter can become DIFFERENT letters (the key changes with
#   position), which hides frequencies better.
#   vigenere  Ci = (Pi + K[i mod len(K)]) mod 26     keyword repeats
#   autokey   k1 = key, k(i) = P(i-1)                key stream = key + plaintext itself
#             decrypt rebuilds the stream from the letters it just recovered
# =====================================================================================
def vigenere_encrypt(text, key):
    p, k = to_nums(text), to_nums(key)
    return to_text([p[i] + k[i % len(k)] for i in range(len(p))])


def vigenere_decrypt(text, key):
    c, k = to_nums(text), to_nums(key)
    return to_text([c[i] - k[i % len(k)] for i in range(len(c))])


def autokey_encrypt(text, key):
    """key = int (manual: 'autokey with key = 7') or a keyword string"""
    p = to_nums(text)
    stream = ([key] if isinstance(key, int) else to_nums(key)) + p
    return to_text([p[i] + stream[i] for i in range(len(p))])


def autokey_decrypt(text, key):
    c = to_nums(text)
    stream = [key] if isinstance(key, int) else to_nums(key)
    p = []
    for i in range(len(c)):
        k = stream[i] if i < len(stream) else p[i - len(stream)]
        p.append((c[i] - k) % 26)
    return to_text(p)


# =====================================================================================
# [D] PLAYFAIR -- 2 letters at a time on a 5x5 matrix
#   1. matrix: keyword letters (no repeats) then the rest of the alphabet; I and J share
#   2. split into pairs; a doubled letter in a pair -> insert 'x'; odd length -> add 'x'
#   3. same row -> letter to the RIGHT | same column -> letter BELOW | rectangle ->
#      swap columns.  Decrypt: LEFT / ABOVE / swap columns.
# =====================================================================================
def playfair_matrix(key):
    seen = ""
    for ch in clean(key).replace("j", "i") + "abcdefghiklmnopqrstuvwxyz":
        if ch not in seen:
            seen += ch
    return [list(seen[i:i + 5]) for i in range(0, 25, 5)]


def print_matrix(m):
    for row in m:
        print("   " + " ".join(ch.upper() for ch in row))


def playfair_pairs(text):
    t = clean(text).replace("j", "i")
    pairs, i = [], 0
    while i < len(t):
        a = t[i]
        b = t[i + 1] if i + 1 < len(t) else "x"
        if a == b:
            pairs.append(a + "x")
            i += 1
        else:
            pairs.append(a + b)
            i += 2
    return pairs


def _find(m, ch):
    for r in range(5):
        for c in range(5):
            if m[r][c] == ch:
                return r, c


def _playfair(pairs, m, step):            # step +1 encrypt, -1 decrypt
    out = ""
    for a, b in pairs:
        r1, c1 = _find(m, a)
        r2, c2 = _find(m, b)
        if r1 == r2:
            out += m[r1][(c1 + step) % 5] + m[r2][(c2 + step) % 5]
        elif c1 == c2:
            out += m[(r1 + step) % 5][c1] + m[(r2 + step) % 5][c2]
        else:
            out += m[r1][c2] + m[r2][c1]
    return out


def playfair_encrypt(text, key):
    return _playfair(playfair_pairs(text), playfair_matrix(key), +1)


def playfair_decrypt(text, key):
    t = clean(text)
    return _playfair([t[i:i + 2] for i in range(0, len(t), 2)], playfair_matrix(key), -1)


# =====================================================================================
# [E] HILL CIPHER -- key is a MATRIX
#   row vectors (Forouzan / the manual):  C = P x K  (mod 26)
#   column vectors (other books):         C = K x P  (mod 26)
#   decrypt with K^-1 mod 26; K is valid only if gcd(det K, 26) = 1
#   2x2 by hand: K=[[a,b],[c,d]] -> K^-1 = det^-1 * [[d,-b],[-c,a]] mod 26
#   weakness: it is linear, so a KNOWN-PLAINTEXT attack recovers K (see [F])
# =====================================================================================
def mat_det(M):
    if len(M) == 1:
        return M[0][0]
    if len(M) == 2:
        return M[0][0] * M[1][1] - M[0][1] * M[1][0]
    return sum(((-1) ** c) * M[0][c] * mat_det([row[:c] + row[c + 1:] for row in M[1:]])
               for c in range(len(M)))


def mat_inv_mod(M, mod=26):
    n = len(M)
    det = mat_det(M) % mod
    if math.gcd(det, mod) != 1:
        raise ValueError(f"matrix not invertible mod {mod} (det = {det})")
    det_inv = pow(det, -1, mod)
    if n == 1:
        return [[det_inv]]
    adj = [[0] * n for _ in range(n)]
    for r in range(n):
        for c in range(n):
            minor = [row[:c] + row[c + 1:] for i, row in enumerate(M) if i != r]
            adj[c][r] = ((-1) ** (r + c)) * mat_det(minor)     # adjugate
    return [[(adj[r][c] * det_inv) % mod for c in range(n)] for r in range(n)]


def mat_mul(A, B, mod=26):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) % mod for j in range(len(B[0]))]
            for i in range(len(A))]


def hill_encrypt(text, K, mode="row", filler="x"):
    n = len(K)
    p = clean(text)
    p += filler * (-len(p) % n)
    out = []
    for i in range(0, len(p), n):
        block = [ord(ch) - 97 for ch in p[i:i + n]]
        if mode == "row":
            out += mat_mul([block], K)[0]
        else:
            out += [r[0] for r in mat_mul(K, [[x] for x in block])]
    return to_text(out)


def hill_decrypt(text, K, mode="row"):
    return hill_encrypt(text, mat_inv_mod(K), mode)


# =====================================================================================
# [F] TRANSPOSITION + ATTACKS
#   transposition: letters unchanged, only POSITIONS move
#     keyless: rail fence | keyed: columnar, block permutation
#   attack names (state them in the exam!)
#     ciphertext-only  : only C       -> brute force / frequency analysis
#     known-plaintext  : some (P,C)   -> solve for the key (manual Q5, Q6)
#     chosen-plaintext : attacker picks P, sees C ('Eve types abcdefghi')
#     chosen-ciphertext: attacker picks C, sees P
# =====================================================================================
def railfence_encrypt(text, rails=2):
    t = clean(text)
    rows, r, step = [""] * rails, 0, 1
    for ch in t:
        rows[r] += ch
        if rails > 1:
            step = 1 if r == 0 else -1 if r == rails - 1 else step
            r += step
    return "".join(rows)


def railfence_decrypt(text, rails=2):
    n = len(text)
    pattern, r, step = [], 0, 1
    for _ in range(n):
        pattern.append(r)
        if rails > 1:
            step = 1 if r == 0 else -1 if r == rails - 1 else step
            r += step
    order = sorted(range(n), key=lambda i: pattern[i])
    out = [""] * n
    for ch, i in zip(text, order):
        out[i] = ch
    return "".join(out)


def column_order(key):
    """'3142' -> numeric order; word key 'zebra' -> alphabetical order"""
    if key.isdigit():
        return sorted(range(len(key)), key=lambda i: key[i])
    return sorted(range(len(key)), key=lambda i: (key[i], i))


def columnar_encrypt(text, key, filler="x"):
    t = clean(text)
    n = len(key)
    t += filler * (-len(t) % n)
    rows = [t[i:i + n] for i in range(0, len(t), n)]
    return "".join("".join(row[c] for row in rows) for c in column_order(key))


def columnar_decrypt(text, key):
    n = len(key)
    nrows = len(text) // n
    cols, idx = [""] * n, 0
    for c in column_order(key):
        cols[c] = text[idx:idx + nrows]
        idx += nrows
    return "".join(cols[c][r] for r in range(nrows) for c in range(n))


def perm_encrypt(text, perm, filler="x"):
    """block permutation (1-based): [3,1,2] means output block = (p3, p1, p2)"""
    t = clean(text)
    n = len(perm)
    t += filler * (-len(t) % n)
    return "".join("".join(t[i + p - 1] for p in perm) for i in range(0, len(t), n))


def perm_decrypt(text, perm):
    inv = [0] * len(perm)
    for out_pos, p in enumerate(perm):
        inv[p - 1] = out_pos + 1
    return perm_encrypt(text, inv)


ENGLISH_FREQ = [8.2, 1.5, 2.8, 4.3, 12.7, 2.2, 2.0, 6.1, 7.0, 0.15, 0.77, 4.0, 2.4,
                6.7, 7.5, 1.9, 0.095, 6.0, 6.3, 9.1, 2.8, 0.98, 2.4, 0.15, 2.0, 0.074]


def chi_squared(text):
    """distance from English letter frequencies. LOWER = more English-like"""
    t = clean(text)
    if not t:
        return float("inf")
    return sum(((t.count(chr(97 + i)) - len(t) * f / 100) ** 2) / (len(t) * f / 100)
               for i, f in enumerate(ENGLISH_FREQ))


def brute_force_additive(ct, keys=range(26)):
    """ciphertext-only: try all keys, most English-looking first"""
    return sorted([(k, additive_decrypt(ct, k)) for k in keys], key=lambda r: chi_squared(r[1]))


def additive_key_from_pair(p_char, c_char):
    """known plaintext: 'CIW' is 'yes' -> k = C - P = c - y = 4"""
    return (ord(c_char.lower()) - ord(p_char.lower())) % 26


def affine_key_from_known(pt, ct):
    """2 known letters: c1 = a*p1 + b, c2 = a*p2 + b -> c1 - c2 = a*(p1 - p2) mod 26"""
    p1, p2 = to_nums(pt)[:2]
    c1, c2 = to_nums(ct)[:2]
    for a in [1, 3, 5, 7, 9, 11, 15, 17, 19, 21, 23, 25]:
        if (a * (p1 - p2)) % 26 == (c1 - c2) % 26:
            b = (c1 - a * p1) % 26
            if affine_encrypt(clean(pt)[:2], a, b) == clean(ct)[:2]:
                return a, b
    raise ValueError("no affine key fits")


def brute_force_affine(ct, known_pt=None, known_ct=None):
    """all 312 keys (optionally only those matching a known pair), best first"""
    out = []
    for a in [1, 3, 5, 7, 9, 11, 15, 17, 19, 21, 23, 25]:
        for b in range(26):
            if known_pt and affine_encrypt(known_pt, a, b) != clean(known_ct):
                continue
            out.append((a, b, affine_decrypt(ct, a, b)))
    return sorted(out, key=lambda r: chi_squared(r[2]))


def hill_key_from_known(pt, ct, n=2, mode="row"):
    """known-plaintext: n*n letters give K.  row: K = P^-1 C   col: K = C P^-1"""
    P = [to_nums(pt)[i * n:(i + 1) * n] for i in range(n)]
    C = [to_nums(ct)[i * n:(i + 1) * n] for i in range(n)]
    if mode == "row":
        return mat_mul(mat_inv_mod(P), C)
    Pc, Cc = [list(r) for r in zip(*P)], [list(r) for r in zip(*C)]
    return mat_mul(Cc, mat_inv_mod(Pc))


def index_of_coincidence(t):
    n = len(t)
    return 0 if n < 2 else sum(t.count(chr(97 + i)) * (t.count(chr(97 + i)) - 1)
                               for i in range(26)) / (n * (n - 1))


def vigenere_crack(ct, max_len=10):
    """ciphertext-only: key length via index of coincidence (English ~0.066),
       then each column is a Caesar cipher -> frequency analysis"""
    t = clean(ct)
    ics = {L: sum(index_of_coincidence(t[i::L]) for i in range(L)) / L for L in range(1, max_len + 1)}
    L = min(L for L in ics if ics[L] >= 0.9 * max(ics.values()))
    key = "".join(chr(97 + min(range(26), key=lambda k: chi_squared(additive_decrypt(t[i::L], k))))
                  for i in range(L))
    return key, vigenere_decrypt(t, key)


def transposition_block_size(chosen_pt, ct):
    """chosen-plaintext on a block permutation: smallest n where every ct block is a
       rearrangement of the matching pt block; returns (n, permutation)"""
    pt, ct = clean(chosen_pt), clean(ct)
    for n in range(1, len(pt) + 1):
        if len(pt) % n == 0 and len(ct) == len(pt) and all(
                sorted(pt[i:i + n]) == sorted(ct[i:i + n]) for i in range(0, len(pt), n)):
            return n, [pt[:n].index(ct[i]) + 1 for i in range(n)]
    return None


# =====================================================================================
# [G] LAB 2 -- DES / 3DES / AES
#   DES : 64-bit block, 56-bit key (given as 8 bytes incl. parity), 16 Feistel rounds:
#         IP -> 16 x [expand R to 48 bits, XOR round key, 8 S-boxes -> 32 bits, P-box,
#         XOR into L, swap] -> FP.  Too weak today (2^56 key search).
#   3DES: E(K1) D(K2) E(K3) with a 24-byte key. If K1=K2 or K2=K3 it collapses to DES,
#         and pycryptodome REFUSES it ("degenerates to single DES").
#   AES : 128-bit block; key 128/192/256 bits -> 10/12/14 rounds; not Feistel.
#         round = SubBytes, ShiftRows, MixColumns, AddRoundKey (last round: no MixColumns)
#
#   MODE  IV/nonce   padding  notes
#   ECB   none       yes      same P block -> same C block: LEAKS PATTERNS
#   CBC   random IV  yes      Ci = E(Pi XOR Ci-1); most common in labs
#   CFB   IV         no       stream-like
#   OFB   IV         no       keystream independent of data
#   CTR   nonce      no       E(nonce||counter) XOR P; parallel; never reuse a nonce
# =====================================================================================
ALGOS = {"DES": (DES, 8), "3DES": (DES3, 24), "AES-128": (AES, 16),
         "AES-192": (AES, 24), "AES-256": (AES, 32)}
MODES = {"ECB": AES.MODE_ECB, "CBC": AES.MODE_CBC, "CFB": AES.MODE_CFB,
         "OFB": AES.MODE_OFB, "CTR": AES.MODE_CTR}     # same constants for DES/DES3


def make_key(algo_name):
    """random key of the right size (3DES: parity fixed and non-degenerate)"""
    algo, size = ALGOS[algo_name]
    if algo is DES3:
        while True:
            try:
                k = DES3.adjust_key_parity(get_random_bytes(24))
                DES3.new(k, DES3.MODE_ECB)
                return k
            except ValueError:
                pass
    return get_random_bytes(size)


def encrypt_block_cipher(algo_name, key, data, mode="CBC", iv=None):
    """returns (iv_or_nonce, ciphertext); iv=None -> a random one is generated"""
    algo, _ = ALGOS[algo_name]
    bs = algo.block_size                      # 8 for DES/3DES, 16 for AES
    m = MODES[mode]
    if mode == "ECB":
        return None, algo.new(key, m).encrypt(pad(data, bs))
    if mode == "CTR":
        nonce = iv if iv is not None else get_random_bytes(bs // 2)
        return nonce, algo.new(key, m, nonce=nonce).encrypt(data)
    iv = iv if iv is not None else get_random_bytes(bs)
    if mode == "CBC":
        return iv, algo.new(key, m, iv).encrypt(pad(data, bs))
    return iv, algo.new(key, m, iv).encrypt(data)          # CFB / OFB


def decrypt_block_cipher(algo_name, key, ct, mode="CBC", iv=None):
    algo, _ = ALGOS[algo_name]
    bs = algo.block_size
    m = MODES[mode]
    if mode == "ECB":
        return unpad(algo.new(key, m).decrypt(ct), bs)
    if mode == "CTR":
        return algo.new(key, m, nonce=iv).decrypt(ct)
    if mode == "CBC":
        return unpad(algo.new(key, m, iv).decrypt(ct), bs)
    return algo.new(key, m, iv).decrypt(ct)


def blocks_hex(data, bs=16):
    return [data[i:i + bs].hex() for i in range(0, len(data), bs)]


# --- the one-liners you will write most often ---
def aes_cbc_encrypt(key, data):
    iv = get_random_bytes(16)
    return iv, AES.new(key, AES.MODE_CBC, iv).encrypt(pad(data, 16))


def aes_cbc_decrypt(key, iv, ct):
    return unpad(AES.new(key, AES.MODE_CBC, iv).decrypt(ct), 16)


def des3_ecb_encrypt(key, data):             # e.g. to wrap a session key
    return DES3.new(key, DES3.MODE_ECB).encrypt(pad(data, 8))


def des3_ecb_decrypt(key, ct):
    return unpad(DES3.new(key, DES3.MODE_ECB).decrypt(ct), 8)


# =====================================================================================
# [EX3] EVERY AES/DES/3DES MODE AS AN INDIVIDUAL FUNCTION (no dispatcher, no simulation)
#   AES key size picks the variant:  16 bytes = AES-128 | 24 = AES-192 | 32 = AES-256.
#   DES key = 8 bytes.  3DES key = 24 bytes (3 distinct 8-byte parts).
#   ECB/CBC pad to the block size (16 for AES, 8 for DES/3DES).
#   CFB/OFB/CTR are stream modes -> NO padding.  CBC/CFB/OFB need a 16/8-byte IV; CTR a nonce.
# =====================================================================================
# ---------- AES (pass a 16/24/32-byte key for 128/192/256) ----------
def aes_ecb_encrypt(key, data):
    return AES.new(key, AES.MODE_ECB).encrypt(pad(data, 16))


def aes_ecb_decrypt(key, ct):
    return unpad(AES.new(key, AES.MODE_ECB).decrypt(ct), 16)


def aes_cbc_enc(key, data, iv):                 # iv = 16 bytes
    return AES.new(key, AES.MODE_CBC, iv).encrypt(pad(data, 16))


def aes_cbc_dec(key, ct, iv):
    return unpad(AES.new(key, AES.MODE_CBC, iv).decrypt(ct), 16)


def aes_cfb_enc(key, data, iv):                 # stream mode, no padding
    return AES.new(key, AES.MODE_CFB, iv).encrypt(data)


def aes_cfb_dec(key, ct, iv):
    return AES.new(key, AES.MODE_CFB, iv).decrypt(ct)


def aes_ofb_enc(key, data, iv):
    return AES.new(key, AES.MODE_OFB, iv).encrypt(data)


def aes_ofb_dec(key, ct, iv):
    return AES.new(key, AES.MODE_OFB, iv).decrypt(ct)


def aes_ctr_enc(key, data, nonce):              # nonce = 8 bytes
    return AES.new(key, AES.MODE_CTR, nonce=nonce).encrypt(data)


def aes_ctr_dec(key, ct, nonce):
    return AES.new(key, AES.MODE_CTR, nonce=nonce).decrypt(ct)


# ---------- DES (key = 8 bytes, block = 8) ----------
def des_ecb_enc(key, data):
    return DES.new(key, DES.MODE_ECB).encrypt(pad(data, 8))


def des_ecb_dec(key, ct):
    return unpad(DES.new(key, DES.MODE_ECB).decrypt(ct), 8)


def des_cbc_enc(key, data, iv):                 # iv = 8 bytes
    return DES.new(key, DES.MODE_CBC, iv).encrypt(pad(data, 8))


def des_cbc_dec(key, ct, iv):
    return unpad(DES.new(key, DES.MODE_CBC, iv).decrypt(ct), 8)


def des_cfb_enc(key, data, iv):
    return DES.new(key, DES.MODE_CFB, iv).encrypt(data)


def des_cfb_dec(key, ct, iv):
    return DES.new(key, DES.MODE_CFB, iv).decrypt(ct)


def des_ofb_enc(key, data, iv):
    return DES.new(key, DES.MODE_OFB, iv).encrypt(data)


def des_ofb_dec(key, ct, iv):
    return DES.new(key, DES.MODE_OFB, iv).decrypt(ct)


def des_ctr_enc(key, data, nonce):              # nonce = 4 bytes
    return DES.new(key, DES.MODE_CTR, nonce=nonce).encrypt(data)


def des_ctr_dec(key, ct, nonce):
    return DES.new(key, DES.MODE_CTR, nonce=nonce).decrypt(ct)


# ---------- 3DES (key = 24 bytes, block = 8) ----------
def des3_ecb_enc(key, data):
    return DES3.new(key, DES3.MODE_ECB).encrypt(pad(data, 8))


def des3_ecb_dec(key, ct):
    return unpad(DES3.new(key, DES3.MODE_ECB).decrypt(ct), 8)


def des3_cbc_enc(key, data, iv):
    return DES3.new(key, DES3.MODE_CBC, iv).encrypt(pad(data, 8))


def des3_cbc_dec(key, ct, iv):
    return unpad(DES3.new(key, DES3.MODE_CBC, iv).decrypt(ct), 8)


def des3_cfb_enc(key, data, iv):
    return DES3.new(key, DES3.MODE_CFB, iv).encrypt(data)


def des3_cfb_dec(key, ct, iv):
    return DES3.new(key, DES3.MODE_CFB, iv).decrypt(ct)


def des3_ofb_enc(key, data, iv):
    return DES3.new(key, DES3.MODE_OFB, iv).encrypt(data)


def des3_ofb_dec(key, ct, iv):
    return DES3.new(key, DES3.MODE_OFB, iv).decrypt(ct)


def des3_ctr_enc(key, data, nonce):
    return DES3.new(key, DES3.MODE_CTR, nonce=nonce).encrypt(data)


def des3_ctr_dec(key, ct, nonce):
    return DES3.new(key, DES3.MODE_CTR, nonce=nonce).decrypt(ct)


# =====================================================================================
# [H] AES FROM SCRATCH (128/192/256) -- for "show all the steps" (manual Lab 2 Q5)
#   S-box is COMPUTED (inverse in GF(2^8), poly x^8+x^4+x^3+x+1, then affine map),
#   so there is no 256-entry table to mistype.  state = 4x4 bytes, s[row + 4*col]
# =====================================================================================
def gf_mul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a = ((a << 1) ^ 0x1B) & 0xFF if a & 0x80 else a << 1
        b >>= 1
    return r


def _make_sbox():
    sbox = [0] * 256
    for x in range(256):
        inv = 0 if x == 0 else next(y for y in range(1, 256) if gf_mul(x, y) == 1)
        s = inv
        for i in range(1, 5):
            s ^= ((inv << i) | (inv >> (8 - i))) & 0xFF
        sbox[x] = s ^ 0x63
    return sbox


SBOX = _make_sbox()
INV_SBOX = [SBOX.index(i) for i in range(256)]
RCON = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36]


def key_expansion(key, verbose=False):
    """Nk = 4/6/8 words, Nr = Nk + 6 rounds, 4*(Nr+1) words.
       every Nk-th word: RotWord, SubWord, XOR Rcon; AES-256 adds SubWord at i % 8 == 4"""
    Nk = len(key) // 4
    Nr = Nk + 6
    w = [list(key[4 * i:4 * i + 4]) for i in range(Nk)]
    for i in range(Nk, 4 * (Nr + 1)):
        t = w[i - 1][:]
        if i % Nk == 0:
            t = t[1:] + t[:1]
            t = [SBOX[b] for b in t]
            t[0] ^= RCON[i // Nk - 1]
        elif Nk > 6 and i % Nk == 4:
            t = [SBOX[b] for b in t]
        w.append([w[i - Nk][j] ^ t[j] for j in range(4)])
    round_keys = [sum(w[4 * r:4 * r + 4], []) for r in range(Nr + 1)]
    if verbose:
        print(f"Key expansion: Nk={Nk} words, Nr={Nr} rounds, {len(w)} words")
        for r, rk in enumerate(round_keys):
            print(f"  round key {r:<2}: {bytes(rk).hex()}")
    return round_keys, Nr


def sub_bytes(s):
    return [SBOX[b] for b in s]


def shift_rows(s):                          # row r rotates LEFT by r
    return [s[r + 4 * ((c + r) % 4)] for c in range(4) for r in range(4)]


def inv_shift_rows(s):                      # row r rotates RIGHT by r
    return [s[r + 4 * ((c - r) % 4)] for c in range(4) for r in range(4)]


def mix_columns(s):                         # column x [[2,3,1,1],[1,2,3,1],[1,1,2,3],[3,1,1,2]]
    out = []
    for c in range(4):
        a = s[4 * c:4 * c + 4]
        out += [gf_mul(a[0], 2) ^ gf_mul(a[1], 3) ^ a[2] ^ a[3],
                a[0] ^ gf_mul(a[1], 2) ^ gf_mul(a[2], 3) ^ a[3],
                a[0] ^ a[1] ^ gf_mul(a[2], 2) ^ gf_mul(a[3], 3),
                gf_mul(a[0], 3) ^ a[1] ^ a[2] ^ gf_mul(a[3], 2)]
    return out


def inv_mix_columns(s):
    out = []
    for c in range(4):
        a = s[4 * c:4 * c + 4]
        out += [gf_mul(a[0], 14) ^ gf_mul(a[1], 11) ^ gf_mul(a[2], 13) ^ gf_mul(a[3], 9),
                gf_mul(a[0], 9) ^ gf_mul(a[1], 14) ^ gf_mul(a[2], 11) ^ gf_mul(a[3], 13),
                gf_mul(a[0], 13) ^ gf_mul(a[1], 9) ^ gf_mul(a[2], 14) ^ gf_mul(a[3], 11),
                gf_mul(a[0], 11) ^ gf_mul(a[1], 13) ^ gf_mul(a[2], 9) ^ gf_mul(a[3], 14)]
    return out


def add_round_key(s, k):
    return [a ^ b for a, b in zip(s, k)]


def aes_block_encrypt_steps(block, key, verbose=True):
    rk, Nr = key_expansion(key, verbose)
    s = list(block)
    if verbose:
        print("Plaintext            :", bytes(s).hex())
    s = add_round_key(s, rk[0])
    if verbose:
        print("Initial AddRoundKey  :", bytes(s).hex())
    for r in range(1, Nr + 1):
        s = sub_bytes(s)
        if verbose:
            print(f"Round {r:<2} SubBytes    :", bytes(s).hex())
        s = shift_rows(s)
        if verbose:
            print(f"Round {r:<2} ShiftRows   :", bytes(s).hex())
        if r != Nr:
            s = mix_columns(s)
            if verbose:
                print(f"Round {r:<2} MixColumns  :", bytes(s).hex())
        s = add_round_key(s, rk[r])
        if verbose:
            print(f"Round {r:<2} AddRoundKey :", bytes(s).hex())
    return bytes(s)


def aes_block_decrypt(block, key):
    rk, Nr = key_expansion(key)
    s = add_round_key(list(block), rk[Nr])
    for r in range(Nr - 1, -1, -1):
        s = [INV_SBOX[b] for b in inv_shift_rows(s)]
        s = add_round_key(s, rk[r])
        if r != 0:
            s = inv_mix_columns(s)
    return bytes(s)


# =====================================================================================
# [I] INTEGRITY -- encryption alone does not tell you if the data was changed
#   A corrupted ciphertext often still "decrypts" (to garbage, or with silent changes),
#   so the receiver needs a MAC to detect it.
#   CBC-MAC = last block of AES-CBC(mac_key, message, IV = 0).
#   Use a mac_key DIFFERENT from the encryption key (key separation).
#   Order: encrypt-then-MAC -> MAC covers iv + ciphertext; verify BEFORE decrypting.
#   (Lab 5 introduces HMAC, the more usual choice.)
# =====================================================================================
def cbc_mac(mac_key, data):
    return AES.new(mac_key, AES.MODE_CBC, bytes(16)).encrypt(pad(data, 16))[-16:]


def cbc_mac_verify(mac_key, data, tag):
    return cbc_mac(mac_key, data) == tag


def corrupt_byte(data, index=0):
    """simulate transmission corruption: change one byte"""
    b = bytearray(data)
    b[index % len(b)] ^= 0xFF
    return bytes(b)


def integrity_demo():
    enc_key, mac_key = get_random_bytes(16), get_random_bytes(16)
    iv, ct = aes_cbc_encrypt(enc_key, b"Transfer 500 to account 12345")
    tag = cbc_mac(mac_key, iv + ct)
    print("tag on original      :", tag.hex(), "| valid:", cbc_mac_verify(mac_key, iv + ct, tag))
    bad = corrupt_byte(ct, 3)
    print("after 1 byte changed : valid:", cbc_mac_verify(mac_key, iv + bad, tag),
          "-> TAMPERING DETECTED, do not decrypt")


# =====================================================================================
# [J] ECB PATTERN LEAK + BENCHMARK (+ matplotlib plot)
# =====================================================================================
def ecb_leak_demo():
    key = get_random_bytes(16)
    msg = b"ATTACKATDAWN1234" * 4                    # 4 identical 16-byte blocks
    _, ecb = encrypt_block_cipher("AES-128", key, msg, "ECB")
    _, cbc = encrypt_block_cipher("AES-128", key, msg, "CBC")
    print("ECB blocks (identical -> pattern visible):")
    for b in blocks_hex(ecb):
        print("  ", b)
    print("CBC blocks (all different):")
    for b in blocks_hex(cbc):
        print("  ", b)


def time_ms(func, *args, repeat=200):
    start = time.perf_counter()
    for _ in range(repeat):
        out = func(*args)
    return (time.perf_counter() - start) * 1000 / repeat, out


def benchmark(messages, algos=("DES", "3DES", "AES-128", "AES-192", "AES-256"),
              modes=("ECB", "CBC", "CFB", "OFB", "CTR"), plot=True):
    """time encryption + decryption of all messages for each algorithm x mode"""
    results = {}
    for name in algos:
        key = make_key(name)
        for mode in modes:
            te = td = 0
            for msg in messages:
                t1, (iv, ct) = time_ms(encrypt_block_cipher, name, key, msg, mode)
                t2, pt = time_ms(decrypt_block_cipher, name, key, ct, mode, iv)
                assert pt == msg
                te, td = te + t1, td + t2
            results[(name, mode)] = (te, td)
            print(f"{name:8} {mode}: encrypt {te:.4f} ms   decrypt {td:.4f} ms")
    if plot:
        import matplotlib.pyplot as plt
        width = 0.8 / len(modes)
        for i, mode in enumerate(modes):
            plt.bar([x + i * width for x in range(len(algos))],
                    [results[(a, mode)][0] for a in algos], width, label=mode)
        plt.xticks([x + 0.4 - width / 2 for x in range(len(algos))], algos)
        plt.ylabel("encryption time (ms)")
        plt.title("Execution time by algorithm and mode")
        plt.legend()
        plt.tight_layout()
        plt.show()
    return results


# =====================================================================================
# [K] SOCKETS + LAYERED CLIENT / SERVER
#   Length-prefixed JSON: 4 bytes = length, then the JSON. TCP can split or merge
#   sends, so ALWAYS read exactly n bytes (recv_exact).
#   bytes -> .hex() before sending; bytes.fromhex() after receiving; ints go as is.
#
#   Protocol here: client applies classical layers in order, then one block cipher.
#   The session key is wrapped with 3DES under a pre-shared MASTER key, and a CBC-MAC
#   (separate pre-shared MAC key) protects iv + ciphertext. The server verifies the MAC,
#   unwraps the key, decrypts, then undoes classical layers in REVERSE order.
# =====================================================================================
HOST, PORT = "127.0.0.1", 5000
MASTER_KEY = bytes.fromhex("0123456789ABCDEFFEDCBA987654321089ABCDEF01234567")  # 3DES, 3 distinct parts
MAC_KEY = bytes.fromhex("00112233445566778899AABBCCDDEEFF")                     # AES-128 for CBC-MAC


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


# each classical layer: (encrypt, decrypt, list of (param name, type) to ask the user)
LAYERS = {
    "additive": (lambda t, p: additive_encrypt(t, p["k"]), lambda t, p: additive_decrypt(t, p["k"]),
                 [("k", int)]),
    "multiplicative": (lambda t, p: multiplicative_encrypt(t, p["k"]),
                       lambda t, p: multiplicative_decrypt(t, p["k"]), [("k", int)]),
    "affine": (lambda t, p: affine_encrypt(t, p["a"], p["b"]),
               lambda t, p: affine_decrypt(t, p["a"], p["b"]), [("a", int), ("b", int)]),
    "vigenere": (lambda t, p: vigenere_encrypt(t, p["key"]),
                 lambda t, p: vigenere_decrypt(t, p["key"]), [("key", str)]),
    "autokey": (lambda t, p: autokey_encrypt(t, p["k"]), lambda t, p: autokey_decrypt(t, p["k"]),
                [("k", int)]),
    "playfair": (lambda t, p: playfair_encrypt(t, p["key"]),
                 lambda t, p: playfair_decrypt(t, p["key"]), [("key", str)]),
    "hill": (lambda t, p: hill_encrypt(t, p["K"]), lambda t, p: hill_decrypt(t, p["K"]),
             [("K", "matrix")]),
    "railfence": (lambda t, p: railfence_encrypt(t, p["rails"]),
                  lambda t, p: railfence_decrypt(t, p["rails"]), [("rails", int)]),
    "columnar": (lambda t, p: columnar_encrypt(t, p["key"]),
                 lambda t, p: columnar_decrypt(t, p["key"]), [("key", str)]),
}


def ask(name, kind):
    raw = input(f"   {name}: ")
    if kind is int:
        return int(raw)
    if kind == "matrix":                     # e.g. 3 3 2 7  -> [[3,3],[2,7]]
        nums = [int(x) for x in raw.replace(",", " ").split()]
        n = math.isqrt(len(nums))
        return [nums[i * n:(i + 1) * n] for i in range(n)]
    return raw


def build_packet(message, layers, algo="AES-128", mode="CBC"):
    """layers = [(name, params_dict), ...]. Returns the JSON-ready packet."""
    text = clean(message)
    print("[0] cleaned          :", text)
    for i, (name, params) in enumerate(layers, 1):
        text = LAYERS[name][0](text, params)
        print(f"[{i}] after {name:<11}:", text)
    session_key = make_key(algo)
    iv, ct = encrypt_block_cipher(algo, session_key, text.encode(), mode)
    iv_hex = iv.hex() if iv else ""
    print(f"[*] {algo}-{mode} key   :", session_key.hex())
    print(f"[*] iv/nonce          :", iv_hex or "(none for ECB)")
    print(f"[*] ciphertext        :", ct.hex())
    enc_key = des3_ecb_encrypt(MASTER_KEY, session_key)
    tag = cbc_mac(MAC_KEY, (iv or b"") + ct)
    print("[*] 3DES-wrapped key  :", enc_key.hex())
    print("[*] CBC-MAC           :", tag.hex())
    return {"layers": [{"name": n, "params": p} for n, p in layers], "algo": algo, "mode": mode,
            "enc_key": enc_key.hex(), "iv": iv_hex, "ct": ct.hex(), "mac": tag.hex()}


def open_packet(pkt):
    """server side: verify MAC -> unwrap key -> decrypt -> undo layers in reverse"""
    iv = bytes.fromhex(pkt["iv"]) if pkt["iv"] else None
    ct = bytes.fromhex(pkt["ct"])
    if not cbc_mac_verify(MAC_KEY, (iv or b"") + ct, bytes.fromhex(pkt["mac"])):
        raise ValueError("TAMPERING DETECTED: MAC mismatch")
    print("[*] MAC verified")
    session_key = des3_ecb_decrypt(MASTER_KEY, bytes.fromhex(pkt["enc_key"]))
    print("[*] session key       :", session_key.hex())
    text = decrypt_block_cipher(pkt["algo"], session_key, ct, pkt["mode"], iv).decode()
    print(f"[*] after {pkt['algo']}-{pkt['mode']}:", text)
    for layer in reversed(pkt["layers"]):
        text = LAYERS[layer["name"]][1](text, layer["params"])
        print(f"[-] undo {layer['name']:<12}:", text)
    return text


def run_server(host=HOST, port=PORT):
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as srv:
        srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        srv.bind((host, port))
        srv.listen(1)
        print(f"Server listening on {host}:{port} ...")
        conn, addr = srv.accept()
        with conn:
            print("Connected by", addr)
            pkt = recv_msg(conn)
            print("Received:", pkt)
            try:
                plain = open_packet(pkt)
                send_msg(conn, {"status": "OK", "plaintext": plain})
            except ValueError as e:
                print("REJECTED:", e)
                send_msg(conn, {"status": "REJECTED", "reason": str(e)})


def run_client(host=HOST, port=PORT):
    message = input("Message: ")
    print("Layers available:", ", ".join(LAYERS))
    chosen = [x.strip() for x in input("Classical layers in order (comma separated, blank = none): ")
              .split(",") if x.strip()]
    layers = []
    for name in chosen:
        if name not in LAYERS:
            print("unknown layer:", name)
            return
        print(f" parameters for {name}" + (" (matrix as: 3 3 2 7)" if name == "hill" else ""))
        layers.append((name, {p: ask(p, kind) for p, kind in LAYERS[name][2]}))
    algo = input(f"Block cipher {list(ALGOS)} [AES-128]: ").strip() or "AES-128"
    mode = input(f"Mode {list(MODES)} [CBC]: ").strip() or "CBC"
    try:
        pkt = build_packet(message, layers, algo, mode)
    except ValueError as e:
        print("ERROR:", e)
        return
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.connect((host, port))
        send_msg(s, pkt)
        print("Server reply:", recv_msg(s))


# =====================================================================================
# [L] DEMOS (manual exercises) + SELF-TEST
# =====================================================================================
def demo():
    line = lambda t: print("\n" + "=" * 15, t, "=" * 15)

    line("LAB 1 Q1  'I am learning information security'")
    m = "I am learning information security"
    print("Additive k=20      :", additive_encrypt(m, 20).upper())
    print("Multiplicative k=15:", multiplicative_encrypt(m, 15).upper())
    c = affine_encrypt(m, 15, 20)
    print("Affine (15,20)     :", c.upper(), "->", affine_decrypt(c, 15, 20))

    line("LAB 1 Q2  'the house is being sold tonight'")
    m = "the house is being sold tonight"
    c = vigenere_encrypt(m, "dollars")
    print("Vigenere dollars:", c.upper(), "->", vigenere_decrypt(c, "dollars"))
    c = autokey_encrypt(m, 7)
    print("Autokey k=7     :", c.upper(), "->", autokey_decrypt(c, 7))

    line("LAB 1 Q3  Playfair key GUIDANCE")
    print_matrix(playfair_matrix("GUIDANCE"))
    m = "The key is hidden under the door pad"
    print("pairs :", playfair_pairs(m))
    c = playfair_encrypt(m, "GUIDANCE")
    print("cipher:", c.upper(), "->", playfair_decrypt(c, "GUIDANCE"))

    line("LAB 1 Q4  Hill K = [[3,3],[2,7]]")
    K = [[3, 3], [2, 7]]
    c = hill_encrypt("We live in an insecure world", K)
    print("cipher:", c.upper(), "->", hill_decrypt(c, K), "| K^-1 =", mat_inv_mod(K))

    line("LAB 1 Q5  CIW = yes, decrypt XVIEWYWI")
    k = additive_key_from_pair("y", "C")
    print(f"known-plaintext attack, k = {k} ->", additive_decrypt("XVIEWYWI", k),
          "(manual typo: should read 'treasure')")

    line("LAB 1 Q6  affine with 'ab' -> 'GL'")
    a, b = affine_key_from_known("ab", "GL")
    print(f"a={a}, b={b} ->", affine_decrypt("XPALASXYFGFUKPXUSOGEUTKCDGEXANMGNVS", a, b))

    line("LAB 1 Additional 1  additive, key near 13")
    ct = "NCJAEZRCLAS/LYODEPRLYZRCLASJLCPEHZDTOPDZOLN&BY"
    for k in range(10, 17):
        print(f"k={k}:", shift_keep_symbols(ct, -k))
    print("frequency analysis picks k =", brute_force_additive(ct)[0][0])

    line("LAB 1 Additional 3  Vigenere HEALTH")
    c = vigenere_encrypt("Life is full of surprises", "HEALTH")
    print(c.upper(), "->", vigenere_decrypt(c, "HEALTH"))

    line("LAB 2 Q1  DES 'Confidential Data', key A1B2C3D4 (8 ASCII bytes)")
    key = key_from("A1B2C3D4", 8)
    _, c = encrypt_block_cipher("DES", key, b"Confidential Data", "ECB")
    print(c.hex(), "->", decrypt_block_cipher("DES", key, c, "ECB"))

    line("LAB 2 Q2  AES-128 'Sensitive Information'")
    key = key_from("0123456789ABCDEF0123456789ABCDEF", 16)
    iv, c = encrypt_block_cipher("AES-128", key, b"Sensitive Information", "CBC")
    print(c.hex(), "->", decrypt_block_cipher("AES-128", key, c, "CBC", iv))

    line("LAB 2 Q3  DES vs AES-256 timing")
    msg = b"Performance Testing of Encryption Algorithms"
    for name in ("DES", "AES-256"):
        k = make_key(name)
        te, (iv, c) = time_ms(encrypt_block_cipher, name, k, msg, "CBC", repeat=2000)
        td, _ = time_ms(decrypt_block_cipher, name, k, c, "CBC", iv, repeat=2000)
        print(f"{name:8} encrypt {te*1000:.2f} us   decrypt {td*1000:.2f} us")

    line("LAB 2 Q4  3DES (manual key is DEGENERATE)")
    try:
        DES3.new(key_from("1234567890ABCDEF" * 3, 24), DES3.MODE_ECB)
    except ValueError as e:
        print("manual key fails:", e)
    key = DES3.adjust_key_parity(key_from("1234567890ABCDEFFEDCBA0987654321ABCDEF1234567890", 24))
    _, c = encrypt_block_cipher("3DES", key, b"Classified Text", "ECB")
    print("with 3 distinct parts:", c.hex(), "->", decrypt_block_cipher("3DES", key, c, "ECB"))

    line("LAB 2 Q5  AES-192 all steps 'Top Secret Data'")
    print("Manual key is 16 bytes; AES-192 needs 24 -> repeat the first 8 bytes")
    key = bytes.fromhex("FEDCBA9876543210FEDCBA9876543210FEDCBA9876543210")
    block = pad(b"Top Secret Data", 16)
    c = aes_block_encrypt_steps(block, key)
    print("from scratch :", c.hex())
    print("pycryptodome :", AES.new(key, AES.MODE_ECB).encrypt(block).hex())

    line("LAB 2 Additional 2  DES blocks, key A1B2C3D4E5F60708")
    key = key_from("A1B2C3D4E5F60708", 8)
    for blk in ["54686973206973206120636f6e666964656e7469616c206d657373616765",
                "416e64207468697320697320746865207365636f6e6420626c6f636b"]:
        _, c = encrypt_block_cipher("DES", key, bytes.fromhex(blk), "ECB")
        print(c.hex(), "->", decrypt_block_cipher("DES", key, c, "ECB").decode())

    line("LAB 2 Additional 3/4/5  AES-256, DES-CBC, AES-CTR")
    key = key_from("0123456789ABCDEF" * 4, 32)
    iv, c = encrypt_block_cipher("AES-256", key, b"Encryption Strength", "CBC")
    print("AES-256:", c.hex(), "->", decrypt_block_cipher("AES-256", key, c, "CBC", iv))
    key, iv = key_from("A1B2C3D4", 8), b"12345678"
    _, c = encrypt_block_cipher("DES", key, b"Secure Communication", "CBC", iv)
    print("DES-CBC:", c.hex(), "->", decrypt_block_cipher("DES", key, c, "CBC", iv))
    key, nonce = key_from("0123456789ABCDEF0123456789ABCDEF", 16), bytes(8)
    _, c = encrypt_block_cipher("AES-128", key, b"Cryptography Lab Exercise", "CTR", nonce)
    print("AES-CTR:", c.hex(), "->", decrypt_block_cipher("AES-128", key, c, "CTR", nonce))

    line("ECB pattern leak")
    ecb_leak_demo()
    line("Integrity with CBC-MAC")
    integrity_demo()


def self_test():
    m = "attackatdawn"
    assert additive_encrypt("abc", 3) == "def" and additive_decrypt("def", 3) == "abc"
    assert multiplicative_decrypt(multiplicative_encrypt(m, 7), 7) == m
    assert affine_decrypt(affine_encrypt(m, 5, 8), 5, 8) == m
    assert vigenere_encrypt(m, "lemon") == "lxfopvefrnhr"
    assert autokey_encrypt("attackistoday", 12) == "mtmtcmsalhrdy"
    assert autokey_decrypt(autokey_encrypt(m, "key"), "key") == m
    assert playfair_encrypt("hide the gold in the tree stump", "playfair example") == \
        "bmodzbxdnabekudmuixmmouvif"
    K3 = [[6, 24, 1], [13, 16, 10], [20, 17, 15]]
    assert hill_encrypt("act", K3, "col") == "poh" and hill_decrypt("poh", K3, "col") == "act"
    K = [[3, 3], [2, 7]]
    assert hill_encrypt("paperleaksatnoon", K, "col") == "tefgghmigqfddudp"
    assert hill_key_from_known("help", "hqax", 2, "col") == K
    assert hill_key_from_known("help", hill_encrypt("help", K), 2, "row") == K
    assert railfence_encrypt("wearediscoveredfleeatonce", 3) == "wecrlteerdsoeefeaocaivden"
    assert railfence_decrypt("wecrlteerdsoeefeaocaivden", 3) == "wearediscoveredfleeatonce"
    assert columnar_decrypt(columnar_encrypt(m, "3142"), "3142").startswith(m)
    assert columnar_decrypt(columnar_encrypt(m, "zebra"), "zebra").startswith(m)
    assert perm_encrypt("abcdef", [3, 1, 2]) == "cabfde"
    assert perm_decrypt("cabfde", [3, 1, 2]) == "abcdef"
    assert transposition_block_size("abcdefghi", perm_encrypt("abcdefghi", [3, 1, 2])) == (3, [3, 1, 2])
    assert affine_key_from_known("dear", "IZJM") == (17, 9)
    assert brute_force_affine("IZJMANAUYZCJLOURNIZPDDZCZWQNLMWPWZ", "dear", "IZJM")[0][:2] == (17, 9)
    long_pt = clean("the quick brown fox jumps over the lazy dog and keeps running far away "
                    "from the hunters who are chasing it through the dark forest at night")
    assert brute_force_additive(additive_encrypt(long_pt, 11))[0][0] == 11
    assert vigenere_crack(vigenere_encrypt(long_pt * 2, "key"))[0] == "key"
    pt = bytes.fromhex("00112233445566778899aabbccddeeff")          # FIPS-197 vectors
    for khex, chex in [("000102030405060708090a0b0c0d0e0f", "69c4e0d86a7b0430d8cdb78070b4c55a"),
                       ("000102030405060708090a0b0c0d0e0f1011121314151617",
                        "dda97ca4864cdfe06eaf70a0ec0d7191"),
                       ("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
                        "8ea2b7ca516745bfeafc49904b496089")]:
        k = bytes.fromhex(khex)
        assert aes_block_encrypt_steps(pt, k, verbose=False).hex() == chex
        assert aes_block_decrypt(bytes.fromhex(chex), k) == pt
    for name in ALGOS:
        k = make_key(name)
        for mode in MODES:
            iv, ct = encrypt_block_cipher(name, k, b"hello block cipher world!", mode)
            assert decrypt_block_cipher(name, k, ct, mode, iv) == b"hello block cipher world!"
    iv, ct = aes_cbc_encrypt(MAC_KEY, b"x")
    assert aes_cbc_decrypt(MAC_KEY, iv, ct) == b"x"
    assert des3_ecb_decrypt(MASTER_KEY, des3_ecb_encrypt(MASTER_KEY, b"key")) == b"key"
    tag = cbc_mac(MAC_KEY, b"data")
    assert cbc_mac_verify(MAC_KEY, b"data", tag) and not cbc_mac_verify(MAC_KEY, b"dbta", tag)
    layers = [("affine", {"a": 5, "b": 8}), ("vigenere", {"key": "lemon"}),
              ("playfair", {"key": "monarchy"}), ("hill", {"K": K}), ("columnar", {"key": "3142"})]
    pkt = json.loads(json.dumps(build_packet("Meet at noon", layers, "AES-256", "CTR")))
    out = open_packet(pkt)
    assert out.startswith("meetatnoon"), out
    pkt["ct"] = corrupt_byte(bytes.fromhex(pkt["ct"]), 1).hex()
    try:
        open_packet(pkt)
        raise AssertionError("tampering not detected")
    except ValueError:
        pass
    # exam extras
    assert len(timestamp()) == 19
    k = key_from_text("sharedpass", 16); iv = key_from_text("myiv", 16)
    assert len(k) == 16 and aes_cbc_decrypt_iv(k, aes_cbc_encrypt_iv(k, b"hi there", iv), iv) == b"hi there"
    dk, div = key_from_text("deskey123", 8), key_from_text("ivfordes", 8)
    assert des_cbc_decrypt(dk, des_cbc_encrypt(dk, b"classified", div), div) == b"classified"
    import os
    write_text("._t12", "record"); assert read_text("._t12") == "record"; os.remove("._t12")
    # individual AES/DES/3DES mode functions
    for ksz, enc, dec in [(16, aes_cbc_enc, aes_cbc_dec), (24, aes_cbc_enc, aes_cbc_dec),
                          (32, aes_cbc_enc, aes_cbc_dec)]:
        k, iv = get_random_bytes(ksz), get_random_bytes(16)
        assert dec(k, enc(k, b"hi aes", iv), iv) == b"hi aes"
    k16 = get_random_bytes(16)
    assert aes_ecb_decrypt(k16, aes_ecb_encrypt(k16, b"block")) == b"block"
    n8 = get_random_bytes(8)
    assert aes_ctr_dec(k16, aes_ctr_enc(k16, b"stream", n8), n8) == b"stream"
    iv16 = get_random_bytes(16)
    assert aes_cfb_dec(k16, aes_cfb_enc(k16, b"cfb msg", iv16), iv16) == b"cfb msg"
    assert aes_ofb_dec(k16, aes_ofb_enc(k16, b"ofb msg", iv16), iv16) == b"ofb msg"
    k8 = get_random_bytes(8)
    assert des_cbc_dec(k8, des_cbc_enc(k8, b"des msg", n8), n8) == b"des msg"
    assert des_ecb_dec(k8, des_ecb_enc(k8, b"des ecb")) == b"des ecb"
    k24 = make_key("3DES")
    assert des3_cbc_dec(k24, des3_cbc_enc(k24, b"3des", n8), n8) == b"3des"
    print("\nALL PASSED")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "demo"
    if cmd == "test":
        self_test()
    elif cmd == "server":
        run_server()
    elif cmd == "client":
        run_client()
    elif cmd == "bench":
        benchmark([get_random_bytes(s) for s in (64, 256, 1024, 4096, 16384)])
    else:
        demo()
