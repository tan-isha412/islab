# =====================================================================================
#  SMART-GRID BILLING PORTAL   (Meter / Billing Officer / Auditor)
#    Meter       : AES-192 encrypt region, Paillier encrypt units, store a region TOKEN,
#                  SHA-256 hash, ElGamal-sign -> store persistently. Can view all.
#    Billing Off : find a region's records by token, verify ElGamal signatures,
#                  homomorphically SUM the Paillier units, decrypt ONLY the total.
#    Auditor     : verify SHA-256 + ElGamal signature, search by region token,
#                  print VALID/INVALID -> NEVER decrypt units or region.
#
#  python smartgrid.py        -> menu-driven
#  python smartgrid.py test   -> self-test (ALL PASSED)
# =====================================================================================
import time, json, os, sys, math, secrets, random, hashlib, hmac
from Crypto.Cipher import AES
from Crypto.Random import get_random_bytes
from Crypto.Util.number import getPrime, GCD
from Crypto.Util.Padding import pad, unpad

STORE = "readings.json"
KEYS = "grid_keys.json"
RATE = 8          # rupees per unit, for the bill


# =====================================================================================
# CRYPTO HELPERS
# =====================================================================================
def timestamp():
    return time.strftime("%Y-%m-%d %H:%M:%S")


def sha256(data):                                  # data is bytes
    return hashlib.sha256(data).hexdigest()


def _hash_int(message, mod):
    return int(hashlib.sha256(message).hexdigest(), 16) % mod


# ---- AES-192 (key = 24 bytes) ----
def aes192_encrypt(key, data):
    iv = get_random_bytes(16)
    return iv, AES.new(key, AES.MODE_CBC, iv).encrypt(pad(data, 16))


def aes192_decrypt(key, iv, ct):
    return unpad(AES.new(key, AES.MODE_CBC, iv).decrypt(ct), 16)


# ---- Paillier (additive HE, for the units) ----
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


def paillier_add(c1, c2, pub):                     # E(a)*E(b) -> E(a+b)
    n, _ = pub
    return (c1 * c2) % (n * n)


# ---- ElGamal digital signature (the step-up from RSA) ----
def elgamal_keygen(bits=256):
    p = getPrime(bits)
    g = 2
    x = random.randint(2, p - 2)
    return (p, g, pow(g, x, p)), x                 # public (p,g,y), private x


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


# ---- deterministic region token (searchable index) ----
def region_token(index_key, region):
    return hmac.new(index_key, region.lower().encode(), hashlib.sha256).hexdigest()


# =====================================================================================
# WHAT GETS HASHED / SIGNED  (rebuild identically at verify time)
#   includes the token too, so tampering with the region/token is also caught
# =====================================================================================
def record_payload(rec):
    return f"{rec['id']}|{rec['region']}|{rec['iv']}|{rec['units']}|{rec['token']}|{rec['timestamp']}".encode()


# =====================================================================================
# RBAC
# =====================================================================================
USER_ROLES = {"m": "meter", "b": "billing", "a": "auditor"}
ROLE_PERMS = {
    "meter":   {"add", "view"},
    "billing": {"sum", "verify", "search"},
    "auditor": {"verify", "search"},               # NOTE: no decrypt for the auditor
}


def can(user, perm):
    return perm in ROLE_PERMS.get(USER_ROLES.get(user), set())


# =====================================================================================
# PERSISTENT STORE + KEYS
# =====================================================================================
def load_records():
    if not os.path.exists(STORE):
        return []
    with open(STORE, "r", encoding="utf-8") as f:
        return json.load(f)


def save_records(records):
    with open(STORE, "w", encoding="utf-8") as f:
        json.dump(records, f, indent=2)


def load_or_create_keys():
    if os.path.exists(KEYS):
        with open(KEYS) as f:
            k = json.load(f)
        return (bytes.fromhex(k["aes"]), bytes.fromhex(k["index_key"]),
                tuple(k["paill_pub"]), tuple(k["paill_priv"]),
                tuple(k["eg_pub"]), k["eg_priv"])
    aes_key = get_random_bytes(24)                 # AES-192
    index_key = get_random_bytes(16)               # for region tokens
    paill_pub, paill_priv = paillier_keygen(512)
    eg_pub, eg_priv = elgamal_keygen(256)
    with open(KEYS, "w") as f:
        json.dump({"aes": aes_key.hex(), "index_key": index_key.hex(),
                   "paill_pub": list(paill_pub), "paill_priv": list(paill_priv),
                   "eg_pub": list(eg_pub), "eg_priv": eg_priv}, f)
    return aes_key, index_key, paill_pub, paill_priv, eg_pub, eg_priv


# =====================================================================================
# ROLE ACTIONS
# =====================================================================================
def meter_add(user, region, units, aes_key, index_key, paill_pub, eg_pub, eg_priv):
    if not can(user, "add"):
        raise PermissionError(f"{user} may not add readings")
    p, g, _ = eg_pub
    iv, ct = aes192_encrypt(aes_key, region.encode())
    rec = {"id": len(load_records()) + 1, "region": ct.hex(), "iv": iv.hex(),
           "units": str(paillier_encrypt(units, paill_pub)),
           "token": region_token(index_key, region), "timestamp": timestamp()}
    payload = record_payload(rec)
    rec["hash"] = sha256(payload)                  # SHA-256 of the record
    rec["sign"] = elgamal_sign(payload, p, g, eg_priv)   # ElGamal signature (r, s)
    records = load_records(); records.append(rec); save_records(records)
    print(f"[STORED] reading {rec['id']}  token={rec['token'][:12]}...  hash={rec['hash'][:16]}...  {rec['timestamp']}")
    return rec


def meter_view(user):
    if not can(user, "view"):
        raise PermissionError(f"{user} may not view")
    recs = load_records()
    print(f"{len(recs)} reading(s):")
    for r in recs:
        print(f"  id={r['id']}  region=<AES>  units=<Paillier>  token={r['token'][:12]}...  {r['timestamp']}")


def _verify(rec, eg_pub):
    p, g, y = eg_pub
    payload = record_payload(rec)
    hash_ok = sha256(payload) == rec["hash"]       # hash+verify BOTH use SHA-256
    sig_ok = elgamal_verify(payload, tuple(rec["sign"]), p, g, y)
    return hash_ok, sig_ok


def find_by_region(index_key, region):
    """search by TOKEN -> list of matching records (no decryption needed)"""
    tok = region_token(index_key, region)
    return [r for r in load_records() if r["token"] == tok]


def billing_sum(user, region, index_key, eg_pub, paill_pub, paill_priv):
    if not can(user, "sum"):
        raise PermissionError(f"{user} may not aggregate")
    matches = find_by_region(index_key, region)
    enc_total, used = None, []
    for rec in matches:
        hash_ok, sig_ok = _verify(rec, eg_pub)         # verify before using
        if not (hash_ok and sig_ok):
            print(f"  reading {rec['id']} TAMPERED, skipping"); continue
        c = int(rec["units"])
        enc_total = c if enc_total is None else paillier_add(enc_total, c, paill_pub)
        used.append(rec["id"])
    if enc_total is None:
        print(f"  no valid readings for region '{region}'"); return None
    total = paillier_decrypt(enc_total, paill_priv)     # decrypt ONLY the total
    print(f"  region '{region}' readings {used} -> {total} units -> bill = {total * RATE}")
    return total


def auditor_check(user, region, index_key, eg_pub):
    if not can(user, "verify"):
        raise PermissionError(f"{user} may not audit")
    matches = find_by_region(index_key, region)
    if not matches:
        print(f"  no readings for region '{region}'"); return
    for rec in matches:                                # verify only, NEVER decrypt
        hash_ok, sig_ok = _verify(rec, eg_pub)
        verdict = "VALID" if (hash_ok and sig_ok) else "INVALID"
        print(f"  AUDIT id={rec['id']}: integrity={'PASS' if hash_ok else 'FAIL'}, "
              f"signature={'VALID' if sig_ok else 'INVALID'} -> {verdict}")


def tamper(rid):
    records = load_records()
    for rec in records:
        if str(rec["id"]) == str(rid):
            ct = bytearray(bytes.fromhex(rec["region"])); ct[0] ^= 0xFF
            rec["region"] = bytes(ct).hex()
    save_records(records)
    print(f"[TAMPERED] flipped a byte in reading {rid}")


# =====================================================================================
# MENU-DRIVEN
# =====================================================================================
def menu():
    aes_key, index_key, paill_pub, paill_priv, eg_pub, eg_priv = load_or_create_keys()
    print("Smart-Grid Portal. Users: m (meter), b (billing officer), a (auditor)")
    while True:
        user = input("\nlogin as (m/b/a, or 'quit'): ").strip()
        if user == "quit":
            break
        role = USER_ROLES.get(user)
        if role is None:
            print("unknown user"); continue
        print(f"--- {user} : {role} ---")

        if role == "meter":
            while True:
                print("1. add reading   2. view all   3. tamper a reading   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    region = input("Region: ")
                    units = int(input("Units consumed: "))
                    meter_add(user, region, units, aes_key, index_key, paill_pub, eg_pub, eg_priv)
                elif c == "2":
                    meter_view(user)
                elif c == "3":
                    tamper(input("reading id to tamper: "))

        elif role == "billing":
            while True:
                print("1. bill a region (verify + sum + decrypt total)   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    billing_sum(user, input("Region: "), index_key, eg_pub, paill_pub, paill_priv)

        elif role == "auditor":
            while True:
                print("1. audit a region (verify only)   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    auditor_check(user, input("Region: "), index_key, eg_pub)


# =====================================================================================
# SELF-TEST
# =====================================================================================
def self_test():
    global STORE, KEYS
    STORE, KEYS = "._grid_test.json", "._gridkeys_test.json"
    for f in (STORE, KEYS):
        if os.path.exists(f):
            os.remove(f)
    aes_key, index_key, paill_pub, paill_priv, eg_pub, eg_priv = load_or_create_keys()

    meter_add("m", "North", 120, aes_key, index_key, paill_pub, eg_pub, eg_priv)
    meter_add("m", "North", 90, aes_key, index_key, paill_pub, eg_pub, eg_priv)
    meter_add("m", "South", 200, aes_key, index_key, paill_pub, eg_pub, eg_priv)
    meter_add("m", "North", 150, aes_key, index_key, paill_pub, eg_pub, eg_priv)

    # all genuine
    assert all(_verify(r, eg_pub) == (True, True) for r in load_records())

    # billing: North = 120+90+150 = 360, South = 200
    assert billing_sum("b", "North", index_key, eg_pub, paill_pub, paill_priv) == 360
    assert billing_sum("b", "South", index_key, eg_pub, paill_pub, paill_priv) == 200

    # RBAC: auditor cannot sum, meter cannot audit
    for bad in [lambda: billing_sum("a", "North", index_key, eg_pub, paill_pub, paill_priv),
                lambda: auditor_check("m", "North", index_key, eg_pub)]:
        try:
            bad(); raise AssertionError("RBAC not enforced")
        except PermissionError:
            pass

    # tamper reading 4 (North) -> excluded -> North total drops to 210
    tamper("4")
    assert _verify(load_records()[3], eg_pub) == (False, False)
    assert billing_sum("b", "North", index_key, eg_pub, paill_pub, paill_priv) == 210

    # keys persist
    aes2, ik2, pp2, ppr2, eg2, egp2 = load_or_create_keys()
    assert aes2 == aes_key and _verify(load_records()[0], eg2)[1] is True

    for f in (STORE, KEYS):
        os.remove(f)
    print("ALL PASSED")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "test":
        self_test()
    else:
        menu()
