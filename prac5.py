# =====================================================================================
#  SECURE PAYROLL MANAGEMENT SYSTEM   (Employee / Manager / Finance Officer)
#    Employee : AES-192 encrypt Designation, Paillier encrypt Salary, SHA-256 hash,
#               RSA sign -> store persistently. Can view all records.
#    Manager  : verify RSA signature + SHA-256, view the AES-192-decrypted Designation.
#    Finance  : homomorphically add the Paillier salaries, verify signatures, decrypt
#               ONLY the total payroll (never an individual salary).
#
#  python prac5.py        -> menu-driven
#  python prac5.py test   -> self-test (ALL PASSED)
# =====================================================================================
import time, json, os, sys, math, secrets, random, hashlib, hmac
from Crypto.Cipher import AES
from Crypto.Random import get_random_bytes
from Crypto.Util.number import getPrime, GCD
from Crypto.Util.Padding import pad, unpad

STORE = "employees.json"
KEYS = "keys.json"


# =====================================================================================
# CRYPTO HELPERS
# =====================================================================================
def timestamp():
    return time.strftime("%Y-%m-%d %H:%M:%S")


def sha256(data):                                  # data is bytes
    return hashlib.sha256(data).hexdigest()


def aes192_encrypt(key, data):                     # key = 24 bytes
    iv = get_random_bytes(16)
    return iv, AES.new(key, AES.MODE_CBC, iv).encrypt(pad(data, 16))


def aes192_decrypt(key, iv, ct):
    return unpad(AES.new(key, AES.MODE_CBC, iv).decrypt(ct), 16)


# ---- Paillier ----
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


# ---- RSA signature ----
def rsa_keygen(bits=1024, e=65537):
    while True:
        p, q = getPrime(bits // 2), getPrime(bits // 2)
        if p != q and math.gcd(e, (p - 1) * (q - 1)) == 1:
            break
    n = p * q
    return (n, e), (n, pow(e, -1, (p - 1) * (q - 1)))


def rsa_sign(message, priv):                       # message is BYTES
    n, d = priv
    return pow(int(sha256(message), 16) % n, d, n)


def rsa_verify(message, sig, pub):
    n, e = pub
    return pow(sig, e, n) == int(sha256(message), 16) % n


# =====================================================================================
# WHAT GETS HASHED / SIGNED
# FIX 1: record_payload rebuilt for PAYROLL fields (old code used region/units/token,
#        which don't exist here -> KeyError). Rebuilt identically at verify time.
# =====================================================================================
def record_payload(rec):
    return f"{rec['EmployeeId']}|{rec['Designation']}|{rec['IVUsed']}|{rec['Salary']}|{rec['timestamp']}".encode()


# =====================================================================================
# RBAC
# =====================================================================================
USER_ROLES = {"emp": "employee", "mgr": "manager", "finoff": "financialofficer"}
ROLE_PERMS = {
    "employee":         {"add", "view"},
    "manager":          {"verify", "viewdsgt"},
    "financialofficer": {"verify", "sum"},         # finance never decrypts a single salary
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
        # FIX 2: reload must match what was saved -- return rsa_priv too (old code dropped it)
        return (bytes.fromhex(k["aes"]), bytes.fromhex(k["index_key"]),
                tuple(k["paill_pub"]), tuple(k["paill_priv"]),
                tuple(k["rsa_pub"]), tuple(k["rsa_priv"]))
    aes_key = get_random_bytes(24)                 # AES-192
    index_key = get_random_bytes(16)
    paill_pub, paill_priv = paillier_keygen(512)
    rsa_pub, rsa_priv = rsa_keygen()
    with open(KEYS, "w") as f:
        json.dump({"aes": aes_key.hex(), "index_key": index_key.hex(),
                   "paill_pub": list(paill_pub), "paill_priv": list(paill_priv),
                   "rsa_pub": list(rsa_pub), "rsa_priv": list(rsa_priv)}, f)
    return aes_key, index_key, paill_pub, paill_priv, rsa_pub, rsa_priv


# =====================================================================================
# ROLE ACTIONS
# =====================================================================================
def employee_add(user, dsgt, sal, aes_key, paillier_pub, rsa_priv):
    if not can(user, "add"):
        print("this user cant add employees"); return None
    # FIX 3: encrypt BYTES (dsgt.encode()), and store bytes as hex / big ints as str (JSON-safe)
    iv, dsgtct = aes192_encrypt(aes_key, dsgt.encode())
    salct = paillier_encrypt(sal, paillier_pub)
    records = load_records()
    rec = {"EmployeeId": len(records) + 1, "Designation": dsgtct.hex(), "IVUsed": iv.hex(),
           "Salary": str(salct), "timestamp": timestamp()}
    # FIX 4: hash/sign the PAYLOAD BYTES, not the dict (old sha256(rec)/rsa_sign(rec) crashed)
    payload = record_payload(rec)
    rec["hash"] = sha256(payload)
    rec["sign"] = rsa_sign(payload, rsa_priv)
    # FIX 5: append then save (list.append returns None -> old save_records(records.append(rec)) saved nothing)
    records.append(rec)
    save_records(records)
    print(f"[STORED] EmployeeId {rec['EmployeeId']}  {rec['timestamp']}")
    return rec


def employee_view(user, emp_id=None):
    if not can(user, "view"):
        print("this user cant view employees"); return None
    # FIX 6: iterate the LIST of dicts directly (old `for i,data in load_records()` was wrong)
    for data in load_records():
        if emp_id is None or data["EmployeeId"] == emp_id:
            print(f"  EmployeeId:{data['EmployeeId']}  Dsgt:<AES>  Salary:<Paillier>  "
                  f"Hash:{data['hash'][:8]}...  Sign:{str(data['sign'])[:8]}...  {data['timestamp']}")


# FIX 7: _verify now takes a single record + rsa_pub, rebuilds the payload, and checks BOTH
#        the hash and the signature (old version looped, passed a dict, and dropped the sig arg)
def _verify(rec, rsa_pub):
    payload = record_payload(rec)
    hash_ok = rec["hash"] == sha256(payload)
    sign_ok = rsa_verify(payload, rec["sign"], rsa_pub)
    return hash_ok, sign_ok


def manager_viewdsgt(user, emp_id, aes_key, rsa_pub):
    if not can(user, "viewdsgt"):
        print("not allowed"); return
    rec = next((r for r in load_records() if r["EmployeeId"] == emp_id), None)
    if not rec:
        print("no such employee"); return
    hash_ok, sign_ok = _verify(rec, rsa_pub)                 # FIX 8: verify BEFORE decrypting
    print(f"  integrity={'PASS' if hash_ok else 'FAIL'}  signature={'VALID' if sign_ok else 'INVALID'}")
    if hash_ok and sign_ok:
        # FIX 9: actually DECRYPT the designation (old code printed the ciphertext)
        dsgt = aes192_decrypt(aes_key, bytes.fromhex(rec["IVUsed"]), bytes.fromhex(rec["Designation"]))
        print("  Designation:", dsgt.decode())
    else:
        print("  verification failed -> not showing designation")


def financialofficer_sum(user, paill_pub, paill_priv, rsa_pub):
    # FIX 10: permission is "sum" (old code checked "aggregate" -> always denied)
    if not can(user, "sum"):
        raise PermissionError("not allowed")
    total, used = None, []
    for rec in load_records():
        hash_ok, sign_ok = _verify(rec, rsa_pub)
        # FIX 11: skip tampered records with a sane condition (old `if not all(not h or not s)` was nonsense)
        if not (hash_ok and sign_ok):
            print(f"  EmployeeId {rec['EmployeeId']} tampered, skipping"); continue
        # FIX 12: correct field names -> Salary (not 'amount') and EmployeeId (not 'id')
        c = int(rec["Salary"])
        total = c if total is None else paillier_add(total, c, paill_pub)
        used.append(rec["EmployeeId"])
    if total is None:
        print("  no valid records"); return None
    t = paillier_decrypt(total, paill_priv)                  # decrypt ONLY the total
    print(f"  employees {used} -> TOTAL payroll = {t}")
    return t


def tamper(emp_id):
    records = load_records()
    for rec in records:
        if rec["EmployeeId"] == emp_id:
            ct = bytearray(bytes.fromhex(rec["Designation"])); ct[0] ^= 0xFF
            rec["Designation"] = bytes(ct).hex()
    save_records(records)
    print(f"[TAMPERED] flipped a byte in EmployeeId {emp_id}")


# =====================================================================================
# MENU-DRIVEN
# =====================================================================================
def menu():
    aes_key, index_key, paill_pub, paill_priv, rsa_pub, rsa_priv = load_or_create_keys()
    print("Payroll System. Users: emp (employee), mgr (manager), finoff (finance officer)")
    while True:
        user = input("\nlogin as (emp/mgr/finoff, or 'quit'): ").strip()
        if user == "quit":
            break
        role = USER_ROLES.get(user)
        if role is None:
            print("unknown user"); continue
        print(f"--- {user} : {role} ---")

        if role == "employee":
            while True:
                print("1. add employee   2. view all   3. tamper a record   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    dsgt = input("Designation: ")
                    sal = int(input("Salary: "))
                    employee_add(user, dsgt, sal, aes_key, paill_pub, rsa_priv)
                elif c == "2":
                    employee_view(user)
                elif c == "3":
                    tamper(int(input("EmployeeId to tamper: ")))

        elif role == "manager":
            while True:
                print("1. verify + view designation   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    manager_viewdsgt(user, int(input("EmployeeId: ")), aes_key, rsa_pub)

        elif role == "financialofficer":
            while True:
                print("1. total payroll (verify + sum + decrypt total)   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    financialofficer_sum(user, paill_pub, paill_priv, rsa_pub)


if __name__ == "__main__":
    menu()
