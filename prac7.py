# =====================================================================================
#  SECURE MILITARY MESSAGE SYSTEM   (Field Unit / Command Centre / Monitoring Officer)
#    Field Unit : establish shared key K with Diffie-Hellman; clean message to A-Z;
#                 gate: if K mod 26 == 5, ask k1 (gcd(k1,26)==1) and Affine-encrypt with
#                 (k1, k2=K mod 26); SHA-256 the ciphertext; store.
#    Command Ctr: recompute K, check both secrets match + the gate, recompute SHA-256 to
#                 detect tampering, then Affine-decrypt. Refuse on any failure.
#    Monitor    : recompute SHA-256 of each ciphertext, report tampered or not, NEVER decrypt.
#
#  python prac7.py        -> menu-driven
#  python prac7.py test   -> self-test (ALL PASSED)
# =====================================================================================
import time, json, os, sys, math, random, hashlib
from Crypto.Util.number import getPrime

STORE = "messages.json"
KEYS = "mil_keys.json"
CHECKPOINT = 5                                   # the gate: K mod 26 must equal this


# =====================================================================================
# HELPERS
# =====================================================================================
def timestamp():
    return time.strftime("%Y-%m-%d %H:%M:%S")


def sha256(data):                                # data is bytes
    return hashlib.sha256(data).hexdigest()


def letters_only(text):                          # uppercase, A-Z only
    return "".join(c for c in text.upper() if c.isalpha())


# ---- Diffie-Hellman ----
def dh_keypair(p, g):
    a = random.randint(2, p - 2)
    return a, pow(g, a, p)                        # private, public


def dh_shared(their_pub, my_priv, p):
    return pow(their_pub, my_priv, p)             # K = B^a = A^b = g^(ab) mod p


# ---- Affine cipher: C = (k1*P + k2) mod 26,  P = k1^-1 * (C - k2) mod 26 ----
def affine_encrypt(text, k1, k2):
    if math.gcd(k1, 26) != 1:
        raise ValueError("k1 must be coprime with 26")
    return "".join(chr((k1 * (ord(c) - 65) + k2) % 26 + 65) for c in letters_only(text))


def affine_decrypt(text, k1, k2):
    inv = pow(k1, -1, 26)
    return "".join(chr((inv * (ord(c) - 65 - k2)) % 26 + 65) for c in letters_only(text))


# =====================================================================================
# STORE + KEYS  (DH session is set up once and persisted so the receiver recomputes K)
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
    """Set up the DH session shared by the Field Unit and the Command Centre.
    We pick privates so that K mod 26 == CHECKPOINT, so the gate passes in this demo
    (in a real exam the p, g and the private exponents are GIVEN in the question)."""
    if os.path.exists(KEYS):
        with open(KEYS) as f:
            k = json.load(f)
        return k["p"], k["g"], k["a"], k["A"], k["b"], k["B"], k["K"]
    p, g = getPrime(256), 5
    while True:
        a, A = dh_keypair(p, g)                   # field unit
        b, B = dh_keypair(p, g)                   # command centre
        Ka = dh_shared(B, a, p)                   # both compute the same K
        Kb = dh_shared(A, b, p)
        if Ka == Kb and Ka % 26 == CHECKPOINT:
            break
    with open(KEYS, "w") as f:
        json.dump({"p": p, "g": g, "a": a, "A": A, "b": b, "B": B, "K": Ka}, f)
    return p, g, a, A, b, B, Ka


# =====================================================================================
# ROLE ACTIONS
# =====================================================================================
def field_unit_send(message, k1, keys):
    p, g, a, A, b, B, K = keys
    print(f"  Field Unit K = {K}")
    # gate 1: K mod 26 == CHECKPOINT
    if K % 26 != CHECKPOINT:
        print(f"  GATE FAILED: K mod 26 = {K % 26} != {CHECKPOINT} -> not encrypting"); return None
    # gate 2: validate k1
    if math.gcd(k1, 26) != 1:
        print(f"  INVALID k1={k1}: gcd(k1,26) != 1 -> not encrypting"); return None
    k2 = K % 26
    msg = letters_only(message)
    ct = affine_encrypt(msg, k1, k2)                  # Affine encrypt with (k1, k2=K mod 26)
    rec = {"id": len(load_records()) + 1, "ciphertext": ct, "k1": k1,
           "hash": sha256(ct.encode()), "timestamp": timestamp()}   # SHA-256 of the ciphertext
    records = load_records(); records.append(rec); save_records(records)
    print(f"  [SENT] id={rec['id']}  k2={k2}  ciphertext={ct}  hash={rec['hash'][:16]}...")
    return rec


def command_centre_receive(rec_id, keys):
    p, g, a, A, b, B, K = keys
    # recompute K independently and verify both shared secrets match
    Kb = dh_shared(A, b, p)
    if Kb != K:
        print("  shared secrets DO NOT match -> terminate"); return None
    print(f"  Command Centre K = {Kb}  (matches Field Unit)")
    if Kb % 26 != CHECKPOINT:
        print(f"  GATE FAILED: K mod 26 != {CHECKPOINT} -> terminate"); return None
    rec = next((r for r in load_records() if r["id"] == rec_id), None)
    if not rec:
        print("  no such message"); return None
    # integrity: recompute SHA-256 of the ciphertext and compare
    if sha256(rec["ciphertext"].encode()) != rec["hash"]:
        print("  INTEGRITY FAIL (ciphertext tampered) -> refusing to decrypt"); return None
    # validate k1
    if math.gcd(rec["k1"], 26) != 1:
        print("  INVALID k1 -> refusing to decrypt"); return None
    k2 = Kb % 26
    plain = affine_decrypt(rec["ciphertext"], rec["k1"], k2)
    print(f"  [DECRYPTED] {plain}")
    return plain


def monitor_check(keys):
    for rec in load_records():                        # verify integrity only, NEVER decrypt
        ok = sha256(rec["ciphertext"].encode()) == rec["hash"]
        print(f"  message {rec['id']}: {'INTACT' if ok else 'TAMPERED'}  ({rec['timestamp']})")


def tamper(rec_id):
    records = load_records()
    for rec in records:
        if rec["id"] == rec_id:
            ct = rec["ciphertext"]
            rec["ciphertext"] = ("B" if ct[0] != "B" else "C") + ct[1:]   # change one letter
    save_records(records)
    print(f"[TAMPERED] altered ciphertext of message {rec_id}")


# =====================================================================================
# MENU-DRIVEN
# =====================================================================================
def menu():
    keys = load_or_create_keys()
    print("Military Message System. Users: field (field unit), cmd (command centre), mon (monitor)")
    print(f"DH set up: p,g given, shared K established, K mod 26 = {keys[6] % 26} (gate needs {CHECKPOINT})")
    while True:
        user = input("\nlogin as (field/cmd/mon, or 'quit'): ").strip()
        if user == "quit":
            break
        if user == "field":
            while True:
                print("1. send message   2. tamper a message   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    msg = input("message: ")
                    k1 = int(input("enter k1 (coprime with 26): "))
                    field_unit_send(msg, k1, keys)
                elif c == "2":
                    tamper(int(input("message id: ")))
        elif user == "cmd":
            while True:
                print("1. receive + decrypt a message   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    command_centre_receive(int(input("message id: ")), keys)
        elif user == "mon":
            while True:
                print("1. check all messages for tampering   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    monitor_check(keys)
        else:
            print("unknown user")


# =====================================================================================
# SELF-TEST
# =====================================================================================
def self_test():
    global STORE, KEYS
    STORE, KEYS = "._msg_test.json", "._milk_test.json"
    for f in (STORE, KEYS):
        if os.path.exists(f):
            os.remove(f)
    keys = load_or_create_keys()
    assert keys[6] % 26 == CHECKPOINT                 # gate passes

    # send with a valid k1
    rec = field_unit_send("attack at dawn", 7, keys)
    assert rec is not None
    # receiver decrypts back
    assert command_centre_receive(rec["id"], keys) == "ATTACKATDAWN"

    # invalid k1 (gcd(2,26)!=1) -> refused at send
    assert field_unit_send("hello", 2, keys) is None

    # monitor sees it intact; tamper -> receiver refuses, monitor flags it
    tamper(rec["id"])
    assert command_centre_receive(rec["id"], keys) is None
    assert sha256(load_records()[0]["ciphertext"].encode()) != load_records()[0]["hash"]

    # keys persist -> same K after reload
    keys2 = load_or_create_keys()
    assert keys2[6] == keys[6]

    for f in (STORE, KEYS):
        os.remove(f)
    print("ALL PASSED")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "test":
        self_test()
    else:
        menu()
