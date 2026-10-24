# =====================================================================================
#  SCHNORR DIGITAL SIGNATURE   -- teaching file + a 3-role signed-document demo
#
#  WHY SCHNORR (vs RSA / ElGamal):
#    - works in a prime-order subgroup q | (p-1) -> shorter signatures, clean maths
#    - the "challenge" e = H(r || M) binds the message to the commitment r
#    - basis of modern EdDSA. NEVER reuse the nonce k (two sigs with same k -> private key).
#
#  THE MATH
#    params : prime p, prime q with q | (p-1), generator g of the order-q subgroup
#    keygen : private x in [1, q-1];  public y = g^x mod p
#    sign M : pick random k in [1, q-1]
#             r = g^k mod p                       (commitment)
#             e = H(r || M) mod q                 (challenge, binds r and M)
#             s = (k + x*e) mod q                 (response)
#             signature = (e, s)
#    verify : rv = g^s * y^(-e) mod p             (reconstruct the commitment)
#             accept iff  e == H(rv || M) mod q
#    WHY IT WORKS: g^s * y^(-e) = g^(k + x*e) * g^(-x*e) = g^k = r, so rv == r,
#                  hence H(rv||M) == H(r||M) == e.
#
#  python prac9.py        -> menu-driven signed-document system
#  python prac9.py test   -> self-test (ALL PASSED)
#  python prac9.py demo   -> print one signing + verification step by step
# =====================================================================================
import time, json, os, sys, math, random, hashlib
from Crypto.Util.number import getPrime, isPrime, long_to_bytes


def sha256(data):
    return hashlib.sha256(data).hexdigest()


# =====================================================================================
# SCHNORR CORE
# =====================================================================================
def schnorr_params(bits=256):
    """find prime q, then a prime p = k*q + 1, then g of order q."""
    while True:
        q = getPrime(bits)
        for k in range(2, 4000):
            p = k * q + 1
            if isPrime(p):
                g = pow(2, (p - 1) // q, p)          # g = h^((p-1)/q); has order q (unless 1)
                if g != 1:
                    return p, q, g


def schnorr_keygen(params):
    p, q, g = params
    x = random.randint(1, q - 1)                     # private key
    return x, pow(g, x, p)                           # (private x, public y = g^x mod p)


def schnorr_sign(message, params, x, k=None):
    p, q, g = params
    k = k or random.randint(1, q - 1)                # random nonce (NEVER reuse)
    r = pow(g, k, p)                                 # commitment
    e = int(sha256(long_to_bytes(r) + message), 16) % q   # challenge e = H(r || M) mod q
    s = (k + x * e) % q                              # response
    return e, s                                      # signature (e, s)


def schnorr_verify(message, sig, params, y):
    p, q, g = params
    e, s = sig
    rv = (pow(g, s, p) * pow(y, (-e) % q, p)) % p    # rv = g^s * y^(-e) = g^k = r
    return e == int(sha256(long_to_bytes(rv) + message), 16) % q


# attack: reusing k on two messages leaks the private key x
def schnorr_recover_x(sig1, sig2, q):
    """s1 = k + x*e1, s2 = k + x*e2  ->  x = (s1 - s2) / (e1 - e2) mod q  (q prime -> always works)"""
    e1, s1 = sig1
    e2, s2 = sig2
    return ((s1 - s2) * pow((e1 - e2) % q, -1, q)) % q


# =====================================================================================
# 3-ROLE SIGNED DOCUMENT SYSTEM  (Author / Verifier / Auditor)
# =====================================================================================
STORE = "schnorr_docs.json"
KEYS = "schnorr_keys.json"
ROLES = {"a": "author", "v": "verifier", "x": "auditor"}
PERMS = {"author": {"add"}, "verifier": {"verify"}, "auditor": {"audit"}}


def can(user, perm):
    return perm in PERMS.get(ROLES.get(user), set())


def load_store():
    if not os.path.exists(STORE):
        return []
    with open(STORE) as f:
        return json.load(f)


def save_store(recs):
    with open(STORE, "w") as f:
        json.dump(recs, f, indent=2)


def load_or_create_keys():
    if os.path.exists(KEYS):
        with open(KEYS) as f:
            k = json.load(f)
        return tuple(k["params"]), k["x"], k["y"]
    params = schnorr_params(256)
    x, y = schnorr_keygen(params)
    with open(KEYS, "w") as f:
        json.dump({"params": list(params), "x": x, "y": y}, f)
    return params, x, y


def author_add(user, text, params, x):
    if not can(user, "add"):
        raise PermissionError("not allowed")
    e, s = schnorr_sign(text.encode(), params, x)
    rec = {"id": len(load_store()) + 1, "doc": text, "sig": [e, s], "timestamp": time.strftime("%Y-%m-%d %H:%M:%S")}
    recs = load_store(); recs.append(rec); save_store(recs)
    print(f"[SIGNED] doc {rec['id']}  signature (e,s) stored")
    return rec


def verify_rec(rec, params, y):
    return schnorr_verify(rec["doc"].encode(), tuple(rec["sig"]), params, y)


def verifier_check(user, rid, params, y):
    if not can(user, "verify"):
        raise PermissionError("not allowed")
    rec = next((r for r in load_store() if r["id"] == rid), None)
    if not rec:
        print("no such doc"); return
    ok = verify_rec(rec, params, y)
    print(f"  doc {rid}: signature {'VALID' if ok else 'INVALID'}")
    if ok:
        print("  document:", rec["doc"])


def auditor_check(user, params, y):
    if not can(user, "audit"):
        raise PermissionError("not allowed")
    for rec in load_store():
        print(f"  doc {rec['id']}: {'VALID' if verify_rec(rec, params, y) else 'INVALID'}")


def tamper(rid):
    recs = load_store()
    for rec in recs:
        if rec["id"] == rid:
            rec["doc"] = rec["doc"] + "X"            # change the document -> signature must fail
    save_store(recs)
    print(f"[TAMPERED] altered doc {rid}")


# =====================================================================================
# MENU + DEMO + TEST
# =====================================================================================
def menu():
    params, x, y = load_or_create_keys()
    print("Schnorr signed documents. Users: a (author), v (verifier), x (auditor)")
    while True:
        user = input("\nlogin as (a/v/x, or 'quit'): ").strip()
        if user == "quit":
            break
        role = ROLES.get(user)
        if role is None:
            print("unknown user"); continue
        print(f"--- {user} : {role} ---")
        if role == "author":
            while True:
                print("1. sign a document   2. tamper a doc   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    author_add(user, input("document text: "), params, x)
                elif c == "2":
                    tamper(int(input("doc id: ")))
        elif role == "verifier":
            while True:
                print("1. verify a document   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    verifier_check(user, int(input("doc id: ")), params, y)
        elif role == "auditor":
            while True:
                print("1. audit all documents   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    auditor_check(user, params, y)


def demo():
    print("=== Schnorr signature, step by step ===")
    params = schnorr_params(256)
    p, q, g = params
    print(f"p (bits={p.bit_length()}), q (bits={q.bit_length()}), g = {g % 100000}...")
    x, y = schnorr_keygen(params)
    print(f"private x = {x % 100000}...   public y = g^x = {y % 100000}...")
    M = b"transfer approved"
    k = random.randint(1, q - 1)
    r = pow(g, k, p)
    e = int(sha256(long_to_bytes(r) + M), 16) % q
    s = (k + x * e) % q
    print(f"sign:  k(random) -> r=g^k ; e=H(r||M)={e % 100000}... ; s=k+x*e={s % 100000}...")
    rv = (pow(g, s, p) * pow(y, (-e) % q, p)) % p
    print(f"verify: rv = g^s * y^(-e) ; rv == r ? {rv == r} ; accept ? {e == int(sha256(long_to_bytes(rv) + M), 16) % q}")


def self_test():
    global STORE, KEYS
    STORE, KEYS = "._sch_test.json", "._schk_test.json"
    for f in (STORE, KEYS):
        if os.path.exists(f):
            os.remove(f)
    params, x, y = load_or_create_keys()

    # core: genuine verifies, tampered fails
    sig = schnorr_sign(b"hello", params, x)
    assert schnorr_verify(b"hello", sig, params, y)
    assert not schnorr_verify(b"hellp", sig, params, y)

    # reused-nonce attack recovers the private key
    k = random.randint(1, params[1] - 1)
    s1 = schnorr_sign(b"msg one", params, x, k)
    s2 = schnorr_sign(b"msg two", params, x, k)
    assert schnorr_recover_x(s1, s2, params[1]) == x

    # 3-role system
    author_add("a", "contract A", params, x)
    author_add("a", "contract B", params, x)
    assert all(verify_rec(r, params, y) for r in load_store())
    # RBAC: verifier cannot sign
    try:
        author_add("v", "x", params, x); raise AssertionError
    except PermissionError:
        pass
    # tamper -> signature fails
    tamper(1)
    assert not verify_rec(load_store()[0], params, y)

    for f in (STORE, KEYS):
        os.remove(f)
    print("ALL PASSED")


if __name__ == "__main__":
    arg = sys.argv[1] if len(sys.argv) > 1 else ""
    if arg == "test":
        self_test()
    elif arg == "demo":
        demo()
    else:
        menu()
