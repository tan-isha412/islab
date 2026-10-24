# =====================================================================================
#  PRIVACY-PRESERVING E-VOTING SYSTEM   (Officer / Voter / Teller)
#    Officer : register candidates (each with a Paillier-encrypted tally starting at 0)
#              and register voters; each candidate record is SHA-256 hashed + ElGamal signed.
#    Voter   : cast ONE vote for a candidate -> homomorphically add E(1) to that candidate's
#              tally (the vote is never decrypted); re-sign the updated tally.
#    Teller  : verify signatures, decrypt ONLY each candidate's final tally, declare winner.
#
#  No individual vote is ever decrypted -- only the per-candidate totals.
#
#  python prac3.py        -> menu-driven
#  python prac3.py test   -> self-test (ALL PASSED)
# =====================================================================================
import time, json, os, sys, math, random, hashlib
from Crypto.Util.number import getPrime

STORE = "election.json"
KEYS = "election_keys.json"


# =====================================================================================
# HELPERS
# =====================================================================================
def timestamp():
    return time.strftime("%Y-%m-%d %H:%M:%S")


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def _hash_int(message, mod):
    return int(sha256(message), 16) % mod


# ---- Paillier (additive HE: the vote tally) ----
def L(u, n):
    return (u - 1) // n


def paillier_keygen(bits=512):
    while True:
        p, q = getPrime(bits // 2), getPrime(bits // 2)
        if p != q and math.gcd(p * q, (p - 1) * (q - 1)) == 1:
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
        r = random.randrange(1, n)
        if math.gcd(r, n) == 1:
            break
    return (pow(g, m, n * n) * pow(r, n, n * n)) % (n * n)


def paillier_decrypt(c, priv):
    lam, mu, n = priv
    return (L(pow(c, lam, n * n), n) * mu) % n


def paillier_add(c1, c2, pub):                     # E(a)*E(b) -> E(a+b)
    n, _ = pub
    return (c1 * c2) % (n * n)


# ---- ElGamal signature (on each candidate tally) ----
def elgamal_keygen(bits=256):
    p = getPrime(bits)
    g = 2
    x = random.randint(2, p - 2)
    return (p, g, pow(g, x, p)), x


def elgamal_sign(message, p, g, x):
    while True:
        k = random.randint(2, p - 2)
        if math.gcd(k, p - 1) == 1:
            break
    r = pow(g, k, p)
    s = ((_hash_int(message, p) - x * r) * pow(k, -1, p - 1)) % (p - 1)
    return r, s


def elgamal_verify(message, sig, p, g, y):
    r, s = sig
    if not 0 < r < p:
        return False
    return pow(g, _hash_int(message, p), p) == (pow(y, r, p) * pow(r, s, p)) % p


# =====================================================================================
# RBAC
# =====================================================================================
USER_ROLES = {"off": "officer", "vtr": "voter", "tlr": "teller"}
ROLE_PERMS = {
    "officer": {"register"},
    "voter":   {"vote"},
    "teller":  {"tally", "audit"},
}


def can(user, perm):
    return perm in ROLE_PERMS.get(USER_ROLES.get(user), set())


# =====================================================================================
# STORE  (one dict: candidates {name -> tally record} + voters {id -> {name, voted}})
# =====================================================================================
def load_store():
    if not os.path.exists(STORE):
        return {"candidates": {}, "voters": {}}
    with open(STORE, "r", encoding="utf-8") as f:
        return json.load(f)


def save_store(db):
    with open(STORE, "w", encoding="utf-8") as f:
        json.dump(db, f, indent=2)


def load_or_create_keys():
    if os.path.exists(KEYS):
        with open(KEYS) as f:
            k = json.load(f)
        return tuple(k["paill_pub"]), tuple(k["paill_priv"]), tuple(k["eg_pub"]), k["eg_priv"]
    paill_pub, paill_priv = paillier_keygen(512)
    eg_pub, eg_priv = elgamal_keygen(256)
    with open(KEYS, "w") as f:
        json.dump({"paill_pub": list(paill_pub), "paill_priv": list(paill_priv),
                   "eg_pub": list(eg_pub), "eg_priv": eg_priv}, f)
    return paill_pub, paill_priv, eg_pub, eg_priv


# what gets hashed/signed for a candidate tally
def cand_payload(name, rec):
    return f"{name}|{rec['tally']}".encode()


# =====================================================================================
# ROLE ACTIONS
# =====================================================================================
def officer_add_candidate(user, name, paill_pub, eg_pub, eg_priv):
    if not can(user, "register"):
        raise PermissionError("not allowed")
    p, g, _ = eg_pub
    db = load_store()
    rec = {"tally": str(paillier_encrypt(0, paill_pub))}        # tally starts at E(0)
    rec["hash"] = sha256(cand_payload(name, rec))
    rec["sign"] = elgamal_sign(cand_payload(name, rec), p, g, eg_priv)
    db["candidates"][name] = rec
    save_store(db)
    print(f"[CANDIDATE] {name} registered")


def officer_reg_voter(user, name):
    if not can(user, "register"):
        raise PermissionError("not allowed")
    db = load_store()
    vid = str(len(db["voters"]) + 1)
    db["voters"][vid] = {"name": name, "voted": False}
    save_store(db)
    print(f"[VOTER] {name} registered with id {vid}")
    return vid


def voter_cast(user, voter_id, candidate, paill_pub, eg_pub, eg_priv):
    if not can(user, "vote"):
        raise PermissionError("not allowed")
    p, g, _ = eg_pub
    db = load_store()
    voter = db["voters"].get(str(voter_id))
    if voter is None:
        print("  no such voter"); return False
    if voter["voted"]:
        print(f"  voter {voter_id} has ALREADY voted"); return False
    if candidate not in db["candidates"]:
        print("  no such candidate"); return False
    rec = db["candidates"][candidate]
    # homomorphically add 1 vote to the candidate's tally (the vote is never decrypted)
    rec["tally"] = str(paillier_add(int(rec["tally"]), paillier_encrypt(1, paill_pub), paill_pub))
    rec["hash"] = sha256(cand_payload(candidate, rec))         # re-hash + re-sign the updated tally
    rec["sign"] = elgamal_sign(cand_payload(candidate, rec), p, g, eg_priv)
    voter["voted"] = True                                      # stop double voting
    save_store(db)
    print(f"  voter {voter_id} voted for {candidate}")
    return True


def _verify(name, rec, eg_pub):
    p, g, y = eg_pub
    pl = cand_payload(name, rec)
    return sha256(pl) == rec["hash"], elgamal_verify(pl, tuple(rec["sign"]), p, g, y)


def teller_tally(user, paill_pub, paill_priv, eg_pub):
    if not can(user, "tally"):
        raise PermissionError("not allowed")
    db = load_store()
    results = {}
    for name, rec in db["candidates"].items():
        hash_ok, sig_ok = _verify(name, rec, eg_pub)
        if not (hash_ok and sig_ok):
            print(f"  {name}: TAMPERED tally, skipping"); continue
        votes = paillier_decrypt(int(rec["tally"]), paill_priv)   # decrypt ONLY the total
        results[name] = votes
        print(f"  {name}: {votes} votes")
    if results:
        winner = max(results, key=results.get)
        print(f"  WINNER: {winner} ({results[winner]} votes)")
    return results


def teller_audit(user, eg_pub):
    if not can(user, "audit"):
        raise PermissionError("not allowed")
    db = load_store()
    for name, rec in db["candidates"].items():
        h, s = _verify(name, rec, eg_pub)
        print(f"  {name}: {'VALID' if h and s else 'INVALID'}")


def tamper(candidate):
    db = load_store()
    if candidate in db["candidates"]:
        rec = db["candidates"][candidate]
        rec["tally"] = str(int(rec["tally"]) + 1)              # alter the encrypted tally
        save_store(db)
        print(f"[TAMPERED] altered {candidate}'s tally")


# =====================================================================================
# MENU-DRIVEN
# =====================================================================================
def menu():
    paill_pub, paill_priv, eg_pub, eg_priv = load_or_create_keys()
    print("E-Voting. Users: off (officer), vtr (voter), tlr (teller)")
    while True:
        user = input("\nlogin as (off/vtr/tlr, or 'quit'): ").strip()
        if user == "quit":
            break
        role = USER_ROLES.get(user)
        if role is None:
            print("unknown user"); continue
        print(f"--- {user} : {role} ---")

        if role == "officer":
            while True:
                print("1. add candidate   2. register voter   3. tamper a tally   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    officer_add_candidate(user, input("candidate name: "), paill_pub, eg_pub, eg_priv)
                elif c == "2":
                    officer_reg_voter(user, input("voter name: "))
                elif c == "3":
                    tamper(input("candidate to tamper: "))

        elif role == "voter":
            while True:
                print("1. cast vote   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    vid = input("your voter id: ")
                    cand = input("candidate: ")
                    voter_cast(user, vid, cand, paill_pub, eg_pub, eg_priv)

        elif role == "teller":
            while True:
                print("1. tally + winner   2. audit signatures   0. logout")
                c = input("choice: ").strip()
                if c == "0":
                    break
                elif c == "1":
                    teller_tally(user, paill_pub, paill_priv, eg_pub)
                elif c == "2":
                    teller_audit(user, eg_pub)


# =====================================================================================
# SELF-TEST
# =====================================================================================
def self_test():
    global STORE, KEYS
    STORE, KEYS = "._elec_test.json", "._ek_test.json"
    for f in (STORE, KEYS):
        if os.path.exists(f):
            os.remove(f)
    paill_pub, paill_priv, eg_pub, eg_priv = load_or_create_keys()

    officer_add_candidate("off", "Alice", paill_pub, eg_pub, eg_priv)
    officer_add_candidate("off", "Bob", paill_pub, eg_pub, eg_priv)
    for name in ("V1", "V2", "V3"):
        officer_reg_voter("off", name)

    assert voter_cast("vtr", "1", "Alice", paill_pub, eg_pub, eg_priv)
    assert voter_cast("vtr", "2", "Alice", paill_pub, eg_pub, eg_priv)
    assert voter_cast("vtr", "3", "Bob", paill_pub, eg_pub, eg_priv)
    # double vote rejected
    assert not voter_cast("vtr", "1", "Bob", paill_pub, eg_pub, eg_priv)

    res = teller_tally("tlr", paill_pub, paill_priv, eg_pub)
    assert res == {"Alice": 2, "Bob": 1}

    # RBAC: voter cannot tally, officer cannot vote
    for bad in [lambda: teller_tally("vtr", paill_pub, paill_priv, eg_pub),
                lambda: voter_cast("off", "1", "Alice", paill_pub, eg_pub, eg_priv)]:
        try:
            bad(); raise AssertionError("RBAC not enforced")
        except PermissionError:
            pass

    # tamper Alice's tally -> verify fails -> excluded from tally
    tamper("Alice")
    name_ok = _verify("Alice", load_store()["candidates"]["Alice"], eg_pub)
    assert name_ok == (False, False)

    for f in (STORE, KEYS):
        os.remove(f)
    print("ALL PASSED")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "test":
        self_test()
    else:
        menu()
