"""
Confirmation checks for T4 (Agent B). Reads the 166-row proper-collapse table
straight out of the WP3 mining report (d, s_d, a, T) and verifies the
constraints derived from the proved results of section 08.

No new census rows are generated. This only re-reads existing data and checks
derived necessary conditions on the existing 166 cases.
"""
import re
from sympy import divisors, factorint

MINING = ("<path>"
          "2026-07-11-negation-paper/code-wp3/realizability-mining.md")


def parse_rows():
    rows = []
    with open(MINING) as f:
        for line in f:
            line = line.strip()
            # table rows look like: | 21 | 12 | 7 | [2, 3, 4] | [...] | [...] |
            if not line.startswith("|"):
                continue
            cells = [c.strip() for c in line.strip("|").split("|")]
            if len(cells) != 6:
                continue
            if not cells[0].isdigit():
                continue
            # Only the 166-case table has bracket-list T, Div, missing columns.
            if not (cells[3].startswith("[") and cells[4].startswith("[")
                    and cells[5].startswith("[")):
                continue
            d = int(cells[0]); s_d = int(cells[1]); a = int(cells[2])
            T = [int(x) for x in re.findall(r"\d+", cells[3])]
            rows.append(dict(d=d, s_d=s_d, a=a, T=sorted(set(T))))
    return rows


def prime_powers(s):
    """The maximal prime-power divisors p^e || s."""
    return [p**e for p, e in factorint(s).items()]


def sign_at(a, pe):
    """+1 / -1 / 0(mixed) of a modulo pe."""
    if a % pe == 1 % pe:
        return +1
    if a % pe == (-1) % pe:
        return -1
    return 0


def all_same_sign_divisors(a, s):
    """Divisors n>1 of s all of whose prime-power parts carry the same sign
       (this is exactly candidate A's predicted T, and equals {n : a^2==1 mod n})."""
    out = []
    for n in divisors(s):
        if n == 1:
            continue
        signs = set()
        ok = True
        for p, e in factorint(n).items():
            pe = p**e
            sg = sign_at(a, pe)
            if sg == 0:
                ok = False
                break
            signs.add(sg)
        if ok and len(signs) == 1:
            out.append(n)
    return sorted(out)


def cand_C_partition(T, s):
    """Connectivity rule: union-find on the distinct primes of s, joining
       p,p' whenever some m in T is divisible by both. Predicted T = union over
       components of divisors(prod of p^e in component)."""
    primes = sorted(factorint(s).keys())
    parent = {p: p for p in primes}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x, y):
        parent[find(x)] = find(y)

    for m in T:
        mp = sorted(factorint(m).keys())
        for i in range(1, len(mp)):
            union(mp[0], mp[i])
    comps = {}
    for p in primes:
        comps.setdefault(find(p), []).append(p)
    ppmap = {p: p**e for p, e in factorint(s).items()}
    predicted = set()
    for comp in comps.values():
        prod = 1
        for p in comp:
            prod *= ppmap[p]
        for n in divisors(prod):
            if n > 1:
                predicted.add(n)
    return sorted(predicted)


def main():
    rows = parse_rows()
    assert len(rows) == 166, f"expected 166 rows, got {len(rows)}"

    # (1) pure-residue: every prime power p^e || s_d has a == +-1 mod p^e
    pure_fail = []
    # (2) A upper bound: actual T subset of candidate-A set
    a_not_upper = []
    a_exact = 0
    # (3) necessary direction n in T => a^2==1 mod n  (direct congruence;
    #     this treats the prime 2 at exponent 1 as a sign wildcard, since
    #     a == +1 == -1 mod 2 always)
    necdir_fail = []
    # (3b) same, but as an upper bound: T subset {n>1 : a^2==1 mod n}
    b_upper_fail = []
    b_upper_exact = 0
    # (4) C predictions: how many exact, and among the misses, does C ever
    #     predict the FULL divisor set (which degree-equality would exclude)?
    c_exact = 0
    c_misses = []
    c_full_predictions = []   # misses where predicted C == all divisors>1
    b_trivial_full = 0        # rows where T_B == all divisors (would be trivial)

    for r in rows:
        d, s, a, T = r["d"], r["s_d"], r["a"], set(r["T"])
        pps = prime_powers(s)
        for pe in pps:
            if sign_at(a, pe) == 0:
                pure_fail.append((d, s, a, pe))

        TA = set(all_same_sign_divisors(a, s))
        if not T.issubset(TA):
            a_not_upper.append((d, s, sorted(T - TA)))
        if T == TA:
            a_exact += 1

        # GLOBAL pure-sign predicate P(n): a == +1 mod n OR a == -1 mod n.
        # This is candidate B's membership (2 treated as a sign wildcard).
        # Necessary direction under test: n in T  =>  P(n).
        def P(n):
            return a % n == 1 % n or a % n == (n - 1) % n
        for n in T:
            if not P(n):
                necdir_fail.append((d, s, n))
        TB = set(n for n in divisors(s) if n > 1 and P(n))
        alldiv2 = set(n for n in divisors(s) if n > 1)
        if not T.issubset(TB):
            b_upper_fail.append((d, s, sorted(T - TB)))
        if T == TB:
            b_upper_exact += 1
        # non-triviality: T_B is a PROPER subset of all divisors on collapse rows
        if TB == alldiv2:
            b_trivial_full += 1

        TC = set(cand_C_partition(sorted(T), s))
        alldiv = set(m for m in divisors(s) if m > 1)
        if TC == T:
            c_exact += 1
        else:
            c_misses.append((d, s, sorted(T), sorted(TC)))
            if TC == alldiv:
                c_full_predictions.append((d, s))

    print("rows parsed:", len(rows))
    print()
    print("(1) pure-residue a==+-1 mod every p^e || s_d : failures =",
          len(pure_fail), "/ 166")
    print("(2) A upper bound  T subset T_A            : failures =",
          len(a_not_upper), "/ 166   (A exact on", a_exact, "rows)")
    print("(3) necessary dir  n in T => a==+-1 mod n  : failures =",
          len(necdir_fail), "/ 166   (GLOBAL congruence)")
    print("(3b) B upper bound T subset T_B(global +-1): failures =",
          len(b_upper_fail), "/ 166   (B exact on", b_upper_exact, "rows)")
    print("     rows where T_B == all divisors (trivial):", b_trivial_full,
          "/ 166  -> non-trivial on", 166 - b_trivial_full, "rows")
    if b_upper_fail:
        for x in b_upper_fail:
            print("     B-upper violation:", x)
    print("(4) C exact:", c_exact, " C misses:", len(c_misses))
    print("    among the", len(c_misses),
          "C misses, rows where C predicts the FULL divisor set")
    print("    (i.e. deg=s_d-1, which thm:degree-equality excludes):",
          len(c_full_predictions))
    if c_full_predictions:
        print("    ->", c_full_predictions)
    print()
    if a_not_upper:
        print("A-upper-bound violations (should be none):")
        for x in a_not_upper:
            print("   ", x)
    if necdir_fail:
        print("necessary-direction violations (should be none):")
        for x in necdir_fail:
            print("   ", x)

    # For each C miss, is it over-prediction (T subset TC), under, or crossing?
    over = under = cross = 0
    for d, s, T, TC in c_misses:
        Ts, TCs = set(T), set(TC)
        if Ts < TCs:
            over += 1
        elif TCs < Ts:
            under += 1
        else:
            cross += 1
    print()
    print("C miss geometry:  over-predict (T subset C):", over,
          " under-predict (C subset T):", under, " crossing:", cross)

    # Does pruning C by the proved upper bound T_B (global +-1) fix any misses?
    cprimeB_exact = 0
    cprimeA_exact = 0
    for r in rows:
        d, s, a, T = r["d"], r["s_d"], r["a"], set(r["T"])
        TC = set(cand_C_partition(sorted(T), s))
        TB = set(n for n in divisors(s) if n > 1 and
                 (a % n == 1 % n or a % n == (n - 1) % n))
        TA = set(all_same_sign_divisors(a, s))  # 2-committed-to-plus
        if (TC & TB) == T:
            cprimeB_exact += 1
        if (TC & TA) == T:
            cprimeA_exact += 1
    print()
    print("C intersect T_B (proved upper bound) exact:", cprimeB_exact, "/ 166")
    print("C intersect T_A (2-committed)         exact:", cprimeA_exact, "/ 166")

    # Degree deficit sanity: every proper collapse has deg S < s_d - 1
    # deg S = sum phi(n) over T ; compare s_d - 1
    from sympy import totient
    deg_full_violations = 0
    for r in rows:
        degS = sum(int(totient(n)) for n in r["T"])
        if degS >= r["s_d"] - 1:
            deg_full_violations += 1
    print()
    print("proper collapses with deg S >= s_d - 1 (should be 0):",
          deg_full_violations)


if __name__ == "__main__":
    main()
