"""
Agent A, T2. Coverage-gap fill: the original downward_closure.py phase 2
(d = 1001..3000) tested only n in {9, 16, 25, 27} plus closure levels, so
n in {49, 81, 121, 125} were NEVER tested on 1001 <= d <= 3000. This run
closes that gap: same range, targets p^a in {49, 121} (a = 2) and
{81, 125} (higher levels of p = 3, 5), prefiltered by the rigorous
necessary condition p | s, with both chains checked at any hit.
"""
import sys, math, time

sys.path.insert(0, "<path>")
sys.path.insert(0, "<path>")
import fastlam  # noqa: E402
from qcore import pell_plus1  # noqa: E402
import sympy as sp

Q = sp.Symbol('q')
TARGETS = {3: [1, 2, 3, 4], 5: [1, 2, 3], 7: [1, 2], 11: [1, 2]}
PHI = {}
for p, As in TARGETS.items():
    for a in As:
        n = p ** a
        PHI[n] = [int(x) for x in sp.Poly(sp.cyclotomic_poly(n, Q), Q).all_coeffs()[::-1]]


def shift(poly):
    if not poly:
        return [0]
    mn = min(poly)
    out = [0] * (max(poly) - mn + 1)
    for e, c in poly.items():
        out[e - mn] = c
    return out


def divides(pdict, n):
    if not pdict:
        return True
    rem = list(shift(pdict))
    divisor = PHI[n]
    dd = len(divisor) - 1
    deg = len(rem) - 1
    while deg >= dd:
        while deg >= 0 and rem[deg] == 0:
            deg -= 1
        if deg < dd:
            break
        lead = rem[deg]
        if lead:
            sh = deg - dd
            for i, dc in enumerate(divisor):
                rem[sh + i] -= lead * dc
        deg -= 1
    return all(c == 0 for c in rem)


def v_p(x, p):
    v = 0
    x = abs(x)
    while x and x % p == 0:
        x //= p
        v += 1
    return v


def main():
    t0 = time.time()
    hits = []
    n_poly = 0
    # only the levels untested in the original phase 2:
    # p=7 (49), p=11 (121), p=3 level 81, p=5 level 125
    for d in range(1001, 3001):
        a0 = math.isqrt(d)
        if a0 * a0 == d:
            continue
        r, s = pell_plus1(d)
        want = []
        if s % 7 == 0:
            want.append((7, 2))
        if s % 11 == 0:
            want.append((11, 2))
        if s % 3 == 0:
            want.append((3, 4))
        if s % 5 == 0:
            want.append((5, 3))
        if not want:
            continue
        n_poly += 1
        (r2, s2), (A, B, C, D_) = fastlam.lam_q_fast(d)
        for p, atop in want:
            if divides(C, p ** atop):
                f = dict(A)
                for e, c in D_.items():
                    f[e] = f.get(e, 0) - c
                chainC = all(divides(C, p ** j) for j in range(1, atop + 1))
                chainAD = all(divides({e: c for e, c in f.items() if c}, p ** j)
                              for j in range(1, atop + 1))
                hits.append((d, p ** atop, chainC, chainAD, v_p(s, p)))
                print(f"HIT d={d} n={p**atop} chainC={chainC} chainAD={chainAD}",
                      flush=True)
        if d % 500 == 0:
            print(f"  d={d} elapsed={time.time()-t0:.1f}s poly={n_poly}", flush=True)
    print(f"\ngap range d=1001..3000, untested levels 49/121/81/125: "
          f"poly-tested {n_poly}, hits (top level divides): {len(hits)}")
    for h in hits:
        print(h)
    print(f"elapsed {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
