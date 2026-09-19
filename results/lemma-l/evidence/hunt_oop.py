"""
T2 (route A). Out-of-population hunt for odd prime-power hits, d > 3000.

Targets every odd prime power the existing 608-hit population never reached
or barely reached: n in {9, 27, 81} (p=3), {25, 125} (p=5), {49} (p=7),
{121} (p=11). The existing population contains ZERO hits at p >= 7 and none
at 81 or 125, so any hit found here is genuinely out of population.

Prefilter: Phi_{p^a} | C requires p | s (Phi_{p^a}(1) = p divides
C(1) = +-s), and s is cheap via pell_plus1. Polynomial work only for d
where at least one target prime divides s.

Guard: d with s above S_DIGITS decimal digits are skipped and counted, so
the hunt's own selection is reported, not hidden.

At every hit p^a, a >= 2, checks BOTH chains:
  chainC : Phi_{p^j} | C     for all 1 <= j <= a  (downward closure)
  chainAD: Phi_{p^j} | (A-D) for all 1 <= j <= a  (Lemma L congruence chain)
plus v_p(s) and v_p((d+1)s).
"""
import sys, math, time, csv

sys.path.insert(0, "<path>")
sys.path.insert(0, "<path>")
import fastlam  # noqa: E402
from qcore import pell_plus1  # noqa: E402
import sympy as sp

Q = sp.Symbol('q')
TARGETS = {3: [1, 2, 3, 4], 5: [1, 2, 3], 7: [1, 2], 11: [1, 2]}
ALL_N = sorted(p ** a for p, As in TARGETS.items() for a in As)
PHI_COEFFS = {}
for n in ALL_N:
    c = [int(x) for x in sp.Poly(sp.cyclotomic_poly(n, Q), Q).all_coeffs()[::-1]]
    assert c[-1] == 1
    PHI_COEFFS[n] = c

D_START = 3001
D_END = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
S_DIGITS = 200


def shift_to_nonneg(poly):
    if not poly:
        return [0]
    mn = min(poly)
    out = [0] * (max(poly) - mn + 1)
    for e, cc in poly.items():
        out[e - mn] = cc
    return out


def poly_rem_monic(dividend, divisor):
    rem = list(dividend)
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
    while len(rem) > 1 and rem[-1] == 0:
        rem.pop()
    return rem


def phi_divides(pdict, n):
    if not pdict:
        return True
    return all(c == 0 for c in poly_rem_monic(shift_to_nonneg(pdict), PHI_COEFFS[n]))


def v_p(x, p):
    if x == 0:
        return 10**9
    v = 0
    x = abs(x)
    while x % p == 0:
        x //= p
        v += 1
    return v


def sub_dict(a, b):
    out = dict(a)
    for e, c in b.items():
        out[e] = out.get(e, 0) - c
        if out[e] == 0:
            del out[e]
    return out


def main():
    t0 = time.time()
    hits = []
    n_tested = n_poly = n_skipped_big = 0
    for d in range(D_START, D_END + 1):
        a0 = math.isqrt(d)
        if a0 * a0 == d:
            continue
        n_tested += 1
        try:
            r, s = pell_plus1(d)
        except RuntimeError:
            # qcore's iteration cap: fundamental solution too large to find.
            # Such d would exceed the S_DIGITS guard anyway; count and skip.
            n_skipped_big += 1
            print(f"  pell_plus1 cap hit at d={d}, skipped", flush=True)
            continue
        ps = [p for p in TARGETS if s % p == 0]
        if not ps:
            continue
        if len(str(s)) > S_DIGITS:
            n_skipped_big += 1
            continue
        n_poly += 1
        (r2, s2), (A, B, C, D_) = fastlam.lam_q_fast(d)
        f = None
        for p in ps:
            # find the largest a with Phi_{p^a} | C among target levels
            div = {}
            for a in TARGETS[p]:
                div[a] = phi_divides(C, p ** a)
            amax = max([a for a in TARGETS[p] if div[a]], default=0)
            if amax >= 2:
                if f is None:
                    f = sub_dict(A, D_)
                chainC = all(div[j] for j in range(1, amax + 1))
                chainAD = all(phi_divides(f, p ** j) for j in range(1, amax + 1))
                hits.append(dict(d=d, p=p, a=amax, n=p ** amax, s=s,
                                 chainC=chainC, chainAD=chainAD,
                                 vps=v_p(s, p), vpds=v_p((d + 1) * s, p),
                                 sub=[div[j] for j in range(1, amax + 1)]))
                h = hits[-1]
                print(f"HIT d={d} n={p**amax} chainC={chainC} chainAD={chainAD} "
                      f"v_p(s)={h['vps']} s_digits={len(str(s))}", flush=True)
        if d % 500 == 0:
            print(f"  d={d} elapsed={time.time()-t0:.1f}s poly_tested={n_poly} "
                  f"skipped_big={n_skipped_big} hits={len(hits)}", flush=True)

    out = "<path>"
    with open(out, "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["d", "n", "p", "a", "s", "chainC", "chainAD", "v_p_s", "v_p_d1s"])
        for h in hits:
            w.writerow([h['d'], h['n'], h['p'], h['a'], h['s'], h['chainC'],
                        h['chainAD'], h['vps'], h['vpds']])
    N = len(hits)
    print(f"\nrange d={D_START}..{D_END}: tested={n_tested}, poly-tested={n_poly}, "
          f"skipped (s > {S_DIGITS} digits) = {n_skipped_big}")
    print(f"odd prime-power hits (a>=2): {N}")
    print(f"by n: { {n: sum(1 for h in hits if h['n']==n) for n in sorted({h['n'] for h in hits})} }")
    print(f"chainC ok: {sum(1 for h in hits if h['chainC'])}/{N}")
    print(f"chainAD ok: {sum(1 for h in hits if h['chainAD'])}/{N}")
    print(f"v_p(s) >= a: {sum(1 for h in hits if h['vps'] >= h['a'])}/{N}")
    bad = [h for h in hits if not (h['chainC'] and h['chainAD'])]
    if bad:
        print("EXCEPTIONS:", [(h['d'], h['n'], h['chainC'], h['chainAD']) for h in bad])
    print(f"elapsed {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
