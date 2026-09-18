"""
Agent A, T2, pi-adic route. Re-runs the downward_closure.py sweep (same
phases, same test set) but checks, at every prime-power hit p^a with a >= 2:

  1. chainC   : Phi_{p^j} | C for every 1 <= j <= a  (the divisibility chain;
                this is all the original script certified)
  2. chainAD  : Phi_{p^j} | (A - D) for every 1 <= j <= a  (the CONGRUENCE
                chain, i.e. Lemma L at every level; the original script never
                tested this)
  3. vps      : v_p(s), and vpds := v_p((d+1) s) = v_p(gamma_1)
  4. gamma1   : |f'(1)| == (d+1) s for f = A - D (shift-invariant first jet)
  5. glow     : gamma_k == 0 mod p for 1 <= k < p^(a-1)   (predicted by
                (q^{p^(a-1)} - 1) | f)
  6. gbound   : gamma_{p^(a-1)} == gamma_1 / p^(a-1) mod p, and hence == 0
                mod p whenever v_p(gamma_1) >= a  (the new boundary-congruence
                mechanism; discharges the open congruence p | gamma_{p^(a-1)})

All arithmetic exact (integer polynomial long division by monic Phi_n,
integer binomials for the Taylor jets mod p).
"""
import sys, math, time, csv

sys.path.insert(0, "<path>")
import fastlam  # noqa: E402
import sympy as sp

Q = sp.Symbol('q')
TEST_SET = [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 25, 27, 32, 49, 81, 121, 125]
PRIME_POWER = {
    2: (2, 1), 4: (2, 2), 8: (2, 3), 16: (2, 4), 32: (2, 5),
    3: (3, 1), 9: (3, 2), 27: (3, 3), 81: (3, 4),
    5: (5, 1), 25: (5, 2), 125: (5, 3),
    7: (7, 1), 49: (7, 2), 11: (11, 1), 121: (11, 2), 13: (13, 1),
}
PHI_COEFFS = {}
for n in TEST_SET:
    poly = sp.Poly(sp.cyclotomic_poly(n, Q), Q)
    c = [int(x) for x in poly.all_coeffs()[::-1]]
    assert c[-1] == 1
    PHI_COEFFS[n] = c


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


def taylor_jets_mod_p(fdict, p, K):
    """Taylor coefficients gamma_0..gamma_K of q^{-min} f at q = 1, mod p.
    gamma_k = sum_e c_e * binom(e', k) with e' = e - min_e."""
    if not fdict:
        return [0] * (K + 1)
    mn = min(fdict)
    jets = [0] * (K + 1)
    for e, c in fdict.items():
        ee = e - mn
        b = 1  # binom(ee, 0)
        cm = c % p
        for k in range(0, K + 1):
            if k > 0:
                b = b * (ee - k + 1) // k
            jets[k] = (jets[k] + cm * (b % p)) % p
    return jets


def gamma1_exact(fdict):
    """f~'(1) for f~ = q^{-min} f; equals f'(1) when f(1) = 0."""
    if not fdict:
        return 0
    mn = min(fdict)
    return sum(c * (e - mn) for e, c in fdict.items())


def examine_hit(d, s, p, a, A, B, C, D, divC):
    f = sub_dict(A, D)
    chainC = all(divC.get(p ** j, phi_divides(C, p ** j)) for j in range(1, a + 1))
    chainAD = all(phi_divides(f, p ** j) for j in range(1, a + 1))
    vps = v_p(s, p)
    g1 = gamma1_exact(f)
    vpds = v_p((d + 1) * s, p)
    g1_ok = (abs(g1) == (d + 1) * s)
    K = p ** (a - 1)
    jets = taylor_jets_mod_p(f, p, K)
    glow = all(jets[k] == 0 for k in range(1, K))
    # boundary: gamma_K mod p vs (gamma_1 / p^(a-1)) mod p
    if v_p(g1, p) >= a - 1:
        pred = (g1 // p ** (a - 1)) % p
        gbound_identity = (jets[K] == pred)
    else:
        gbound_identity = None  # gamma_1 / p^(a-1) not an integer: flag
    gbound_zero = (jets[K] == 0)
    return dict(d=d, n=p ** a, p=p, a=a, s=s, chainC=chainC, chainAD=chainAD,
                vps=vps, vpds=vpds, g1_ok=g1_ok, glow=glow,
                gbound_identity=gbound_identity, gbound_zero=gbound_zero)


def main():
    t0 = time.time()
    rows = []
    # Phase 1: exhaustive d = 2..1000, full test set
    for d in range(2, 1001):
        a0 = math.isqrt(d)
        if a0 * a0 == d:
            continue
        (r, s), (A, B, C, D) = fastlam.lam_q_fast(d)
        divC = {n: phi_divides(C, n) for n in TEST_SET}
        for n, (p, a) in PRIME_POWER.items():
            if a >= 2 and divC[n]:
                rows.append(examine_hit(d, s, p, a, A, B, C, D, divC))
        if d % 200 == 0:
            print(f"  phase1 d={d} elapsed={time.time()-t0:.1f}s hits={len(rows)}", flush=True)
    # Phase 2: d = 1001..3000, hunt {9,16,25,27} + closure levels
    hunt_ns = (9, 16, 25, 27)
    hunt_test = sorted({p ** j for n in hunt_ns
                        for p, a in [PRIME_POWER[n]] for j in range(1, a + 1)})
    for d in range(1001, 3001):
        a0 = math.isqrt(d)
        if a0 * a0 == d:
            continue
        (r, s), (A, B, C, D) = fastlam.lam_q_fast(d)
        divC = {n: phi_divides(C, n) for n in hunt_test}
        for n in hunt_ns:
            p, a = PRIME_POWER[n]
            if divC[n]:
                rows.append(examine_hit(d, s, p, a, A, B, C, D, divC))
        if d % 400 == 0:
            print(f"  phase2 d={d} elapsed={time.time()-t0:.1f}s hits={len(rows)}", flush=True)

    rows.sort(key=lambda h: (h['d'], h['n']))
    out = "<path>"
    with open(out, "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["d", "n", "p", "a", "s", "chainC", "chainAD", "v_p_s",
                    "v_p_d1s", "g1_ok", "glow", "gbound_identity", "gbound_zero"])
        for h in rows:
            w.writerow([h['d'], h['n'], h['p'], h['a'], h['s'], h['chainC'],
                        h['chainAD'], h['vps'], h['vpds'], h['g1_ok'], h['glow'],
                        h['gbound_identity'], h['gbound_zero']])
    N = len(rows)
    def cnt(k): return sum(1 for h in rows if h[k] is True)
    print(f"\ntotal hits (a>=2): {N}  [expect 608]")
    print(f"chainC  (divisibility chain, j=1..a): {cnt('chainC')}/{N}")
    print(f"chainAD (congruence chain,  j=1..a): {cnt('chainAD')}/{N}")
    print(f"v_p(s) >= a: {sum(1 for h in rows if h['vps'] >= h['a'])}/{N}")
    print(f"v_p((d+1)s) >= a: {sum(1 for h in rows if h['vpds'] >= h['a'])}/{N}")
    print(f"|gamma_1| == (d+1)s: {cnt('g1_ok')}/{N}")
    print(f"gamma_k = 0 mod p for k < p^(a-1): {cnt('glow')}/{N}")
    print(f"gamma_(p^(a-1)) == gamma_1/p^(a-1) mod p: {cnt('gbound_identity')}/{N} "
          f"(None-flags: {sum(1 for h in rows if h['gbound_identity'] is None)})")
    print(f"gamma_(p^(a-1)) == 0 mod p: {cnt('gbound_zero')}/{N}")
    for k in ('chainC', 'chainAD', 'g1_ok', 'glow', 'gbound_zero'):
        bad = [h for h in rows if h[k] is not True]
        if bad:
            print(f"EXCEPTIONS {k}: {[(h['d'], h['n']) for h in bad][:20]}")
    print(f"elapsed {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
