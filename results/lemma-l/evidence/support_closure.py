"""
T2 (route A). Full-support divisor-closedness census.

For each nonsquare d <= DMAX, computes the COMPLETE cyclotomic support of C,
supp(d) = {n >= 2 : Phi_n | C}, by testing every n with phi(n) <= deg C,
and checks whether supp(d) is divisor-closed: for every n in supp and every
divisor m of n with m >= 2, is m in supp?

Downward closure at prime powers is the special case m, n both powers of the
same p. If full divisor-closedness ever fails at non-prime-power indices, the
prime-power phenomenon is index-specific; if it never fails, the phenomenon
is plausibly one face of a single structural law about supp(C).

Also records, per d, whether n | s for every n in supp (the strong Lemma L
conclusion of proof (ii), here tested far outside n <= 5).
"""
import sys, math, time

sys.path.insert(0, "<path>")
import fastlam  # noqa: E402
import sympy as sp

Q = sp.Symbol('q')
DMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 300
PHI_CACHE = {}


def phi_coeffs(n):
    if n not in PHI_CACHE:
        c = [int(x) for x in sp.Poly(sp.cyclotomic_poly(n, Q), Q).all_coeffs()[::-1]]
        PHI_CACHE[n] = c
    return PHI_CACHE[n]


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


def phi_divides_list(coeffs, n):
    return all(c == 0 for c in poly_rem_monic(coeffs, phi_coeffs(n)))


def main():
    t0 = time.time()
    n_closed = n_open = 0
    violations = []
    strong_fail = []  # (d, n) with Phi_n | C but n does not divide s
    for d in range(2, DMAX + 1):
        a0 = math.isqrt(d)
        if a0 * a0 == d:
            continue
        (r, s), (A, B, C, D) = fastlam.lam_q_fast(d)
        coeffs = shift_to_nonneg(C)
        degC = len(coeffs) - 1
        supp = []
        n = 2
        while n <= 6 * degC + 6:
            if sp.totient(n) <= degC and phi_divides_list(coeffs, n):
                supp.append(n)
            n += 1
        closed = True
        for n in supp:
            for m in range(2, n):
                if n % m == 0 and m not in supp:
                    closed = False
                    violations.append((d, n, m))
        for n in supp:
            if s % n != 0:
                strong_fail.append((d, n))
        if closed:
            n_closed += 1
        else:
            n_open += 1
        if d % 50 == 0:
            print(f"  d={d} elapsed={time.time()-t0:.1f}s closed={n_closed} open={n_open}",
                  flush=True)
    print(f"\nd = 2..{DMAX}: divisor-closed supports: {n_closed}, violations: {n_open}")
    if violations:
        print("VIOLATIONS (d, n in supp, divisor m missing):", violations[:40])
    print(f"strong-form failures (Phi_n | C but n does not divide s): "
          f"{strong_fail[:40] if strong_fail else 'NONE'}")
    print(f"elapsed {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
