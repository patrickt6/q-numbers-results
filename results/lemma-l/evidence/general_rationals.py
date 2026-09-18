"""
Agent A, T2. Discriminating test: is downward closure a property of MGO
q-denominators in general, or of Pell automorphs specifically?

The automorph entry C equals, up to sign and a monomial, the MGO denominator
S_(r/s) of the q-rational [r/s]_q at the fundamental Pell solution (checked:
d = 5 gives C = -q^(-2)(q^3+q^2+q+1), matching q_rational(9,4)). So (DC) is a
statement about S at PELL fractions. This script computes the full cyclotomic
support of S_(r/s) for ALL coprime fractions in a box (no Pell filter) and
checks divisor-closedness. If it fails generically, the Pell structure is
load-bearing in (DC), and any proof must use it; if it never fails, (DC) is
plausibly a general q-rational theorem, provable without Pell input.

Support = {n >= 2 : Phi_n | S}. Also records whether n | s for n in support.
"""
import sys, math, time
from fractions import Fraction

sys.path.insert(0, '<path>')
import sympy as sp
from qreals import q_rational

Q = sp.Symbol('q')
SMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 60
PHI_CACHE = {}


def phi_coeffs(n):
    if n not in PHI_CACHE:
        PHI_CACHE[n] = [int(x) for x in
                        sp.Poly(sp.cyclotomic_poly(n, Q), Q).all_coeffs()[::-1]]
    return PHI_CACHE[n]


def rem_is_zero(coeffs, divisor):
    rem = list(coeffs)
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


def main():
    t0 = time.time()
    n_frac = n_closed = 0
    violations = []
    n_div_s_fail = []
    for s in range(2, SMAX + 1):
        for r in range(s + 1, 2 * s):
            if math.gcd(r, s) != 1:
                continue
            n_frac += 1
            expr = q_rational(r, s)
            num, den = sp.fraction(sp.together(expr))
            coeffs = [int(c) for c in sp.Poly(sp.expand(den), Q).all_coeffs()[::-1]]
            degS = len(coeffs) - 1
            supp = []
            n = 2
            while n <= 6 * degS + 6:
                if sp.totient(n) <= degS and rem_is_zero(coeffs, phi_coeffs(n)):
                    supp.append(n)
                n += 1
            closed = True
            for n in supp:
                for m in range(2, n):
                    if n % m == 0 and m not in supp:
                        closed = False
                        violations.append((r, s, n, m))
            if closed:
                n_closed += 1
            for n in supp:
                if s % n != 0:
                    n_div_s_fail.append((r, s, n))
        if s % 10 == 0:
            print(f"  s<={s} fractions={n_frac} closed={n_closed} "
                  f"violations={len(violations)} elapsed={time.time()-t0:.1f}s",
                  flush=True)
    print(f"\nfractions r/s, 1 < r/s < 2, s <= {SMAX}: {n_frac}")
    print(f"divisor-closed supports: {n_closed}; violations: {n_frac - n_closed}")
    if violations:
        print("VIOLATIONS (r, s, n in supp, missing divisor m):", violations[:60])
    print(f"n | s failures (Phi_n | S but n does not divide s): "
          f"{n_div_s_fail[:60] if n_div_s_fail else 'NONE'} "
          f"(total {len(n_div_s_fail)})")
    print(f"elapsed {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
