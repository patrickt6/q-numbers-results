"""Attack 3: the mismatch ratio r(x) = q^(mu+1) C(1/q) / C(q).

Tests the closed form
    r(x) = eps * q^(mu + 1 - 2 gamma - D) * Sstar(q) / S(q)
where C = eps * q^gamma * S(q), S = S_{a/c} the reduced denominator of
[a/c]_q with a = M[0][0], c = M[1][0], D = deg S, and Sstar is the reciprocal
(reversal) polynomial of S.

Consequence tested: r(x) is plus-or-minus a monomial  <=>  S palindromic
<=>  a^2 = 1 (mod c) (KMRWY Theorem 3.6). The two "not monomial" rows of
cor:named should be exactly the rows failing a^2 = 1 mod c.

Imports qperiod.py from the T3 folder read-only. No files there are modified.
"""
import sys
import sympy as sp

T3_OPUS = (
    "<path>"
    "2026-07-21-next-steps/problems/T3-quadratic-conjecture/attempts/opus"
)
sys.path.insert(0, T3_OPUS)

import qperiod as qp  # noqa: E402

q = sp.symbols("q")

# x, automorph M = [[a, b], [c, d']], recorded r(x) from cor:named.
CASES = [
    ("(1+sqrt(5))/2", [[2, 1], [1, 1]], "q"),
    ("1+sqrt(2)", [[5, 2], [2, 1]], "q^2"),
    ("2+sqrt(2)", [[7, -4], [2, -1]], "q^4"),
    ("(3+sqrt(13))/2", [[10, 3], [3, 1]], "q^3"),
    ("3+sqrt(3)", [[5, -6], [1, -1]], "q^6"),
    ("(1+sqrt(2))/2", [[5, 1], [4, 1]], "q"),
    ("(1+sqrt(3))/2", [[3, 1], [2, 1]], "q"),
    ("(2+sqrt(7))/3", [[14, 3], [9, 2]], "not monomial"),
    ("(1+sqrt(13))/3", [[829, 720], [540, 469]], "not monomial"),
]


def poly_from_ldict(C):
    """Return (gamma, coeffs) with C = q^gamma * sum coeffs[i] q^i, coeffs[0]!=0."""
    gamma = min(C)
    top = max(C)
    D = top - gamma
    coeffs = [C.get(gamma + i, 0) for i in range(D + 1)]
    return gamma, coeffs, D


def is_palindrome(coeffs):
    return coeffs == coeffs[::-1]


def main():
    print(f"{'x':18} {'a/c':10} {'a^2 mod c':10} {'palin?':7} "
          f"{'mono?':6} {'k=mu+1-2g-D':12} {'r(x)':14} {'recorded':13} ok")
    all_ok = True
    for xrepr, M, recorded in CASES:
        a, c = M[0][0], M[1][0]
        Mq = qp.rho_q(M)
        A, B, C, D_ = Mq
        # mu from det X = q^mu
        detX = qp.p_add(qp.p_mul(A, D_), qp.p_mul(B, C), scale=-1)
        assert len(detX) == 1, f"det not a monomial: {detX}"
        mu = next(iter(detX))
        assert detX[mu] == 1, f"det not q^mu: {detX}"

        gamma, coeffs, D = poly_from_ldict(C)
        S_expr = sum(coeffs[i] * q**i for i in range(len(coeffs)))
        palin = is_palindrome(coeffs)

        # r(x) = q^(mu+1) C(1/q) / C(q), computed exactly.
        C_expr = qp.ldict_to_expr(C)
        C_inv = C_expr.subs(q, 1 / q)
        r = sp.simplify(q**(mu + 1) * C_inv / C_expr)
        r = sp.cancel(r)

        # closed-form prediction: eps * q^(mu+1-2gamma-D) * Sstar/S
        Sstar = sum(coeffs[D - i] * q**i for i in range(len(coeffs)))
        k = mu + 1 - 2 * gamma - D
        r_pred = sp.cancel(q**k * Sstar / S_expr)
        # r itself may differ from r_pred by the sign eps^2 = 1, so compare
        # up to overall sign as a safety net, but they should match exactly.
        match_pred = sp.simplify(r - r_pred) == 0

        # monomial test on r
        r_poly = sp.cancel(r)
        is_mono = r_poly.is_Pow or r_poly.is_Symbol or r_poly == 1 or (
            r_poly.is_Mul and all(t.is_Pow or t.is_Symbol or t.is_number
                                  for t in r_poly.args)
            and sp.Poly(sp.numer(r_poly), q).is_monomial
            and sp.Poly(sp.denom(r_poly), q).is_monomial
        )
        # robust monomial test: r is +-q^n
        num, den = sp.fraction(sp.together(r))
        try:
            mono = (sp.Poly(num, q).is_monomial and sp.Poly(den, q).is_monomial)
        except sp.PolynomialError:
            mono = num.is_number and den.is_number
        cong = pow(a, 2, c)
        ok = (mono == palin) and (palin == (cong == 1 % c if c != 0 else True)) \
            and match_pred
        pred_label = f"q^{k}" if palin else "(non-mono)"
        all_ok = all_ok and ok
        print(f"{xrepr:18} {str(a)+'/'+str(c):10} {cong:<10} "
              f"{str(palin):7} {str(mono):6} {pred_label:12} "
              f"{str(r):14} {recorded:13} {ok}")
    print()
    print("ALL CHECKS PASS" if all_ok else "SOME CHECK FAILED")
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
