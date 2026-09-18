"""Test the consequence of the reduction lemma, and audit beta as an upper bound.

Consequence under test:
    coeff of G(x) at degree beta(x)  ==  coeff of G(r) at degree beta(x)  -  1,
    where r = [[c_1, c_2]] is the second HJ convergent of x.

Hence the beta bound fails at degree beta(x) exactly when g_beta(r) == 1.

G(x) here is built from deep HJ convergents of x and of -x independently, so it
does not go through qreals.negation.locked_series. Exact arithmetic only.
"""
from fractions import Fraction

from qreals.quadratic import QuadraticIrrational, hj_terms
from reduction_check import convergent, padd, pneg

NT = 26


def hj_rational(r, cap=400):
    """Hirzebruch-Jung (ceiling) expansion of a rational. Terminates."""
    terms = []
    x = Fraction(r)
    for _ in range(cap):
        c = -((-x.numerator) // x.denominator)  # ceil
        terms.append(c)
        if x == c:
            return terms
        x = 1 / (c - x)
    raise RuntimeError("HJ did not terminate")


def series_of(x_ab, D, cap, nterms=NT):
    a, b = x_ab
    x = QuadraticIrrational.from_ab(a, b, D)
    terms, _, _ = hj_terms(x, nterms)
    return convergent(terms, cap), terms


def g_series_quadratic(a, b, D, cap):
    pos, tp = series_of((a, b), D, cap)
    neg, tn = series_of((-a, -b), D, cap)
    return padd(pos, neg), tp, tn


def g_series_rational(r, cap):
    p = convergent(hj_rational(r), cap)
    n = convergent(hj_rational(-r), cap)
    return padd(p, n)


def second_convergent(terms):
    c1, c2 = terms[0], terms[1]
    return Fraction(c1) - Fraction(1, c2)


def main():
    checked = 0
    mismatch = []
    exceed = []
    for D in (2, 3, 5):
        for an in range(-20, 21):
            for bn in range(-12, 13):
                if bn == 0:
                    continue
                a, b = Fraction(an, 4), Fraction(bn, 4)
                x = QuadraticIrrational.from_ab(a, b, D)
                terms, _, _ = hj_terms(x, NT)
                tneg, _, _ = hj_terms(QuadraticIrrational.from_ab(-a, -b, D), NT)
                if len(terms) < 4 or len(tneg) < 4:
                    continue
                beta = (terms[0] - 1) + (terms[1] - 1)
                bneg = (tneg[0] - 1) + (tneg[1] - 1)
                pred = max(beta, bneg)
                if beta < 0 or beta > 60:
                    continue
                cap = max(beta, bneg, 14) + 8
                G, _, _ = g_series_quadratic(a, b, D, cap)
                r = second_convergent(terms)
                Gr = g_series_rational(r, cap)
                lhs = G.get(beta, 0)
                rhs = Gr.get(beta, 0) - 1
                checked += 1
                if lhs != rhs:
                    mismatch.append((D, a, b, beta, lhs, rhs))
                # independent audit of the census bound
                if pred >= 6:
                    tail = next((d for d in range(6, cap + 1) if G.get(d, 0) != 0), None)
                    if tail is not None and tail > pred:
                        exceed.append((D, a, b, beta, bneg, pred, tail,
                                       Gr.get(beta, 0)))
    print(f"consequence checked on {checked} points, mismatches: {len(mismatch)}")
    for m in mismatch[:10]:
        print("   MISMATCH", m)
    print()
    print(f"beta-bound exceedances (pred>=6): {len(exceed)}")
    print("   D, a, b, beta(x), beta(-x), pred, true tail, g_beta(r)")
    for e in exceed[:25]:
        print("   ", e)


if __name__ == "__main__":
    main()
