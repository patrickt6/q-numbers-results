"""Exact algebraic finiteness certificate for G(x) = [x]_q + [-x]_q,
x a quadratic irrational.  No zero runs, no beta, no locking heuristic.

Mathematical basis
------------------
The Hirzebruch-Jung expansion of a quadratic irrational is eventually periodic,
say [c_1,...,c_k, (c_{k+1},...,c_{k+p})^inf].  With
M(c) = [[ [c]_q, -q^(c-1) ], [1, 0]] over Z[q,q^-1], and the Moebius action
[[A,B],[C,D]] . z = (Az+B)/(Cz+D), the n-th HJ convergent of [x]_q is
P_n . infinity with P_n = M(c_1)...M(c_n).  Hence

    [x]_q = P_pre . w,     w = P_per . w,

so w is a root of  C w^2 + (D - A) w - B = 0  with P_per = [[A,B],[C,D]], and
u = [x]_q is a root of the quadratic obtained by substituting the inverse
Moebius map w = (d u - b)/(a - c u), P_pre = [[a,b],[c,d]]:

    Q(z) = C (dz - b)^2 + (D - A)(dz - b)(a - cz) - B (a - cz)^2.

Q has coefficients in Z[q, q^-1] and degree 2 in z.  So [x]_q is algebraic of
degree at most 2 over Q(q), exactly.  Same for [-x]_q, giving Q_minus.

Certificate.  G = u + v equals a Laurent polynomial h if and only if v = h - u,
i.e. z = u is a common root of Q_plus(z) and Q_minus(h - z).  When Q_plus is
irreducible over Q(q), a nonconstant gcd of the two forces that common root to
be u itself, so

    deg_z gcd( Q_plus(z), Q_minus(h - z) ) >= 1   <=>   G = h.

This is an exact yes/no test on polynomials over Q(q).  Nothing is estimated.
"""
from fractions import Fraction

import sympy as sp

from qreals.quadratic import QuadraticIrrational, hj_terms

q = sp.Symbol("q")
z = sp.Symbol("z")


def qbracket(c):
    """[c]_q = (1 - q^c)/(1 - q), valid as a rational function for every c in Z."""
    return sp.cancel((1 - q ** c) / (1 - q))


def Mstep(c):
    return sp.Matrix([[qbracket(c), -q ** (c - 1)], [sp.Integer(1), sp.Integer(0)]])


def hj_split(x, budget=4000):
    terms, ps, pl = hj_terms(x, budget)
    if ps is None:
        raise RuntimeError("no HJ period detected within budget")
    return terms[:ps], terms[ps:ps + pl]


def minimal_quadratic(x):
    """Q(z) in Z[q,q^-1][z], degree 2, with [x]_q as a root.  Returns a sympy
    expression, cleared of denominators in q."""
    pre, per = hj_split(x)
    Pper = sp.eye(2)
    for c in per:
        Pper = sp.cancel(Pper * Mstep(c))
    A, B, C, Dd = Pper[0, 0], Pper[0, 1], Pper[1, 0], Pper[1, 1]
    Ppre = sp.eye(2)
    for c in pre:
        Ppre = sp.cancel(Ppre * Mstep(c))
    a, b, c_, d = Ppre[0, 0], Ppre[0, 1], Ppre[1, 0], Ppre[1, 1]
    num = d * z - b
    den = a - c_ * z
    Q = sp.expand(sp.cancel(C * num ** 2 + (Dd - A) * num * den - B * den ** 2))
    Q = sp.cancel(sp.together(Q))
    Q = sp.numer(Q)
    return sp.Poly(sp.expand(Q), z)


def series_of_root(Q, n_terms, lo):
    """All Laurent-series roots of the degree-2 Q, as dicts, is not needed:
    this helper only checks a candidate against Q by exact substitution."""
    raise NotImplementedError


def is_root(Q, expr):
    return sp.simplify(sp.cancel(Q.as_expr().subs(z, expr))) == 0


def certify_finite(x, h):
    """Exact test: is G(x) = h, for a Laurent polynomial h (sympy expr in q)?

    Returns (verdict, detail).  verdict is True (G = h, proved), False
    (G != h, proved), or None (inconclusive: Q_plus reducible, needs the
    conjugate-root check).
    """
    Qp = minimal_quadratic(x)
    Qm = minimal_quadratic(-x)
    shifted = sp.Poly(sp.expand(Qm.as_expr().subs(z, sp.expand(h - z))), z)
    dom = sp.QQ.frac_field(q)
    Pp = sp.Poly(Qp.as_expr(), z, domain=dom)
    Ps = sp.Poly(shifted.as_expr(), z, domain=dom)
    g = Pp.gcd(Ps)
    irreducible = len(sp.factor_list(sp.Poly(Qp.as_expr(), z, domain=dom))[1]) == 1 and \
        sp.Poly(Qp.as_expr(), z, domain=dom).degree() == 2 and \
        sp.factor_list(sp.Poly(Qp.as_expr(), z, domain=dom))[1][0][1] == 1
    if g.degree() >= 1:
        if g.degree() == 2 or irreducible:
            return True, f"gcd degree {g.degree()}, Q_plus irreducible={irreducible}"
        return None, f"gcd degree {g.degree()} but Q_plus reducible; conjugate check needed"
    return False, "gcd is constant: G is not equal to h"


def laurent_expr(coeffs):
    """Turn a {degree: Fraction} dict into a sympy Laurent polynomial in q."""
    e = sp.Integer(0)
    for d, c in sorted(coeffs.items()):
        e += sp.Rational(c.numerator, c.denominator) * q ** d
    return sp.expand(e)
