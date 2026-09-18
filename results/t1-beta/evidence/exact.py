"""Exact, untruncated Laurent machinery for the negation sum G(x) = [x]_q + [-x]_q.

Nothing here truncates a matrix entry. P_n = M(c_1)...M(c_n) is carried as an
exact Laurent polynomial matrix over Q (in fact over Z), and the convergent
R_n / S_n is expanded by exact long division. Since S_n has constant term 1,
the division is exact term by term. Certification of the limit uses the
determinant identity

    R_n S_{n-1} - S_n R_{n-1} = -q^{C_{n-1}},   C_k = sum_{i<=k} (c_i - 1),

so [x]_q agrees with R_n / S_n in every degree strictly below C_n.

No floats decide any coefficient.
"""

from __future__ import annotations

import sys
from fractions import Fraction

sys.path.insert(0, "<path>")

from qreals.quadratic import QuadraticIrrational, hj_terms  # noqa: E402

Lau = dict  # {int degree: Fraction}


def lmul(a, b):
    out = {}
    for ka, va in a.items():
        if not va:
            continue
        for kb, vb in b.items():
            if not vb:
                continue
            k = ka + kb
            out[k] = out.get(k, 0) + va * vb
    return {k: v for k, v in out.items() if v}


def ladd(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + v
    return {k: v for k, v in out.items() if v}


def lsub(a, b):
    return ladd(a, {k: -v for k, v in b.items()})


def q_bracket(c: int):
    d = {}
    if c > 0:
        for i in range(c):
            d[i] = Fraction(1)
    elif c < 0:
        for i in range(c, 0):
            d[i] = Fraction(-1)
    return d


def M(c: int):
    """M(c) = [[ [c]_q, -q^(c-1) ], [1, 0]] as (m00, m01, m10, m11)."""
    return (q_bracket(c), {c - 1: Fraction(-1)}, {0: Fraction(1)}, {})


IDENT = ({0: Fraction(1)}, {}, {}, {0: Fraction(1)})


def mat_mul(A, B):
    a00, a01, a10, a11 = A
    b00, b01, b10, b11 = B
    return (
        ladd(lmul(a00, b00), lmul(a01, b10)),
        ladd(lmul(a00, b01), lmul(a01, b11)),
        ladd(lmul(a10, b00), lmul(a11, b10)),
        ladd(lmul(a10, b01), lmul(a11, b11)),
    )


def divide(num, den, max_deg):
    """num/den as an exact Laurent series through degree max_deg."""
    if not num:
        return {}
    vn = min(num)
    vd = min(den)
    numc = {k - vn: v for k, v in num.items()}
    denc = {k - vd: v for k, v in den.items()}
    d0 = denc[0]
    order = max_deg - (vn - vd)
    if order < 0:
        return {}
    c = {}
    for n in range(order + 1):
        s = numc.get(n, Fraction(0))
        for i in range(1, n + 1):
            di = denc.get(i)
            if di:
                s -= di * c[n - i]
        c[n] = s / d0
    return {(vn - vd + n): v for n, v in c.items() if v}


def hj(x: QuadraticIrrational, n: int):
    terms, _, _ = hj_terms(x, n)
    return terms


def C_partial(terms):
    """Cumulative C_k = sum_{i<=k} (c_i - 1), returned as a list indexed from 1."""
    out = [0]
    s = 0
    for c in terms:
        s += c - 1
        out.append(s)
    return out


def q_series(x: QuadraticIrrational, target_deg: int, max_terms: int = 4000):
    """Exact Laurent coefficients of [x]_q in degrees <= target_deg.

    Returns (series, n_used, C_n) where every coefficient in degree < C_n is
    certified exact by the determinant identity, and C_n > target_deg.
    """
    terms = hj(x, max_terms)
    Cs = C_partial(terms)
    n = None
    for k in range(1, len(Cs)):
        if Cs[k] > target_deg:
            n = k
            break
    if n is None:
        raise RuntimeError("term budget exhausted")
    P = IDENT
    for c in terms[:n]:
        P = mat_mul(P, M(c))
    ser = divide(P[0], P[2], target_deg)
    return ser, n, Cs[n]


def convergent_series(x: QuadraticIrrational, n: int, target_deg: int):
    """Exact Laurent series of the n-th HJ convergent R_n/S_n through target_deg."""
    terms = hj(x, n)
    P = IDENT
    for c in terms[:n]:
        P = mat_mul(P, M(c))
    return divide(P[0], P[2], target_deg)


def convergent_ratfun(x: QuadraticIrrational, n: int):
    """(R_n, S_n) as exact Laurent polynomials."""
    terms = hj(x, n)
    P = IDENT
    for c in terms[:n]:
        P = mat_mul(P, M(c))
    return P[0], P[2]


def G_exact(x: QuadraticIrrational, target_deg: int):
    """Exact Laurent coefficients of G(x) = [x]_q + [-x]_q in degrees <= target_deg."""
    a, _, _ = q_series(x, target_deg)
    b, _, _ = q_series(-x, target_deg)
    return {k: v for k, v in ladd(a, b).items() if v}


def beta(x: QuadraticIrrational) -> int:
    t = hj(x, 2)
    return (t[0] - 1) + (t[1] - 1)


def beta_max(x: QuadraticIrrational) -> int:
    return max(beta(x), beta(-x))


def first_tail(g, target_deg, tail_start=6):
    for d in range(tail_start, target_deg + 1):
        if g.get(d, 0):
            return d
    return None
