"""Local, self-contained tools for the T1 beta-bound investigation.

Nothing here is executed from the evidence-ab-sqrt2 folder; the beta logic is
re-implemented from its documented definition and cross-checked against the
qreals library primitives.  Exact arithmetic only.
"""
from fractions import Fraction

from qreals.quadratic import QuadraticIrrational, hj_terms
from qreals.negation import (
    DEFAULT_WINDOW_LO,
    classify,
    locked_series,
    valuation_floor,
    window_bounds,
)


def hj(x, n):
    terms, ps, pl = hj_terms(x, n)
    return terms


def beta(x, k=2):
    """(c_1 - 1) + ... + (c_k - 1) over the first k HJ terms of x."""
    t = hj(x, k)
    return sum(c - 1 for c in t[:k])


def C_seq(x, n):
    """Partial sums C_j = sum_{i<=j} (c_i - 1), j = 1..n."""
    t = hj(x, n)
    out, s = [], 0
    for c in t:
        s += c - 1
        out.append(s)
    return out


def predicted(x):
    return max(beta(x), beta(-x))


def g_series(x, top_degree, min_zero_run=60, tail_start=6):
    """Certified locked coefficients of G(x) up to `top_degree`.

    Returns (g, lo, locked_depth) where g maps degree -> Fraction over
    [lo, lo + locked_depth).  Windows are derived from the valuation exactly as
    `escalate_official.g_verdict` does (F1 fix), so every reported coefficient
    is certified.
    """
    vf = min(valuation_floor(x), valuation_floor(-x))
    lo, hi = window_bounds(vf, top_degree)
    eff_depth = hi - lo
    eff_target = top_degree - lo + 1
    pos, pd = locked_series(x, eff_depth, max_hj_terms=None,
                            lock_target=eff_target, window_lo=lo, window_hi=hi)
    neg, nd = locked_series(-x, eff_depth, max_hj_terms=None,
                            lock_target=eff_target, window_lo=lo, window_hi=hi)
    ld = min(pd, nd)
    g = {d: pos.get(d, 0) + neg.get(d, 0) for d in range(lo, lo + ld)}
    return g, lo, ld


def first_tail(g, lo, ld, tail_start=6):
    """First degree >= tail_start with a nonzero certified coefficient.

    Returns (degree, top_certified_degree).  degree is None if the whole
    certified range at or above tail_start is zero.
    """
    top = lo + ld - 1
    for d in range(max(tail_start, lo), top + 1):
        if g.get(d, 0) != 0:
            return d, top
    return None, top


def qi(a, b, D):
    return QuadraticIrrational.from_ab(Fraction(a), Fraction(b), D)
