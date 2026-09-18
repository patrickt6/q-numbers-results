"""Independent empirical test of the beta bound (T1), D in {2,3,5}.

Self-contained copy of the budget/verdict logic. Does not import or execute
anything from evidence-ab-sqrt2/. Exact arithmetic only.

For each sampled x = a + b*sqrt(D) it records:
  bx  = beta(x)  = (c1-1)+(c2-1) over HJ terms of x
  bnx = beta(-x)
  tail = true first nonzero coefficient degree >= 6 of G(x) = [x]_q + [-x]_q
and reports exceedances against max(bx,bnx) and against min(bx,bnx).
"""
import sys
from fractions import Fraction

from qreals.quadratic import QuadraticIrrational
from qreals.negation import (
    DEFAULT_WINDOW_LO,
    classify,
    locked_series,
    valuation_floor,
    window_bounds,
)

MIN_ZERO_RUN = 60
MARGIN = 40


def hj_budget(a, b, D, k=2):
    total = 0
    for _ in range(k):
        x = QuadraticIrrational.from_ab(a, b, D)
        c = x.ceil()
        total += c - 1
        ca, cb = Fraction(c) - a, -b
        if cb == 0 and ca == 0:
            break
        y = QuadraticIrrational.from_ab(ca, cb, D).reciprocal()
        a, b = y.as_fraction_pair()
    return total


def g_verdict(a, b, D, depth):
    x = QuadraticIrrational.from_ab(a, b, D)
    vf = min(valuation_floor(x), valuation_floor(-x))
    top_degree = DEFAULT_WINDOW_LO + depth - 1
    lo, hi = window_bounds(vf, top_degree)
    eff_depth = hi - lo
    eff_target = top_degree - lo + 1
    pos, pd = locked_series(x, eff_depth, max_hj_terms=None,
                            lock_target=eff_target, window_lo=lo, window_hi=hi)
    neg, nd = locked_series(-x, eff_depth, max_hj_terms=None,
                            lock_target=eff_target, window_lo=lo, window_hi=hi)
    ld = min(pd, nd)
    g = {d: pos.get(d, 0) + neg.get(d, 0) for d in range(lo, lo + ld)}
    v = classify(g, ld, min_zero_run=MIN_ZERO_RUN, window_lo=lo)
    return v.kind, v.first_nonzero_tail_index, lo, ld


def run(D, pairs):
    rows = []
    for (a, b) in pairs:
        x = QuadraticIrrational.from_ab(a, b, D)
        bx = hj_budget(a, b, D)
        bnx = hj_budget(-a, -b, D)
        pred_max, pred_min = max(bx, bnx), min(bx, bnx)
        base = max(0, x.ceil())
        depth = max(120, pred_max + MARGIN) + base + 12
        kind, tail, lo, ld = g_verdict(a, b, D, depth)
        rows.append((D, a, b, bx, bnx, pred_max, pred_min, kind, tail, lo + ld - 1))
    return rows


def main():
    import itertools
    out = []
    for D in (2, 3, 5):
        pairs = []
        # a, b over a modest exact grid of eighths, |x| kept moderate
        for an in range(-24, 25):
            for bn in range(-16, 17):
                if bn == 0:
                    continue
                a, b = Fraction(an, 8), Fraction(bn, 8)
                pairs.append((a, b))
        pairs = pairs[:: max(1, len(pairs) // 260)]
        out.extend(run(D, pairs))
    hdr = "D,a,b,beta_x,beta_negx,pred_max,pred_min,kind,tail,top_locked"
    print(hdr)
    for r in out:
        print(",".join(str(v) for v in r))


if __name__ == "__main__":
    main()
