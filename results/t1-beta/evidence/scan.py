"""Systematic scan for exceedances of the beta bound.

For every x = a + b*sqrt(D) on a rational grid, compute
  B  = max(beta(x), beta(-x)),   beta(y) = (c_1 - 1) + (c_2 - 1) of HJ(y)
  d  = first degree >= 6 with a nonzero certified coefficient of G(x)
and record whether d > B (a literal exceedance) and whether d > max(B, 6)
(a dangerous exceedance, the kind that can produce a false finite_looking).
"""
import sys
from fractions import Fraction as F

from gtools import beta, first_tail, g_series, hj, predicted, qi

TOP = int(sys.argv[1]) if len(sys.argv) > 1 else 60
DENOMS = [1, 2, 3, 4, 5]
NUMRANGE = range(-6, 7)


def grid(D):
    seen = set()
    for qa in DENOMS:
        for pa in NUMRANGE:
            for qb in DENOMS:
                for pb in NUMRANGE:
                    if pb == 0:
                        continue
                    a, b = F(pa, qa), F(pb, qb)
                    if (a, b) in seen:
                        continue
                    seen.add((a, b))
                    yield a, b


def main():
    lit, dang, tot, fin = 0, 0, 0, 0
    lit_rows, dang_rows = [], []
    for D in (2, 3, 5):
        for a, b in grid(D):
            x = qi(a, b, D)
            B = predicted(x)
            g, lo, ld = g_series(x, TOP)
            d, top = first_tail(g, lo, ld)
            tot += 1
            if d is None:
                fin += 1
                continue
            if d > B:
                lit += 1
                lit_rows.append((D, a, b, B, d))
                if d > 6:
                    dang += 1
                    dang_rows.append((D, a, b, B, d, hj(x, 3), hj(-x, 3)))
    print(f"scanned {tot}, no-tail-in-window {fin}")
    print(f"literal exceedances d > B: {lit}")
    print(f"dangerous exceedances d > max(B,6): {dang}")
    for r in dang_rows[:40]:
        print("  DANGEROUS", r)
    for r in lit_rows[:20]:
        print("  literal  ", r)


if __name__ == "__main__":
    main()
