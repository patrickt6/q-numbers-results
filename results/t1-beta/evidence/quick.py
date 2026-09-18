"""Fast search for dangerous exceedances: first tail degree d > max(B, 6)."""
from fractions import Fraction as F
from gtools import beta, first_tail, g_series, hj, predicted, qi

TOP = 24
rows = []
tot = 0
for D in (2, 3, 5):
    for qa in (1, 2, 3):
        for pa in range(-4, 5):
            for qb in (1, 2, 3):
                for pb in range(-4, 5):
                    if pb == 0:
                        continue
                    a, b = F(pa, qa), F(pb, qb)
                    x = qi(a, b, D)
                    tot += 1
                    B = predicted(x)
                    g, lo, ld = g_series(x, TOP)
                    d, top = first_tail(g, lo, ld)
                    if d is not None and d > max(B, 6):
                        rows.append((D, a, b, B, d, hj(x, 3), hj(-x, 3)))
print("scanned", tot, "dangerous:", len(rows))
for r in rows[:60]:
    print("  ", r)
