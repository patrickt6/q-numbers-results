"""Fallback deliverable (b): extend the beta check to the escalation-style
population (large beta, near-integer points) for D = 3 and D = 5.

The committed escalation covers D=2 (1525) and D=3 (1371) and no D=5 at all.
This selects grid points whose B = max(beta(x), beta(-x)) lies in [20, 160],
computes the certified G to degree B + 25, and compares the true first tail
degree with B.
"""
import sys
from fractions import Fraction as F
from gtools import beta, first_tail, g_series, predicted, qi

DS = [int(a) for a in sys.argv[1:]] or [5]
LOW, HIGH = 20, 80
DEN = range(1, 8)
NUM = range(-7, 8)

for D in DS:
    seen, checked, exceed, equal, nolock = set(), 0, [], 0, 0
    for qa in DEN:
        for pa in NUM:
            for qb in DEN:
                for pb in NUM:
                    if pb == 0:
                        continue
                    a, b = F(pa, qa), F(pb, qb)
                    if (a, b) in seen:
                        continue
                    seen.add((a, b))
                    x = qi(a, b, D)
                    B = predicted(x)
                    if not (LOW <= B <= HIGH):
                        continue
                    g, lo, ld = g_series(x, B + 25)
                    d, top = first_tail(g, lo, ld)
                    if top < B + 5:
                        nolock += 1
                        continue
                    checked += 1
                    if d is None or d > B:
                        exceed.append((D, a, b, B, d, top))
                    elif d == B:
                        equal += 1
    print(f"D={D}: checked {checked} points with B in [{LOW},{HIGH}], "
          f"exceedances {len(exceed)}, sharp (d==B) {equal}, lock-short {nolock}")
    for r in exceed[:20]:
        print("   EXCEED", r)
