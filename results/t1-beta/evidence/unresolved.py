"""Diagnose the 282 long-run points that showed no tail up to degree 100.

Distinguishes three cases:
  (a) genuine known finite values (on-axis k*sqrt(D)),
  (b) LOCK-SHORT: the certified window never reached degree 100, so "no tail"
      is a statement about the search, not about G,
  (c) genuinely zero through a certified degree 100 while off-axis, which would
      be a candidate counterexample to the census headline claim.
"""
from fractions import Fraction as F
from gtools import first_tail, g_series, hj, predicted, qi

DEN = [1, 2, 3, 4, 5, 6, 7, 8]
NUM = range(-8, 9)
TOP2 = 100

seen, unres = set(), []
for D in (2, 3, 5):
    for qa in DEN:
        for pa in NUM:
            for qb in DEN:
                for pb in NUM:
                    if pb == 0:
                        continue
                    a, b = F(pa, qa), F(pb, qb)
                    if (D, a, b) in seen:
                        continue
                    seen.add((D, a, b))
                    x = qi(a, b, D)
                    g, lo, ld = g_series(x, 16)
                    d, top = first_tail(g, lo, ld)
                    if d is not None:
                        continue
                    g, lo, ld = g_series(x, TOP2)
                    d, top = first_tail(g, lo, ld)
                    if d is None:
                        unres.append((D, a, b, top, a == 0))

onaxis = [u for u in unres if u[4]]
short = [u for u in unres if not u[4] and u[3] < TOP2]
real = [u for u in unres if not u[4] and u[3] >= TOP2]
print(f"no tail through degree {TOP2}: {len(unres)} total")
print(f"  on-axis (a == 0, expected finite family): {len(onaxis)}")
print(f"  off-axis but LOCK-SHORT (topcert < {TOP2}): {len(short)}")
print(f"  off-axis and certified to {TOP2}: {len(real)}")
# THE DECISIVE SPLIT.  A zero run to degree 100 is entirely expected when
# B > 100: the bound itself predicts the first tail only at degree B, so the
# search simply has not gone deep enough and the point is UNRESOLVED.
# Only B <= TOP2 would be a genuine long-run counterexample, i.e. G certified
# zero on [6, 100] while the bound promised a tail at or below B <= 100.
big = [u for u in real if predicted(qi(u[1], u[2], u[0])) > TOP2]
small = [u for u in real if predicted(qi(u[1], u[2], u[0])) <= TOP2]
print(f"    of these, B > {TOP2} (expected, unresolved, guard masks): {len(big)}")
print(f"    of these, B <= {TOP2} (GENUINE long-run counterexample): {len(small)}")
for u in small[:40]:
    D, a, b, top, _ = u
    print(f"      COUNTEREXAMPLE D={D} x={a}+{b}sqrt({D}) B={predicted(qi(a,b,D))} topcert={top}")
if big:
    bs = sorted(predicted(qi(u[1], u[2], u[0])) for u in big)
    print(f"    B range among the expected ones: {bs[0]} to {bs[-1]}")
for u in real[:40]:
    D, a, b, top, _ = u
    print(f"    D={D} x={a}+{b}sqrt({D}) topcert={top} B={predicted(qi(a,b,D))} hj={hj(qi(a,b,D),4)}")
if short:
    print("  lock-short topcert range:", min(u[3] for u in short), "to", max(u[3] for u in short))
