"""Two-stage scan: find x whose G has a LONG zero run in the tail, then
compare the true first tail degree d against B = max(beta(x), beta(-x)).

Stage 1 computes G only to degree 16 (cheap).  Points with a tail found there
are recorded immediately.  Points with no tail by 16 are recomputed to degree
TOP2 (expensive but rare).
"""
import sys
from fractions import Fraction as F
from gtools import first_tail, g_series, hj, predicted, qi

TOP2 = int(sys.argv[1]) if len(sys.argv) > 1 else 100
DEN = [1, 2, 3, 4, 5, 6, 7, 8]
NUM = range(-8, 9)

bad, worst, tot, long_pts = [], (0, None), 0, []
seen = set()
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
                    tot += 1
                    x = qi(a, b, D)
                    g, lo, ld = g_series(x, 16)
                    d, top = first_tail(g, lo, ld)
                    if d is None:
                        g, lo, ld = g_series(x, TOP2)
                        d, top = first_tail(g, lo, ld)
                        long_pts.append((D, a, b, d, top))
                    if d is None:
                        continue
                    B = predicted(x)
                    if d > max(B, 6):
                        bad.append((D, a, b, B, d))
                        if d - B > worst[0]:
                            worst = (d - B, (D, a, b, B, d, hj(x, 6), hj(-x, 6)))
print("scanned", tot)
print("dangerous exceedances d > max(B,6):", len(bad), f"({100*len(bad)/tot:.1f}%)")
print("worst gap d-B:", worst)
print("points with no tail below degree 16:", len(long_pts))
nexc = 0
for p in long_pts:
    D, a, b, d, top = p
    B = predicted(qi(a, b, D))
    if d is not None and d > max(B, 6):
        nexc += 1
print("LONG-RUN POINTS: total", len(long_pts), "exceedances", nexc,
      "finite-looking", sum(1 for p in long_pts if p[3] is None))
for p in long_pts[:80]:
    D, a, b, d, top = p
    x = qi(a, b, D)
    B = predicted(x)
    flag = "EXCEED" if (d is not None and d > max(B, 6)) else ("finite?" if d is None else "ok")
    print(f"   D={D} x={a}+{b}sqrt{D}  B={B} d={d} topcert={top}  {flag}")
