#!/usr/bin/env python3
"""Task 5: analogous families d=(n^2+1)/y^2 for y in {13,17,25,29}, d<=6000,
looked up against the census is_finite column."""
import csv
import math

CENSUS = "<path>"

census = {}
for r in csv.DictReader(open(CENSUS)):
    census[int(r["d"])] = r

D_MAX = 6000

for y in (13, 17, 25, 29):
    y2 = y * y
    n_max = math.isqrt(D_MAX * y2) + 2
    found = []
    for n in range(1, n_max + 1):
        val = n * n + 1
        if val % y2 == 0:
            d = val // y2
            if d <= D_MAX:
                a0 = math.isqrt(d)
                is_sq = a0 * a0 == d
                found.append((n, d, is_sq))
    print(f"\n=== y={y} (y^2={y2}) ===  {len(found)} members with d<=6000")
    for n, d, is_sq in found:
        if is_sq:
            print(f"  n={n:5d}  d={d:6d}  (PERFECT SQUARE, excluded from census)")
            continue
        row = census.get(d)
        if row is None:
            print(f"  n={n:5d}  d={d:6d}  NOT FOUND IN CENSUS")
        else:
            print(f"  n={n:5d}  d={d:6d}  is_finite={row['is_finite']}  "
                  f"S_is_cyc_sqfree={row['S_is_cyc_squarefree_product']}  "
                  f"cf_period_len={row['cf_period_length']} parity={row['cf_period_parity']}")
