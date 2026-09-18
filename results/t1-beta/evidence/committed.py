"""Exceedance rate of the beta bound measured directly on the COMMITTED census.

Reads sweep-D{2,3,5}-results.csv.gz (read only), restricts to |x| <= 12 where
the F1 window defect does not corrupt the recorded tail index, and compares the
recorded first_nonzero_tail_index against B = max(beta(x), beta(-x)) recomputed
from the HJ expansion.
"""
import csv
import gzip
import os
from fractions import Fraction as F
from gtools import predicted, qi

SRC = "<path>"

for D in (5,):
    path = os.path.join(SRC, f"sweep-D{D}-results.csv.gz")
    tot = exc = danger = sharp = 0
    worst = (0, None)
    with gzip.open(path, "rt") as fh:
        for row in csv.DictReader(fh):
            if row["verdict"] != "infinite" or not row["first_nonzero_tail_index"]:
                continue
            if abs(float(row["x_decimal"])) > 12:
                continue          # F1-corrupted tail indices, excluded
            tot += 1
            d = int(row["first_nonzero_tail_index"])
            a, b = F(int(row["pa"]), int(row["qa"])), F(int(row["pb"]), int(row["qb"]))
            B = predicted(qi(a, b, D))
            if d == B:
                sharp += 1
            if d > B:
                exc += 1
                if d > 6:
                    danger += 1
                    if d - B > worst[0]:
                        worst = (d - B, (D, a, b, B, d))
    print(f"D={D}: rows |x|<=12 with a tail index {tot}; "
          f"d > B: {exc} ({100*exc/max(tot,1):.1f}%); "
          f"d > max(B,6): {danger} ({100*danger/max(tot,1):.1f}%); "
          f"d == B: {sharp}; worst gap {worst}")
