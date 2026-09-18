"""Adversarial search over Hirzebruch-Jung words for a large first-tail degree
with a small beta_max, i.e. a counterexample to the census stopping rule.

Words are generated directly, so the residual regime (where the main theorem is
silent because neither x nor -x has a large second HJ term) is sampled densely,
which the a + b sqrt(D) grid does not do.
"""

from __future__ import annotations

import csv
import sys
from itertools import product
from multiprocessing import Pool

from words import from_word, hj, G_exact, first_tail, random_residual_words

TARGET = 160


def job(item):
    pre, per = item
    x = from_word(list(pre), list(per))
    if x is None:
        return None
    tx, tn = hj(x, 2), hj(-x, 2)
    bx = tx[0] + tx[1] - 2
    bn = tn[0] + tn[1] - 2
    g = G_exact(x, TARGET)
    ft = first_tail(g, TARGET, 6)
    return dict(pre=".".join(map(str, pre)), per=".".join(map(str, per)),
                c1=tx[0], c2=tx[1], d1=tn[0], d2=tn[1], bx=bx, bn=bn,
                bmax=max(bx, bn), ft=-1 if ft is None else ft)


def systematic(c1lo, c1hi, small, maxlen):
    rows = []
    for c1 in range(c1lo, c1hi + 1):
        for k in range(1, maxlen + 1):
            for per in product(range(2, small + 1), repeat=k):
                rows.append(((c1,), per))
                for m in range(1, 3):
                    for pre in product(range(2, small + 1), repeat=m):
                        rows.append(((c1,) + pre, per))
    return rows


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "sys"
    out_path = sys.argv[2] if len(sys.argv) > 2 else "words.csv"
    if mode == "sys":
        rows = systematic(-8, 8, 5, 2)
    else:
        rows = random_residual_words(int(sys.argv[3]), int(sys.argv[4]),
                                     small=int(sys.argv[5]) if len(sys.argv) > 5 else 6)
        rows = [(tuple(p), tuple(q)) for p, q in rows]
    rows = list(dict.fromkeys(rows))
    print("words", len(rows), flush=True)
    worst = []
    n = 0
    with Pool(4) as p, open(out_path, "w", newline="") as fh:
        w = None
        for r in p.imap_unordered(job, rows, chunksize=8):
            if r is None:
                continue
            if w is None:
                w = csv.DictWriter(fh, fieldnames=list(r))
                w.writeheader()
            w.writerow(r)
            n += 1
            if r["ft"] > max(r["bmax"], 7):
                worst.append(r)
            if n % 4000 == 0:
                print(n, "over bound", len(worst), flush=True)
    worst.sort(key=lambda r: -(r["ft"] - max(r["bmax"], 7)))
    print("realized", n, "over bound", len(worst))
    for r in worst[:40]:
        print("  OVER", r["ft"] - max(r["bmax"], 7), r)


if __name__ == "__main__":
    main()
