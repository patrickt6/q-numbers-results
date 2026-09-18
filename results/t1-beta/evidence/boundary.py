"""Targeted probe of the residual regime near the boundary of hypothesis H.

The largest first-tail degrees seen in the residual regime come from long sides
whose second term sits just below the threshold of H, so this enumerates exactly
those: e_2 in [max(3, 2|e_1| - 3), 2|e_1| + 1] for |e_1| up to 14, with varied
tails, and reports the largest first-tail degree found.
"""

from __future__ import annotations

import sys
from itertools import product
from multiprocessing import Pool

from words import from_word, hj, G_exact, first_tail

TARGET = 220


def H(e1, e2):
    return e2 >= 2 * e1 + 2 if e1 >= 1 else e2 >= -e1 + 2 + max(-e1, 1)


def job(item):
    pre, per = item
    x = from_word(list(pre), list(per))
    if x is None:
        return None
    c1, c2 = hj(x, 2)
    d1, d2 = hj(-x, 2)
    if H(c1, c2) or H(d1, d2):
        return None
    g = G_exact(x, TARGET)
    ft = first_tail(g, TARGET, 6)
    return dict(pre=pre, per=per, c1=c1, c2=c2, d1=d1, d2=d2,
                bmax=max(c1 + c2 - 2, d1 + d2 - 2), ft=-1 if ft is None else ft)


def main():
    emax = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    rows = []
    for e1 in list(range(-emax, 0)) + list(range(1, emax + 1)):
        thr = 2 * abs(e1) + 1
        for e2 in range(max(3, thr - 4), thr + 1):
            for k in (1, 2, 3):
                for per in product((2, 3, 4, 7), repeat=k):
                    rows.append(((e1, e2), per))
                    for t3 in (2, 3, 5):
                        rows.append(((e1, e2, t3), per))
    rows = list(dict.fromkeys(rows))
    print("candidates", len(rows), flush=True)
    best = []
    n = 0
    with Pool(6) as p:
        for r in p.imap_unordered(job, rows, chunksize=16):
            if r is None:
                continue
            n += 1
            best.append(r)
            if n % 3000 == 0:
                print(n, "max ft so far",
                      max(z["ft"] for z in best), flush=True)
    print("residual words realized", n)
    if not best:
        return
    print("max ft", max(z["ft"] for z in best))
    best.sort(key=lambda z: -z["ft"])
    for z in best[:20]:
        print("  ", z)


if __name__ == "__main__":
    main()
