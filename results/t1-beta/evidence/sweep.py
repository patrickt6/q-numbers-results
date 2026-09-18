"""Exact sweep: first nonzero tail degree of G(x) versus beta_max(x).

Every coefficient is exact (Fraction) and certified by the determinant identity
R_n S_{n-1} - S_n R_{n-1} = -q^{C_{n-1}}; nothing is locked empirically and no
window truncation is used, so a reported first-tail degree is a theorem about
G(x), not an observation about a truncated model of it.
"""

from __future__ import annotations

import csv
import sys
from fractions import Fraction as F
from multiprocessing import Pool

from exact import (
    C_partial,
    G_exact,
    QuadraticIrrational,
    first_tail,
    hj,
)

TAIL_START = 6


def job(item):
    pa, qa, pb, qb, D, target = item
    a, b = F(pa, qa), F(pb, qb)
    x = QuadraticIrrational.from_ab(a, b, D)
    tx = hj(x, 6)
    tn = hj(-x, 6)
    Cx = C_partial(tx)
    Cn = C_partial(tn)
    g = G_exact(x, target)
    ft = first_tail(g, target, TAIL_START)
    return dict(
        pa=pa, qa=qa, pb=pb, qb=qb, D=D,
        c1=tx[0], c2=tx[1], c3=tx[2],
        d1=tn[0], d2=tn[1], d3=tn[2],
        b2x=Cx[2], b2n=Cn[2], b3x=Cx[3], b3n=Cn[3],
        bmax=max(Cx[2], Cn[2]), bmin=min(Cx[2], Cn[2]),
        ft=-1 if ft is None else ft,
        target=target,
    )


def grid(amax, bmax_, dens, Ds):
    seen = set()
    out = []
    for D in Ds:
        for qa in dens:
            for qb in dens:
                for pa in range(-amax * qa, amax * qa + 1):
                    for pb in range(1, bmax_ * qb + 1):
                        a, b = F(pa, qa), F(pb, qb)
                        key = (a, b, D)
                        if key in seen:
                            continue
                        seen.add(key)
                        out.append((a.numerator, a.denominator,
                                    b.numerator, b.denominator, D))
    return out


def main():
    target = int(sys.argv[1]) if len(sys.argv) > 1 else 130
    amax = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    bmx = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    dmax = int(sys.argv[4]) if len(sys.argv) > 4 else 5
    out_path = sys.argv[5] if len(sys.argv) > 5 else "sweep.csv"
    items = [(*g, target) for g in grid(amax, bmx, list(range(1, dmax + 1)), (2, 3, 5))]
    print("grid size", len(items), flush=True)
    with Pool(10) as p, open(out_path, "w", newline="") as fh:
        w = None
        n = 0
        raw = soft = 0
        for r in p.imap_unordered(job, items, chunksize=8):
            if w is None:
                w = csv.DictWriter(fh, fieldnames=list(r))
                w.writeheader()
            w.writerow(r)
            n += 1
            if r["ft"] >= 0:
                if r["ft"] > r["bmax"]:
                    raw += 1
                if r["ft"] > max(r["bmax"], 65):
                    soft += 1
            if n % 2000 == 0:
                print(n, "raw", raw, "soft", soft, flush=True)
    print("done", n, "raw", raw, "soft", soft, flush=True)


if __name__ == "__main__":
    main()
