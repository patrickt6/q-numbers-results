"""Check the main theorem's prediction, and hunt the residual regime.

Theorem (proved from the reversal decomposition).  Let y be irrational with HJ
expansion [[e_1, e_2, ...]] and suppose e_2 >= 2|e_1| + 2.  Write
gamma_2 = e_1 + e_2 - 2 = beta(y) and delta_2 = e_2 - e_1 - 1.  Then the
nonnegative-degree coefficients of G(y) = [y]_q + [-y]_q are

  e_1 >= 1 :  +1 on [0, e_1-2],  0 at e_1-1,  +1 at e_1,
              0 on [e_1+1, delta_2-1],  +1 at delta_2
  e_1 <= 0 :  +1 on [0, |e_1|-1],  0 on [|e_1|, gamma_2-1],  -1 at gamma_2

Because G(x) = G(-x), the theorem may be applied to whichever of x, -x
satisfies the hypothesis.
"""

from __future__ import annotations

import csv
import sys
from fractions import Fraction as F
from multiprocessing import Pool

from exact import G_exact, QuadraticIrrational, first_tail, hj


def hypothesis(e1, e2):
    """The theorem's hypothesis: the first genuine event clears the explicit head."""
    if e1 >= 1:
        return e2 >= 2 * e1 + 2
    N = -e1
    return e2 >= N + 2 + max(N, 1)


def predicted_profile(e1, e2, upto):
    """Predicted coefficients on [0, upto], or None where the theorem is silent."""
    if not hypothesis(e1, e2):
        return None
    prof = {}
    if e1 >= 1:
        d2 = e2 - e1 - 1
        for d in range(0, upto + 1):
            if d <= e1 - 2:
                prof[d] = 1
            elif d == e1 - 1:
                prof[d] = 0
            elif d == e1:
                prof[d] = 1
            elif d < d2:
                prof[d] = 0
            elif d == d2:
                prof[d] = 1
            else:
                break
    else:
        N = -e1
        top = max(N, 1) - 1
        g2 = e1 + e2 - 2
        for d in range(0, upto + 1):
            if d <= top:
                prof[d] = 1
            elif d < g2:
                prof[d] = 0
            elif d == g2:
                prof[d] = -1
            else:
                break
    return prof


def theorem_ft(e1, e2):
    """First tail degree predicted by the theorem, or None if it is silent."""
    if not hypothesis(e1, e2):
        return None
    if e1 >= 1:
        d2 = e2 - e1 - 1
        if e1 >= 8:
            return 6
        if e1 == 7:
            return 7
        if e1 == 6:
            return 6
        return d2 if d2 >= 6 else None
    N = -e1
    top = max(N, 1) - 1
    g2 = e1 + e2 - 2
    if top >= 6:
        return 6
    return g2 if g2 >= 6 else None


def job(item):
    pa, qa, pb, qb, D, target = item
    x = QuadraticIrrational.from_ab(F(pa, qa), F(pb, qb), D)
    tx, tn = hj(x, 2), hj(-x, 2)
    g = G_exact(x, target)
    ft = first_tail(g, target, 6)
    prof_ok = True
    for e1, e2 in (tuple(tx), tuple(tn)):
        prof = predicted_profile(e1, e2, target)
        if prof is None:
            continue
        for d, v in prof.items():
            if g.get(d, 0) != v:
                prof_ok = False
    pred = [theorem_ft(*tx), theorem_ft(*tn)]
    pred = [p for p in pred if p is not None]
    return dict(pa=pa, qa=qa, pb=pb, qb=qb, D=D,
                c1=tx[0], c2=tx[1], d1=tn[0], d2=tn[1],
                bx=tx[0] + tx[1] - 2, bn=tn[0] + tn[1] - 2,
                ft=-1 if ft is None else ft,
                prof_ok=int(prof_ok),
                thm=min(pred) if pred else -1,
                residual=int(not hypothesis(*tx) and not hypothesis(*tn)),
                target=target)


def grid(amax, bmax_, dmax, Ds):
    seen, out = set(), []
    for D in Ds:
        for qa in range(1, dmax + 1):
            for qb in range(1, dmax + 1):
                for pa in range(-amax * qa, amax * qa + 1):
                    for pb in range(1, bmax_ * qb + 1):
                        a, b = F(pa, qa), F(pb, qb)
                        if (a, b, D) in seen:
                            continue
                        seen.add((a, b, D))
                        out.append((a.numerator, a.denominator,
                                    b.numerator, b.denominator, D))
    return out


def main():
    target = int(sys.argv[1]) if len(sys.argv) > 1 else 150
    amax = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    bmx = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    dmax = int(sys.argv[4]) if len(sys.argv) > 4 else 6
    Ds = tuple(int(s) for s in (sys.argv[5].split(",") if len(sys.argv) > 5
                                else ["2", "3", "5"]))
    out_path = sys.argv[6] if len(sys.argv) > 6 else "theorem.csv"
    items = [(*g, target) for g in grid(amax, bmx, dmax, Ds)]
    print("grid", len(items), flush=True)
    nbad = nres = nresbig = 0
    worst = []
    with Pool(4) as p, open(out_path, "w", newline="") as fh:
        w = None
        n = 0
        for r in p.imap_unordered(job, items, chunksize=8):
            if w is None:
                w = csv.DictWriter(fh, fieldnames=list(r))
                w.writeheader()
            w.writerow(r)
            n += 1
            if not r["prof_ok"]:
                nbad += 1
                if nbad < 10:
                    print("PROFILE FAIL", r, flush=True)
            if r["thm"] >= 0 and r["ft"] >= 0 and r["ft"] != r["thm"]:
                print("FT MISMATCH", r, flush=True)
            if r["residual"]:
                nres += 1
                if r["ft"] > max(r["bx"], r["bn"], 7):
                    nresbig += 1
                    worst.append(r)
            if n % 5000 == 0:
                print(n, "profile fails", nbad, "residual", nres,
                      "residual over bound", nresbig, flush=True)
    print("done", n, "profile fails", nbad, "residual", nres,
          "residual over bound", nresbig)
    worst.sort(key=lambda r: -(r["ft"] - max(r["bx"], r["bn"], 7)))
    for r in worst[:30]:
        print("  WORST", r)


if __name__ == "__main__":
    main()
