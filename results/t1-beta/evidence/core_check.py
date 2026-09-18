"""Check the decomposition G = K + R, K = [c1]+[1-c1] - q^{c1-1}/[c2] - q^{-c1}/[d2].

R = G - K must have valuation exactly m = min(C_2(x), C_2(-x)) and leading
coefficient -1 (if the two differ) or -2 (if they agree). K itself must have no
nonzero coefficient in degrees (c1, m].
"""

from __future__ import annotations

import sys
from fractions import Fraction as F
from itertools import product

from exact import (
    G_exact,
    QuadraticIrrational,
    divide,
    hj,
    ladd,
    lsub,
    q_bracket,
)


def K_series(c1, c2, d2, target):
    g1 = ladd(q_bracket(c1), q_bracket(1 - c1))
    t1 = divide({c1 - 1: F(-1)}, q_bracket(c2), target)
    u1 = divide({-c1: F(-1)}, q_bracket(d2), target)
    return {k: v for k, v in ladd(ladd(g1, t1), u1).items() if v and k <= target}


def check(a, b, D, target=90):
    x = QuadraticIrrational.from_ab(a, b, D)
    tx, tn = hj(x, 3), hj(-x, 3)
    c1, c2 = tx[0], tx[1]
    d1, d2 = tn[0], tn[1]
    bx = (c1 - 1) + (c2 - 1)
    bn = (d1 - 1) + (d2 - 1)
    m = min(bx, bn)
    g = G_exact(x, target)
    k = K_series(c1, c2, d2, target)
    r = {kk: v for kk, v in lsub(g, k).items() if v}
    lo = min(r) if r else None
    lead = r.get(lo) if r else None
    okdual = (d1 == 1 - c1)
    # K must vanish strictly above tau = max(c1, 1-c1) and up to m inclusive
    tau = max(c1, 1 - c1)
    kzero = all(k.get(d, 0) == 0 for d in range(tau + 1, m + 1))
    return dict(c1=c1, c2=c2, d1=d1, d2=d2, bx=bx, bn=bn, m=m, tau=tau,
                val_R=lo, lead_R=lead,
                val_ok=(lo == m), lead_ok=(lead in (-1, -2)),
                lead_expected=(-2 if bx == bn else -1),
                d1_ok=okdual, K_gap_ok=kzero)


def main():
    target = 90
    bad = 0
    n = 0
    for D in (2, 3, 5, 7, 13):
        for qa, qb in product(range(1, 5), repeat=2):
            for pa in range(-4 * qa, 4 * qa + 1):
                for pb in range(1, 3 * qb + 1):
                    a, b = F(pa, qa), F(pb, qb)
                    res = check(a, b, D, target)
                    n += 1
                    ok = (res["val_ok"] and res["lead_ok"] and res["d1_ok"]
                          and res["K_gap_ok"]
                          and res["lead_R"] == res["lead_expected"])
                    if not ok:
                        bad += 1
                        if bad < 25:
                            print("FAIL", a, b, D, res, flush=True)
    print(f"checked {n}, failures {bad}")


if __name__ == "__main__":
    sys.exit(main())
