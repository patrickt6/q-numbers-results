"""Targeted search for beta-bound exceedances in the large-pred regime.

The census only ever evaluates the bound at pred >= 70, because it escalates
near-rational points. This scan builds near-rational points deliberately:
x = a + b*sqrt(D) with small |b|, which drives beta(x) or beta(-x) large.

Exact arithmetic. Independent of qreals.negation.locked_series.
"""
import sys
from collections import Counter
from fractions import Fraction

from qreals.quadratic import QuadraticIrrational, hj_terms
from reduction_check import convergent, padd

TAIL_START = 6
HEADROOM = 12


def budget(t):
    return (t[0] - 1) + (t[1] - 1)


def deep_enough(terms, cap):
    C, k = 0, 0
    for c in terms:
        C += c - 1
        k += 1
        if C > cap + 4 and k >= 3:
            return terms[:k], C
    return terms, C


def analyse(a, b, D, pred_lo, pred_hi):
    tx, _, _ = hj_terms(QuadraticIrrational.from_ab(a, b, D), 4000)
    tn, _, _ = hj_terms(QuadraticIrrational.from_ab(-a, -b, D), 4000)
    if len(tx) < 4 or len(tn) < 4:
        return None
    bx, bn = budget(tx), budget(tn)
    pred = max(bx, bn)
    if not (pred_lo <= pred <= pred_hi):
        return None
    cap = pred + HEADROOM
    dx, Cx = deep_enough(tx, cap)
    dn, Cn = deep_enough(tn, cap)
    if Cx <= cap or Cn <= cap:
        return None
    G = padd(convergent(dx, cap), convergent(dn, cap))
    tail = next((d for d in range(TAIL_START, cap + 1) if G.get(d, 0) != 0), None)
    return bx, bn, pred, tail


def main():
    pred_lo, pred_hi = int(sys.argv[1]), int(sys.argv[2])
    tot, exc, eq, none = 0, [], 0, 0
    for D in (2, 3, 5):
        for sden in (1, 2, 3, 4, 5, 8):
            for snum in range(-5 * sden, 5 * sden + 1):
                a = Fraction(snum, sden)
                for bden in range(2, 60):
                    for bnum in (1, -1, 2, -2, 3, -3):
                        b = Fraction(bnum, bden)
                        if b == 0:
                            continue
                        res = analyse(a, b, D, pred_lo, pred_hi)
                        if res is None:
                            continue
                        bx, bn, pred, tail = res
                        tot += 1
                        if tail is None:
                            none += 1
                        elif tail > pred:
                            exc.append((D, a, b, bx, bn, pred, tail, tail - pred))
                        elif tail == pred:
                            eq += 1
    print(f"pred band [{pred_lo}, {pred_hi}]")
    print(f"certified points   {tot}")
    print(f"exceedances        {len(exc)}")
    print(f"exact equalities   {eq}")
    print(f"no tail in window  {none}")
    if exc:
        print("excess sizes:", sorted(Counter(e[7] for e in exc).items()))
        for e in exc[:20]:
            print(f"   D={e[0]} x={e[1]}+{e[2]}*sqrt({e[0]}) beta(x)={e[3]} "
                  f"beta(-x)={e[4]} pred={e[5]} tail={e[6]}")


if __name__ == "__main__":
    main()
