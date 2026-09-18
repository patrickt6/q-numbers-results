"""Scan for exceedances of the beta bound and measure their size.

Independent of qreals.negation.locked_series: [x]_q and [-x]_q are each built
from a deep HJ convergent with exact integer polynomial arithmetic, and the
convergent depth is certified against the agreement bound C_n.
"""
from collections import Counter
from fractions import Fraction

from qreals.quadratic import QuadraticIrrational, hj_terms
from reduction_check import convergent, padd

TAIL_START = 6


def budget(terms):
    return (terms[0] - 1) + (terms[1] - 1)


def analyse(a, b, D, headroom=14):
    x = QuadraticIrrational.from_ab(a, b, D)
    nx = QuadraticIrrational.from_ab(-a, -b, D)
    tx, _, _ = hj_terms(x, 400)
    tn, _, _ = hj_terms(nx, 400)
    if len(tx) < 4 or len(tn) < 4:
        return None
    bx, bn = budget(tx), budget(tn)
    pred = max(bx, bn)
    if pred < TAIL_START:
        return None                      # bound is vacuous below the tail start
    cap = pred + headroom
    # certify convergent depth: keep terms until C_n exceeds cap on both sides
    def deep(terms):
        C, k = 0, 0
        for c in terms:
            C += c - 1
            k += 1
            if C > cap + 4 and k >= 3:
                break
        return terms[:k], C
    dx, Cx = deep(tx)
    dn, Cn = deep(tn)
    if Cx <= cap or Cn <= cap:
        return None                      # not certified to `cap`; skip
    G = padd(convergent(dx, cap), convergent(dn, cap))
    tail = next((d for d in range(TAIL_START, cap + 1) if G.get(d, 0) != 0), None)
    return bx, bn, pred, tail, cap


def main():
    tot = 0
    exc = []
    nocert = 0
    for D in (2, 3, 5):
        for an in range(-40, 41):
            for bn in range(-24, 25):
                if bn == 0:
                    continue
                a, b = Fraction(an, 8), Fraction(bn, 8)
                res = analyse(a, b, D)
                if res is None:
                    continue
                bx, bnn, pred, tail, cap = res
                tot += 1
                if tail is None:
                    nocert += 1          # no nonzero found within the window
                elif tail > pred:
                    exc.append((D, a, b, bx, bnn, pred, tail, tail - pred))
    print(f"points with pred >= {TAIL_START}, certified: {tot}")
    print(f"exceedances of max(beta(x), beta(-x)): {len(exc)}"
          f"  ({100.0 * len(exc) / tot:.2f}%)")
    print(f"no nonzero found inside the window (finite-looking): {nocert}")
    print()
    print("exceedance size (tail - pred):", sorted(Counter(e[7] for e in exc).items()))
    print("by D:", Counter(e[0] for e in exc))
    print("pred value at exceedances:", sorted(Counter(e[5] for e in exc).items())[:20])
    print()
    print("largest exceedances:")
    for e in sorted(exc, key=lambda t: -t[7])[:15]:
        print(f"   D={e[0]} x={e[1]}+{e[2]}*sqrt({e[0]})  beta(x)={e[3]} "
              f"beta(-x)={e[4]} pred={e[5]} tail={e[6]} excess={e[7]}")
    print()
    print("smallest counterexamples by |x| (paper-facing candidates):")
    keyed = sorted(exc, key=lambda t: abs(float(t[1]) + float(t[2]) * t[0] ** 0.5))
    for e in keyed[:10]:
        print(f"   D={e[0]} x={e[1]}+{e[2]}*sqrt({e[0]})  pred={e[5]} tail={e[6]}")


if __name__ == "__main__":
    main()
