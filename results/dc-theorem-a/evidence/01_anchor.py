"""Anchor checks. All exact.

1. The recurrence (previous-quotient exponent) against the qreals engine,
   words of length 3 to 7.
2. The residue-ring evaluation (ring.py) against full sympy division by
   Phi_k, on random words and many k.
3. The wrong convention (current-quotient exponent) diverges at length 4.
"""
import random
import sys
from fractions import Fraction

import sympy as sp
from sympy import symbols, cyclotomic_poly

sys.path.insert(0, "<path>")
sys.path.insert(0, "<path>"
                    "<path>")
import qreals  # noqa: E402
from ring import CycRing  # noqa: E402

q = symbols('q')
random.seed(20260730)


def qint(c):
    return sum(q**i for i in range(c))


def S_recur(cs, wrong=False):
    """cs = (c_1, ..., c_n). Returns S_n as a sympy polynomial."""
    prev, cur = sp.Integer(1), qint(cs[1])
    for i in range(2, len(cs)):
        e = cs[i] - 1 if wrong else cs[i - 1] - 1
        prev, cur = cur, sp.expand(qint(cs[i]) * cur - q**e * prev)
    return cur


def hj_value(cs):
    v = Fraction(cs[-1])
    for c in reversed(cs[:-1]):
        v = Fraction(c) - 1 / v
    return v


print("1. engine anchor, lengths 3..7")
ok = tot = 0
for n in range(3, 8):
    for _ in range(6):
        cs = [random.randint(2, 6) for _ in range(n)]
        x = hj_value(cs)
        expr = sp.cancel(qreals.q_rational(x.numerator, x.denominator))
        num, den = sp.fraction(expr)
        S = S_recur(cs)
        ratio = sp.cancel(sp.expand(den) / S)
        good = bool(ratio.is_number) and ratio != 0
        tot += 1
        ok += good
        if not good:
            print("  MISMATCH", cs)
print(f"  matched {ok} of {tot}")

print("2. residue-ring evaluation vs sympy Phi_k division")
bad = tot = 0
for _ in range(300):
    n = random.randint(3, 8)
    cs = [random.randint(1, 25) for _ in range(n)]
    S = sp.Poly(S_recur(cs), q)
    k = random.randint(2, 24)
    R = CycRing(k)
    rs = [c % k for c in cs[1:]]
    ringzero = R.S_of_residues(rs) == R.zero
    phik = sp.Poly(cyclotomic_poly(k, q), q)
    symzero = sp.rem(S, phik, q) == 0
    tot += 1
    if ringzero != symzero:
        bad += 1
        print("  MISMATCH", cs, k)
print(f"  agreed on {tot - bad} of {tot} (hits included by chance only)")

# force some genuine hits: family C words at various k
print("3. forced hits: word (e,2e,e) mod k patterns, and Z1/Z2 patterns")
bad = tot = 0
for k in range(3, 21):
    R = CycRing(k)
    phik = sp.Poly(cyclotomic_poly(k, q), q)
    for rs in [(1, 2, 1), (2, 1, 2), (0, 5 % k, 0), (3 % k, 0, (-3) % k)]:
        cs = [2] + [r if r >= 2 else r + k for r in rs]
        S = sp.Poly(S_recur(cs), q)
        symzero = sp.rem(S, phik, q) == 0
        ringzero = R.S_of_residues([c % k for c in cs[1:]]) == R.zero
        tot += 1
        if not (symzero and ringzero):
            bad += 1
            print("  FAILED HIT", k, cs, symzero, ringzero)
print(f"  {tot - bad} of {tot} forced hits confirmed by both methods")

print("4. convention divergence at length 4")
cs = [2, 3, 5, 4]
d = sp.expand(S_recur(cs) - S_recur(cs, wrong=True))
print("  S(right) - S(wrong) for (2,3,5,4):", d, " (nonzero expected)")
