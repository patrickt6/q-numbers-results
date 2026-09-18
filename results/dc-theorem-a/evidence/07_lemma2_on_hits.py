"""Empirical confirmation of Lemma 2 and Theorem A on real hit data.

All residue tuples (n = 5) with Phi_12 | S are checked against:
  Lemma 2, p = 2, l = 6:  S(zeta_6) zero or of even content;
  Theorem A, 12 = 3 * 4:  Phi_4 | S;
  Theorem A, 12 = 4 * 3:  Phi_3 | S;
  chain 12 -> 4 -> 2:     Phi_2 | S.
Result on 2026-07-30: 120 hits, 0 failures.
"""
import sys
from itertools import product
from math import gcd

sys.path.insert(0, "<path>"
                    "<path>")
from ring import CycRing  # noqa: E402

R12, R6, R4, R3, R2 = [CycRing(k) for k in (12, 6, 4, 3, 2)]


def cont(v):
    g = 0
    for c in v:
        g = gcd(g, abs(c))
    return g


hits = bad = 0
for rs in product(range(12), repeat=4):
    if R12.S_of_residues(rs) == R12.zero:
        hits += 1
        v6 = R6.S_of_residues([r % 6 for r in rs])
        ok = (not any(v6) or cont(v6) % 2 == 0)
        ok &= R4.S_of_residues([r % 4 for r in rs]) == R4.zero
        ok &= R3.S_of_residues([r % 3 for r in rs]) == R3.zero
        ok &= R2.S_of_residues([r % 2 for r in rs]) == R2.zero
        if not ok:
            bad += 1
            print("BAD", rs)
print(f"k=12 n=5 hits: {hits}  lemma/theorem failures: {bad}")
