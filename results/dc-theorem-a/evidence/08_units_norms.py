"""Referee audit of Lemma 3: the full value sets F_l with norms.

For l in {2, 3, 4, 5}: recompute the orbit closure, list every value of
S(zeta_l), and for each nonzero value compute exactly
  - its content (gcd of its coordinates in the basis 1, zeta, ...,
    zeta^{phi(l)-1}); since Z[zeta_l] is a free Z-module on that basis,
    v lies in p Z[zeta_l] if and only if p divides the content, so
    content 1 is EXACTLY the condition Theorem A needs;
  - its field norm N(v) = Res(Phi_l, v)(the product of v over all
    primitive l-th roots), computed by sympy resultant; |N(v)| = 1 if
    and only if v is a unit. Unit-ness is sufficient for the theorem
    but strictly stronger than needed, and indeed non-units of content
    1 occur (for example 1 + i at l = 4, norm 2).
Exact arithmetic only.
"""
import sys
from math import gcd

import sympy as sp
from sympy import symbols, cyclotomic_poly

sys.path.insert(0, "<path>"
                    "<path>")
from ring import CycRing  # noqa: E402

x = symbols('x')


def orbit_values(l):
    R = CycRing(l)
    seen = set()
    frontier = []
    for r in range(l):
        st = (R.qint[r], R.one, r)
        seen.add(st)
        frontier.append(st)
    while frontier:
        new = []
        for (cur, prev, r_old) in frontier:
            for r in range(l):
                nxt = (R.sub(R.mul(R.qint[r], cur),
                             R.mul(R.qpow[(r_old - 1) % l], prev)),
                       cur, r)
                if nxt not in seen:
                    seen.add(nxt)
                    new.append(nxt)
        frontier = new
    return {st[0] for st in seen}


for l in (2, 3, 4, 5):
    phi = sp.Poly(cyclotomic_poly(l, x), x)
    values = orbit_values(l)
    nonunit = badcontent = 0
    print(f"l = {l}: |F_l| = {len(values)} (zero included)")
    for v in sorted(values):
        if not any(v):
            print("    0")
            continue
        c = 0
        for co in v:
            c = gcd(c, abs(co))
        vp = sp.Poly(list(reversed(v)), x)
        norm = int(sp.resultant(phi, vp))
        unit = abs(norm) == 1
        nonunit += (not unit)
        badcontent += (c != 1)
        print(f"    {v}  content={c}  norm={norm}  unit={unit}")
    print(f"    nonzero values with content > 1: {badcontent}  "
          f"(THEOREM NEEDS 0 HERE)")
    print(f"    nonzero values that are not units: {nonunit}")
