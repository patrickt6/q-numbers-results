"""Orbit closure of the continuant state at a fixed root of unity.

State after reading residues (r_2, ..., r_i):
    ( S_i(w), S_{i-1}(w), r_i )      with w a primitive l-th root.
Transition by a next residue r:
    ( [r]_w S_i - w^{r_i - 1} S_{i-1},  S_i,  r ).
Seed states: ( [r]_w, 1, r ) for r = 0..l-1  (S_1 = 1, and c_1 never
enters S, anchored in 01_anchor.py and in the phi8-board work).

If the reachable state set is FINITE, then the set of values S_n(w) over
ALL words of ALL lengths is exactly the finite set of first components,
and this BFS is an exact proof of that, no literature needed.

For each l, report: whether the orbit closes (cap 400000 states), the
value set F_l = {S(w)}, and the set of rational primes p dividing the
content of some NONZERO value (these are the only p for which the
congruence obstruction S(zeta_l) in pZ[zeta_l] \\ {0} can occur).
"""
import sys
from math import gcd

sys.path.insert(0, "<path>"
                    "<path>")
from ring import CycRing  # noqa: E402

CAP = 400000


def orbit(l):
    R = CycRing(l)
    seen = set()
    frontier = []
    for r in range(l):
        st = (R.qint[r], R.one, r)
        if st not in seen:
            seen.add(st)
            frontier.append(st)
    closed = True
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
            if len(seen) > CAP:
                closed = False
                new = []
                break
        if not closed:
            break
        frontier = new
    values = {st[0] for st in seen}
    return closed, len(seen), values


def content(v):
    g = 0
    for c in v:
        g = gcd(g, abs(c))
    return g


def prime_factors(n):
    ps = set()
    d = 2
    while d * d <= n:
        while n % d == 0:
            ps.add(d)
            n //= d
        d += 1
    if n > 1:
        ps.add(n)
    return ps


for l in range(2, 10):
    closed, nstates, values = orbit(l)
    if not closed:
        print(f"l={l}: orbit does NOT close within {CAP} states -> value set "
              f"not proved finite this way ({nstates}+ states)")
        continue
    nz = [v for v in values if any(v)]
    contents = sorted({content(v) for v in nz})
    bad_primes = set()
    for c in contents:
        if c > 1:
            bad_primes |= prime_factors(c)
    print(f"l={l}: orbit CLOSES, states={nstates}, |values|={len(values)}, "
          f"zero in values={any(not any(v) for v in values)}")
    print(f"    nonzero-value contents: {contents}")
    print(f"    primes p with F_l meets pZ[zeta_l]\\{{0}}: "
          f"{sorted(bad_primes) if bad_primes else 'NONE'}")
    if l <= 5:
        print(f"    values: {sorted(values)}")
