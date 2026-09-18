"""The l >= 6 frontier: is the congruence obstruction actually populated?

By the Frobenius lemma, a counterexample to DC(p^a l -> l) must have
S(zeta_l) in pZ[zeta_l] \\ {0}. For l in {2,3,4,5} that locus is empty
(03_value_sets.py), which proves DC there. This script asks, for
l in {6,7,8,9,10,12}: does the locus S(zeta_l) in pZ[zeta_l] \\ {0}
contain words at all, and if so, does Phi_{p l} | S ever co-occur
(co-occurrence would be a DC counterexample).

Method: exhaustive residue tuples at l for n = 4, 5 and random tuples
for n = 6..10. For each tuple with content(S(zeta_l)) divisible by a
prime p, evaluate S at a primitive (p l)-th root using the same residues
lifted (any word with those residues mod pl reduces correctly; we test
tuples mod pl directly: for each found (tuple mod l, p) we search all
lifts is too big, so instead we run the complementary direction, which
the exhaustive sweep 02 already covers: all tuples mod pl with
Phi_{pl} | S were checked against l. Here we only measure the locus.)
Exact arithmetic only.
"""
import random
import sys
from math import gcd

sys.path.insert(0, "<path>"
                    "<path>")
from ring import CycRing  # noqa: E402

random.seed(1)


def content(v):
    g = 0
    for c in v:
        g = gcd(g, abs(c))
    return g


def prime_factors(n):
    ps, d = set(), 2
    while d * d <= n:
        while n % d == 0:
            ps.add(d)
            n //= d
        d += 1
    if n > 1:
        ps.add(n)
    return ps


for l in (6, 7, 8, 9, 10, 12):
    R = CycRing(l)
    found = {}   # prime -> example (n, tuple)
    counts = {}  # prime -> count
    total = 0

    def scan(rs):
        global total
        total += 1
        v = R.S_of_residues(rs)
        c = content(v)
        if c > 1:
            for p in prime_factors(c):
                counts[p] = counts.get(p, 0) + 1
                if p not in found:
                    found[p] = (len(rs) + 1, tuple(rs))

    # exhaustive n = 4, 5
    for n in (4, 5):
        idx = [0] * (n - 1)
        while True:
            scan(idx)
            i = 0
            while i < n - 1:
                idx[i] += 1
                if idx[i] < l:
                    break
                idx[i] = 0
                i += 1
            if i == n - 1:
                break
    # random n = 6..10
    for _ in range(120000):
        n = random.randint(6, 10)
        scan([random.randrange(l) for _ in range(n - 1)])

    print(f"l={l}: scanned {total} tuples; congruence locus by prime:")
    if not counts:
        print("    EMPTY, no nonzero S(zeta_l) with content > 1 found")
    for p in sorted(counts):
        n, rs = found[p]
        print(f"    p={p}: {counts[p]} tuples, e.g. n={n} residues={rs}")
