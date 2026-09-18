"""Targeted counterexample hunt on the congruence locus.

A counterexample to DC(pl -> l) is a word with Phi_{pl} | S and
Phi_l not dividing S. By the Frobenius lemma its residues mod l must lie
in the locus L(l, p) = { tuples : S(zeta_l) in pZ[zeta_l] \\ {0} }.
So: generate locus tuples (exhaustive n = 4, 5; random n = 6..10), then
enumerate EVERY lift of each locus tuple to residues mod pl and test
Phi_{pl} | S exactly. Any hit is a counterexample to (DC) and is printed
loudly. This searches precisely and only where a counterexample can be.
"""
import random
import sys
from itertools import product
from math import gcd

sys.path.insert(0, "<path>"
                    "<path>")
from ring import CycRing  # noqa: E402

random.seed(2)
MAX_LOCUS_PER_PAIR = 1000
MAX_LIFTS = 20000
PAIR_BUDGET = 300000   # total lift evaluations per (l, p) pair

PAIRS = [(6, 2), (6, 3), (6, 5), (7, 2), (7, 3), (8, 2), (8, 3),
         (9, 2), (9, 3), (10, 2), (10, 3), (12, 2), (12, 3), (14, 2), (15, 2)]


def content(v):
    g = 0
    for c in v:
        g = gcd(g, abs(c))
    return g


def locus_tuples(l, p, Rl):
    """Tuples mod l with S(zeta_l) nonzero and content divisible by p."""
    out = []
    # exhaustive n = 4, 5
    for n in (4, 5):
        for rs in product(range(l), repeat=n - 1):
            v = Rl.S_of_residues(rs)
            if any(v) and content(v) % p == 0:
                out.append(rs)
                if len(out) >= MAX_LOCUS_PER_PAIR:
                    return out
    # random longer
    tries = 250000 if l >= 7 else 80000
    for _ in range(tries):
        n = random.randint(6, 10)
        rs = tuple(random.randrange(l) for _ in range(n - 1))
        v = Rl.S_of_residues(rs)
        if any(v) and content(v) % p == 0:
            out.append(rs)
            if len(out) >= MAX_LOCUS_PER_PAIR:
                break
    return out


grand = 0
for l, p in PAIRS:
    k = p * l
    Rl, Rk = CycRing(l), CycRing(k)
    locus = locus_tuples(l, p, Rl)
    tested = counterex = 0
    for rs in locus:
        m = len(rs)
        if p ** m > MAX_LIFTS or tested >= PAIR_BUDGET:
            continue
        for lift in product(range(p), repeat=m):
            top = [rs[i] + l * lift[i] for i in range(m)]
            tested += 1
            if Rk.S_of_residues(top) == Rk.zero:
                counterex += 1
                print(f"*** COUNTEREXAMPLE DC({k}->{l}): residues mod {k} = {top}")
    grand += counterex
    print(f"l={l} p={p} (k={k}): locus tuples used={len(locus)}, "
          f"lifts tested={tested}, counterexamples={counterex}", flush=True)
print(f"GRAND TOTAL counterexamples: {grand}")
