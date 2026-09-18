"""Targeted sweep of the smallest open instance of downward closure.

Tests whether Phi_8 | S implies Phi_4 | S, over random Hirzebruch-Jung words.
Exact arithmetic throughout: divisibility is decided by polynomial remainder
over Z[q], never by evaluation at a floating point root.

Convention note. The continuant recurrence carries the PREVIOUS quotient in the
exponent:

    S_{i+1} = [c_{i+1}]_q S_i - q^{c_i - 1} S_{i-1},   (S_0, S_1) = (0, 1)

The variant with q^{c_{i+1}-1} is wrong. The two agree at length three and
diverge from length four onward, so a length-three check does not distinguish
them.

Result recorded 2026-07-30: 20000 words of lengths three to seven, quotients
drawn from 2 to 10, gave 432 words with Phi_8 | S and zero words where Phi_4
failed to divide.
"""

import random

import sympy as sp

q = sp.Symbol("q")
PHI8 = sp.cyclotomic_poly(8, q)
PHI4 = sp.cyclotomic_poly(4, q)


def q_integer(c):
    """The q-integer [c]_q, defined for negative c as well."""
    if c > 0:
        return sum(q**i for i in range(c))
    if c == 0:
        return sp.Integer(0)
    return -sum(q**i for i in range(c, 0))


def denominator(quotients):
    """S_n for the Hirzebruch-Jung word given by quotients."""
    s_prev, s_cur = sp.Integer(0), sp.Integer(1)
    for i in range(1, len(quotients)):
        s_new = sp.expand(
            q_integer(quotients[i]) * s_cur
            - q ** (quotients[i - 1] - 1) * s_prev
        )
        s_prev, s_cur = s_cur, s_new
    return s_cur


def divides(divisor, poly):
    """Exact divisibility over Z[q]."""
    return sp.rem(sp.Poly(poly, q), sp.Poly(divisor, q)).is_zero


def sweep(seed=1, lengths=range(3, 8), per_length=4000, lo=2, hi=10):
    random.seed(seed)
    words = [
        [random.randint(lo, hi) for _ in range(length)]
        for length in lengths
        for _ in range(per_length)
    ]

    hits = 0
    violations = []
    for word in words:
        s = denominator(word)
        if divides(PHI8, s):
            hits += 1
            if not divides(PHI4, s):
                violations.append(word)

    return len(words), hits, violations


if __name__ == "__main__":
    total, hits, violations = sweep()
    print("words tested:      ", total)
    print("Phi_8 divides S:   ", hits)
    print("Phi_4 fails:       ", len(violations))
    for word in violations:
        print("  counterexample:  ", word)
