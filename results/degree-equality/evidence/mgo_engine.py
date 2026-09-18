#!/usr/bin/env python3
"""
Independent, standalone reimplementation of the MGO q-continuant matrix
engine, shared by several verification scripts in this sweep.

Does NOT import qreals, qpoly, census, or any other project module. Built
directly from the algorithm definition (as already validated in
verify_twin_primes_tail.py and verify_degree_equality_d400.py for the
rational case): Laurent polynomials as plain Python dict {exponent: coeff},
q-deformed 2x2 matrix blocks with alternating parity convention, matrix
product built with elementary dict arithmetic. sympy is used only for
cyclotomic polynomials and polynomial GCD/quo over ZZ, called directly (not
via any project wrapper).

Two continuant constructions are provided:
  1. rational_matrix(r, s)   -- full 2x2 matrix for a finite continued
     fraction of the rational r/s (reused, unchanged in substance, from the
     twin-primes script).
  2. sqrt_period_matrix(d)   -- full 2x2 matrix for one period of the
     (ordinary, non-q) periodic continued fraction of sqrt(d), with the
     same q-deformed block convention applied digit-by-digit across the
     period. This is the natural generalization used to test the reduction
     documented in project memory ("Pell negation theorem": F(d) = (A-D)/C
     reduces the Ex 6.4 finiteness question to one polynomial divisibility,
     C | (A-D)).

Both constructions are exact integer polynomial arithmetic; no floating
point is used anywhere in the CF or matrix code (sqrt(d) periods are found
with the standard integer PQa algorithm, not floating sqrt).
"""
from __future__ import annotations

import math
import sympy as sp

q = sp.symbols("q")

ZERO = {}
ONE = {0: 1}


def dadd(a, b):
    out = dict(a)
    for e, c in b.items():
        v = out.get(e, 0) + c
        if v:
            out[e] = v
        elif e in out:
            del out[e]
    return out


def dsub(a, b):
    return dadd(a, {e: -c for e, c in b.items()})


def dmul(a, b):
    if not a or not b:
        return {}
    out = {}
    for e1, c1 in a.items():
        for e2, c2 in b.items():
            e = e1 + e2
            out[e] = out.get(e, 0) + c1 * c2
    return {e: c for e, c in out.items() if c != 0}


def qint(a):
    return {i: 1 for i in range(a)} if a > 0 else {}


def qint_inv(a):
    return {i - (a - 1): 1 for i in range(a)} if a > 0 else {}


def mono(k):
    return {k: 1}


def mat_mul(M, N):
    a, b = M[0]
    c, e = M[1]
    p, r = N[0]
    s, t = N[1]
    return [
        [dadd(dmul(a, p), dmul(b, s)), dadd(dmul(a, r), dmul(b, t))],
        [dadd(dmul(c, p), dmul(e, s)), dadd(dmul(c, r), dmul(e, t))],
    ]


def q_block(i, a):
    """MGO block at position i (0-indexed) for digit a >= 1:
    i even: [[ [a]_q,     q^a  ], [1, 0]]
    i odd : [[ [a]_{1/q}, q^-a ], [1, 0]]
    """
    if i % 2 == 0:
        return [[qint(a), mono(a)], [ONE, ZERO]]
    return [[qint_inv(a), mono(-a)], [ONE, ZERO]]


def cf_terms(r, s):
    r, s = int(r), int(s)
    terms = []
    while s != 0:
        a = r // s
        terms.append(a)
        r, s = s, r - a * s
    return terms


def make_even_length(a):
    a = list(a)
    if len(a) % 2 == 0:
        return a
    if a[-1] >= 2:
        a[-1] -= 1
        a.append(1)
        return a
    if len(a) >= 2 and a[-1] == 1:
        a.pop()
        a[-1] += 1
        return a
    raise ValueError(f"cannot make even-length CF from {a!r}")


def rational_matrix(r, s):
    """Full 2x2 MGO matrix for the (even-length-normalized) continued
    fraction of r/s. Returns [[A,B],[C,D]] as Laurent dicts."""
    cf = make_even_length(cf_terms(r, s))
    M = [[ONE, ZERO], [ZERO, ONE]]
    for i, a in enumerate(cf):
        M = mat_mul(M, q_block(i, a))
    return M


def laurent_to_sympy_poly(d):
    """Laurent dict -> sympy Poly in q over ZZ, after clearing the minimal
    exponent (i.e. treated up to an overall monomial factor, which is what
    matters for a divisibility test)."""
    if not d:
        return sp.Poly(0, q, domain="ZZ")
    mn, mx = min(d), max(d)
    coeffs_desc = [d.get(e, 0) for e in range(mx, mn - 1, -1)]
    return sp.Poly(coeffs_desc, q, domain="ZZ")


def pqa_sqrt_period(d):
    """Standard integer PQa algorithm for the periodic continued fraction
    of sqrt(d), d a positive nonsquare integer. Returns (a0, period_digits)
    where period_digits = [a1, ..., ap] is the minimal repeating block.
    All arithmetic is plain Python int (exact), no floating sqrt is used
    for anything beyond the initial integer floor via math.isqrt.
    """
    a0 = math.isqrt(d)
    if a0 * a0 == d:
        raise ValueError(f"{d} is a perfect square")
    m, den, a = 0, 1, a0
    period = []
    seen = {}
    while True:
        m = den * a - m
        den = (d - m * m) // den
        a = (a0 + m) // den
        state = (m, den)
        if state in seen:
            break
        seen[state] = len(period)
        period.append(a)
        if a == 2 * a0:
            # standard termination: a_p = 2*a0 always ends a period
            break
    return a0, period


def pell_fundamental_solution(d):
    """Return (x, y) the fundamental solution of x^2 - d*y^2 = +-1 via the
    convergents of the periodic CF (standard number theory, independent of
    any q-deformation)."""
    a0, period = pqa_sqrt_period(d)
    # Classical theorem: the convergent at index p-1 (a0 plus the first
    # p-1 period digits) satisfies x^2 - d*y^2 = (-1)^p. When p is even
    # that is already the fundamental +1 solution; when p is odd it gives
    # -1, and the +1 solution requires going around the period twice, i.e.
    # using index 2p-1 (a0, the full period, then the first p-1 digits of
    # a second copy of the period).
    if len(period) % 2 == 0:
        terms = [a0] + period[:-1]
    else:
        terms = [a0] + period + period[:-1]
    h_prev2, h_prev1 = 1, terms[0]
    k_prev2, k_prev1 = 0, 1
    for a in terms[1:]:
        h = a * h_prev1 + h_prev2
        k = a * k_prev1 + k_prev2
        h_prev2, h_prev1 = h_prev1, h
        k_prev2, k_prev1 = k_prev1, k
    return h_prev1, k_prev1, len(period)


def sqrt_period_matrix(d):
    """Full 2x2 MGO matrix for one period [a1,...,ap] of sqrt(d)'s CF (the
    a0 integer part is not part of the periodic block, matching the
    standard Pell-automorph construction). Digit parity indices restart at
    0 at the start of the period. Returns [[A,B],[C,D]] as Laurent dicts,
    plus the period length and the (r_d, s_d) classical fundamental
    solution for cross-checking."""
    a0, period = pqa_sqrt_period(d)
    cf = make_even_length(period)
    M = [[ONE, ZERO], [ZERO, ONE]]
    for i, a in enumerate(cf):
        M = mat_mul(M, q_block(i, a))
    r_d, s_d, plen = pell_fundamental_solution(d)
    return M, r_d, s_d, plen


def is_finite_via_C_divides_AmD(d):
    """Independent test of the Ex 6.4 / F(d) finiteness reduction recorded
    in project memory: F(d) = (A-D)/C is a Laurent polynomial (i.e. F(d) is
    finite) iff C divides A-D exactly as polynomials. Returns
    (is_finite_bool, r_d, s_d, period_length)."""
    M, r_d, s_d, plen = sqrt_period_matrix(d)
    A, B, C, D = M[0][0], M[0][1], M[1][0], M[1][1]
    Ap = laurent_to_sympy_poly(A)
    Dp = laurent_to_sympy_poly(D)
    Cp = laurent_to_sympy_poly(C)
    AmD = Ap - Dp
    if Cp.degree() < 0:
        # C identically zero: degenerate, should not occur for d >= 2
        return (AmD.degree() < 0, r_d, s_d, plen)
    if AmD.degree() < 0:
        return (True, r_d, s_d, plen)
    q_, rem = sp.div(AmD, Cp, domain="QQ")
    finite = rem.is_zero
    return (finite, r_d, s_d, plen)


if __name__ == "__main__":
    # Tiny smoke test.
    for d in (2, 3, 5, 6, 7, 8):
        finite, r_d, s_d, plen = is_finite_via_C_divides_AmD(d)
        print(d, "finite=", finite, "r_d=", r_d, "s_d=", s_d, "period_len=", plen)
