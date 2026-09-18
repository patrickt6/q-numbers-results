#!/usr/bin/env python3
"""
Independent recomputation of claim negpaper_twin_primes_tail.

Reimplements the MGO q-continuant construction for a rational r/s from its
mathematical definition (as documented in the docstring of
<path>, which this script does NOT
import). Does not import qreals or qpoly or census. Uses only Python
integers, fractions.Fraction, and sympy called directly for cyclotomic
polynomials and for polynomial GCD over ZZ (sympy is not the qreals
package and its use here is direct symbolic computation, not a call into
the tracked codebase).

Claim under test:
  Among 293 pairs of odd primes p < p' with p*p' <= 1500, the mixed-root
  q-denominator S has the two-cyclotomic-factor tail S = Phi_p * Phi_p'
  exactly for the 5 twin-prime pairs and for none of the 288 non-twin
  pairs.
"""
from __future__ import annotations

from fractions import Fraction
import sympy as sp

q = sp.symbols("q")


# ---------------------------------------------------------------------
# Laurent polynomials as dict {exponent: coeff}, built from scratch.
# ---------------------------------------------------------------------
def dadd(a, b):
    out = dict(a)
    for e, c in b.items():
        v = out.get(e, 0) + c
        if v:
            out[e] = v
        elif e in out:
            del out[e]
    return out


def dmul(a, b):
    if not a or not b:
        return {}
    out = {}
    for e1, c1 in a.items():
        for e2, c2 in b.items():
            e = e1 + e2
            out[e] = out.get(e, 0) + c1 * c2
    return {e: c for e, c in out.items() if c != 0}


ZERO = {}
ONE = {0: 1}


def qint(a):
    """[a]_q = 1 + q + ... + q^{a-1}."""
    return {i: 1 for i in range(a)} if a > 0 else {}


def qint_inv(a):
    """[a]_{1/q} = q^{-(a-1)}[a]_q."""
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
    """MGO block at position i (0-indexed), digit a >= 1:
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


def denominator_poly(r, s):
    """Return the (unreduced, as Laurent dict) matrix entry M[1][0] for the
    continuant of r/s, i.e. the raw q-denominator before common-factor
    reduction against the numerator."""
    cf = make_even_length(cf_terms(r, s))
    M = [[ONE, ZERO], [ZERO, ONE]]
    for i, a in enumerate(cf):
        M = mat_mul(M, q_block(i, a))
    return M[0][0], M[1][0]  # R, S as Laurent dicts


def laurent_to_poly(d):
    """dict -> ascending-order plain integer coefficient list, dropping the
    overall q-power shift (i.e. divide out q^min_exponent)."""
    if not d:
        return []
    mn, mx = min(d), max(d)
    return [d.get(e, 0) for e in range(mn, mx + 1)]


def reduce_S(Rpoly, Spoly):
    """Reduce Num/Den to lowest terms over Q(q) and return the reduced
    denominator as a primitive integer sympy Poly, using sympy's ZZ gcd
    directly (not via qpoly.reduce_ratio)."""
    if not Spoly:
        raise ZeroDivisionError
    if not Rpoly:
        return sp.Poly(1, q, domain="ZZ")
    pn = sp.Poly(list(reversed(Rpoly)), q, domain="ZZ")
    pd = sp.Poly(list(reversed(Spoly)), q, domain="ZZ")
    g = pn.gcd(pd)
    qd = pd.quo(g)
    _, qd = qd.primitive()
    if qd.LC() < 0:
        qd = -qd
    return qd


def S_of(r, s):
    R, S = denominator_poly(r, s)
    Rpoly = laurent_to_poly(R)
    Spoly = laurent_to_poly(S)
    return reduce_S(Rpoly, Spoly)


def crt_mixed_root(p, pp):
    """a such that a = -1/p mod pp scaled: matches the CRT construction in
    the original producer (independently re-derived here from its stated
    formula a = 1 + p*k, k = -2*p^{-1} mod pp)."""
    dd = p * pp
    pinv = pow(p, -1, pp)
    k = (-2 * pinv) % pp
    a = (1 + p * k) % dd
    return a, dd


def main():
    P_TIMES_PP_MAX = 1500
    primes = list(sp.primerange(3, P_TIMES_PP_MAX))
    pairs = []
    for i, p in enumerate(primes):
        for pp in primes[i + 1:]:
            if p * pp > P_TIMES_PP_MAX:
                break
            pairs.append((p, pp))

    twin_total = twin_two_factor = 0
    nontwin_total = nontwin_two_factor = 0
    mismatches = []

    for p, pp in pairs:
        a, dd = crt_mixed_root(p, pp)
        S_poly = S_of(a, dd)
        Phi_p = sp.Poly(sp.cyclotomic_poly(p, q), q, domain="ZZ")
        Phi_pp = sp.Poly(sp.cyclotomic_poly(pp, q), q, domain="ZZ")
        product = Phi_p * Phi_pp
        is_two_factor = (S_poly == product)
        is_twin = (pp == p + 2)
        if is_twin:
            twin_total += 1
            if is_two_factor:
                twin_two_factor += 1
            else:
                mismatches.append((p, pp, "twin_pair_should_be_two_factor_but_isnt"))
        else:
            nontwin_total += 1
            if is_two_factor:
                nontwin_two_factor += 1
                mismatches.append((p, pp, "nontwin_pair_unexpectedly_two_factor"))

    result = {
        "p_times_pp_max": P_TIMES_PP_MAX,
        "total_pairs": len(pairs),
        "twin_pairs": twin_total,
        "twin_pairs_two_factor_tail": twin_two_factor,
        "nontwin_pairs": nontwin_total,
        "nontwin_pairs_two_factor_tail": nontwin_two_factor,
        "verdict_iff_twin": (twin_two_factor == twin_total and nontwin_two_factor == 0),
        "mismatches": mismatches,
    }
    print(result)
    return result


if __name__ == "__main__":
    main()
