"""
Clean-room Pell-equation solver (from the continued fraction of sqrt(d)),
plus convergent-based independent computation of F(d) = lim G(x_n), and
comparison against G(r_d/s_d). Written from scratch, no existing project
code consulted.
"""
import sympy as sp
from mgo import q, G, qint, mgo_qrational

import math


def cf_sqrt_terms(d, num_terms):
    """Return the first num_terms terms [a0,a1,...] of the (periodic)
    regular continued fraction of sqrt(d), for nonsquare integer d>0,
    via the standard m,den,a recurrence."""
    a0 = int(math.isqrt(d))
    assert a0 * a0 != d, "d must be a nonsquare"
    terms = [a0]
    m, den, a = 0, 1, a0
    while len(terms) < num_terms:
        m = den * a - m
        den = (d - m * m) // den
        a = (a0 + m) // den
        terms.append(a)
    return terms


def convergents(terms):
    """Given CF terms [a0,a1,...,aN], return list of (p_k,q_k) for
    k=0..N (standard convergent recurrence)."""
    convs = []
    p_prev2, p_prev1 = 1, 0  # p_{-2}, p_{-1}  (using shifted indices)
    q_prev2, q_prev1 = 0, 1
    # Actually use conventional indexing: p_{-1}=1,p_{-2}=0, q_{-1}=0,q_{-2}=1
    p_m1, p_m2 = 1, 0
    q_m1, q_m2 = 0, 1
    for a in terms:
        p = a * p_m1 + p_m2
        qk = a * q_m1 + q_m2
        convs.append((p, qk))
        p_m2, p_m1 = p_m1, p
        q_m2, q_m1 = q_m1, qk
    return convs


def fundamental_pell_plus1(d, max_terms=200):
    """Brute-force (but exact, self-verifying) search over CF convergents
    of sqrt(d) for the FIRST one satisfying r^2 - d*s^2 == 1. This is
    guaranteed by CF/Pell theory to be the fundamental solution, and
    sidesteps any period-parity off-by-one bugs since we verify directly."""
    terms = cf_sqrt_terms(d, max_terms)
    convs = convergents(terms)
    for k, (p, qk) in enumerate(convs):
        val = p * p - d * qk * qk
        if val == 1:
            assert p * p - d * qk * qk == 1
            return p, qk, k, terms[:k + 1]
    raise RuntimeError(f"no fundamental +1 solution found within {max_terms} terms for d={d}")


def laurent_coeffs(expr, qq, lo=-30, hi=30):
    """Compute the coefficient dict {power: coeff} of the Laurent expansion
    of a rational function `expr` in variable qq, about qq=0, covering
    powers lo..hi. Handles genuine poles at 0 (finite negative order) via
    sympy's series/Laurent machinery; assumes no essential singularities
    (expr is a ratio of polynomials, guaranteed here)."""
    expr = sp.cancel(sp.together(expr))
    num, den = sp.fraction(expr)
    num = sp.Poly(num, qq)
    den = sp.Poly(den, qq)
    # factor out the qq^k common trailing power to expose any pole at 0
    num_lo_deg = min(m[0] for m in num.monoms())
    den_lo_deg = min(m[0] for m in den.monoms())
    shift = num_lo_deg - den_lo_deg
    num_reduced = sp.Poly(sp.cancel(num.as_expr() / qq**num_lo_deg), qq)
    den_reduced = sp.Poly(sp.cancel(den.as_expr() / qq**den_lo_deg), qq)
    # now den_reduced(0) != 0 by construction -> ordinary power series exists
    assert den_reduced.eval(0) != 0
    need_hi = hi - shift + 1  # number of power-series coeffs c_0..c_{need_hi-1}
    if need_hi < 1:
        need_hi = 1

    # Exact power-series division N(qq)/D(qq) with D(0) != 0, done by the
    # standard coefficient recurrence over exact rationals (no sympy series,
    # no floats, no truncation error):
    #     c_k = ( n_k - sum_{j=1..k} d_j * c_{k-j} ) / d_0
    N = num_reduced.all_coeffs()[::-1]   # ascending: n_0, n_1, ...
    D = den_reduced.all_coeffs()[::-1]   # ascending: d_0, d_1, ...
    d0 = sp.Rational(D[0])
    assert d0 != 0
    c = []
    for k in range(need_hi):
        n_k = sp.Rational(N[k]) if k < len(N) else sp.Integer(0)
        acc = n_k
        for j in range(1, min(k, len(D) - 1) + 1):
            acc -= sp.Rational(D[j]) * c[k - j]
        c.append(sp.cancel(acc / d0))

    result = {}
    for p_ in range(lo, hi + 1):
        idx = p_ - shift   # power p_ of qq corresponds to series index p_-shift
        if 0 <= idx < len(c):
            result[p_] = sp.nsimplify(c[idx])
        else:
            result[p_] = sp.Integer(0)
    return result


def window_str(coeffs, lo=-30, hi=30):
    return tuple(coeffs[p_] for p_ in range(lo, hi + 1))


if __name__ == "__main__":
    # sanity check: d=2
    for d in [2, 3, 5]:
        r, s, k, terms = fundamental_pell_plus1(d)
        print(f"d={d}: fundamental (r,s)=({r},{s}) at convergent index {k}, "
              f"CF terms used={terms}, check r^2-d*s^2={r*r-d*s*s}")
