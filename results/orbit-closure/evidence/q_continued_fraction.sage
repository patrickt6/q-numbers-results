"""q-continued-fraction implementation, Morier-Genoud-Ovsienko (MGO).

Computes [p/s]_q for rationals and [x]_q to N stable Taylor coefficients
for arbitrary positive reals. Uses MGO Proposition 1.1 (reals.pdf): at CF
depth n with partial-quotient sum S_n, exactly S_n - 1 power-series
coefficients of [p_n/q_n]_q agree with [x]_q. So we stop the CF at the
first depth where S_n >= N + 1.

References:
  - <path>, Part 4.3
  - <path>
  - Morier-Genoud and Ovsienko, "q-deformed rationals and q-continued
    fractions", Forum Math. Sigma 8 (2020), e13. (Definition 1.1, Prop 1.1)

Conventions:
  - [n]_q := 1 + q + q^2 + ... + q^{n-1}  for n >= 0
  - [-n]_q := -[n]_q / q^n                for n > 0  (lecture 3.2 rule)
  - [n]_{q^{-1}} := q^{-(n-1)} * [n]_q    (substitution q -> q^{-1})
  - MGO formula expects an even-length regular CF [a_1, ..., a_{2m}],
    obtained from the Euclidean output by:
      (i) absorb a trailing 1: [.., a_{k-1}, 1] -> [.., a_{k-1} + 1]
      (ii) if length is still odd, split last entry: [.., a_k] -> [.., a_k - 1, 1]
    Step (i) only fires when the CF was generated outside the canonical
    Euclidean form. Step (ii) is the workhorse.
"""

from sage.all import (
    QQ, ZZ, PolynomialRing, FractionField, LaurentSeriesRing,
    continued_fraction,
)


# Default ambient ring: rational functions in q over QQ.
R = PolynomialRing(QQ, 'q')
F = FractionField(R)
q = F.gen()


def q_int(n, ring=None, q_val=None):
    """[n]_q in `ring` (default: F). Handles n in Z."""
    n = ZZ(n)
    if ring is None:
        ring, q_val = F, q
    if n == 0:
        return ring.zero()
    if n > 0:
        return sum(q_val**i for i in range(n))
    return -q_int(-n, ring, q_val) / q_val**(-n)


def q_int_qinv(n, ring=None, q_val=None):
    """[n]_{q^{-1}} in `ring`. Equals q^{-(n-1)} * [n]_q for n > 0."""
    n = ZZ(n)
    if ring is None:
        ring, q_val = F, q
    if n == 0:
        return ring.zero()
    if n > 0:
        return q_int(n, ring, q_val) / q_val**(n - 1)
    # n < 0: [-m]_{q^{-1}} = -[m]_{q^{-1}} * q^m  (substitute q -> q^{-1} in [-m]_q)
    return -q_int_qinv(-n, ring, q_val) * q_val**(-n)


def _make_even_length(a):
    """Produce the even-length regular CF representative of a.

    Two moves (absorb / split) are applied at most once each:
      - if last entry is 1 and the absorb is meaningful, absorb it
      - if length is then odd, split last entry (which is now >= 2)

    For Euclidean output of r/s > 1 with gcd(r, s) = 1, the last entry is
    always >= 2, so only the split move ever fires.
    """
    a = list(a)
    if len(a) % 2 == 0:
        return a
    # Length is odd.
    if a[-1] >= 2:
        a[-1] -= 1
        a.append(1)
        return a
    # Last entry is 1 in an odd-length CF: absorb it (length must be >= 2).
    if len(a) >= 2 and a[-1] == 1:
        a.pop()
        a[-1] += 1
        return a
    # Length 1 with a_0 in {0, 1}: outside MGO domain (r/s = 1 or rs < 0).
    raise ValueError("cannot make even-length CF from " + str(a))


def _mgo_build(a, ring=None, q_val=None):
    """Apply the MGO formula bottom-up to even-length CF list a.

    Convention (1-indexed positions): odd positions use [a_i]_q with
    numerator q^{a_i} above; even positions use [a_i]_{q^{-1}} with
    numerator q^{-a_i} above. Innermost (position 2m, even) is
    [a_{2m}]_{q^{-1}} with no numerator below.
    """
    if ring is None:
        ring, q_val = F, q
    n = len(a)
    if n == 0:
        return ring.zero()

    def term(i, ai):
        # 1-indexed position is i + 1.
        if (i + 1) % 2 == 1:
            return q_int(ai, ring, q_val)
        return q_int_qinv(ai, ring, q_val)

    def num_above(i, ai):
        if (i + 1) % 2 == 1:
            return q_val**ai
        return q_val**(-ai)

    result = term(n - 1, a[n - 1])
    for i in range(n - 2, -1, -1):
        result = term(i, a[i]) + num_above(i, a[i]) / result
    return result


def q_rational(p, s):
    """[p/s]_q as a rational function in q, for p, s in Z, s != 0."""
    p = ZZ(p)
    s = ZZ(s)
    if s == 0:
        raise ZeroDivisionError("denominator zero")
    if p == s:
        return F.one()
    cf = continued_fraction(QQ((p, s)))
    a = _make_even_length(list(cf.quotients()))
    return _mgo_build(a)


def q_real_truncated(x, N):
    """[x]_q to first N stable Taylor coefficients, as a Laurent series.

    Uses MGO Prop 1.1: the smallest CF depth n with S_n = a_1 + ... + a_n
    >= N + 1 yields exactly S_n - 1 stable coefficients, which is >= N.
    No external "depth" parameter to tune; the CF accumulation itself
    fixes the depth.

    Args:
      x: any input accepted by sage.continued_fraction (Sage symbolic
         constant such as pi, e, sqrt(2); Sage rational; Sage real).
      N: number of stable power-series coefficients required.

    Returns:
      LaurentSeries over ZZ. The first N coefficients (from the series'
      valuation) are guaranteed stable per Prop 1.1.
    """
    L = LaurentSeriesRing(ZZ, 'q', default_prec=N + 10)
    qL = L.gen()

    cf = continued_fraction(x)
    a = []
    S = 0
    i = 0
    while S < N + 1:
        try:
            ai_raw = cf.quotient(i)
        except (IndexError, StopIteration):
            break
        ai = int(ai_raw)
        a.append(ai)
        S += ai
        i += 1

    a = _make_even_length(a)
    return _mgo_build(a, ring=L, q_val=qL)


# ----- Validation -----
# Run with: sage q_continued_fraction.sage
if __name__ == "__main__":
    print("Validating MGO q-rational implementation...\n")

    # Plan tests, lines 134-138 of WEEKEND-5090-EXPLORATION-PLAN.md.
    expected_1 = (1 + q + q**2) / (1 + q)
    actual_1 = q_rational(3, 2)
    assert actual_1 == expected_1, "q_rational(3, 2) failed: got " + str(actual_1)
    print("PASS  q_rational(3, 2) == (1 + q + q^2) / (1 + q)")

    actual_2 = q_rational(19, 7)
    assert actual_2.subs(q=1) == QQ((19, 7)), "q_rational(19, 7).subs(q=1) failed"
    print("PASS  q_rational(19, 7).subs(q=1) == 19/7")

    expected_3 = q / (1 + q)
    actual_3 = q_rational(1, 2)
    assert actual_3 == expected_3, "q_rational(1, 2) failed: got " + str(actual_3)
    print("PASS  q_rational(1, 2) == q / (1 + q)")

    # MGO Prop 1.1 sanity check using pi.
    # CF of pi starts [3, 7, 15, 1, 292], so S_5 = 318. The paper claims
    # depth 5 stabilizes 317 power-series coefficients of [pi]_q.
    from sage.all import pi as sage_pi
    cf_pi = continued_fraction(sage_pi)
    S_5 = sum(int(cf_pi.quotient(i)) for i in range(5))
    assert S_5 == 318, "sanity check failed: S_5 of pi should be 318, got " + str(S_5)
    print("PASS  S_5(pi) == 318  (matches MGO reals.pdf claim of 317 stable coeffs)")

    # End-to-end: compute [pi]_q to N=50 stable coefficients.
    qpi_50 = q_real_truncated(sage_pi, 50)
    print("OK    [pi]_q first 10 coeffs: " + str([int(qpi_50[k]) for k in range(10)]))

    # End-to-end on the worst case: phi (golden ratio).
    # CF is [1; 1, 1, ...], so S_n = n; depth needed for N stable coeffs is
    # exactly N + 1. Test small N.
    from sage.all import sqrt
    phi = (1 + sqrt(5)) / 2
    qphi_20 = q_real_truncated(phi, 20)
    assert int(qphi_20[0]) == 1, "[phi]_q constant term should be 1"
    print("OK    [phi]_q first 10 coeffs: " + str([int(qphi_20[k]) for k in range(10)]))

    print("\nAll validation tests passed.")
