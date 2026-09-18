#!/usr/bin/env python3
r"""
q-deformed bihomographic continued-fraction arithmetic (a q-Gosper engine).

This is the q-analogue of the classical bihomographic state machine. The
classical engine carries a 2x4 integer state and ingests partial quotients of x
and y by right-multiplying by the Kronecker-factored matrices P(t)=A(t)(x)I,
Q(t)=I(x)A(t) with the continued-fraction block A(t)=[[t,1],[1,0]]. Here every
integer entry is promoted to its MGO q-deformed counterpart, so the state carries
Laurent polynomials in q and the engine computes a q-deformed bilinear function
of the q-reals [x]_q and [y]_q directly from the continued fractions of x and y.

The MGO q-block (matching the qreals package's regular-CF convention exactly).
For an even-length regular continued fraction a=[a_1,...,a_{2m}] the q-real is
read off the first column of the product of 2x2 blocks over Z[q,q^{-1}]:

    A_q^{(i)}(a) = [[ [a]_q   ,  q^{ a} ],[1,0]]   at odd  positions (1-indexed),
                   [[ [a]_{1/q},  q^{-a} ],[1,0]]   at even positions,

and  [x]_q = R_x / S_x  where  (R_x, S_x)^T  is the first column of
prod_i A_q^{(i)}(a_i). This reproduces qreals.q_rational coefficient for
coefficient (verified in a separate verification harness).

Bihomographic state. With monomial columns (XY, X, Y, 1) the state
    S = [[a,b,c,d],[e,f,g,h]]   represents   z(X,Y) = (aXY+bX+cY+d)/(eXY+fX+gY+h).
Ingesting one x-quotient at position i right-multiplies by P_q = A_q^{(i)}(.)(x)I_2;
one y-quotient by Q_q = I_2(x)A_q^{(j)}(.). After full ingestion the first column
of S.(prod P_q)(prod Q_q) is S.((R_x,S_x)^T (x) (R_y,S_y)^T), so

    a_/e_  =  z([x]_q, [y]_q).

For the addition coefficients (0,1,1,0, 0,0,0,1) this is [x]_q + [y]_q; for the
multiplication coefficients (1,0,0,0, 0,0,0,1) it is [x]_q * [y]_q.

CAVEAT (the load-bearing one): this engine computes [x]_q + [y]_q (the sum of the
two q-series), NOT [x+y]_q (the q-deformation of the real sum). The MGO
deformation map x |-> [x]_q is not additive, so these differ; a separate
verification harness reports the exact deficit.
"""
from __future__ import annotations

from fractions import Fraction

import sympy as sp

q = sp.Symbol("q")


# ----------------------------------------------------------------------------
# q-integers (independent re-implementation; cross-checked against qreals)
# ----------------------------------------------------------------------------
def q_int(n: int) -> sp.Expr:
    """[n]_q = 1 + q + ... + q^{n-1} for n>0, 0 for n=0, -[ -n ]_q/q^{-n} for n<0."""
    n = int(n)
    if n == 0:
        return sp.Integer(0)
    if n > 0:
        return sum((q**i for i in range(n)), sp.Integer(0))
    return -q_int(-n) / q ** (-n)


def q_int_qinv(n: int) -> sp.Expr:
    """[n]_{q^{-1}} = q^{-(n-1)} [n]_q for n>0."""
    n = int(n)
    if n == 0:
        return sp.Integer(0)
    if n > 0:
        return q_int(n) / q ** (n - 1)
    return -q_int_qinv(-n) * q ** (-n)


# ----------------------------------------------------------------------------
# continued fractions (even-length regular CF, matching qreals)
# ----------------------------------------------------------------------------
def cf_terms(fr: Fraction) -> list[int]:
    """Regular continued-fraction partial quotients of a rational."""
    quotients = sp.continued_fraction(sp.Rational(fr.numerator, fr.denominator))
    return [int(t) for t in quotients]


def make_even_length(a: list[int]) -> list[int]:
    """Even-length regular-CF representative (qreals convention)."""
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


def q_cf(fr: Fraction) -> list[int]:
    """The even-length regular CF whose digits the q-engine ingests."""
    return make_even_length(cf_terms(fr))


# ----------------------------------------------------------------------------
# the MGO q-block and the classical block (for side-by-side reuse of the proof)
# ----------------------------------------------------------------------------
def q_block(i: int, a: int) -> sp.Matrix:
    """The MGO 2x2 q-continuant block at position i (0-indexed) with digit a.

    Position parity follows the qreals formula: 1-indexed-odd positions (i even)
    carry [a]_q with q^{a} above; 1-indexed-even positions (i odd) carry
    [a]_{1/q} with q^{-a} above. The general shape is [[alpha, beta],[1,0]] with
    (alpha, beta) the (diagonal, numerator-above) pair.
    """
    if i % 2 == 0:
        return sp.Matrix([[q_int(a), q**a], [1, 0]])
    return sp.Matrix([[q_int_qinv(a), q ** (-a)], [1, 0]])


def A_classical(t):
    """The classical CF block A(t)=[[t,1],[1,0]] (the q=1 / undeformed limit)."""
    return sp.Matrix([[t, 1], [1, 0]])


def kron(M: sp.Matrix, N: sp.Matrix) -> sp.Matrix:
    """Kronecker product in the (XY, X, Y, 1) = (X,1)(x)(Y,1) block layout."""
    return sp.Matrix(
        sp.BlockMatrix([[M[i, j] * N for j in range(M.cols)] for i in range(M.rows)])
    )


# ----------------------------------------------------------------------------
# one-variable q-engine: [x]_q from the CF of x
# ----------------------------------------------------------------------------
def q_convergent_matrix(cf: list[int]) -> sp.Matrix:
    """Product of MGO q-blocks for an even-length CF; first column is (R, S)."""
    M = sp.eye(2)
    for i, a in enumerate(cf):
        M = M * q_block(i, a)
    return M


def q_real_rational(fr: Fraction) -> sp.Expr:
    """[x]_q as a reduced rational function in q, via the q-block product."""
    M = q_convergent_matrix(q_cf(fr))
    return sp.cancel(M[0, 0] / M[1, 0])


# ----------------------------------------------------------------------------
# bihomographic q-engine: z([x]_q, [y]_q) from the CFs of x and y
# ----------------------------------------------------------------------------
# Bilinear operation coefficients in monomial order (XY, X, Y, 1), two rows.
OPS = {
    "add": (0, 1, 1, 0, 0, 0, 0, 1),   # z = X + Y      -> [x]_q + [y]_q
    "sub": (0, 1, -1, 0, 0, 0, 0, 1),  # z = X - Y      -> [x]_q - [y]_q
    "mul": (1, 0, 0, 0, 0, 0, 0, 1),   # z = X * Y      -> [x]_q * [y]_q
    "div": (0, 1, 0, 0, 0, 0, 1, 0),   # z = X / Y      -> [x]_q / [y]_q
}


def state_matrix(op: str) -> sp.Matrix:
    a, b, c, d, e, f, g, h = OPS[op]
    return sp.Matrix([[a, b, c, d], [e, f, g, h]])


def q_gosper_state(x: Fraction, y: Fraction, op: str = "add") -> sp.Matrix:
    """The 2x4 q-state after full ingestion of x's and y's q-CF quotients."""
    M = state_matrix(op)
    for i, a in enumerate(q_cf(x)):
        M = M * kron(q_block(i, a), sp.eye(2))
    for j, b in enumerate(q_cf(y)):
        M = M * kron(sp.eye(2), q_block(j, b))
    return M


def q_gosper(x: Fraction, y: Fraction, op: str = "add") -> sp.Expr:
    """The q-Gosper value z([x]_q,[y]_q): first-column ratio of the q-state.

    For op='add' this is [x]_q + [y]_q (NOT [x+y]_q -- see module docstring).
    """
    M = q_gosper_state(x, y, op)
    return sp.cancel(M[0, 0] / M[1, 0])


# ----------------------------------------------------------------------------
# Laurent-coefficient read-out (to a stated order q^M)
# ----------------------------------------------------------------------------
def q_valuation(expr: sp.Expr) -> int:
    """Lowest power of q in a Laurent rational function: val(num) - val(den)."""
    expr = sp.cancel(expr)
    if expr == 0:
        return 0
    num, den = sp.fraction(expr)
    pn = sp.Poly(sp.expand(num), q)
    pd = sp.Poly(sp.expand(den), q)
    vn = min(m[0] for m in pn.monoms()) if pn.terms() else 0
    vd = min(m[0] for m in pd.monoms()) if pd.terms() else 0
    return int(vn - vd)


def laurent_coeffs(expr: sp.Expr, hi: int, lo: int | None = None) -> tuple[int, list[int]]:
    """Integer Laurent coefficients of expr for exponents lo..hi (inclusive).

    Returns (lo, [c_lo, ..., c_hi]). If lo is None it is set to the valuation,
    so the list starts at the first possibly-nonzero coefficient. Coefficients
    are returned as ints (the MGO q-rationals have integer Laurent coefficients).
    """
    expr = sp.cancel(expr)
    if lo is None:
        lo = q_valuation(expr) if expr != 0 else 0
    n = hi - lo + 1
    if n <= 0:
        return lo, []
    shifted = sp.cancel(expr * q ** (-lo))           # now regular at q=0
    ser = shifted.series(q, 0, n).removeO()
    poly = sp.Poly(sp.expand(ser), q)
    out = []
    for k in range(n):
        coeff = poly.coeff_monomial(q**k)
        out.append(int(coeff))
    return lo, out


def taylor_coeffs(expr: sp.Expr, N: int) -> list[int]:
    """First N Taylor coefficients [c_0..c_{N-1}] (valuation assumed >= 0)."""
    _, c = laurent_coeffs(expr, N - 1, lo=0)
    return c


if __name__ == "__main__":
    # quick smoke test
    x, y = Fraction(3, 2), Fraction(13, 5)
    val = q_gosper(x, y, "add")
    print("q-Gosper [x]_q+[y]_q for x=3/2, y=13/5:")
    print("  rational function:", val)
    print("  first 8 Taylor coeffs:", taylor_coeffs(val, 8))
