r"""General-quadratic q-deformed period matrix, and the (A - D)/C test.

What this module supplies, and why it exists
--------------------------------------------
The Pell reduction (`thm:pell`, `03-pell.tex` lines 94 to 164) computes
F(d) = [sqrt d]_q + [-sqrt d]_q as the single rational function (A - D)/C,
where (A, B; C, D) = rho(Lambda) is the q-deformation of the fundamental
automorph Lambda of sqrt(d). Existing code covers only that pure-surd case:
`fastlam.lam_q_fast(d)` hard-codes Lambda = [[r, d s], [s, r]].

This module builds the same object for an ARBITRARY real quadratic
irrational x = (p + r sqrt D)/s:

  1. the Hirzebruch-Jung continued fraction of x with genuine period
     detection (`qreals.quadratic.hj_terms`),
  2. the preperiod matrix V and the period matrix W over that expansion,
  3. the automorph M = V W V^(-1) in SL(2, Z), which fixes x,
  4. its q-deformation M_q = rho(M) as exact Laurent polynomials,
  5. the candidate rational function (A - D)/C,
  6. the exact stabilized Laurent window of the true sum
     G(x) = [x]_q + [-x]_q (`qreals.negation.negation_sum_exact`),
  7. the comparison of 5 against 6, and the structural predicates
     M symmetric (a = d') and N M N = M^(-1), both at the integer level and
     at the q level in PGL(2, Z[q, q^(-1)]).

Conventions
-----------
Hirzebruch-Jung: x = c_1 - 1/(c_2 - 1/(c_3 - ...)), so each step is the
Mobius action of the block

    P(c) = [[c, -1], [1, 0]],   det P(c) = 1,

acting by x = P(c) . x_next. If hj_terms reports the state at index t equal
to the state at index t + L, then with

    V = P(c_1) ... P(c_t),      W = P(c_{t+1}) ... P(c_{t+L}),

the tail y at index t satisfies y = W . y, and x = V . y, so

    M = V W V^(-1)

fixes x. For x = 1 + sqrt 2 this returns exactly [[5, 2], [2, 1]], the
automorph recorded in `ssec:beyond-pure`. For x = sqrt d it returns the
fundamental automorph [[r, d s], [s, r]] of the +1 Pell solution.

q-deformation: rho is the isomorphism PSL(2, Z) -> PSL_q(2, Z) of
Leclere and Morier-Genoud, Proposition 1.1, sending

    R = [[1, 1], [0, 1]]  ->  R_q = [[q, 1], [0, 1]],
    S = [[0, -1], [1, 0]] ->  S_q = [[0, -q^(-1)], [1, 0]].

The word decomposition and the fast Laurent-dict evaluation of rho are
reused verbatim from `proof_verification.sl2_word` and `fastlam.rho_fast`,
so nothing about the q-deformation is reimplemented here.

Oracle
------
On pure surds x = sqrt d the automorph and its q-deformation must agree with
`fastlam.lam_q_fast(d)`. `check_oracle.py` runs that comparison.

Usage
-----
    PYTHONPATH=<path> \
        python3 qperiod.py "1+sqrt(2)"

or, as a library,

    from qperiod import analyse
    rep = analyse("1+sqrt(2)")
    rep.matches            # False
    rep.automorph          # ((5, 2), (2, 1))
    rep.intertwines        # False
"""

from __future__ import annotations

import sys
from dataclasses import dataclass, field
from fractions import Fraction

QREALS_SRC = "<path>"
ALEXCODE = "<path>"
PAPERGAPS = "<path>"
for _p in (QREALS_SRC, ALEXCODE, PAPERGAPS):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import sympy as sp  # noqa: E402

from qreals.quadratic import QuadraticIrrational, hj_terms  # noqa: E402
from qreals.negation import (  # noqa: E402
    _parse_quadratic_or_rational,
    negation_sum_exact,
)
from fastlam import p_add, p_mul, rho_fast  # noqa: E402
from proof_verification import sl2_word  # noqa: E402

q = sp.Symbol("q")

Mat = tuple[tuple[int, int], tuple[int, int]]
LDict = dict  # {exponent: int}


# ---------------------------------------------------------------------------
# integer 2x2 helpers
# ---------------------------------------------------------------------------
def mat_mul(A: Mat, B: Mat) -> Mat:
    (a, b), (c, d) = A
    (e, f), (g, h) = B
    return ((a * e + b * g, a * f + b * h), (c * e + d * g, c * f + d * h))


def mat_det(A: Mat) -> int:
    (a, b), (c, d) = A
    return a * d - b * c


def mat_inv(A: Mat) -> Mat:
    """Inverse of an integer matrix of determinant +-1."""
    (a, b), (c, d) = A
    det = mat_det(A)
    if det not in (1, -1):
        raise ValueError(f"determinant {det}, expected +-1")
    return ((d // det, -b // det), (-c // det, a // det))


def mat_neg(A: Mat) -> Mat:
    (a, b), (c, d) = A
    return ((-a, -b), (-c, -d))


IDENT: Mat = ((1, 0), (0, 1))
N_MAT: Mat = ((-1, 0), (0, 1))


def hj_block(c: int) -> Mat:
    """P(c) = [[c, -1], [1, 0]], the Hirzebruch-Jung step matrix."""
    return ((c, -1), (1, 0))


# ---------------------------------------------------------------------------
# Laurent-dict helpers, on top of fastlam's p_add / p_mul
# ---------------------------------------------------------------------------
def ldict_to_expr(p: LDict) -> sp.Expr:
    return sum((sp.Integer(c) * q**e for e, c in sorted(p.items())), sp.Integer(0))


def ldict_from_expr(expr: sp.Expr) -> LDict:
    """Laurent dict of an expression known to be a Laurent polynomial."""
    expr = sp.expand(sp.cancel(expr))
    if expr == 0:
        return {}
    num, den = sp.fraction(sp.together(expr))
    den = sp.expand(den)
    shift = 0
    scale = sp.Integer(1)
    if den.has(q):
        dp = sp.Poly(den, q)
        if not dp.is_monomial:
            raise ValueError("not a Laurent polynomial")
        shift = dp.monoms()[0][0]
        scale = dp.coeffs()[0]
    else:
        scale = den
    np_ = sp.Poly(sp.expand(num), q)
    out: LDict = {}
    for m, c in zip(np_.monoms(), np_.coeffs()):
        v = sp.nsimplify(c / scale)
        if v != 0:
            out[m[0] - shift] = int(v)
    return out


def laurent_valuation(p: LDict) -> int:
    return min(p) if p else 0


def laurent_series(num: LDict, den: LDict, n_terms: int) -> tuple[int, list[Fraction]]:
    """First n_terms Laurent coefficients of num/den, exactly, by long division.

    Returns (valuation, coefficients) with coefficients[i] the coefficient of
    q^(valuation + i). Coefficients are Fractions because the leading
    coefficient of den need not be a unit.
    """
    if not num:
        return 0, [Fraction(0)] * n_terms
    if not den:
        raise ZeroDivisionError("zero denominator")
    vn, vd = laurent_valuation(num), laurent_valuation(den)
    val = vn - vd
    d0 = Fraction(den[vd])
    # normalise: work with shifted dicts starting at exponent 0
    r = {e - vn: Fraction(c) for e, c in num.items()}
    dd = {e - vd: Fraction(c) for e, c in den.items()}
    out: list[Fraction] = []
    for k in range(n_terms):
        ck = r.get(k, Fraction(0)) / d0
        out.append(ck)
        if ck:
            for e, c in dd.items():
                if e + k < k + n_terms + 1:
                    r[e + k] = r.get(e + k, Fraction(0)) - ck * c
    return val, out


# ---------------------------------------------------------------------------
# period data for a general quadratic irrational
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class PeriodData:
    x: QuadraticIrrational
    terms: list[int]
    period_start: int
    period_length: int
    preperiod: Mat  # V
    period: Mat  # W
    automorph: Mat  # M = V W V^(-1)

    @property
    def periodic_word(self) -> list[int]:
        return self.terms[self.period_start : self.period_start + self.period_length]


def fixes(M: Mat, x: QuadraticIrrational) -> bool:
    """Exact test of M . x = x, i.e. c x^2 + (d - a) x - b = 0."""
    (a, b), (c, d) = M
    # x = (p + r sqrt D)/s, so x^2 = (p^2 + r^2 D + 2 p r sqrt D)/s^2.
    p, r, s, D = x.p, x.r, x.s, x.D
    # multiply the quadratic through by s^2
    rat = c * (p * p + r * r * D) + (d - a) * p * s - b * s * s
    irr = c * (2 * p * r) + (d - a) * r * s
    return rat == 0 and irr == 0


def period_data(x: QuadraticIrrational, max_terms: int = 400) -> PeriodData:
    """HJ expansion, preperiod matrix, period matrix and automorph of x."""
    terms, start, length = hj_terms(x, max_terms)
    if start is None or length is None:
        raise ValueError(f"no HJ period found for {x} within {max_terms} terms")
    V: Mat = IDENT
    for c in terms[:start]:
        V = mat_mul(V, hj_block(c))
    W: Mat = IDENT
    for c in terms[start : start + length]:
        W = mat_mul(W, hj_block(c))
    M = mat_mul(mat_mul(V, W), mat_inv(V))
    if not fixes(M, x):
        raise AssertionError(f"automorph {M} does not fix {x}")
    return PeriodData(x, terms, start, length, V, W, M)


# ---------------------------------------------------------------------------
# q-deformation of a general automorph
# ---------------------------------------------------------------------------
def rho_q(M: Mat) -> tuple[LDict, LDict, LDict, LDict]:
    """rho(M) = (A, B, C, D) as Laurent dicts, for M in SL(2, Z).

    Delegates the word decomposition to `proof_verification.sl2_word` and the
    evaluation to `fastlam.rho_fast`, so this is the same map the pure-surd
    code uses, applied to a general automorph.
    """
    if mat_det(M) != 1:
        raise ValueError(f"rho needs determinant 1, got {mat_det(M)}")
    word = sl2_word([[M[0][0], M[0][1]], [M[1][0], M[1][1]]])
    return rho_fast(word)


def rho_check_at_one(Mq: tuple[LDict, LDict, LDict, LDict], M: Mat) -> bool:
    """rho is a homomorphism, so setting q = 1 recovers M up to sign."""
    vals = tuple(sum(p.values()) for p in Mq)
    target = (M[0][0], M[0][1], M[1][0], M[1][1])
    return vals == target or vals == tuple(-t for t in target)


def ad_over_c(Mq: tuple[LDict, LDict, LDict, LDict]) -> sp.Expr:
    """The Pell-reduction candidate (A - D)/C, cancelled."""
    A, B, C, D = Mq
    num = ldict_to_expr(p_add(A, D, scale=-1))
    den = ldict_to_expr(C)
    if den == 0:
        raise ZeroDivisionError("C = 0")
    return sp.cancel(num / den)


def is_laurent_poly(expr: sp.Expr) -> bool:
    try:
        ldict_from_expr(expr)
    except ValueError:
        return False
    return True


# ---------------------------------------------------------------------------
# structural predicates: the N M N = M^(-1) question (attack 1)
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class Structure:
    symmetric: bool  # a = d'
    intertwines_z: bool  # N M N = M^(-1) in SL(2, Z), up to sign
    intertwines_q: bool  # (N M N)_q = (M_q)^(-1) in PGL(2, Z[q, q^-1])
    conjugate_matrix: Mat  # N M N


def structure(M: Mat) -> Structure:
    NMN = mat_mul(mat_mul(N_MAT, M), N_MAT)
    Minv = mat_inv(M)
    sym = M[0][0] == M[1][1]
    inter_z = NMN == Minv or NMN == mat_neg(Minv)
    # q level: compare rho(N M N) with the adjugate of rho(M), projectively.
    inter_q = False
    if mat_det(NMN) == 1:
        A2, B2, C2, D2 = rho_q(NMN)
        A, B, C, D = rho_q(M)
        adj = (D, {e: -c for e, c in B.items()}, {e: -c for e, c in C.items()}, A)
        inter_q = _proportional((A2, B2, C2, D2), adj)
    return Structure(sym, inter_z, inter_q, NMN)


def _proportional(P: tuple[LDict, ...], Q: tuple[LDict, ...]) -> bool:
    """True if P = lambda Q for a single Laurent monomial or rational lambda."""
    ratio = None
    for a, b in zip(P, Q):
        ea, eb = ldict_to_expr(a), ldict_to_expr(b)
        if ea == 0 and eb == 0:
            continue
        if ea == 0 or eb == 0:
            return False
        r = sp.cancel(ea / eb)
        if ratio is None:
            ratio = r
        elif sp.simplify(r - ratio) != 0:
            return False
    return ratio is not None


# ---------------------------------------------------------------------------
# the comparison
# ---------------------------------------------------------------------------
@dataclass
class Report:
    repr_: str
    x: QuadraticIrrational
    period: PeriodData
    automorph: Mat
    Mq: tuple[LDict, LDict, LDict, LDict]
    candidate: sp.Expr  # (A - D)/C
    candidate_is_laurent: bool
    candidate_at_one: sp.Expr  # (A - D)/C at q = 1; must be 0 for any valid formula
    struct: Structure
    window_valuation: int
    window: dict[int, Fraction]  # the locked G(x) = [x]_q + [-x]_q window
    window_verdict: str
    locked_depth: int
    candidate_coeffs: dict[int, Fraction]
    matches: bool
    first_mismatch: int | None
    compared_degrees: int
    notes: list[str] = field(default_factory=list)


def analyse(x_repr: str, depth: int = 120, min_zero_run: int = 30) -> Report:
    """Full period-matrix report for the quadratic irrational x_repr.

    Computes the automorph, its q-deformation, the candidate (A - D)/C, the
    locked exact window of G(x) = [x]_q + [-x]_q, and their comparison, plus
    the two structural predicates.
    """
    kind, value = _parse_quadratic_or_rational(x_repr)
    if kind != "quadratic":
        raise ValueError(f"{x_repr} is rational; this routine is for quadratic irrationals")
    x = value
    pd = period_data(x)
    M = pd.automorph
    Mq = rho_q(M)
    notes: list[str] = []
    if not rho_check_at_one(Mq, M):
        notes.append("WARNING: rho(M)|_{q=1} does not recover M up to sign")
    cand = ad_over_c(Mq)
    cand_laurent = is_laurent_poly(cand)
    st = structure(M)

    res = negation_sum_exact(x_repr, depth=depth, min_zero_run=min_zero_run)
    window = {d: Fraction(c) for d, c in res.locked_coefficients.items()}
    lo = min(window) if window else 0
    n_terms = len(window)

    # Laurent expansion of the candidate over the same degree range.
    num, den = sp.fraction(sp.together(cand))
    nd = ldict_from_expr(sp.expand(num))
    dd = ldict_from_expr(sp.expand(den))
    cval, ccoef = laurent_series(nd, dd, max(n_terms, 1) + max(0, lo - (laurent_valuation(nd) - laurent_valuation(dd))) + 8)
    cand_coeffs = {cval + i: c for i, c in enumerate(ccoef)}

    degrees = sorted(d for d in window if d in cand_coeffs or d < cval)
    first_mismatch = None
    compared = 0
    for d in degrees:
        compared += 1
        cw = window[d]
        cc = cand_coeffs.get(d, Fraction(0)) if d >= cval else Fraction(0)
        if cw != cc:
            first_mismatch = d
            break
    matches = first_mismatch is None and compared > 0
    # Guard: never report a match on a partially covered window. If the
    # candidate expansion stops below the top of the locked window, the
    # untested degrees are exactly where a discrepancy would hide.
    if window:
        top_window = max(window)
        top_cand = cval + len(ccoef) - 1
        if top_cand < top_window:
            matches = False
            notes.append(
                f"candidate expansion covers only up to q^{top_cand} but the window "
                f"reaches q^{top_window}; match suppressed as unverified"
            )

    return Report(
        repr_=x_repr,
        x=x,
        period=pd,
        automorph=M,
        Mq=Mq,
        candidate=cand,
        candidate_is_laurent=cand_laurent,
        candidate_at_one=sp.simplify(sp.limit(cand, q, 1)),
        struct=st,
        window_valuation=lo,
        window=window,
        window_verdict=res.verdict,
        locked_depth=res.locked_depth,
        candidate_coeffs=cand_coeffs,
        matches=matches,
        first_mismatch=first_mismatch,
        compared_degrees=compared,
        notes=notes,
    )


# ---------------------------------------------------------------------------
# rational-function reconstruction: is the window ANY low-degree P/Q?
# ---------------------------------------------------------------------------
def rational_reconstruct(
    window: dict[int, Fraction], max_deg: int, holdout: int = 6
) -> tuple[bool, sp.Expr | None, int | None]:
    """Does a rational function P/Q with deg P, deg Q <= max_deg fit the window?

    The window is a set of exact Laurent coefficients of G. Writing
    G = P / Q with P of degree <= m and Q of degree <= n (after clearing the
    valuation so the series starts at q^0), the condition G Q - P = O(q^K)
    is linear in the unknown coefficients. The system is solved exactly over
    Q using the first K = len(window) - holdout coefficients, and any solution
    is then verified against the held-out coefficients. Returns
    (found, expr, degree) where degree is the smallest max_deg that worked;
    the caller sweeps max_deg upward.

    A negative answer at max_deg = 18 rules out, in particular, every
    candidate built as a ratio of entries of M_q and (N M N)_q whose numerator
    and denominator degrees are at most 18, since any such candidate IS a
    rational function of that degree.

    Method. Shift the window down by its valuation so the series starts at
    q^0: ser_0, ser_1, ... With G = P/Q, deg P <= m, deg Q <= n, the identity
    G Q = P forces, for every k > m,

        sum_{j=0}^{n} u_j ser_{k-j} = 0,

    a homogeneous Toeplitz system in the n + 1 unknown denominator
    coefficients u_j alone. Its nullspace is computed exactly over Q. A
    trivial nullspace is a proof (relative to the window, which consists of
    certified coefficients) that no such P/Q exists. A nontrivial nullspace
    yields candidate denominators, each of which determines P and is then
    verified against the full window including the held-out coefficients.
    """
    if not window:
        return False, None, None
    nz = [d for d in sorted(window) if window[d] != 0]
    if not nz:
        return True, sp.Integer(0), 0
    # Anchor at the true valuation, not at the window floor: leading zeros in
    # the window would otherwise inflate the reported numerator degree by the
    # gap between the window floor and the valuation.
    lo = nz[0]
    hi = max(window)
    n_coef = hi - lo + 1
    ser = [window.get(lo + i, Fraction(0)) for i in range(n_coef)]
    use = n_coef - holdout
    m = n = max_deg
    n_eq = use - m - 1
    if n_eq < n + 1:
        return False, None, None  # not enough certified coefficients to decide
    rows = []
    for k in range(m + 1, use):
        rows.append([sp.Rational(ser[k - j]) if 0 <= k - j < n_coef else sp.Integer(0) for j in range(n + 1)])
    Mx = sp.Matrix(rows)
    ns = Mx.nullspace()
    if not ns:
        return False, None, None
    for vec in ns:
        u = [sp.nsimplify(vec[j]) for j in range(n + 1)]
        qexpr = sp.expand(sum(u[j] * q**j for j in range(n + 1)))
        if qexpr == 0:
            continue
        pcoef = [sum(u[j] * ser[k - j] for j in range(min(n, k) + 1)) for k in range(m + 1)]
        pexpr = sp.expand(sum(pcoef[k] * q**k for k in range(m + 1)))
        g = sp.cancel(pexpr / qexpr * q**lo)
        num, den = sp.fraction(sp.together(g))
        try:
            nd = ldict_from_expr(sp.expand(num))
            dd = ldict_from_expr(sp.expand(den))
        except ValueError:
            continue
        if not dd:
            continue
        val, coef = laurent_series(nd, dd, n_coef + 4)
        ok = all(
            window.get(d, Fraction(0))
            == (coef[d - val] if 0 <= d - val < len(coef) else Fraction(0))
            for d in window
        )
        if ok:
            return True, sp.cancel(g), max_deg
    return False, None, None


def rational_search(window: dict[int, Fraction], max_deg: int = 18, holdout: int = 6):
    """Sweep degrees 1..max_deg for a rational fit; return the first success."""
    for deg in range(1, max_deg + 1):
        found, expr, d = rational_reconstruct(window, deg, holdout=holdout)
        if found:
            return True, expr, d
    return False, None, None


# ---------------------------------------------------------------------------
# rendering
# ---------------------------------------------------------------------------
def format_report(rep: Report) -> str:
    L = []
    L.append(f"x                 = {rep.repr_}   ({rep.x!r}, decimal {rep.x.decimal():.10f})")
    L.append(
        f"HJ expansion      = {rep.period.terms[: rep.period.period_start]} then "
        f"{rep.period.periodic_word} repeating "
        f"(period_start {rep.period.period_start}, period_length {rep.period.period_length})"
    )
    (a, b), (c, d) = rep.automorph
    L.append(f"automorph M       = [[{a}, {b}], [{c}, {d}]]   det {mat_det(rep.automorph)}")
    L.append(f"M symmetric (a=d) = {rep.struct.symmetric}")
    L.append(f"N M N = M^-1 (Z)  = {rep.struct.intertwines_z}")
    L.append(f"(NMN)_q = M_q^-1  = {rep.struct.intertwines_q}")
    A, B, C, D = rep.Mq
    L.append(f"A                 = {sp.factor(ldict_to_expr(A))}")
    L.append(f"B                 = {sp.factor(ldict_to_expr(B))}")
    L.append(f"C                 = {sp.factor(ldict_to_expr(C))}")
    L.append(f"D                 = {sp.factor(ldict_to_expr(D))}")
    L.append(f"(A - D)/C         = {sp.factor(rep.candidate)}")
    L.append(f"  is Laurent poly = {rep.candidate_is_laurent}")
    L.append(f"  at q = 1        = {rep.candidate_at_one}   (must be 0, since G(x)|_(q=1) = x + (-x) = 0)")
    L.append(
        f"G(x) window       = {len(rep.window)} exact locked coefficients from q^{rep.window_valuation}, "
        f"verdict {rep.window_verdict}, locked_depth {rep.locked_depth}"
    )
    L.append(f"(A - D)/C == G(x) = {rep.matches}")
    if not rep.matches:
        L.append(f"  first mismatch at degree q^{rep.first_mismatch}")
        d = rep.first_mismatch
        if d is not None:
            L.append(f"    G(x) coefficient      = {rep.window.get(d, 0)}")
            L.append(f"    (A - D)/C coefficient = {rep.candidate_coeffs.get(d, 0)}")
    for note in rep.notes:
        L.append(f"NOTE: {note}")
    return "\n".join(L)


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print(__doc__)
        print("usage: python3 qperiod.py '<quadratic irrational>' [--degree 18]")
        return 1
    x_repr = argv[1]
    max_deg = 18
    if "--degree" in argv:
        max_deg = int(argv[argv.index("--degree") + 1])
    rep = analyse(x_repr)
    print(format_report(rep))
    if not rep.matches and "--search" in argv:
        print(f"\nrational-function search to degree {max_deg} ...")
        found, expr, deg = rational_search(rep.window, max_deg=max_deg)
        if found:
            print(f"  FIT at degree {deg}: {sp.factor(expr)}")
        else:
            print(f"  no rational function of numerator and denominator degree <= {max_deg} fits")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
