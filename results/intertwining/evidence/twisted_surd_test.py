"""Exact test of conj:quadratic-64 on the "twisted pure surd" family x = sqrt(m/n).

Background (full derivation in WRITEUP.md in this folder). The Pell reduction
proof (03-pell.tex, thm:pell) only uses one algebraic fact about the
fundamental automorph Lambda = [[a,b],[c,d']] of the fixed quadratic
irrational: the intertwining relation N Lambda N = Lambda^{-1}, which holds
exactly when a = d' (equal diagonal). For Lambda = [[r, d*s],[s, r]], the
fundamental automorph of sqrt(d), a = d' = r automatically.

The equal-diagonal condition a = d' forces the fixed point of Lambda to solve
c*x^2 = b, i.e. x = sqrt(b/c) for a RATIONAL b/c, not only for an integer d.
Concretely, for any coprime positive integers m, n with n > 1 and m*n not a
perfect square, the matrix

    M = [[r, m*s], [n*s, r]],   (r, s) the fundamental solution of r^2 - (mn) s^2 = 1

is an SL(2,Z) automorph fixing x = sqrt(m/n), an "off-axis" quadratic
irrational not of the form +-sqrt(d) for any integer d (n > 1 makes
sqrt(m/n) a value distinct from sqrt(any integer)). Because a = d' = r by
construction, M satisfies N M N = M^{-1} exactly, so the SAME proof as
thm:pell (letter for letter: negation-at-rationals, intertwining,
equivariance, Cayley-Hamilton, MGO convergence) gives

    [x]_q + [-x]_q = (A - D) / C          exactly,

where Lambda_q = rho(M) = [[A, B], [C, D]] and rho is the same
PSL(2,Z) -> PSL_q(2,Z) homomorphism used throughout the paper.

This is NOT a re-run of the forbidden "extend Pell reduction to a general
period matrix" route: it never touches a matrix with a != d'. It is a
targeted search inside the one sub-family where the theorem's OWN hypothesis
(a = d') already holds by construction, asking whether that sub-family
contains anything besides the pure surds already covered by the paper.

Every claim offered as a CERTIFICATE (not a window artifact) is checked by
exact integer/rational/polynomial arithmetic: Pell solving over Python ints,
SL(2,Z) word decomposition, a collected-coefficient-dict Laurent-polynomial
rho (no truncation, no sympy blowup), and sympy.cancel-based divisibility. No
truncation length appears anywhere in the certificate path. The
convergent-membership check additionally confirms M.infinity is a genuine
regular-continued-fraction convergent of x, the fact the "passage to the
irrational" step of thm:pell's proof needs from MGO's convergence theorem;
that check is exact (fraction equality against a symbolically computed
periodic continued fraction), not a numeric window.

Depends on stdlib + sympy, plus READ-ONLY imports of three existing,
already-validated scripts (nothing in them is executed with side effects,
nothing in them is modified):
    <path>               (G, is_laurent_poly, pell_plus1)
    <path>  (sl2_word: fast, pure integer)
    <path>             (rho_fast: collected-dict rho,
                                                                 avoids the sympy-simplify blowup
                                                                 fastlam.py's own docstring
                                                                 documents for long SL(2,Z) words)
"""
from __future__ import annotations

import sys
from dataclasses import dataclass
from fractions import Fraction
from math import gcd, isqrt

ALEXEMAIL_CODE = "<path>"
PAPERGAPS_CODE = "<path>"
for _p in (ALEXEMAIL_CODE, PAPERGAPS_CODE):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import sympy as sp  # noqa: E402

from qcore import q, G, is_laurent_poly, pell_plus1  # noqa: E402
from proof_verification import sl2_word  # noqa: E402
from fastlam import rho_fast, mat2_mul  # noqa: E402


def is_perfect_square(n: int) -> bool:
    if n < 0:
        return False
    r = isqrt(n)
    return r * r == n


def dict_to_expr(d: dict) -> sp.Expr:
    if not d:
        return sp.Integer(0)
    return sp.together(sum(c * q**e for e, c in d.items()))


@dataclass
class Candidate:
    m: int
    n: int

    def __post_init__(self) -> None:
        if self.m <= 0 or self.n <= 0:
            raise ValueError("m, n must be positive")
        if gcd(self.m, self.n) != 1:
            raise ValueError(f"m={self.m}, n={self.n} not coprime")
        if self.n == 1:
            raise ValueError("n = 1 is the already-known pure-surd case, not off-axis")
        if is_perfect_square(self.m * self.n):
            raise ValueError(f"m*n = {self.m * self.n} is a perfect square; x is rational")

    @property
    def mn(self) -> int:
        return self.m * self.n

    def label(self) -> str:
        return f"sqrt({self.m}/{self.n})"


@dataclass
class CandidateResult:
    cand: Candidate
    r: int
    s: int
    word_len: int
    laurent: bool
    pred: sp.Expr
    matches_route_b: bool
    constant_k123: bool
    convergent_ok: bool


def regular_cf_convergents(m: int, n: int, num_terms: int = 80) -> list[Fraction]:
    """Exact regular continued-fraction convergents of sqrt(m/n) = sqrt(mn)/n.

    Uses sympy's exact (integer-only) periodic-continued-fraction routine for
    (p + sqrt(d))/q with p=0, q=n, d=m*n. Requires q | (d - p^2), satisfied
    here since n | m*n.
    """
    d = m * n
    terms = sp.continued_fraction_periodic(0, n, d)
    seq: list[int] = []
    for t in terms:
        if isinstance(t, (list, tuple)):
            period = list(t)
            if not period:
                break
            while len(seq) < num_terms:
                seq.extend(period)
        else:
            seq.append(int(t))
        if len(seq) >= num_terms:
            break
    seq = seq[:num_terms]
    convs = list(sp.continued_fraction_convergents(seq))
    out = []
    for c in convs:
        c = sp.nsimplify(c)
        num, den = sp.fraction(c)
        out.append(Fraction(int(num), int(den)))
    return out


def test_candidate(cand: Candidate, k_check=(1, 2, 3), cf_terms: int = 80) -> CandidateResult:
    r, s = pell_plus1(cand.mn)
    M_int = [[r, cand.m * s], [cand.n * s, r]]

    # --- algebraic gatekeeper: equal diagonal, det 1, N M N == M^{-1} exactly ---
    a, b, c, dprime = M_int[0][0], M_int[0][1], M_int[1][0], M_int[1][1]
    assert a == dprime, "equal-diagonal hypothesis failed unexpectedly"
    det = a * dprime - b * c
    assert det == 1, ("det != 1", cand, det)
    # N M N = [[a,-b],[-c,d']]; M^{-1} = [[d',-b],[-c,a]] since det=1. Equal iff a=d'.

    # --- exact fixed-point check: M fixes x = sqrt(m/n) (c x^2 - b = 0 <=> x^2=m/n) ---
    assert c * cand.m == b * cand.n, "M does not fix sqrt(m/n)"

    # --- rho(M) via the collected-dict backend (avoids sympy-simplify blowup) ---
    w = sl2_word(sp.Matrix(M_int))
    A, B, C, D = rho_fast(w)

    # homomorphism sanity: evaluate the dicts at q=1, should recover +-M
    def ev1(d_):
        return sum(d_.values())

    chk = [[ev1(A), ev1(B)], [ev1(C), ev1(D)]]
    assert chk == M_int or chk == [[-x for x in row] for row in M_int], (
        "rho_fast homomorphism check failed", cand, chk, M_int
    )

    Aexpr, Bexpr, Cexpr, Dexpr = (dict_to_expr(A), dict_to_expr(B), dict_to_expr(C), dict_to_expr(D))
    pred = sp.cancel((Aexpr - Dexpr) / Cexpr)
    laurent = is_laurent_poly(pred)

    # --- Cayley-Hamilton constancy across k in k_check, using the same dict engine ---
    ok = []
    Lk = ({0: 1}, {}, {}, {0: 1})
    Lq = (A, B, C, D)
    k_done = 0
    for k in range(1, max(k_check) + 1):
        Lk = mat2_mul(Lk, Lq)
        k_done = k
        if k in k_check:
            Ak, Ck, Dk = dict_to_expr(Lk[0]), dict_to_expr(Lk[2]), dict_to_expr(Lk[3])
            gk = sp.cancel((Ak - Dk) / Ck)
            ok.append(sp.cancel(gk - pred) == 0)
    constant_k123 = all(ok)

    # --- independent cross-check via Route B (T/S rules only, no continuants) ---
    rs_frac = Fraction(r, cand.n * s)
    gind = G(rs_frac)
    matches_route_b = sp.cancel(gind - pred) == 0

    # --- convergent-membership: is r/(n s) a genuine CF convergent of x? ---
    convs = regular_cf_convergents(cand.m, cand.n, num_terms=cf_terms)
    convergent_ok = rs_frac in convs

    return CandidateResult(
        cand=cand, r=r, s=s, word_len=len(w), laurent=laurent, pred=pred,
        matches_route_b=matches_route_b, constant_k123=constant_k123,
        convergent_ok=convergent_ok,
    )


def summarize(res: CandidateResult) -> str:
    c = res.cand
    certified = res.laurent and res.matches_route_b and res.constant_k123 and res.convergent_ok
    if res.laurent and not certified:
        status = "LAURENT BUT UNCERTIFIED (sanity check failed, investigate before trusting)"
    elif res.laurent:
        status = "CERTIFIED FINITE -- COUNTEREXAMPLE"
    else:
        status = "not Laurent (infinite); consistent with the conjecture"
    return (
        f"x={c.label()}  (r,s)=({res.r},{res.s})  mn={c.mn}  word_len={res.word_len}\n"
        f"  Laurent: {res.laurent}   RouteB match: {res.matches_route_b}   "
        f"k=1,2,3 constant: {res.constant_k123}   r/(ns) is CF convergent: {res.convergent_ok}\n"
        f"  (A-D)/C = {sp.factor(res.pred)}\n"
        f"  verdict: {status}\n"
    )


if __name__ == "__main__":
    import argparse

    ap = argparse.ArgumentParser()
    ap.add_argument("--m", type=int)
    ap.add_argument("--n", type=int)
    args = ap.parse_args()
    if args.m and args.n:
        cand = Candidate(args.m, args.n)
        res = test_candidate(cand)
        print(summarize(res))
    else:
        for m, n in [(5, 2), (7, 3), (2, 5)]:
            try:
                cand = Candidate(m, n)
            except ValueError as e:
                print(f"skip m={m},n={n}: {e}")
                continue
            res = test_candidate(cand)
            print(summarize(res))
