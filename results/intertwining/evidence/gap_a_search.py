"""Wide search for a Gap A violation: a nonzero-trace automorph satisfying
fable's rationality criterion (P).

Background. `attempts/fable/characterization.tex` (theorem summarized in the
coordinator's relay message) proves: if `G(x) = [x]_q + [-x]_q` is a rational
function of q at all, then, writing `Mq = rho(automorph of x) = [[A,B],[C,D]]`
and `det(Mq) = q^m`,

    (P):   q^(m+1) * C(1/q) = +- C(q)          exactly, as an identity in q.

This is NECESSARY for finiteness, checkable directly from the automorph with
no series, no window, and no reference to G(x) itself. Fable's own scan found
(P) holds if and only if the automorph is trace-zero (a = d), on 4072
positive R/L words (length 2..11, both letters present) and 336 quadratic
forms (A in 1..6, B,C in -6..6). That equivalence is NOT proved in general;
it is Gap A. This script searches wider for a violation: a NONZERO-trace
automorph where (P) holds anyway. Finding one would reopen the only-if
direction of `conj:quadratic-64` (a genuine damaging counterexample-shape
result, per the coordinator's relay); finding none over a documented wider
box is negative evidence, not a proof, and is reported as such.

Everything here is pure-integer / Laurent-dict arithmetic (no sympy in the
hot path): `fast_word.sl2_word_fast` for the SL(2,Z) word, `fastlam.rho_fast`
(already validated elsewhere in this tree) for the q-deformation, and a
direct dict-level determinant + criterion check. This is cheaper per
candidate than anything in `broad_sweep.py`, since it never computes or
cancels (A-D)/C, only the single entry C and the determinant exponent m.

Two search modes, both wider than fable's boxes:

  - `word_scan`: exhaustive over words in {R, L} (single-step generators,
    R=[[1,1],[0,1]], L=[[1,0],[1,1]]) containing both letters, up to a length
    bound well past fable's 11 (default 20, exhaustive; 2^20 ~ 1e6 is the
    practical ceiling for exhaustive enumeration at this cost per candidate).
  - `form_scan`: primitive binary quadratic forms (A, B, C), nonsquare
    positive discriminant, over a box well past fable's A in 1..6, B,C in
    -6..6 (default A in 1..40, B in -40..40 with B != 0 so every case is
    genuinely nonzero-trace, C in -40..40).

Requires no PYTHONPATH (imports only from this folder and read-only from
`attempts/opus`, `attempts/fable` is not imported here since its verify.py
runs as a top-level script; the small pieces needed are reimplemented).
"""
from __future__ import annotations

import itertools
import sys
import time
from math import gcd, isqrt

FALSIFY_DIR = "<path>"
PAPERGAPS_CODE = "<path>"
for _p in (FALSIFY_DIR, PAPERGAPS_CODE):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from fast_word import sl2_word_fast, mat_mul as _mat_mul  # noqa: E402
from fastlam import rho_fast, p_add, p_mul  # noqa: E402

Mat = tuple[tuple[int, int], tuple[int, int]]
LDict = dict


def mat_mul(A: Mat, B: Mat) -> Mat:
    return _mat_mul(A, B)


def det_exponent(A: LDict, B: LDict, C: LDict, D: LDict) -> tuple[int, int] | None:
    """det(Mq) = A*D - B*C; return (m, sign) if it is +-q^m, else None."""
    det = p_add(p_mul(A, D), p_mul(B, C), scale=-1)
    if len(det) != 1:
        return None
    (e, c), = det.items()
    if c == 1:
        return e, 1
    if c == -1:
        return e, -1
    return None


def criterion_holds(C: LDict, m: int) -> tuple[bool, int | None]:
    """(P): q^(m+1) C(1/q) = +- C(q). Returns (holds, sign) purely by dict
    comparison (substituting q -> 1/q is negating every exponent; multiplying
    by q^(m+1) is shifting every exponent by m+1)."""
    if not C:
        return False, None
    shifted = {(-e) + (m + 1): c for e, c in C.items()}
    if shifted == C:
        return True, 1
    if shifted == {e: -c for e, c in C.items()}:
        return True, -1
    return False, None


def automorph_criterion(M: Mat) -> tuple[bool, int | None, int | None]:
    """(criterion_holds, sign, m) for the automorph M in SL(2,Z)."""
    a, b = M[0]
    c, d = M[1]
    if a * d - b * c != 1:
        raise ValueError(f"not SL(2,Z): det={a * d - b * c}")
    word = sl2_word_fast(M)
    A, B, C, D = rho_fast(word)
    de = det_exponent(A, B, C, D)
    if de is None:
        return False, None, None
    m, _sign_det = de
    holds, sign = criterion_holds(C, m)
    return holds, sign, m


# ---------------------------------------------------------------------------
# word scan: R, L generators, exhaustive over both-letter words up to length N
# ---------------------------------------------------------------------------
R_MAT: Mat = ((1, 1), (0, 1))
L_MAT: Mat = ((1, 0), (1, 1))


def word_scan(max_len: int, min_len: int = 2, time_budget_s: float | None = None):
    """Exhaustive scan over {R,L}^n, min_len <= n <= max_len, both letters present."""
    violations = []
    tested = 0
    t0 = time.time()
    for n in range(min_len, max_len + 1):
        for bits in itertools.product("RL", repeat=n):
            if "R" not in bits or "L" not in bits:
                continue
            if time_budget_s is not None and time.time() - t0 > time_budget_s:
                print(f"  [word_scan time budget reached at length {n}, stopping]", flush=True)
                return violations, tested
            M: Mat = ((1, 0), (0, 1))
            for ch in bits:
                M = mat_mul(M, R_MAT if ch == "R" else L_MAT)
            a, d = M[0][0], M[1][1]
            tested += 1
            try:
                holds, sign, m = automorph_criterion(M)
            except ValueError:
                continue
            trace_zero = a == d
            if holds and not trace_zero:
                violations.append(("".join(bits), M, holds, sign, m))
                print(f"  GAP A VIOLATION (word): {''.join(bits)}  M={M}  "
                      f"criterion holds, a != d", flush=True)
        print(f"  word length {n} done, cumulative tested {tested}, "
              f"elapsed {time.time() - t0:.1f}s, violations {len(violations)}", flush=True)
    return violations, tested


# ---------------------------------------------------------------------------
# form scan: primitive binary quadratic forms (A, B, C), nonzero trace (B!=0)
# ---------------------------------------------------------------------------
def fundamental_tu(Delta: int, umax: int = 20000) -> tuple[int, int] | None:
    """Smallest positive (t, u) solving t^2 - Delta u^2 = 4."""
    for u in range(1, umax):
        t2 = 4 + Delta * u * u
        t = isqrt(t2)
        if t * t == t2:
            return t, u
    return None


def form_scan(
    amax: int, bmax: int, cmax: int, word_len_guard: int = 4000,
    time_budget_s: float | None = None, umax: int = 20000,
):
    """Primitive forms (A,B,C), A in [1,amax], B in [-bmax,bmax]\\{0} (nonzero
    trace only), C in [-cmax,cmax], positive nonsquare discriminant."""
    seen = set()
    violations = []
    tested = 0
    skipped_no_tu = 0
    skipped_word_len = 0
    t0 = time.time()
    stop = False
    for A_ in range(1, amax + 1):
        if stop:
            break
        for B_ in range(-bmax, bmax + 1):
            if B_ == 0:
                continue  # trace-zero, not the target of this search
            if stop:
                break
            for C_ in range(-cmax, cmax + 1):
                if time_budget_s is not None and time.time() - t0 > time_budget_s:
                    stop = True
                    break
                Delta = B_ * B_ - 4 * A_ * C_
                if Delta <= 0:
                    continue
                r = isqrt(Delta)
                if r * r == Delta:
                    continue
                if gcd(gcd(A_, abs(B_)), abs(C_)) != 1:
                    continue
                key = (A_, B_, C_)
                if key in seen:
                    continue
                seen.add(key)
                fu = fundamental_tu(Delta, umax=umax)
                if fu is None:
                    skipped_no_tu += 1
                    continue
                t, u = fu
                if (t - B_ * u) % 2 != 0:
                    continue
                a = (t - B_ * u) // 2
                b = -C_ * u
                c = A_ * u
                d = (t + B_ * u) // 2
                if a * d - b * c != 1:
                    continue
                M: Mat = ((a, b), (c, d))
                try:
                    word = sl2_word_fast(M)
                except Exception:
                    continue
                wlen = sum(abs(t_[1]) if t_[0] == "R" else 1 for t_ in word)
                if wlen > word_len_guard:
                    skipped_word_len += 1
                    continue
                tested += 1
                A_d, B_d, C_d, D_d = rho_fast(word)
                de = det_exponent(A_d, B_d, C_d, D_d)
                if de is None:
                    continue
                m, _ = de
                holds, sign = criterion_holds(C_d, m)
                if holds:
                    violations.append((key, M, sign, m))
                    print(f"  GAP A VIOLATION (form): (A,B,C)={key}  M={M}  "
                          f"criterion holds, B != 0", flush=True)
                if tested % 2000 == 0:
                    print(f"  ... forms tested {tested}, elapsed {time.time() - t0:.1f}s, "
                          f"violations {len(violations)}, skipped(no t/u)={skipped_no_tu}, "
                          f"skipped(word too long)={skipped_word_len}", flush=True)
    return violations, tested, skipped_no_tu, skipped_word_len


if __name__ == "__main__":
    import argparse

    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=["word", "form", "both"], default="both")
    ap.add_argument("--wordmax", type=int, default=20)
    ap.add_argument("--amax", type=int, default=40)
    ap.add_argument("--bmax", type=int, default=40)
    ap.add_argument("--cmax", type=int, default=40)
    ap.add_argument("--budget", type=float, default=None)
    args = ap.parse_args()

    if args.mode in ("word", "both"):
        print(f"WORD SCAN: {{R,L}}^n for n = 2..{args.wordmax}, both letters present")
        v, n = word_scan(args.wordmax, time_budget_s=args.budget)
        print(f"word scan done: tested={n} violations={len(v)}\n")

    if args.mode in ("form", "both"):
        print(f"FORM SCAN: A in [1,{args.amax}], B in [-{args.bmax},{args.bmax}]\\{{0}}, "
              f"C in [-{args.cmax},{args.cmax}]")
        v2, n2, skip1, skip2 = form_scan(
            args.amax, args.bmax, args.cmax, time_budget_s=args.budget
        )
        print(f"form scan done: tested={n2} violations={len(v2)} "
              f"skipped(no fundamental t,u within box)={skip1} skipped(word too long)={skip2}\n")
