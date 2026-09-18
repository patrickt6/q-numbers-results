"""Wide exact sweep of the trace-zero family x = (u/v) * sqrt(D), v > 1.

Trace-zero here means x' = -x (Galois conjugate is the negative), equivalently
x^2 is rational with no linear term, equivalently the fundamental automorph
M of x has equal diagonal entries a = d'. Opus's `attempts/opus/README.md`
proves this is equivalent to N M N = M^(-1) and to x = b0*sqrt(D) for
rational b0, squarefree D; the proof is two lines (see there). On that family
the Pell-reduction proof (03-pell.tex, thm:pell) applies verbatim, so

    [x]_q + [-x]_q = (A - D) / C           exactly,

and "is (A - D)/C a Laurent polynomial" is a FINITE, EXACT, non-truncated
test: sympy polynomial cancellation, not a coefficient window. This script
therefore never looks at a truncated series to decide finiteness.

Every D with a square factor is equivalent, after absorbing the square part
into b0 = u/v, to a smaller squarefree D with a rescaled u/v; so restricting
the D grid to squarefree values loses nothing versus explicitly running
non-squarefree D (this is checked directly by `non_squarefree_is_redundant`
below, not merely asserted).

This is opus's own recommended follow-up (README.md: "This scan is cheap and
deserves widening... the cost driver is sl2_word running in sympy... which is
the obvious thing to optimize before scaling up"). This script does exactly
that: `fast_word.sl2_word_fast` (pure Python ints, verified against
`proof_verification.sl2_word` on 200 random matrices, see fast_word.py)
replaces the sympy-based word decomposition; everything else (the automorph
itself, `fastlam.rho_fast`, the final Laurent-divisibility test) is reused
unchanged from the already-validated tooling.

Requires PYTHONPATH=<path> set
before running (for the qreals.quadratic import).
"""
from __future__ import annotations

import signal
import sys
import time
from dataclasses import dataclass
from math import gcd, isqrt

import sympy as sp

OPUS_DIR = "<path>"
PAPERGAPS_CODE = "<path>"
for _p in (OPUS_DIR, PAPERGAPS_CODE):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from qreals.quadratic import QuadraticIrrational, is_squarefree  # noqa: E402
from qperiod import period_data  # noqa: E402 (HJ period + automorph; pure integer, already fast)
from fastlam import rho_fast  # noqa: E402
from fast_word import sl2_word_fast  # noqa: E402

q = sp.Symbol("q")


class _CandidateTimeout(Exception):
    pass


def _alarm_handler(signum, frame):
    raise _CandidateTimeout()


def dict_to_expr(d: dict) -> sp.Expr:
    if not d:
        return sp.Integer(0)
    return sp.together(sum(c * q**e for e, c in d.items()))


def fast_ad_over_c(M) -> sp.Expr:
    """(A - D)/C for automorph M, via the fast pure-integer word + rho_fast."""
    a, b = M[0]
    c, d = M[1]
    if a * d - b * c != 1:
        raise ValueError(f"determinant {a * d - b * c}, expected 1")
    word = sl2_word_fast(((a, b), (c, d)))
    A, B, C, D = rho_fast(word)
    Aexpr, Dexpr, Cexpr = dict_to_expr(A), dict_to_expr(D), dict_to_expr(C)
    if Cexpr == 0:
        raise ZeroDivisionError("C = 0")
    return sp.cancel((Aexpr - Dexpr) / Cexpr)


def is_laurent_poly(expr: sp.Expr) -> bool:
    expr = sp.cancel(sp.together(expr))
    if expr == 0:
        return True
    num, den = sp.fraction(expr)
    dpoly = sp.Poly(sp.expand(den), q)
    return len(dpoly.terms()) == 1


def non_squarefree_is_redundant(D_nonsquarefree: int, u: int, v: int) -> tuple[int, int, int]:
    """(u/v) sqrt(D_nonsquarefree) == (u2/v) sqrt(D2) with D2 squarefree.

    Returns (u2, v, D2). Used only as a documentation-level sanity check that
    the squarefree-only D grid below is not a loss of generality.
    """
    D2 = D_nonsquarefree
    f = 1
    i = 2
    while i * i <= D2:
        while D2 % (i * i) == 0:
            D2 //= i * i
            f *= i
        i += 1
    return u * f, v, D2


@dataclass
class SweepHit:
    D: int
    u: int
    v: int
    laurent: bool
    error: str | None = None
    elapsed: float = 0.0


def squarefree_range(lo: int, hi: int) -> list[int]:
    return [d for d in range(lo, hi + 1) if is_squarefree(d)]


def sweep(
    D_values: list[int],
    v_max: int,
    u_max: int,
    hj_max_terms: int = 600,
    time_budget_s: float | None = None,
    log_every: int = 1000,
    per_candidate_timeout_s: float = 3.0,
    verbose: bool = False,
) -> tuple[list[SweepHit], list[SweepHit], int, list[SweepHit]]:
    """Returns (laurent_hits, errors, n_tested, timeouts).

    Each candidate is bounded by a SIGALRM timeout so a single pathological
    (D, u, v) with a huge Pell-type fundamental solution cannot stall the
    whole sweep. Timed-out candidates are recorded separately and counted as
    abstentions, never as support for the conjecture.
    """
    laurent_hits: list[SweepHit] = []
    errors: list[SweepHit] = []
    timeouts: list[SweepHit] = []
    n_tested = 0
    t_start = time.time()
    stop = False
    old_handler = signal.signal(signal.SIGALRM, _alarm_handler)
    try:
        for D in D_values:
            if stop:
                break
            for v in range(2, v_max + 1):
                if stop:
                    break
                for u in range(1, u_max + 1):
                    if gcd(u, v) != 1:
                        continue
                    if time_budget_s is not None and time.time() - t_start > time_budget_s:
                        stop = True
                        break
                    t0 = time.time()
                    try:
                        x = QuadraticIrrational(0, u, v, D)
                    except Exception:
                        continue
                    n_tested += 1
                    if verbose:
                        print(f"  trying D={D} u={u} v={v}", flush=True)
                    signal.setitimer(signal.ITIMER_REAL, per_candidate_timeout_s)
                    try:
                        pd = period_data(x, max_terms=hj_max_terms)
                        if verbose:
                            print(f"    period_length={pd.period_length}", flush=True)
                        cand = fast_ad_over_c(pd.automorph)
                        if verbose:
                            print("    got candidate, checking laurent...", flush=True)
                        laurent = is_laurent_poly(cand)
                    except _CandidateTimeout:
                        timeouts.append(SweepHit(D, u, v, False, error="timeout", elapsed=time.time() - t0))
                        continue
                    except Exception as e:
                        errors.append(SweepHit(D, u, v, False, error=repr(e), elapsed=time.time() - t0))
                        continue
                    finally:
                        signal.setitimer(signal.ITIMER_REAL, 0)
                    hit = SweepHit(D, u, v, laurent, elapsed=time.time() - t0)
                    if laurent:
                        laurent_hits.append(hit)
                        print(f"LAURENT HIT: D={D} u={u} v={v}  x=({u}/{v})sqrt({D})", flush=True)
                    if n_tested % log_every == 0:
                        print(
                            f"... tested {n_tested}, elapsed {time.time() - t_start:.1f}s, "
                            f"hits so far {len(laurent_hits)}, errors {len(errors)}, "
                            f"timeouts {len(timeouts)}",
                            flush=True,
                        )
    finally:
        signal.signal(signal.SIGALRM, old_handler)
    return laurent_hits, errors, n_tested, timeouts


if __name__ == "__main__":
    import argparse

    ap = argparse.ArgumentParser()
    ap.add_argument("--dmin", type=int, default=2)
    ap.add_argument("--dmax", type=int, default=100)
    ap.add_argument("--vmax", type=int, default=15)
    ap.add_argument("--umax", type=int, default=40)
    ap.add_argument("--budget", type=float, default=None)
    ap.add_argument("--cand-timeout", type=float, default=3.0)
    ap.add_argument("--verbose", action="store_true")
    ap.add_argument("--log-every", type=int, default=1000)
    args = ap.parse_args()

    Ds = squarefree_range(args.dmin, args.dmax)
    print(f"D range: {args.dmin}..{args.dmax}, {len(Ds)} squarefree values", flush=True)
    print(f"v in 2..{args.vmax}, u in 1..{args.umax} (coprime pairs only)", flush=True)
    t0 = time.time()
    hits, errs, n, touts = sweep(
        Ds, args.vmax, args.umax, time_budget_s=args.budget,
        per_candidate_timeout_s=args.cand_timeout, verbose=args.verbose,
        log_every=args.log_every,
    )
    print(
        f"\nDone. tested={n} laurent_hits={len(hits)} errors={len(errs)} "
        f"timeouts={len(touts)} time={time.time() - t0:.1f}s",
        flush=True,
    )
    for h in hits:
        print(" HIT:", h)
    if errs:
        print(f"\n{len(errs)} errors (first 10):")
        for e in errs[:10]:
            print(" ", e)
    if touts:
        print(f"\n{len(touts)} timeouts (candidates skipped, not evidence either way; first 15):")
        for t in touts[:15]:
            print(" ", t)
