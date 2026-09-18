r"""The symmetric-automorph characterization, and what it buys.

FINDING (this file is the evidence for it)
------------------------------------------
Let x be a real quadratic irrational, M = [[a, b], [c, d]] its automorph in
SL(2, Z) as computed by `qperiod.period_data`, and N = diag(-1, 1). Write x'
for the Galois conjugate of x. Then

    a = d   <=>   N M N = M^(-1)   <=>   x' = -x   <=>   x = b0 sqrt(D)
                                                          for some rational b0.

Proof. M fixes x, so c x^2 + (d - a) x - b = 0. For c nonzero this is the
minimal polynomial of x up to scale, whence x + x' = (a - d)/c, giving
a = d <=> x + x' = 0. In SL(2, Z), N M N = [[a, -b], [-c, d]] and
M^(-1) = [[d, -b], [-c, a]], so a = d <=> N M N = M^(-1). Finally x' = -x is
exactly the statement that x has zero trace, that is x = b0 sqrt(D). QED

CONSEQUENCE. The intertwining step of `thm:pell` is the only place the proof
uses anything special about sqrt(d). It therefore goes through verbatim for
every x = b0 sqrt(D) with b0 rational, not merely for b0 = 1:

    [x]_q + [-x]_q = (A - D)/C,   (A, B; C, D) = rho(automorph of x),

so the sum is a finite Laurent polynomial exactly when C divides A - D up to
a monomial. This is a strict enlargement of the class the paper's theorem
covers, and it makes the conjecture EXACTLY DECIDABLE on that class by a
single polynomial division, with no series window at all.

CONSEQUENCE FOR THE CONJECTURE. `conj:quadratic-64` asserts that the sum is
finite if and only if x = +-sqrt(d) with F(d) finite. Every x = (u/v) sqrt(D)
with v > 1, u/v in lowest terms and D squarefree, is NOT a pure surd: it
equals sqrt(u^2 D / v^2), and u^2 D / v^2 is an integer only if v^2 | D, which
a squarefree D > 1 forbids for v > 1. So any such x whose (A - D)/C is a
Laurent polynomial is a counterexample to the conjecture. This script scans
that family.

What the script does
--------------------
  PART 1. Verifies the characterization over a grid of quadratic irrationals,
          reporting any case where symmetry, intertwining and zero trace do
          not coincide.
  PART 2. Verifies the extended reduction, (A - D)/C against the exact locked
          window of G(x), on a sample of trace-zero non-pure-surds. This is
          the check that the transferred proof is actually correct and not
          just formally plausible.
  PART 3. Scans x = (u/v) sqrt(D) for a Laurent (A - D)/C, that is, for a
          counterexample to `conj:quadratic-64`.

Run:
    PYTHONPATH=<path> \
        python3 scan_trace_zero.py [--umax 6] [--vmax 6] [--dmax 30]
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction
from math import gcd

import sympy as sp

from qperiod import (
    N_MAT,
    ad_over_c,
    analyse,
    is_laurent_poly,
    mat_inv,
    mat_mul,
    mat_neg,
    period_data,
    rho_q,
)
from qreals.quadratic import QuadraticIrrational, is_squarefree

MAX_TERMS = 2000


def characterization_row(a: Fraction, b: Fraction, D: int):
    """(symmetric, intertwines, trace_zero) for x = a + b sqrt(D), or None."""
    x = QuadraticIrrational.from_ab(a, b, D)
    try:
        pd = period_data(x, MAX_TERMS)
    except (ValueError, AssertionError):
        return None
    M = pd.automorph
    sym = M[0][0] == M[1][1]
    NMN = mat_mul(mat_mul(N_MAT, M), N_MAT)
    Mi = mat_inv(M)
    inter = NMN == Mi or NMN == mat_neg(Mi)
    return sym, inter, a == 0, M


def part1(dmax: int) -> tuple[int, list]:
    print("=" * 78)
    print("PART 1: symmetric <=> N M N = M^(-1) <=> trace(x) = 0")
    print("=" * 78)
    a_grid = [Fraction(0), Fraction(1), Fraction(1, 2), Fraction(2, 3), Fraction(3, 2), Fraction(-1, 4)]
    b_grid = [Fraction(1), Fraction(1, 2), Fraction(2, 3), Fraction(3), Fraction(5, 2), Fraction(1, 5)]
    D_grid = [D for D in range(2, dmax + 1) if is_squarefree(D)]
    tested = 0
    skipped = 0
    violations = []
    for D in D_grid:
        for a in a_grid:
            for b in b_grid:
                row = characterization_row(a, b, D)
                if row is None:
                    skipped += 1
                    continue
                sym, inter, tz, M = row
                tested += 1
                if not (sym == inter == tz):
                    violations.append(
                        {"a": str(a), "b": str(b), "D": D, "symmetric": sym,
                         "intertwines": inter, "trace_zero": tz,
                         "automorph": [list(M[0]), list(M[1])]}
                    )
    print(f"tested {tested} quadratic irrationals ({skipped} skipped on period budget)")
    print(f"violations: {len(violations)}")
    for v in violations[:10]:
        print("   ", v)
    print()
    return tested, violations


def part2(samples: list[str]) -> list[dict]:
    print("=" * 78)
    print("PART 2: extended reduction (A - D)/C == G(x) on trace-zero non-pure-surds")
    print("=" * 78)
    out = []
    for xr in samples:
        rep = analyse(xr)
        row = {
            "x": xr,
            "automorph": [list(rep.automorph[0]), list(rep.automorph[1])],
            "symmetric": rep.struct.symmetric,
            "intertwines": rep.struct.intertwines_z,
            "candidate": str(sp.factor(rep.candidate)),
            "candidate_is_laurent": rep.candidate_is_laurent,
            "matches_window": rep.matches,
            "window_verdict": rep.window_verdict,
            "window_coefficients": len(rep.window),
        }
        out.append(row)
        print(
            f"  {xr:<16} sym={rep.struct.symmetric!s:<5} "
            f"(A-D)/C == G(x): {rep.matches!s:<5} "
            f"Laurent={rep.candidate_is_laurent!s:<5} verdict={rep.window_verdict:<16} "
            f"({len(rep.window)} coefficients)"
        )
        print(f"      (A - D)/C = {sp.factor(rep.candidate)}")
    ok = all(r["matches_window"] for r in out)
    print(f"\nall samples reproduce the window: {ok}")
    print()
    return out


def part3(umax: int, vmax: int, dmax: int) -> list[dict]:
    print("=" * 78)
    print("PART 3: scan x = (u/v) sqrt(D), v > 1, for a Laurent (A - D)/C")
    print("=" * 78)
    print("A Laurent hit at v > 1 is a counterexample to conj:quadratic-64.")
    hits = []
    tested = 0
    skipped = 0
    for D in range(2, dmax + 1):
        if not is_squarefree(D):
            continue
        for v in range(2, vmax + 1):
            for u in range(1, umax + 1):
                if gcd(u, v) != 1:
                    continue
                x = QuadraticIrrational(0, u, v, D)
                try:
                    pd = period_data(x, MAX_TERMS)
                except (ValueError, AssertionError):
                    skipped += 1
                    continue
                M = pd.automorph
                if M[0][0] != M[1][1]:
                    print(f"  UNEXPECTED: {u}/{v} sqrt({D}) has non-symmetric automorph {M}")
                    continue
                try:
                    cand = ad_over_c(rho_q(M))
                except (ZeroDivisionError, ValueError):
                    skipped += 1
                    continue
                tested += 1
                if is_laurent_poly(cand):
                    hits.append(
                        {"u": u, "v": v, "D": D, "x": f"({u}/{v})*sqrt({D})",
                         "candidate": str(sp.factor(cand)),
                         "automorph": [list(M[0]), list(M[1])]}
                    )
                    print(f"  HIT  x = ({u}/{v}) sqrt({D}):  (A - D)/C = {sp.factor(cand)}")
    print(f"\ntested {tested} trace-zero non-pure-surds ({skipped} skipped)")
    print(f"Laurent hits (counterexample candidates): {len(hits)}")
    print()
    return hits


def main(argv: list[str]) -> int:
    def opt(name: str, default: int) -> int:
        return int(argv[argv.index(name) + 1]) if name in argv else default

    umax = opt("--umax", 6)
    vmax = opt("--vmax", 6)
    dmax = opt("--dmax", 30)
    p1_tested, violations = part1(min(dmax, 15))
    samples = [
        "sqrt(3)/2", "sqrt(2)/3", "2*sqrt(2)/3", "3*sqrt(5)/2",
        "sqrt(7)/2", "5*sqrt(3)/4",
    ]
    p2 = part2(samples)
    hits = part3(umax, vmax, dmax)

    print("=" * 78)
    print("CONCLUSIONS")
    print("=" * 78)
    print(f"  characterization holds on {p1_tested} cases, {len(violations)} violations")
    print(f"  extended reduction verified against the window on {len(p2)} trace-zero samples: "
          f"{all(r['matches_window'] for r in p2)}")
    print(f"  counterexample candidates found: {len(hits)}")
    if not hits:
        print("  => no counterexample to conj:quadratic-64 in the scanned trace-zero family;")
        print("     the conjecture survives on the one class where it is now exactly decidable.")

    with open("trace-zero-scan.json", "w") as fh:
        json.dump(
            {"characterization_tested": p1_tested, "characterization_violations": violations,
             "extended_reduction_samples": p2, "counterexample_candidates": hits,
             "scan_bounds": {"umax": umax, "vmax": vmax, "dmax": dmax}},
            fh, indent=2,
        )
    print("\nrecord written to trace-zero-scan.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
