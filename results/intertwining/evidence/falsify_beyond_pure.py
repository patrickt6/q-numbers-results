r"""Runnable reproduction of the `ssec:beyond-pure` falsification.

`03-pell.tex` lines 256 to 270 records, in prose only, that the Pell reduction
does not extend past pure square roots:

  * for x = 1 + sqrt 2, with automorph M = [[5, 2], [2, 1]], already
    (A - D)/C is not equal to G(5/2);
  * for eight further non-pure-surd quadratics, among them (1 + sqrt 5)/2,
    (3 + sqrt 13)/2 and 2 + sqrt 2, the sum G(x) = [x]_q + [-x]_q was computed
    as an exact stabilized Laurent window of 59 coefficients, and no rational
    function of numerator and denominator degree up to 18 matches any of them.

This script reproduces both parts as a record. For each of the nine
quadratics it reports:

  1. the Hirzebruch-Jung period and the automorph M, computed generally;
  2. whether M is symmetric (a = d') and whether N M N = M^(-1), at the
     integer level and at the q level (the `ssec:beyond-pure` obstruction, and
     the input to the structural-characterization line of attack);
  3. the candidate (A - D)/C, and its value at q = 1, which must be 0 for any
     valid formula because G(x)|_(q=1) = x + (-x) = 0;
  4. the exact stabilized Laurent window of G(x), with its verdict;
  5. the comparison of 3 against 4, with the first mismatching degree;
  6. the exact rational-function search: is the window the expansion of ANY
     P/Q with deg P, deg Q <= 18?

Positive control. The same search, run on the pure surds where the answer is
known, recovers the true (A - D)/C exactly: degree 3 for sqrt 2, degree 15 for
sqrt 19. So a negative answer below is a real negative and not a broken
search. Its honest scope is stated in the README.

Run:
    PYTHONPATH=<path> \
        python3 falsify_beyond_pure.py > falsification-record.txt
"""

from __future__ import annotations

import json
import sys
import time
from fractions import Fraction

import sympy as sp

from qperiod import analyse, format_report, mat_det, rational_search

# The recorded case, then eight further non-pure-surd quadratics. The three
# named in `ssec:beyond-pure` are included verbatim.
RECORDED = "1+sqrt(2)"
EIGHT = [
    "(1+sqrt(5))/2",   # named in the paper
    "(3+sqrt(13))/2",  # named in the paper
    "2+sqrt(2)",       # named in the paper
    "3+sqrt(3)",
    "(1+sqrt(2))/2",
    "(1+sqrt(3))/2",
    "(2+sqrt(7))/3",
    "(1+sqrt(13))/3",
]

# Positive controls: pure surds, where the Pell reduction is a theorem.
CONTROLS = ["sqrt(2)", "sqrt(19)"]

# Trace-zero non-pure-surds. These are NOT part of the falsification: for
# them the automorph is symmetric, the intertwining holds, and (A - D)/C is
# correct. They are included to mark the exact boundary of the obstruction,
# and are the subject of `scan_trace_zero.py`.
TRACE_ZERO = ["sqrt(3)/2", "sqrt(2)/3", "3*sqrt(5)/2"]

MAX_DEG = 18


def run_one(x_repr: str, max_deg: int = MAX_DEG) -> dict:
    t0 = time.time()
    rep = analyse(x_repr)
    print("=" * 78)
    print(format_report(rep))
    found, expr, deg = rational_search(rep.window, max_deg=max_deg)
    if found:
        print(f"rational fit deg <= {max_deg}: FOUND at degree {deg}: {sp.factor(expr)}")
    else:
        print(
            f"rational fit deg <= {max_deg}: NONE. No P/Q with deg P, deg Q <= {max_deg} "
            f"reproduces the {len(rep.window)}-coefficient window."
        )
    print(f"[{time.time() - t0:.1f}s]")
    print()
    (a, b), (c, d) = rep.automorph
    return {
        "x": x_repr,
        "automorph": [[a, b], [c, d]],
        "det": mat_det(rep.automorph),
        "hj_preperiod": rep.period.terms[: rep.period.period_start],
        "hj_period": rep.period.periodic_word,
        "symmetric": rep.struct.symmetric,
        "intertwines_Z": rep.struct.intertwines_z,
        "intertwines_q": rep.struct.intertwines_q,
        "candidate_A_minus_D_over_C": str(sp.factor(rep.candidate)),
        "candidate_is_laurent": rep.candidate_is_laurent,
        "candidate_at_q_equals_1": str(rep.candidate_at_one),
        "window_coefficient_count": len(rep.window),
        "window_valuation": rep.window_valuation,
        "window_verdict": rep.window_verdict,
        "window_locked_depth": rep.locked_depth,
        "candidate_matches_window": rep.matches,
        "first_mismatch_degree": rep.first_mismatch,
        "rational_fit_max_degree": max_deg,
        "rational_fit_found": found,
        "rational_fit_degree": deg,
        "rational_fit_expr": str(sp.factor(expr)) if expr is not None else None,
        "window_coefficients": {str(k): str(v) for k, v in sorted(rep.window.items())},
    }


def main() -> int:
    print("Reproduction of 03-pell.tex, ssec:beyond-pure, lines 256 to 270.")
    print(f"Rational-function search bound: numerator and denominator degree <= {MAX_DEG}.")
    print()

    print("#" * 78)
    print("# POSITIVE CONTROLS (pure surds, where the Pell reduction is a theorem)")
    print("#" * 78)
    print()
    controls = [run_one(x) for x in CONTROLS]
    control_ok = all(c["candidate_matches_window"] and c["rational_fit_found"] for c in controls)

    print("#" * 78)
    print("# THE RECORDED CASE")
    print("#" * 78)
    print()
    recorded = run_one(RECORDED)

    print("#" * 78)
    print("# THE EIGHT FURTHER NON-PURE-SURD QUADRATICS")
    print("#" * 78)
    print()
    eight = [run_one(x) for x in EIGHT]

    print("#" * 78)
    print("# BOUNDARY MARKERS: trace-zero non-pure-surds, where the reduction SURVIVES")
    print("#" * 78)
    print()
    trace_zero = [run_one(x) for x in TRACE_ZERO]

    print("=" * 78)
    print("SUMMARY")
    print("=" * 78)
    header = f"{'x':<18} {'automorph':<20} {'sym':<5} {'NMN=M^-1':<9} {'(A-D)/C=G':<10} {'fit<=18':<8}"
    print(header)
    print("-" * len(header))
    for r in controls + [recorded] + eight + trace_zero:
        M = r["automorph"]
        mstr = f"[[{M[0][0]},{M[0][1]}],[{M[1][0]},{M[1][1]}]]"
        print(
            f"{r['x']:<18} {mstr:<20} {str(r['symmetric']):<5} "
            f"{str(r['intertwines_Z']):<9} {str(r['candidate_matches_window']):<10} "
            f"{str(r['rational_fit_found']):<8}"
        )
    print()

    ok_recorded = not recorded["candidate_matches_window"]
    ok_eight = all(not r["rational_fit_found"] for r in eight)
    ok_struct = all(
        (not r["symmetric"]) and (not r["intertwines_Z"]) for r in [recorded] + eight
    )
    ok_tz = all(
        r["symmetric"] and r["intertwines_Z"] and r["candidate_matches_window"]
        for r in trace_zero
    )
    print(f"positive controls reproduce the known answer : {control_ok}")
    print(f"recorded case 1 + sqrt 2 falsified           : {ok_recorded}")
    print(f"eight further quadratics: no fit to degree 18: {ok_eight}")
    print(f"all nine nonzero-trace: a != d', no N M N = M^-1: {ok_struct}")
    print(f"trace-zero markers: reduction survives         : {ok_tz}")

    payload = {
        "source": "03-pell.tex ssec:beyond-pure, lines 256 to 270",
        "max_degree": MAX_DEG,
        "controls": controls,
        "recorded": recorded,
        "eight": eight,
        "trace_zero_boundary": trace_zero,
        "verdicts": {
            "controls_reproduce_known_answer": control_ok,
            "recorded_case_falsified": ok_recorded,
            "eight_no_rational_fit_to_degree_18": ok_eight,
            "all_nine_asymmetric_and_non_intertwining": ok_struct,
            "trace_zero_reduction_survives": ok_tz,
        },
    }
    out = "falsification-record.json"
    with open(out, "w") as fh:
        json.dump(payload, fh, indent=2)
    print(f"\nmachine-readable record written to {out}")
    return 0 if (control_ok and ok_recorded and ok_eight and ok_struct and ok_tz) else 1


if __name__ == "__main__":
    raise SystemExit(main())
