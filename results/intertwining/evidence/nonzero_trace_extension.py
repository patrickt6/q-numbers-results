"""Window-based extension of the nonzero-trace (non-pure-surd) search.

IMPORTANT SCOPE NOTE: everything in this file is WINDOW EVIDENCE, not a
certificate. On the nonzero-trace family (a != d' in the automorph,
equivalently x' != -x) the intertwining relation N M N = M^(-1) fails, so the
Pell-reduction proof does not apply and there is no known exact algebraic
test analogous to the trace-zero divisibility check in `broad_sweep.py`. This
script only asks whether a long, exactly-certified Laurent WINDOW of
G(x) = [x]_q + [-x]_q is consistent with any low-degree rational function
(the same reconstruction method `03-pell.tex` and `attempts/attempt-1` already
use), and reports "no counterexample found in this window" rather than
"proved infinite". A miss here is not a proof; a hit would still need an
independent algebraic argument before being trusted, exactly per the
falsification brief's instructions.

Extends `attempts/attempt-1/falsify_beyond_pure.py`'s nine points (denominators
only up to 3, D in {2, 3, 5, 7, 13}) to larger denominators (up to 19) and
more D values (7, 11, 17, 23, 29, 31, 37, 41, 43, 53, 61, 83), all with a
genuine nonzero trace (p != 0 in the (p + r sqrt D)/s representation).

Requires PYTHONPATH=<path>
"""
from __future__ import annotations

import signal
import sys
import time

ATTEMPT1_DIR = "<path>"
if ATTEMPT1_DIR not in sys.path:
    sys.path.insert(0, ATTEMPT1_DIR)

from qperiod import analyse, rational_search  # noqa: E402

CANDIDATES = [
    "(1+sqrt(7))/5",
    "(2+sqrt(11))/7",
    "(3+sqrt(17))/8",
    "(1+sqrt(23))/9",
    "(4+sqrt(29))/11",
    "(5+sqrt(31))/13",
    "(2+sqrt(41))/13",
    "(7+sqrt(53))/17",
    "(3+sqrt(61))/14",
    "(1+sqrt(43))/19",
    "(5+sqrt(37))/16",
    "(2+sqrt(83))/15",
]


class _Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise _Timeout()


def main(max_deg: int = 18, per_candidate_timeout_s: float = 45.0) -> None:
    print(f"nonzero-trace window extension, {len(CANDIDATES)} points, rational-fit degree <= {max_deg}")
    print("(window evidence only; see module docstring for what this does and does not prove)\n")
    old = signal.signal(signal.SIGALRM, _alarm)
    skipped = []
    try:
        for xr in CANDIDATES:
            t0 = time.time()
            signal.setitimer(signal.ITIMER_REAL, per_candidate_timeout_s)
            try:
                rep = analyse(xr)
                (a, b), (c, d) = rep.automorph
                print(
                    f"x={xr:<18} automorph=[[{a},{b}],[{c},{d}]]  sym(a=d)={rep.struct.symmetric}  "
                    f"Laurent(A-D)/C={rep.candidate_is_laurent}  window_verdict={rep.window_verdict}  "
                    f"window_coeffs={len(rep.window)}"
                )
                if rep.candidate_is_laurent:
                    print("  NOTE: (A-D)/C is Laurent here, but this is the nonzero-trace case where the")
                    print("  reduction is NOT proved to equal G(x); matches_window below is the only check.")
                    print(f"  (A-D)/C == G(x) window check: {rep.matches}")
                found, expr, deg = rational_search(rep.window, max_deg=max_deg, holdout=6)
            except _Timeout:
                print(f"x={xr:<18} SKIPPED: exceeded {per_candidate_timeout_s:.0f}s per-candidate budget "
                      f"(automorph likely too large for this pass; abstention, not evidence either way)")
                skipped.append(xr)
                print(f"  [{time.time() - t0:.1f}s]\n")
                continue
            finally:
                signal.setitimer(signal.ITIMER_REAL, 0)
            if found:
                print(f"  RATIONAL FIT at degree {deg}: {expr}  <-- investigate before trusting")
            else:
                print(f"  no rational function of degree <= {max_deg} fits the window "
                      f"(consistent with the conjecture; not a proof of infinitude)")
            print(f"  [{time.time() - t0:.1f}s]\n")
    finally:
        signal.signal(signal.SIGALRM, old)
    if skipped:
        print(f"{len(skipped)} candidates skipped on time budget: {skipped}")


if __name__ == "__main__":
    main()
