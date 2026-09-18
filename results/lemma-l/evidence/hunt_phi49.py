"""
Agent B, T2. Out-of-population test: hunt for Phi_49 | C (p = 7, a = 2),
a stratum with ZERO instances in the 608-hit population (which contains
odd-p data only for p in {3, 5}).

Prefilter: by the scalar specialization theorem (see PROOF.md), Phi_49 | C
forces 49 | s, so only d with 49 | s_d can be hits. s_d is cheap via
qcore.pell_plus1, so the sweep d <= 30000 reduces to 1047 candidates, of
which those with s below 40 digits (783) are run through fastlam.

Result of the recorded run (68.7 s): 27 hits, d up to 29414. Every hit
satisfies downward closure (Phi_7 | C), Lemma L at 49 (Phi_49 | A - D),
Phi_49 | B, and 49 | s. See RESULTS.txt.
"""
import sys
import math
import time

sys.path.insert(0, "<path>")
sys.path.insert(0, "<path>")
from qcore import pell_plus1  # noqa: E402
import fastlam  # noqa: E402

sys.path.insert(0, "<path>")
from test_scalar_theorem import phi_divides, sub_poly  # noqa: E402


def main(dmax=30000, digit_cap=40, timebox_s=330):
    t0 = time.time()
    cands = []
    for d in range(2, dmax + 1):
        a0 = math.isqrt(d)
        if a0 * a0 == d:
            continue
        r, s = pell_plus1(d)
        if s % 49 == 0:
            cands.append((d, s))
    print(f"prefilter d<={dmax}, 49|s: {len(cands)} candidates, {time.time()-t0:.1f}s")
    cands.sort(key=lambda t: t[1])
    hits = []
    checked = 0
    skipped = 0
    for d, s in cands:
        if len(str(s)) > digit_cap:
            skipped += 1
            continue
        if time.time() - t0 > timebox_s:
            print("timebox reached; stopping scan")
            break
        (r, s2), (A, B, C, D) = fastlam.lam_q_fast(d)
        checked += 1
        if phi_divides(C, 49):
            AmD = sub_poly(A, D)
            row = dict(d=d, s=s,
                       closure_phi7=phi_divides(C, 7),
                       lemL_AmD=phi_divides(AmD, 49),
                       lemL_B=phi_divides(B, 49),
                       s49=(s % 49 == 0))
            hits.append(row)
            print("HIT:", row)
    print(f"checked {checked} candidates ({skipped} skipped as too big), {time.time()-t0:.1f}s")
    print("Phi_49 hits:", len(hits) if hits else "NONE found in this window")
    return hits


if __name__ == "__main__":
    main()
