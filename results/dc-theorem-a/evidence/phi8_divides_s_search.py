"""
Exhaustive search for a counterexample to:

    Phi_8 | S_{r/s}   implies   8 | s

for irreducible fractions r/s, where S_{r/s} is the Morier-Genoud and Ovsienko
q-denominator, reduced, monic, computed by qreals.rational.q_rational_pair.

Also records, at no extra cost, the converse direction: whether 8 | s always
gives Phi_8 | S, and the empirical shape of the hit set (which residues r mod s
produce Phi_8 | S).

Exact arithmetic only. Divisibility is decided by sympy.rem of two sympy.Poly
objects over the integers, dividing S by Phi_8 = q^4 + 1 and checking the
remainder is the zero polynomial. No floating point and no evaluation at a
numerical root of unity is used anywhere.

S_{r/s} depends only on r mod s, so r ranges over residues coprime to s in
[1, s-1], not over an unbounded range.

Run with:
    PYTHONPATH=<path> python3 phi8_divides_s_search.py
"""

import sys
import time
import json
from math import gcd

sys.path.insert(0, "<path>")

from qreals.rational import q_rational_pair
import sympy
from sympy import symbols, Poly, cyclotomic_poly, rem

q = symbols("q")
PHI8 = Poly(cyclotomic_poly(8, q), q, domain="ZZ")
PHI4 = Poly(cyclotomic_poly(4, q), q, domain="ZZ")


def denom_poly(r, s):
    _, den = q_rational_pair(r, s)
    return Poly(den.as_expr(), q, domain="ZZ")


def divides(divisor_poly, S_poly):
    return rem(S_poly, divisor_poly) == 0


def sanity_checks():
    # Known small values, confirm calling convention before trusting a large run.
    # q_rational_pair(p, s) returns (numerator, denominator) reduced, monic.
    num, den = q_rational_pair(1, 2)
    assert den.as_expr() == q + 1, den
    num, den = q_rational_pair(1, 3)
    assert den.as_expr() == q**2 + q + 1, den
    # 3/8: denominator should be divisible by Phi_8 (KMRWY diagonal / direct check)
    S = denom_poly(3, 8)
    print("S_{3/8} =", S.as_expr())
    print("Phi_8 | S_{3/8}:", divides(PHI8, S))
    print("Phi_4 | S_{3/8}:", divides(PHI4, S))


def main():
    sanity_checks()

    EXHAUSTIVE_BOUND = 400  # s from 2..EXHAUSTIVE_BOUND, exhaustive
    SAMPLE_BOUND = 1200     # s from EXHAUSTIVE_BOUND+1..SAMPLE_BOUND, sampled
    SAMPLE_STEP = 3         # sample every 3rd s in the tail range (still exact arithmetic per pair)

    total_pairs = 0
    phi8_hits = 0
    phi4_given_phi8_ok = 0  # sanity check on the already-proved Phi_4 <=> 4|s fact
    counterexamples = []  # Phi_8 | S but 8 does not divide s
    converse_failures = []  # 8 | s but Phi_8 does not divide S

    # hit-set shape tracking: for s where at least one hit occurs, record which
    # residues r (mod s) produce Phi_8 | S, and also r mod 8 for pattern-spotting
    hit_records = []  # (s, r) pairs where Phi_8 | S

    s_values_exhaustive = list(range(2, EXHAUSTIVE_BOUND + 1))
    s_values_sampled = list(range(EXHAUSTIVE_BOUND + 1, SAMPLE_BOUND + 1, SAMPLE_STEP))

    t0 = time.time()

    def scan_s(s):
        nonlocal total_pairs, phi8_hits, phi4_given_phi8_ok
        local_hits = []
        for r in range(1, s):
            if gcd(r, s) != 1:
                continue
            total_pairs += 1
            S = denom_poly(r, s)
            has8 = divides(PHI8, S)
            if has8:
                phi8_hits += 1
                local_hits.append(r)
                hit_records.append((s, r))
                if s % 8 != 0:
                    counterexamples.append((r, s, S.as_expr()))
                has4 = divides(PHI4, S)
                if has4:
                    phi4_given_phi8_ok += 1
            if s % 8 == 0:
                has8_check = has8
                if not has8_check:
                    # converse direction: 8 | s but Phi_8 does not divide S
                    converse_failures.append((r, s))
        return local_hits

    print(f"\nStarting exhaustive scan s = 2..{EXHAUSTIVE_BOUND} ...")
    for s in s_values_exhaustive:
        scan_s(s)
        if counterexamples:
            print("!!! COUNTEREXAMPLE FOUND, stopping exhaustive scan early !!!")
            break

    exhaustive_max_reached = s_values_exhaustive[-1] if not counterexamples else s

    print(f"Exhaustive scan done in {time.time()-t0:.1f}s. "
          f"Pairs so far: {total_pairs}, Phi_8 hits so far: {phi8_hits}")

    if not counterexamples:
        print(f"\nStarting sampled tail scan s in "
              f"{EXHAUSTIVE_BOUND+1}..{SAMPLE_BOUND} step {SAMPLE_STEP} ...")
        for s in s_values_sampled:
            scan_s(s)
            if counterexamples:
                print("!!! COUNTEREXAMPLE FOUND in sampled tail, stopping !!!")
                break

    elapsed = time.time() - t0
    print(f"\nTotal elapsed: {elapsed:.1f}s")
    print(f"Total (r,s) pairs tested: {total_pairs}")
    print(f"Total Phi_8 | S hits: {phi8_hits}")
    print(f"Counterexamples (Phi_8|S, 8 not| s): {len(counterexamples)}")
    print(f"Converse failures (8|s, Phi_8 not| S): {len(converse_failures)}")
    print(f"Phi_4|S given Phi_8|S, agreement count: {phi4_given_phi8_ok} / {phi8_hits}")

    # Hit-set shape: for each s with hits, residues r mod s, and r mod 8
    shape_by_s = {}
    r_mod8_tally = {}
    r_pm1_mod_s_count = 0
    r_pm1_mod8_count = 0
    for (s, r) in hit_records:
        shape_by_s.setdefault(s, []).append(r)
        rm8 = r % 8
        r_mod8_tally[rm8] = r_mod8_tally.get(rm8, 0) + 1
        if r % s in (1, s - 1):
            r_pm1_mod_s_count += 1
        if rm8 in (1, 7):
            r_pm1_mod8_count += 1

    result = {
        "exhaustive_s_range": [2, exhaustive_max_reached],
        "sampled_s_range": [EXHAUSTIVE_BOUND + 1, SAMPLE_BOUND, SAMPLE_STEP]
        if not counterexamples else None,
        "total_pairs_tested": total_pairs,
        "phi8_hits": phi8_hits,
        "counterexamples": [(r, s, str(S)) for (r, s, S) in counterexamples],
        "converse_failures": converse_failures,
        "phi4_given_phi8_agreement": [phi4_given_phi8_ok, phi8_hits],
        "r_mod8_tally": r_mod8_tally,
        "r_pm1_mod_s_count": r_pm1_mod_s_count,
        "r_pm1_mod8_count": r_pm1_mod8_count,
        "hits_by_s_sample": {s: shape_by_s[s] for s in list(shape_by_s)[:30]},
        "elapsed_seconds": elapsed,
    }

    out_path = "<path>"
    with open(out_path, "w") as f:
        json.dump(result, f, indent=2, default=str)
    print(f"\nWrote raw result JSON to {out_path}")

    return result


if __name__ == "__main__":
    main()
