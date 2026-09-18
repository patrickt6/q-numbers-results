"""
WP2 task: prime-power downward closure of cyclotomic factors of C.

For every nonsquare d, compute the Pell automorph Lambda_q = [[A,B],[C,D]]
(via fastlam.lam_q_fast, reused unchanged from
<path>) and test, for each prime
power n = p^a in a fixed test set, whether the cyclotomic polynomial
Phi_n(q) divides the Laurent polynomial C.

Exact divisibility test (generalizes task3_phi4_census.py's q^2=-1 trick
to arbitrary Phi_n): C is a Laurent polynomial (dict {exponent:int}).
Phi_n has nonzero constant term (Phi_n(0) != 0 for all n), so q is a unit
mod Phi_n; multiplying C by q^k for any k does not change whether Phi_n
divides it. So shift C to an ordinary polynomial (nonnegative exponents)
by multiplying by q^{-min_exponent}, then do exact integer polynomial
long division by Phi_n (monic, integer coefficients from sympy), which
stays exact throughout because the divisor is monic (no rational
coefficients ever appear). Phi_n | C iff the remainder is the zero
polynomial.

For every d where Phi_{p^a} | C with a >= 2 (a "prime-power hit"), we
check downward closure: does Phi_{p^j} | C for every 1 <= j < a? We also
record v_p(s), the p-adic valuation of the Pell solution's s (expected
p^a | s based on prior Phi_4 census data, i.e. v_p(s) >= a).
"""
import sys
import math
import time

sys.path.insert(0, "<path>")
import fastlam  # noqa: E402

import sympy as sp

Q = sp.Symbol('q')

# prime-power test set (as specified in the task)
TEST_SET = [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 25, 27, 32, 49, 81, 121, 125]

# map n -> (p, a)
PRIME_POWER = {
    2: (2, 1), 4: (2, 2), 8: (2, 3), 16: (2, 4), 32: (2, 5),
    3: (3, 1), 9: (3, 2), 27: (3, 3), 81: (3, 4),
    5: (5, 1), 25: (5, 2), 125: (5, 3),
    7: (7, 1), 49: (7, 2),
    11: (11, 1), 121: (11, 2),
    13: (13, 1),
}

# precompute Phi_n coefficient lists (low-degree-first), monic, integer
PHI_COEFFS = {}
for n in TEST_SET:
    poly = sp.Poly(sp.cyclotomic_poly(n, Q), Q)
    coeffs_high_first = poly.all_coeffs()  # high degree first
    coeffs_low_first = coeffs_high_first[::-1]
    assert coeffs_low_first[-1] == 1, f"Phi_{n} not monic?!"
    PHI_COEFFS[n] = [int(c) for c in coeffs_low_first]


def shift_to_nonneg(poly: dict) -> list:
    """Convert a Laurent polynomial dict {exponent:int} to an ordinary
    polynomial coefficient list (low-degree-first), by shifting all
    exponents up by -min_exponent (equivalent to multiplying by q^k,
    a unit, so divisibility by any Phi_n is unaffected)."""
    if not poly:
        return [0]
    min_e = min(poly.keys())
    max_e = max(poly.keys())
    length = max_e - min_e + 1
    out = [0] * length
    for e, c in poly.items():
        out[e - min_e] = c
    return out


def poly_rem_monic(dividend: list, divisor: list) -> list:
    """Exact integer polynomial remainder of dividend / divisor, where
    divisor is monic (leading coeff 1), both low-degree-first lists.
    Since divisor is monic, no division ever occurs -- pure integer
    subtract-and-shift, so the whole computation is exact integer
    arithmetic (this generalizes the q^2=-1 bucket trick used for Phi_4
    in task3_phi4_census.py to a general monic-divisor long division)."""
    rem = list(dividend)
    dvd_deg = len(divisor) - 1
    # strip leading zeros conceptually by tracking degree
    deg = len(rem) - 1
    while deg >= dvd_deg:
        # find actual leading coefficient (skip trailing zero coeffs)
        while deg >= 0 and rem[deg] == 0:
            deg -= 1
        if deg < dvd_deg:
            break
        lead = rem[deg]
        if lead != 0:
            shift = deg - dvd_deg
            for i, dc in enumerate(divisor):
                rem[shift + i] -= lead * dc
        deg -= 1
    # trim
    while len(rem) > 1 and rem[-1] == 0:
        rem.pop()
    return rem


def is_zero_poly(p: list) -> bool:
    return all(c == 0 for c in p)


def phi_divides(poly_dict: dict, n: int) -> bool:
    if not poly_dict:
        return True  # zero polynomial divisible by anything
    dividend = shift_to_nonneg(poly_dict)
    divisor = PHI_COEFFS[n]
    rem = poly_rem_monic(dividend, divisor)
    return is_zero_poly(rem)


def v_p(x: int, p: int) -> int:
    if x == 0:
        return -1  # sentinel: infinite valuation, flag separately
    v = 0
    x = abs(x)
    while x % p == 0:
        x //= p
        v += 1
    return v


def main(dmax_exhaustive=1000, dmax_hunt=3000, hunt_ns=(9, 16, 25, 27)):
    t0 = time.time()
    hit_rows = []  # rows with a >= 2
    n_tested = 0
    n_squares_skipped = 0
    timing_log = []

    def process_d(d, ns_to_test):
        nonlocal n_tested
        a0 = math.isqrt(d)
        if a0 * a0 == d:
            return None
        n_tested += 1
        (r, s), (A, B, C, D) = fastlam.lam_q_fast(d)
        # for each prime present in ns_to_test, find max power that divides
        results = {}
        for n in ns_to_test:
            results[n] = phi_divides(C, n)
        return s, results

    # Phase 1: exhaustive over d <= dmax_exhaustive, test the FULL set
    print(f"Phase 1: exhaustive d=2..{dmax_exhaustive}, full test set {TEST_SET}")
    for d in range(2, dmax_exhaustive + 1):
        a0 = math.isqrt(d)
        if a0 * a0 == d:
            n_squares_skipped += 1
            continue
        n_tested += 1
        (r, s), (A, B, C, D) = fastlam.lam_q_fast(d)
        divides = {n: phi_divides(C, n) for n in TEST_SET}
        for n, (p, a) in PRIME_POWER.items():
            if a >= 2 and divides[n]:
                # downward closure check
                closure_ok = all(divides[p ** j] for j in range(1, a))
                vps = v_p(s, p)
                hit_rows.append(dict(d=d, n=n, p=p, a=a, closure_ok=closure_ok,
                                      v_p_s=vps, s=s))
        if d % 200 == 0:
            print(f"  d={d} done, elapsed={time.time()-t0:.1f}s, hits so far={len(hit_rows)}")

    phase1_elapsed = time.time() - t0
    print(f"Phase 1 done: elapsed={phase1_elapsed:.1f}s, n_tested={n_tested}, hits={len(hit_rows)}")

    # Phase 2: hunt for Phi_9/16/25/27 (and their downward-closure primes)
    # from dmax_exhaustive+1 .. dmax_hunt. For each hunt n=p^a, we must also
    # test p^1..p^(a-1) for the closure check, so include those in ns_to_test.
    hunt_test_ns = set()
    for n in hunt_ns:
        p, a = PRIME_POWER[n]
        for j in range(1, a + 1):
            hunt_test_ns.add(p ** j)
    hunt_test_ns = sorted(hunt_test_ns)
    print(f"Phase 2: hunting d={dmax_exhaustive+1}..{dmax_hunt} for n in {hunt_ns}, "
          f"testing {hunt_test_ns}")

    t1 = time.time()
    n_tested_phase2 = 0
    for d in range(dmax_exhaustive + 1, dmax_hunt + 1):
        a0 = math.isqrt(d)
        if a0 * a0 == d:
            continue
        n_tested_phase2 += 1
        (r, s), (A, B, C, D) = fastlam.lam_q_fast(d)
        divides = {n: phi_divides(C, n) for n in hunt_test_ns}
        for n in hunt_ns:
            p, a = PRIME_POWER[n]
            if divides[n]:
                closure_ok = all(divides[p ** j] for j in range(1, a))
                vps = v_p(s, p)
                hit_rows.append(dict(d=d, n=n, p=p, a=a, closure_ok=closure_ok,
                                      v_p_s=vps, s=s))
        if d % 200 == 0:
            print(f"  d={d} done, elapsed={time.time()-t1:.1f}s, hits so far={len(hit_rows)}")

    phase2_elapsed = time.time() - t1
    total_elapsed = time.time() - t0
    print(f"Phase 2 done: elapsed={phase2_elapsed:.1f}s, n_tested={n_tested_phase2}")
    print(f"Total elapsed: {total_elapsed:.1f}s")

    return dict(
        dmax_exhaustive=dmax_exhaustive,
        dmax_hunt=dmax_hunt,
        hunt_ns=hunt_ns,
        n_tested_phase1=n_tested,
        n_tested_phase2=n_tested_phase2,
        hit_rows=hit_rows,
        phase1_elapsed=phase1_elapsed,
        phase2_elapsed=phase2_elapsed,
        total_elapsed=total_elapsed,
    )


if __name__ == "__main__":
    res = main()
    hits = res["hit_rows"]
    hits.sort(key=lambda h: (h["d"], h["n"]))

    print("\n=== FULL HIT LIST (a >= 2) ===")
    print(f"{'d':>6} {'p^a':>6} {'p':>3} {'a':>2} {'closure_ok':>11} {'v_p(s)':>7} {'s':>10}")
    for h in hits:
        print(f"{h['d']:>6} {h['n']:>6} {h['p']:>3} {h['a']:>2} {str(h['closure_ok']):>11} "
              f"{h['v_p_s']:>7} {h['s']:>10}")

    n_closure_ok = sum(1 for h in hits if h["closure_ok"])
    n_closure_fail = sum(1 for h in hits if not h["closure_ok"])
    print(f"\nVerdict: {len(hits)} prime-power (a>=2) hits total; "
          f"{n_closure_ok} satisfy downward closure, {n_closure_fail} do NOT.")
    if n_closure_fail:
        print("EXCEPTIONS (closure fails):")
        for h in hits:
            if not h["closure_ok"]:
                print(f"  d={h['d']} n={h['n']} p={h['p']} a={h['a']}")

    # v_p(s) >= a check
    n_vps_ge_a = sum(1 for h in hits if h["v_p_s"] >= h["a"])
    n_vps_lt_a = sum(1 for h in hits if h["v_p_s"] < h["a"])
    print(f"\nv_p(s) >= a holds for {n_vps_ge_a}/{len(hits)}; fails for {n_vps_lt_a}")
    if n_vps_lt_a:
        print("EXCEPTIONS (v_p(s) < a):")
        for h in hits:
            if h["v_p_s"] < h["a"]:
                print(f"  d={h['d']} n={h['n']} p={h['p']} a={h['a']} v_p(s)={h['v_p_s']}")

    # write csv
    import csv
    with open("downward-closure-hits.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["d", "n", "p", "a", "closure_ok", "v_p_s", "s"])
        for h in hits:
            w.writerow([h["d"], h["n"], h["p"], h["a"], h["closure_ok"], h["v_p_s"], h["s"]])
    print("\nfull hit list written to downward-closure-hits.csv")
