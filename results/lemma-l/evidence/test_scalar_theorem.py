"""
T2 (route B). Numerical falsification test for the proposed extension of
Lemma L proof (ii) past n = 5 via triangle-group rigidity.

Claimed theorem under test (the "scalar specialization theorem"):
  For every n >= 2 with n != 6, if Phi_n | C then Lambda_q(zeta_n) is a
  scalar matrix, i.e.
     (1) Phi_n | (A - D)
     (2) Phi_n | B
     (3) n | s
If ANY hit (d, n) with n != 6 violates (1), (2) or (3), the proposed proof
is WRONG and must be withdrawn.

n = 6 is excluded by the proof (the specialized representation is reducible
exactly at zeta_6); n = 6 hits are still checked and reported separately as
empirical data, not as a test of the theorem.

Three test populations:
  T-A: the composite-index hits already recorded in the 2026-07-11
       open-questions census (d <= 180), n in {6,10,12,14,18,20,22,24,26}.
  T-B: a fresh exhaustive sweep d = 2..600 over a composite test set
       {6,10,12,14,15,18,20,21,22,24,26,28,33,36}, finding all hits and
       checking them. This exercises indices with two distinct odd primes
       (15, 21, 33) that the census never hit.
  T-C: every odd prime-power row (n in {9,25,27}) of the 608-hit CSV from
       code-wp2, d <= 3000: the exact population of the T2 brief.

All arithmetic is exact: integer Laurent-polynomial dicts from
fastlam.lam_q_fast, monic integer long division by Phi_n.
"""
import sys
import csv
import math

sys.path.insert(0, "<path>")
import fastlam  # noqa: E402
import sympy as sp  # noqa: E402

Q = sp.Symbol('q')
PHI = {}


def phi_coeffs(n):
    if n not in PHI:
        poly = sp.Poly(sp.cyclotomic_poly(n, Q), Q)
        cl = [int(c) for c in poly.all_coeffs()[::-1]]
        assert cl[-1] == 1
        PHI[n] = cl
    return PHI[n]


def shift_to_nonneg(poly):
    if not poly:
        return [0]
    mn = min(poly)
    mx = max(poly)
    out = [0] * (mx - mn + 1)
    for e, c in poly.items():
        out[e - mn] = c
    return out


def poly_rem_monic(dividend, divisor):
    rem = list(dividend)
    dvd = len(divisor) - 1
    deg = len(rem) - 1
    while deg >= dvd:
        while deg >= 0 and rem[deg] == 0:
            deg -= 1
        if deg < dvd:
            break
        lead = rem[deg]
        if lead != 0:
            sh = deg - dvd
            for i, dc in enumerate(divisor):
                rem[sh + i] -= lead * dc
        deg -= 1
    while len(rem) > 1 and rem[-1] == 0:
        rem.pop()
    return rem


def phi_divides(pdict, n):
    if not pdict:
        return True
    return all(c == 0 for c in poly_rem_monic(shift_to_nonneg(pdict), phi_coeffs(n)))


def sub_poly(a, b):
    out = dict(a)
    for e, c in b.items():
        out[e] = out.get(e, 0) - c
        if out[e] == 0:
            del out[e]
    return out


LAM_CACHE = {}


def lam(d):
    if d not in LAM_CACHE:
        LAM_CACHE[d] = fastlam.lam_q_fast(d)
    return LAM_CACHE[d]


def check_hit(d, n):
    """Returns dict of the four properties for one (d, n)."""
    (r, s), (A, B, C, D) = lam(d)
    hitC = phi_divides(C, n)
    AmD = sub_poly(A, D)
    return dict(
        d=d, n=n, s=s,
        phi_div_C=hitC,
        phi_div_AmD=phi_divides(AmD, n),
        phi_div_B=phi_divides(B, n),
        n_div_s=(s % n == 0),
    )


def report(rows, label, exclude6=True):
    tested = [r for r in rows if r["phi_div_C"]]
    body = [r for r in tested if r["n"] != 6] if exclude6 else tested
    six = [r for r in tested if r["n"] == 6]
    viol = [r for r in body
            if not (r["phi_div_AmD"] and r["phi_div_B"] and r["n_div_s"])]
    print(f"\n=== {label} ===")
    print(f"hits tested (n != 6): {len(body)}; violations: {len(viol)}")
    for r in viol:
        print("  VIOLATION:", r)
    if six:
        v6 = [r for r in six
              if not (r["phi_div_AmD"] and r["phi_div_B"] and r["n_div_s"])]
        print(f"n = 6 hits (outside theorem): {len(six)}; "
              f"empirical violations of (1)(2)(3): {len(v6)}")
        for r in v6:
            print("  n=6 counter-instance:", r)
    return viol


def main():
    all_rows = []

    # T-A: known composite hits from the open-questions census
    census_hits = {
        6: [10, 34, 37, 38, 52, 76, 78, 82, 84, 117, 140, 142, 145, 146, 148, 154, 165],
        10: [26, 98, 101, 102],
        12: [37, 142, 145, 146],
        14: [50], 18: [82], 20: [101], 22: [122], 24: [145], 26: [170],
    }
    ta = []
    for n, ds in census_hits.items():
        for d in ds:
            rr = check_hit(d, n)
            if not rr["phi_div_C"]:
                print(f"  WARNING: census says Phi_{n} | C at d={d} but recheck fails")
            ta.append(rr)
    report(ta, "T-A: census composite hits, d <= 180")
    all_rows += ta

    # T-B: fresh sweep
    tb = []
    SWEEP_NS = [6, 10, 12, 14, 15, 18, 20, 21, 22, 24, 26, 28, 33, 36]
    for d in range(2, 601):
        a0 = math.isqrt(d)
        if a0 * a0 == d:
            continue
        (r, s), (A, B, C, D) = lam(d)
        for n in SWEEP_NS:
            if phi_divides(C, n):
                tb.append(check_hit(d, n))
    from collections import Counter
    cnt = Counter(r["n"] for r in tb)
    print("\nT-B hit counts by n:", dict(sorted(cnt.items())))
    report(tb, "T-B: fresh composite sweep d = 2..600")
    all_rows += tb

    # T-C: the odd prime-power rows of the 608-hit CSV
    tc = []
    csv_path = ("<path>"
                "<path>")
    for row in csv.DictReader(open(csv_path)):
        n = int(row["n"])
        if n in (9, 25, 27):
            tc.append(check_hit(int(row["d"]), n))
    report(tc, "T-C: odd prime-power hits (n in {9,25,27}) from the 608 CSV, d <= 3000")
    all_rows += tc

    # write full results
    out = ("<path>"
           "2026-07-21-next-steps/problems/T2-lemma-L-prime-powers/attempts/"
           "routeB/test_scalar_theorem_results.csv")
    with open(out, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["d", "n", "s", "phi_div_C", "phi_div_AmD", "phi_div_B", "n_div_s"])
        for r in all_rows:
            w.writerow([r["d"], r["n"], r["s"], r["phi_div_C"],
                        r["phi_div_AmD"], r["phi_div_B"], r["n_div_s"]])
    print(f"\nfull results written to {out}")


if __name__ == "__main__":
    main()
