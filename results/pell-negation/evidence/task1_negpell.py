#!/usr/bin/env python3
"""Task 1: fundamental negative-Pell solution (x0,y0) of x^2 - d y^2 = -1
for the 30 exceptional d (census_d2_6000_slim.csv: is_finite=True,
S_is_cyc_squarefree_product=False) plus d=2. Exact integer CF method.
"""
import csv
import math
import sys

sys.path.insert(0, "<path>")

CENSUS = "<path>"


def cf_sqrt_terms(d, num_terms):
    a0 = math.isqrt(d)
    assert a0 * a0 != d
    terms = [a0]
    m, den, a = 0, 1, a0
    while len(terms) < num_terms:
        m = den * a - m
        den = (d - m * m) // den
        a = (a0 + m) // den
        terms.append(a)
    return terms


def convergents(terms):
    convs = []
    p_m1, p_m2 = 1, 0
    q_m1, q_m2 = 0, 1
    for a in terms:
        p = a * p_m1 + p_m2
        qk = a * q_m1 + q_m2
        convs.append((p, qk))
        p_m2, p_m1 = p_m1, p
        q_m2, q_m1 = q_m1, qk
    return convs


def fundamental_neg_pell(d, max_terms=400):
    """Brute-force but exact search over CF convergents of sqrt(d) for the
    FIRST one with p^2 - d*qk^2 == -1. Returns None if none found within
    max_terms (i.e. -1 not solvable, or period too long)."""
    terms = cf_sqrt_terms(d, max_terms)
    convs = convergents(terms)
    for k, (p, qk) in enumerate(convs):
        val = p * p - d * qk * qk
        if val == -1:
            return p, qk, k, terms[:k + 1]
    return None


def sqrt_cf_period_length(d):
    a0 = math.isqrt(d)
    m, den, a = 0, 1, a0
    period = []
    while True:
        m = den * a - m
        den = (d - m * m) // den
        a = (a0 + m) // den
        period.append(a)
        if a == 2 * a0:
            break
    return len(period)


def n_for_d(d):
    """d = (n^2+1)/25 with n = +-7 mod 25, n>0 minimal such n (n = 5*sqrt(d) approx)."""
    # n^2 = 25d - 1
    val = 25 * d - 1
    n = math.isqrt(val)
    if n * n == val:
        return n
    return None


if __name__ == "__main__":
    rows = list(csv.DictReader(open(CENSUS)))
    exc = [int(r["d"]) for r in rows
           if r["is_finite"] == "True" and r["S_is_cyc_squarefree_product"] == "False"]
    exc = sorted(exc)
    assert len(exc) == 30, len(exc)

    targets = [2] + exc
    out_rows = []
    for d in targets:
        n = n_for_d(d)
        res = fundamental_neg_pell(d)
        plen = sqrt_cf_period_length(d)
        if res is None:
            out_rows.append((d, n, None, None, None, plen))
            continue
        x0, y0, k, terms = res
        assert x0 * x0 - d * y0 * y0 == -1
        out_rows.append((d, n, x0, y0, k, plen))

    print(f"{'d':>6} {'n':>6} {'x0':>10} {'y0':>6} {'conv_idx':>9} {'cf_period':>10}")
    for d, n, x0, y0, k, plen in out_rows:
        print(f"{d:>6} {n!s:>6} {x0!s:>10} {y0!s:>6} {k!s:>9} {plen!s:>10}")

    # write CSV
    with open("<path>", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["d", "n", "x0", "y0", "conv_idx", "cf_period_length"])
        for row in out_rows:
            w.writerow(row)

    # verification summary
    exc_y0 = [row[3] for row in out_rows if row[0] != 2]
    d2_y0 = [row[3] for row in out_rows if row[0] == 2][0]
    print()
    print("All 30 exceptional y0==5:", all(y == 5 for y in exc_y0))
    print("d=2 y0:", d2_y0, "(expect 1)")
    print("All n match +-7 mod 25:", all(n is not None and (n % 25 in (7, 18)) for d, n, *_ in out_rows))
