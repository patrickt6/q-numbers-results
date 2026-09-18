#!/usr/bin/env python3
"""Task 2: negative-Pell y-stratification for all nonsquare d<=6000.

For each d with cf_period_parity=='odd' (i.e. x^2-d y^2=-1 solvable), compute
the exact fundamental (x0,y0) via the CF-of-sqrt(d) periodic algorithm, then
cross-tabulate is_finite (from the census) by y0.
"""
import csv
import math
from collections import Counter, defaultdict

CENSUS = "<path>"
OUT_DIR = "<path>"


def sqrt_cf_period(d):
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
    return a0, period


def fundamental_neg_pell_fast(d):
    """d nonsquare. Returns (x0,y0) if -1 solvable (period odd), else None.
    Uses the standard fact: fundamental (x0,y0) = convergent at index l-1
    (0-indexed, terms = [a0, period[0], ..., period[l-2]])."""
    a0, period = sqrt_cf_period(d)
    l = len(period)
    if l % 2 == 0:
        return None
    terms = [a0] + period[:l - 1]  # length l
    p_m1, p_m2 = 1, 0
    q_m1, q_m2 = 0, 1
    p, qk = None, None
    for a in terms:
        p = a * p_m1 + p_m2
        qk = a * q_m1 + q_m2
        p_m2, p_m1 = p_m1, p
        q_m2, q_m1 = q_m1, qk
    assert p * p - d * qk * qk == -1, (d, p, qk)
    return p, qk


if __name__ == "__main__":
    rows = list(csv.DictReader(open(CENSUS)))
    solvable_rows = []
    unsolvable_finite = 0
    unsolvable_total = 0
    y0_by_d = {}

    for r in rows:
        d = int(r["d"])
        is_finite = r["is_finite"] == "True"
        parity = r["cf_period_parity"]
        if parity == "odd":
            res = fundamental_neg_pell_fast(d)
            assert res is not None
            x0, y0 = res
            y0_by_d[d] = y0
            solvable_rows.append((d, x0, y0, is_finite))
        else:
            unsolvable_total += 1
            if is_finite:
                unsolvable_finite += 1

    # cross-tab is_finite by y0
    tab = defaultdict(lambda: [0, 0])  # y0 -> [n_finite, n_infinite]
    for d, x0, y0, is_finite in solvable_rows:
        tab[y0][0 if is_finite else 1][()] if False else None
    tab = defaultdict(lambda: {"finite": 0, "infinite": 0, "d_finite": [], "d_infinite": []})
    for d, x0, y0, is_finite in solvable_rows:
        key = "finite" if is_finite else "infinite"
        tab[y0][key] += 1
        tab[y0][f"d_{key}"].append(d)

    print(f"Total nonsquare d in [2,6000]: {len(rows)}")
    print(f"Negative-Pell solvable (odd period): {len(solvable_rows)}")
    print(f"Negative-Pell UNsolvable (even period): {unsolvable_total}")
    print(f"  of which is_finite=True: {unsolvable_finite}  "
          f"(fraction {unsolvable_finite/unsolvable_total:.4f})")
    print()
    print("Cross-tab: is_finite by fundamental y0 (negative-Pell solvable d only)")
    print(f"{'y0':>6} {'n_finite':>9} {'n_infinite':>11} {'total':>7}")
    exceptions = []
    for y0 in sorted(tab.keys()):
        e = tab[y0]
        total = e["finite"] + e["infinite"]
        print(f"{y0:>6} {e['finite']:>9} {e['infinite']:>11} {total:>7}")

    print()
    rule_exceptions_15_infinite = []  # y0 in {1,5} but infinite
    rule_exceptions_other_finite = []  # y0 not in {1,5} but finite
    for d, x0, y0, is_finite in solvable_rows:
        if y0 in (1, 5) and not is_finite:
            rule_exceptions_15_infinite.append((d, x0, y0))
        if y0 not in (1, 5) and is_finite:
            rule_exceptions_other_finite.append((d, x0, y0))

    print("Rule test: 'neg-Pell solvable => finite iff y0 in {1,5}'")
    print(f"  y0 in {{1,5}} but is_finite=False (exceptions): {len(rule_exceptions_15_infinite)}")
    for row in rule_exceptions_15_infinite:
        print("   ", row)
    print(f"  y0 not in {{1,5}} but is_finite=True (exceptions): {len(rule_exceptions_other_finite)}")
    for row in rule_exceptions_other_finite:
        print("   ", row)

    with open(f"{OUT_DIR}/task2_negpell_all.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["d", "x0", "y0", "is_finite"])
        for row in solvable_rows:
            w.writerow(row)

    with open(f"{OUT_DIR}/task2_crosstab.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["y0", "n_finite", "n_infinite", "total"])
        for y0 in sorted(tab.keys()):
            e = tab[y0]
            w.writerow([y0, e["finite"], e["infinite"], e["finite"] + e["infinite"]])
