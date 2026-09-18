#!/usr/bin/env python3
"""
Independent recomputation covering two claims:

1. Cross-check of r_d, s_d, cf_period_length, cf_period_parity in the
   pinned census CSV (all 5923 nonsquare d in [2,6000]) against a fresh,
   standalone PQa continued-fraction / Pell solver (mgo_engine.py), which
   does not import qreals/qpoly/census.

2. negpaper_certification_split: classify the 868 d<=6000 with
   r_d = +-1 (mod s_d) into "s_d prime or s_d=4" (unconditional) vs the
   remainder, and further split the remainder by whether s_d is a genuine
   prime power p^a, a>=2.

No qreals/qpoly/census import anywhere in this script.
"""
import csv
import sympy as sp

from mgo_engine import pell_fundamental_solution

CSV_PATH = "../../../2026-07-11-alexemail/code/census_d2_6000_slim.csv"


def is_prime_power(n):
    """Return (True, p, a) if n = p^a, a>=1, p prime; else (False, None, None)."""
    if n <= 1:
        return (False, None, None)
    fac = sp.factorint(n)
    if len(fac) == 1:
        p, a = next(iter(fac.items()))
        return (True, p, a)
    return (False, None, None)


def main():
    with open(CSV_PATH) as f:
        rows = list(csv.DictReader(f))

    n_rows = len(rows)
    mismatches_rs = []
    mismatches_period = []

    cert_hits = []  # d with r_d = +-1 mod s_d

    for r in rows:
        d = int(r["d"])
        file_r_d = int(r["r_d"])
        file_s_d = int(r["s_d"])
        file_plen = int(r["cf_period_length"])
        file_parity = r["cf_period_parity"]

        my_r_d, my_s_d, my_plen = pell_fundamental_solution(d)
        my_parity = "even" if my_plen % 2 == 0 else "odd"

        if (my_r_d, my_s_d) != (file_r_d, file_s_d):
            mismatches_rs.append((d, (file_r_d, file_s_d), (my_r_d, my_s_d)))
        if my_plen != file_plen or my_parity != file_parity:
            mismatches_period.append(
                (d, (file_plen, file_parity), (my_plen, my_parity))
            )

        # certification_split uses r_d, s_d; use the file's values as the
        # object under test (same numbers the paper claim is about), since
        # this part of the script is now cross-validated against them above.
        if (file_r_d % file_s_d) in (1 % file_s_d, (file_s_d - 1) % file_s_d):
            cert_hits.append((d, file_r_d, file_s_d))

    unconditional = []  # s_d prime or s_d == 4
    conditional_prime_power = []  # s_d = p^a, a>=2 (genuine prime power, not prime, not 4)
    conditional_other = []

    for d, r_d, s_d in cert_hits:
        if s_d == 4 or sp.isprime(s_d):
            unconditional.append((d, s_d))
            continue
        ok, p, a = is_prime_power(s_d)
        if ok and a >= 2:
            conditional_prime_power.append((d, s_d, p, a))
        else:
            conditional_other.append((d, s_d))

    result = {
        "n_rows_checked": n_rows,
        "rs_mismatches": len(mismatches_rs),
        "rs_mismatch_examples": mismatches_rs[:10],
        "period_mismatches": len(mismatches_period),
        "period_mismatch_examples": mismatches_period[:10],
        "certification_split": {
            "total_r_pm1_mod_s": len(cert_hits),
            "unconditional_s_prime_or_4": len(unconditional),
            "conditional_total": len(conditional_prime_power) + len(conditional_other),
            "conditional_genuine_prime_power": len(conditional_prime_power),
            "conditional_other": len(conditional_other),
        },
        "claim_recorded": {
            "total_r_pm1_mod_s": 868,
            "unconditional_s_prime_or_4": 329,
            "conditional_total": 539,
            "conditional_genuine_prime_power": 93,
            "conditional_other": 446,
        },
    }
    print(result)
    return result


if __name__ == "__main__":
    main()
