#!/usr/bin/env python3
"""
Independent recomputation of claim negpaper_degree_equality_d400.

Reuses the independent q-continuant engine in verify_twin_primes_tail.py
(built from the algorithm definition, not from qpoly.py or qreals). Adds
no new dependency on the tracked codebase.

Claim under test:
  For all 2<=d<=400 and all 1<=a<d with gcd(a,d)=1 (48,677 pairs),
  deg S_{a/d} = d-1 holds if and only if a in {1,d-1}, and in those cases
  S = [d]_q exactly; zero exceptions.
"""
import math
import sys
import os

sys.path.insert(0, os.path.dirname(__file__))
from verify_twin_primes_tail import S_of  # noqa: E402


def main(d_max=400):
    n_checked = 0
    exceptions = []
    for d in range(2, d_max + 1):
        for a in range(1, d):
            if math.gcd(a, d) != 1:
                continue
            n_checked += 1
            S = S_of(a, d)
            deg_s = S.degree()
            predicted_full = a in (1, d - 1)
            actual_full = (deg_s == d - 1)
            if predicted_full != actual_full:
                exceptions.append((a, d, deg_s, "degree_mismatch"))
                continue
            if actual_full:
                coeffs = S.all_coeffs()[::-1]  # ascending
                if coeffs != [1] * d:
                    exceptions.append((a, d, coeffs, "S_not_full_qint"))

    result = {
        "d_max": d_max,
        "n_pairs_checked": n_checked,
        "n_exceptions": len(exceptions),
        "exceptions": exceptions[:20],
    }
    print(result)
    return result


if __name__ == "__main__":
    main()
