r"""Oracle check: the general routine must reproduce the pure-surd code.

Three independent checks, all on x = sqrt(d) for nonsquare d:

  A. The automorph computed by `qperiod.period_data` from the Hirzebruch-Jung
     period equals the fundamental Pell automorph [[r, d s], [s, r]] used by
     `fastlam.lam_q_fast`, or a power of it. Equality of (A - D)/C across
     powers is exactly what Cayley-Hamilton guarantees in `thm:pell`, so a
     power is an acceptable outcome and is reported when it occurs.
  B. The q-deformation rho(M) computed here agrees entry-by-entry with
     `lam_q_fast(d)` whenever check A gives the fundamental automorph itself.
  C. The candidate (A - D)/C computed here equals the one computed from
     `lam_q_fast(d)`, as an exact identity of rational functions. This is the
     check that matters, since (A - D)/C is the object the conjecture is about
     and it is power-invariant.

Additionally, D: the structural predicates report `symmetric = True` and
`intertwines = True` for every pure surd, which is the content of the
`ssec:beyond-pure` observation that a = d' holds for a pure square root.

No pytest: plain assertions, per project policy.

Run:
    PYTHONPATH=<path> python3 check_oracle.py
"""

from __future__ import annotations

import sys

import sympy as sp

from qperiod import (
    ad_over_c,
    mat_mul,
    period_data,
    rho_q,
    structure,
)
from qreals.quadratic import QuadraticIrrational
from fastlam import lam_q_fast

D_LIST = [2, 3, 5, 6, 7, 8, 10, 11, 12, 13, 15, 18, 19, 21, 22, 27, 29, 31, 43, 45, 50, 53, 61, 75]


def sqrt_qi(d: int) -> QuadraticIrrational:
    """sqrt(d) as a QuadraticIrrational, pulling out any square factor."""
    D = d
    f = 1
    i = 2
    while i * i <= D:
        while D % (i * i) == 0:
            D //= i * i
            f *= i
        i += 1
    return QuadraticIrrational(0, f, 1, D)


def matrix_power(M, k):
    out = ((1, 0), (0, 1))
    for _ in range(k):
        out = mat_mul(out, M)
    return out


def main() -> int:
    failures = []
    for d in D_LIST:
        x = sqrt_qi(d)
        pd = period_data(x)
        M = pd.automorph
        (r, s), (fA, fB, fC, fD) = lam_q_fast(d)
        Lam = ((r, d * s), (s, r))

        # A: automorph identification
        power = None
        P = ((1, 0), (0, 1))
        for k in range(1, 5):
            P = mat_mul(P, Lam)
            if M == P:
                power = k
                break
        if power is None:
            failures.append(f"d={d}: automorph {M} is not a power <=4 of {Lam}")
            continue

        # B: entrywise rho agreement, when M is the fundamental automorph
        A, B, C, Dq = rho_q(M)
        if power == 1:
            same = (A == fA and B == fB and C == fC and Dq == fD)
            if not same:
                failures.append(f"d={d}: rho entries differ from lam_q_fast")

        # C: the power-invariant candidate
        mine = ad_over_c((A, B, C, Dq))
        theirs = ad_over_c((fA, fB, fC, fD))
        if sp.cancel(mine - theirs) != 0:
            failures.append(f"d={d}: (A-D)/C mismatch, {sp.factor(mine)} vs {sp.factor(theirs)}")

        # D: structural predicates
        st = structure(M)
        if not st.symmetric:
            failures.append(f"d={d}: pure surd automorph reported non-symmetric")
        if not st.intertwines_z:
            failures.append(f"d={d}: N M N = M^-1 failed at the integer level")
        if not st.intertwines_q:
            failures.append(f"d={d}: (N M N)_q = M_q^-1 failed at the q level")

        print(
            f"d={d:3d}  pell=({r},{s})  automorph = Lambda^{power}  "
            f"rho {'match' if power == 1 else 'n/a'}  (A-D)/C match  "
            f"sym={st.symmetric} intertwine_Z={st.intertwines_z} intertwine_q={st.intertwines_q}  "
            f"(A-D)/C = {sp.factor(mine)}"
        )

    print()
    if failures:
        print(f"FAIL: {len(failures)} problems")
        for f in failures:
            print("  " + f)
        return 1
    print(f"PASS: {len(D_LIST)} values of d, all four checks green")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
