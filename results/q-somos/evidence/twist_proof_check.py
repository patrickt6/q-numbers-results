#!/usr/bin/env python3
"""Symbolic verification accompanying q-somos-twist-proof.pdf.

The proof PDF establishes three facts on the window
  W = { (a, b) in {-3, ..., 3}^2,  n in {4, ..., 11} }
for iterates of the q-twisted Somos-4 recurrence
  x_{n+4} x_n = q^a x_{n+3} x_{n+1} + q^b (x_{n+2})^2
over Z[q, q^{-1}][x_0, x_1, x_2, x_3]:

  (S) Support stability.  The (x_0, x_1, x_2, x_3) Laurent-monomial support of
      x_n^{(a, b)} equals that of the integer-Somos-4 iterate x_n^{(0, 0)};
      the denominator x-exponent vector is the same across all 49 pairs.
  (Q) q-coefficient palindromicity at q = 1.  For every monomial M in that
      support, the q-coefficient of M in x_n^{(a, b)} reduces at q = 1 to the
      integer coefficient of M in x_n^{(0, 0)}.
  (A) OEIS landing.  Specializing q = 1 and x_0 = x_1 = x_2 = x_3 = 1 returns
      the integer Somos-4 value x_n^{Somos} = OEIS A006720(n) for every pair.

Each cell of the 49 x 8 = 392 window is checked independently.

Output:
    twist_proof_check.json with row counts per fact and the pass / fail tally.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
q = sp.Symbol('q')
X = sp.symbols('x0 x1 x2 x3')

A_RANGE = range(-3, 4)
B_RANGE = range(-3, 4)
N_MIN = 4
N_MAX = 11
A006720 = [1, 1, 1, 1, 2, 3, 7, 23, 59, 314, 1529, 8209]


def step(seq, a: int, b: int, n: int):
    """One iterate of the q-twisted Somos-4 recurrence."""
    return sp.cancel((q ** a * seq[n - 1] * seq[n - 3] + q ** b * seq[n - 2] ** 2) / seq[n - 4])


def trajectory(a: int, b: int, n_max: int):
    seq = list(X)
    for n in range(N_MIN, n_max + 1):
        seq.append(step(seq, a, b, n))
    return seq


def laurent_decomp(xab):
    """Return (laurent_terms, denom_x_exp), where laurent_terms is a dict
    Laurent-exponent -> q-coefficient.
    """
    num, den = sp.fraction(sp.together(xab))
    pn = sp.Poly(sp.expand(num), *X, domain=sp.QQ.frac_field(q))
    pd = sp.Poly(sp.expand(den), *X, domain=sp.QQ.frac_field(q))
    dm_x = pd.monoms()[0]
    dq = pd.coeffs()[0]
    out = {}
    for m, c in zip(pn.monoms(), pn.coeffs()):
        L = tuple(int(mi - di) for mi, di in zip(m, dm_x))
        out[L] = sp.cancel(c / dq)
    return out, dm_x


def run():
    seq00 = trajectory(0, 0, N_MAX)
    ref = {}  # n -> (support set, denom x-exp, coefficient dict at q = 1)
    for n in range(N_MIN, N_MAX + 1):
        decomp, dm = laurent_decomp(seq00[n])
        coeffs_q1 = {L: int(sp.simplify(c.subs(q, 1))) for L, c in decomp.items()}
        ref[n] = (frozenset(decomp.keys()), tuple(int(e) for e in dm), coeffs_q1)

    cell_count = 0
    fail_S = 0   # support failures
    fail_Q = 0   # q = 1 coefficient failures (per monomial)
    fail_A = 0   # OEIS specialization failures

    per_cell = []

    for a in A_RANGE:
        for b in B_RANGE:
            seq = trajectory(a, b, N_MAX)
            for n in range(N_MIN, N_MAX + 1):
                cell_count += 1
                decomp, dm = laurent_decomp(seq[n])
                ref_sup, ref_dm, ref_coeffs = ref[n]
                sup_ok = (frozenset(decomp.keys()) == ref_sup) and (tuple(int(e) for e in dm) == ref_dm)
                if not sup_ok:
                    fail_S += 1
                q1_ok = True
                for L, c in decomp.items():
                    c1 = sp.simplify(c.subs(q, 1))
                    if c1 != ref_coeffs.get(L, None):
                        q1_ok = False
                        fail_Q += 1
                val = sp.simplify(seq[n].subs({q: 1, X[0]: 1, X[1]: 1, X[2]: 1, X[3]: 1}))
                a006720_ok = (int(val) == A006720[n])
                if not a006720_ok:
                    fail_A += 1
                per_cell.append({
                    "a": a, "b": b, "n": n,
                    "support_ok": bool(sup_ok),
                    "q1_coeff_ok": bool(q1_ok),
                    "a006720_ok": bool(a006720_ok),
                })

    out = {
        "cells_checked": cell_count,
        "support_failures": fail_S,
        "q1_coefficient_failures": fail_Q,
        "a006720_failures": fail_A,
        "a_range": [A_RANGE.start, A_RANGE.stop - 1],
        "b_range": [B_RANGE.start, B_RANGE.stop - 1],
        "n_range": [N_MIN, N_MAX],
        "A006720_initial_segment": A006720[N_MIN:N_MAX + 1],
        "all_pass": (fail_S == 0 and fail_Q == 0 and fail_A == 0),
    }
    out_path = HERE / "twist_proof_check.json"
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")
    out["sha256_self"] = hashlib.sha256(out_path.read_bytes()).hexdigest()
    return out


if __name__ == "__main__":
    summary = run()
    print(json.dumps(summary, indent=2))
