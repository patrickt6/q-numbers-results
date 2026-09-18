#!/usr/bin/env python3
"""Reproduce the integer Hankel + Somos / Gale-Robinson tables of
Ovsienko and Pedon, arXiv:2312.17009v2, on the metallic numbers
y_1 (golden), y_2 (silver), y_3 (bronze), y_4.

The definition (Section 1.3, eq (1.16)). For a q-real x with
  [x]_q = sum_{n>=0} a_n q^n
the n-th Hankel determinant is
  Delta_n(x) = det( a_{i+j} ){0<=i,j<n}
and the shifted variant Delta_n^(ell)(x) drops the first ell coefficients
of [x]_q before computing the determinant. The first row Delta_1 = a_0.

The unified target (Conjecture 1.9 / Theorem of Han-Pedon arXiv:2502.05993).
For y_k = (k + sqrt(k^2 + 4))/2 and each shift ell with 0 <= ell <= k+1,
the Hankel sequence (Delta_n^(ell)(y_k)) is 2k(k+1)-periodic for even k
or 2k(k+1)-antiperiodic for odd k, and satisfies the three-term
Gale-Robinson recurrence
  Delta_{n+2k+2} Delta_n = Delta_{n+2k+1} Delta_{n+1} - (Delta_{n+k+1})^2 .

This file
  (1) builds [y_k]_q to N coefficients via qreals.q_real_truncated,
  (2) computes Delta_n^(ell)(y_k) for n = 1, ..., N_check,
  (3) writes somos_table.csv (n in 0..period-1 stores Delta_{n+1}^(ell)),
  (4) writes somos_check.csv with the recurrence test, indexed so that
      row n stores
        lhs = Delta_{n+2k+2}^(ell) * Delta_n^(ell) (n in 1..N_check - 2k - 2),
        rhs = Delta_{n+2k+1}^(ell) * Delta_{n+1}^(ell) - (Delta_{n+k+1}^(ell))^2,
        match = (lhs == rhs),
  (5) prints a small summary and SHA-256 of somos_check.csv.

The script is pure (deterministic): re-running produces the same files
modulo timestamps. Registration into provstore is done by register_somos.py.
"""

from __future__ import annotations

import csv
import hashlib
import sys
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
QNROOT = HERE.parent.parent  # qnumbers/
QREALS_SRC = QNROOT.parent / "qreals" / "src"
if QREALS_SRC.is_dir():
    sys.path.insert(0, str(QREALS_SRC))

from qreals import q_real_truncated  # noqa: E402


# Metallic numbers y_k = (k + sqrt(k^2 + 4)) / 2.
def metallic(k: int) -> sp.Expr:
    return (sp.Integer(k) + sp.sqrt(k * k + 4)) / 2


# Period of the Hankel row predicted by Conjecture 1.9 (full period: the
# smallest p > 0 with Delta_{n+p}^(ell) = +Delta_n^(ell)). For even k this is
# 2k(k+1) (the conjecture's "2k(k+1)-periodic"). For odd k the row is
# 2k(k+1)-antiperiodic, so the full period is 4k(k+1); Theorem 1.6 confirms
# this for k=1 with full period 8.
def predicted_period(k: int) -> int:
    if k % 2 == 0:
        return 2 * k * (k + 1)
    return 4 * k * (k + 1)


# Coefficient budget for one k. We need at least N_check + ell + 2k+2 coefficients
# of [y_k]_q to compute Delta_{N_check + 2k + 2}^(ell). N_check is set so the
# recurrence covers at least one full period.
def coeff_budget(k: int, n_check: int) -> int:
    # Largest Hankel size used is n_check + 2k + 2. That determinant needs
    # coefficients a_0 .. a_{2 (n_check + 2k + 2) - 2 + ell}, so with the
    # maximum shift ell = k+1 the largest index needed is
    # 2(n_check + 2k + 2) - 2 + (k + 1) = 2 n_check + 5k + 3.
    return 2 * n_check + 5 * k + 4


def hankel_det(seq: list[int], n: int, shift: int) -> int:
    """Delta_n^(shift) from a coefficient list. Uses sympy's integer det."""
    if n == 0:
        return 1  # convention: Delta_0 = 1 (the empty product)
    M = sp.Matrix(n, n, lambda i, j: seq[shift + i + j])
    return int(M.det())


def build_delta_row(seq: list[int], shift: int, n_max: int) -> list[int]:
    """[Delta_1^(shift), ..., Delta_{n_max}^(shift)]."""
    return [hankel_det(seq, n, shift) for n in range(1, n_max + 1)]


def write_somos_table(rows: list[tuple[int, int, int, int]], out: Path) -> None:
    with out.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["k", "shift_ell", "n", "delta_value"])
        for row in rows:
            w.writerow(row)


def write_somos_check(rows: list[tuple[int, int, int, int, int, bool]], out: Path) -> None:
    with out.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["k", "shift_ell", "n", "lhs", "rhs", "match"])
        for row in rows:
            w.writerow(row)


def sha256_of(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def run(out_dir: Path) -> dict:
    out_dir.mkdir(parents=True, exist_ok=True)

    table_rows: list[tuple[int, int, int, int]] = []
    check_rows: list[tuple[int, int, int, int, int, bool]] = []

    coeff_blocks: dict[int, list[int]] = {}
    delta_rows: dict[tuple[int, int], list[int]] = {}

    # Per-k summary.
    summary: dict[int, dict] = {}

    for k in (1, 2, 3, 4):
        period = predicted_period(k)
        # Cover at least one full period plus the recurrence reach 2k+2.
        n_check = period + 2 * k + 2
        budget = coeff_budget(k, n_check)
        # Compute the q-real series.
        coeffs = q_real_truncated(metallic(k), budget)
        coeff_blocks[k] = coeffs

        max_dets_per_row: dict[int, int] = {}

        for ell in range(0, k + 2):  # ell = 0, 1, ..., k+1 inclusive
            row = build_delta_row(coeffs, shift=ell, n_max=n_check)
            delta_rows[(k, ell)] = row

            # Table: n in 0..period - 1 stores Delta_{n+1}^(ell).
            for n in range(0, period):
                table_rows.append((k, ell, n, row[n]))

            # Recurrence check (1-indexed reading of (1.22)):
            # Delta_{m+2k+2} Delta_m = Delta_{m+2k+1} Delta_{m+1} - Delta_{m+k+1}^2
            # We sweep m = 1, ..., (period). The CSV records lhs, rhs, match.
            n_match = 0
            n_total = 0
            for m in range(1, period + 1):
                # Indices into row: row[i-1] = Delta_i^(ell).
                d_m = row[m - 1]
                d_m1 = row[m]
                d_mk1 = row[m + k]
                d_m2k1 = row[m + 2 * k]
                d_m2k2 = row[m + 2 * k + 1]
                lhs = d_m2k2 * d_m
                rhs = d_m2k1 * d_m1 - d_mk1 * d_mk1
                match = (lhs == rhs)
                n_total += 1
                if match:
                    n_match += 1
                check_rows.append((k, ell, m, int(lhs), int(rhs), bool(match)))

            max_dets_per_row[ell] = max(abs(int(v)) for v in row)

            print(f"  k={k} ell={ell}  period={period}  recurrence "
                  f"{n_match}/{n_total} match  |Delta|_max={max_dets_per_row[ell]}")

        summary[k] = {
            "period": period,
            "n_check": n_check,
            "budget": budget,
            "max_abs_delta": max(max_dets_per_row.values()),
        }

    # Write tables.
    table_path = out_dir / "somos_table.csv"
    check_path = out_dir / "somos_check.csv"
    write_somos_table(table_rows, table_path)
    write_somos_check(check_rows, check_path)

    # Per-k match counts in the final dict.
    per_k_match: dict[int, tuple[int, int]] = {}
    for row in check_rows:
        k = row[0]
        per_k_match.setdefault(k, [0, 0])
        per_k_match[k][1] += 1
        if row[5]:
            per_k_match[k][0] += 1

    return {
        "table_rows": len(table_rows),
        "check_rows": len(check_rows),
        "per_k_match": {k: (m, t) for k, (m, t) in per_k_match.items()},
        "table_sha256": sha256_of(table_path),
        "check_sha256": sha256_of(check_path),
        "summary": summary,
    }


if __name__ == "__main__":
    result = run(HERE)
    print()
    print("table rows         :", result["table_rows"])
    print("check rows         :", result["check_rows"])
    for k in (1, 2, 3, 4):
        m, t = result["per_k_match"][k]
        rate = m / t if t else float("nan")
        print(f"k={k} match rate    : {m}/{t}  ({rate:.4f})")
    print()
    print("somos_table.csv sha256 :", result["table_sha256"])
    print("somos_check.csv sha256 :", result["check_sha256"])
