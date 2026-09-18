#!/usr/bin/env python3
r"""
Exact multiplication-deficit dataset from the q-Gosper engine.

For a pair of rationals x, y > 1 the q-Gosper engine (q_gosper.py) gives two
exact rational functions in q, both read off the SAME MGO q-blocks:

    [x]_q * [y]_q  =  q_gosper(x, y, "mul")      # bihomographic engine value
    [xy]_q         =  q_real_rational(x * y)      # single q-real, same q-blocks

The multiplication deficit is their exact difference

    Dx_{x,y}(q)  =  [xy]_q - [x]_q * [y]_q,

a Laurent (in fact ordinary-plus-rational, since x,y>1) rational function over
Z[q,q^{-1}]. The MGO deformation map x|->[x]_q is not multiplicative, so Dx is
generically nonzero; the structural invariants observed across every pair are

    Dx(0) = 0        (constant term: 1 from [xy]_q minus 1*1 from [x]_q*[y]_q),
    Dx(1) = 0        (multiplicativity is restored at q=1, where [x]_q -> x).

Unlike the additive deficit (whose Dx(0) is the fixed -1), the multiplicative
deficit vanishes at q=0 and, on some pairs, vanishes identically: a handful of
x,y satisfy [xy]_q = [x]_q*[y]_q exactly. Those rows are flagged "exact" and
counted; this module does NOT assume any closed form for Dx (that is later
work) -- it only records the engine's exact output.

This module builds a dataset of >= 200 such pairs (both integer-product and
non-integer-product), recording for each the head Laurent coefficients of Dx
together with Dx(1) and Dx(0). It REUSES the engine entry points in q_gosper.py
verbatim (q_real_rational, q_gosper, laurent_coeffs, q_valuation) -- no q-blocks
are re-derived here, and neither q_gosper.py nor the qreals package is modified.

The independent qreals-vs-engine ground-truth cross-check lives in a separate
verification harness (its positive arm proves q_gosper(.,.,"mul") == qreals
[x]_q*[y]_q); this module therefore trusts the engine and stays self-contained.
It mirrors make_deficit_dataset.py (the additive sibling) field for field.

Entry points:
    build_mult_deficit_summary()  -- deterministic, JSON-serialisable summary of
                                     the whole dataset (the provenance entry).
    write_csv(path)               -- compute and write mult_deficit_dataset.csv.

Run:  python make_mult_deficit_dataset.py     # writes mult_deficit_dataset.csv
"""
from __future__ import annotations

import csv
import sys
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from q_gosper import (  # noqa: E402  (reuse the engine; do not re-derive blocks)
    laurent_coeffs,
    q,
    q_gosper,
    q_real_rational,
    q_valuation,
)

# Number of head Laurent coefficients c_0..c_{HEAD_K-1} recorded per pair.
# >= 6 so the (2,3) anchor row carries the full head 0,-1,-1,0,1,1 of
# Dx = q(q+1)(q^3-1).
HEAD_K = 10

CSV_NAME = "mult_deficit_dataset.csv"

# Observed head of the anchor row (2,3): Dx_{2,3} = q(q+1)(q^3-1).
# Recorded as an observed fact for the check, not as a general closed form.
ANCHOR_X = Fraction(2, 1)
ANCHOR_Y = Fraction(3, 1)
ANCHOR_HEAD6 = [0, -1, -1, 0, 1, 1]


# ----------------------------------------------------------------------------
# deterministic pair generator (x, y > 1; integer-product and non-integer)
# ----------------------------------------------------------------------------
def _generate_pairs() -> list[tuple[Fraction, Fraction]]:
    """A fixed, deterministic battery of >= 200 ordered rational pairs.

    Two disjoint families, deduplicated as unordered pairs so each row carries
    distinct mathematical content:

      * integer-product -- x*y in Z, built as y = P/x for a target integer P,
                           which guarantees the product is exactly P;
      * non-integer     -- x*y not in Z (assorted denominators).

    The anchor (2, 3) is emitted first so the check can find it at row 0.
    """
    int_prod: list[tuple[Fraction, Fraction]] = []
    non_prod: list[tuple[Fraction, Fraction]] = []
    seen_unordered: set[frozenset] = set()

    def add(pool: list, x: Fraction, y: Fraction) -> None:
        if x <= 1 or y <= 1:
            return
        key = frozenset((x, y))
        if key in seen_unordered:
            return
        seen_unordered.add(key)
        pool.append((x, y))

    # anchor required by the check (integer product: 2 * 3 = 6)
    add(int_prod, ANCHOR_X, ANCHOR_Y)

    # integer-product family: y = P/x for a target integer product P, so x*y = P
    # exactly. x = a/b > 1 (a > b, in lowest terms); b=1 admits integer x.
    for P in range(2, 13):
        for b in range(1, 9):
            for a in range(b + 1, 6 * b):
                x = Fraction(a, b)
                y = Fraction(P) / x
                if y > 1:
                    add(int_prod, x, y)

    # non-integer-product family: assorted denominators/numerators, x*y not in Z
    for d1 in range(2, 9):
        for d2 in range(d1, 9):
            for n1 in range(d1 + 1, d1 + 8):
                for n2 in range(d2 + 1, d2 + 8):
                    x, y = Fraction(n1, d1), Fraction(n2, d2)
                    if (x * y).denominator != 1:
                        add(non_prod, x, y)

    # balance the two families (>= 120 each => >= 240 total, comfortably > 200)
    cap = 120
    return int_prod[:cap] + non_prod[:cap]


PAIRS: list[tuple[Fraction, Fraction]] = _generate_pairs()


# ----------------------------------------------------------------------------
# per-pair exact deficit and its recorded fields
# ----------------------------------------------------------------------------
@lru_cache(maxsize=None)
def mult_deficit_expr(x: Fraction, y: Fraction) -> sp.Expr:
    """The exact deficit Dx_{x,y}(q) = [xy]_q - [x]_q*[y]_q, reduced.

    Both terms come from the q-Gosper engine over the same MGO q-blocks:
    [xy]_q via q_real_rational(x*y), [x]_q*[y]_q via q_gosper(x,y,'mul').
    Memoised so the CSV-write and summary passes in one process share the
    (symbolically heavy) computation; the function is pure of its arguments.
    """
    return sp.cancel(q_real_rational(x * y) - q_gosper(x, y, "mul"))


def _eval_int_at(expr: sp.Expr, point: int) -> int:
    """Integer value of a rational function in q at q=point (limit fallback)."""
    val = sp.cancel(expr).subs(q, point)
    if val in (sp.zoo, sp.nan, sp.oo, -sp.oo):
        val = sp.limit(expr, q, point)
    return int(sp.nsimplify(val))


def _frac_str(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}"


def mult_deficit_row(x: Fraction, y: Fraction, D: sp.Expr | None = None) -> dict:
    """One JSON-serialisable dataset row for the pair (x, y).

    Fields are integers / strings / bools only, so the summary that aggregates
    them hashes deterministically under the provenance tracker.
    """
    if D is None:
        D = mult_deficit_expr(x, y)
    z = x * y
    val = q_valuation(D)
    # head Laurent coefficients c_0..c_{HEAD_K-1} (lo pinned to 0; Dx(0)=0 => c0=0)
    _, head = laurent_coeffs(D, HEAD_K - 1, lo=0)
    return {
        "x": _frac_str(x),
        "y": _frac_str(y),
        "x_times_y": _frac_str(z),
        "integer_product": z.denominator == 1,
        "exact": sp.expand(D) == 0,
        "valuation": int(val),
        "head_coeffs": [int(c) for c in head],
        "D_at_q0": _eval_int_at(D, 0),
        "D_at_q1": _eval_int_at(D, 1),
    }


def _iter_rows():
    """Yield (x, y, D, row) for every pair exactly once."""
    for x, y in PAIRS:
        D = mult_deficit_expr(x, y)
        yield x, y, D, mult_deficit_row(x, y, D)


# ----------------------------------------------------------------------------
# provenance-tracked entry point: deterministic dataset summary
# ----------------------------------------------------------------------------
def build_mult_deficit_summary() -> dict:
    """Deterministic, JSON-serialisable summary of the whole deficit dataset.

    This is the function the provenance tracker records: re-running it must
    reproduce the same value bit-for-bit (it is pure -- no RNG, no file I/O), so
    verification over its record returns ok=True.
    """
    rows = [row for *_unused, row in _iter_rows()]
    n_int = sum(1 for r in rows if r["integer_product"])
    n_non = len(rows) - n_int
    n_exact = sum(1 for r in rows if r["exact"])
    d0_values = sorted({r["D_at_q0"] for r in rows})
    # locate the required anchor row and its head
    anchor = next(
        (r for r in rows
         if r["x"] == _frac_str(ANCHOR_X) and r["y"] == _frac_str(ANCHOR_Y)),
        None,
    )
    anchor_head6 = anchor["head_coeffs"][:6] if anchor else None
    return {
        "csv_name": CSV_NAME,
        "head_len": HEAD_K,
        "n_pairs": len(rows),
        "n_integer_product": n_int,
        "n_noninteger_product": n_non,
        "n_exact": n_exact,
        "all_D0_is_zero": all(r["D_at_q0"] == 0 for r in rows),
        "all_D1_is_zero": all(r["D_at_q1"] == 0 for r in rows),
        "all_valuation_nonneg": all(r["valuation"] >= 0 for r in rows),
        "observed_D0_values": d0_values,
        "observed_D0": d0_values[0] if len(d0_values) == 1 else None,
        "anchor_2__3_head6": anchor_head6,
        "anchor_is_q_qp1_q3m1": anchor_head6 == ANCHOR_HEAD6,
        "deficit_definition": "Dx(q) = [xy]_q - [x]_q*[y]_q",
        "engine_source": "q_gosper.q_real_rational(x*y) - q_gosper.q_gosper(x,y,'mul')",
        "rows": rows,
        "sympy_version": sp.__version__,
    }


# ----------------------------------------------------------------------------
# CSV writer (adds the exact rational function as a human-readable column)
# ----------------------------------------------------------------------------
def write_csv(path: str | Path | None = None) -> Path:
    """Compute the dataset and write mult_deficit_dataset.csv. Returns the path."""
    out = Path(path) if path is not None else (HERE / CSV_NAME)
    coeff_cols = [f"c{i}" for i in range(HEAD_K)]
    header = (
        ["idx", "x", "y", "x_times_y", "integer_product", "exact", "valuation"]
        + coeff_cols
        + ["D_at_q0", "D_at_q1", "Dx_exact"]
    )
    with out.open("w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(header)
        for idx, (x, y, D, row) in enumerate(_iter_rows()):
            head = row["head_coeffs"]
            w.writerow(
                [
                    idx,
                    row["x"],
                    row["y"],
                    row["x_times_y"],
                    row["integer_product"],
                    row["exact"],
                    row["valuation"],
                ]
                + head
                + [row["D_at_q0"], row["D_at_q1"], sp.sstr(sp.expand(D))]
            )
    return out


def main() -> int:
    out = write_csv()
    s = build_mult_deficit_summary()
    print(f"wrote {out}")
    print(f"  pairs                : {s['n_pairs']} "
          f"({s['n_integer_product']} integer-product, "
          f"{s['n_noninteger_product']} non-integer-product)")
    print(f"  head coeffs per row  : c0..c{s['head_len'] - 1}")
    print(f"  Dx(0) all rows       : {s['observed_D0_values']} "
          f"(constant: {s['all_D0_is_zero']})")
    print(f"  Dx(1) =  0 all rows  : {s['all_D1_is_zero']}")
    print(f"  identically-zero rows: {s['n_exact']} (exact multiplicativity)")
    print(f"  valuation >= 0 all   : {s['all_valuation_nonneg']}")
    print(f"  (2,3) head[:6]       : {s['anchor_2__3_head6']}  "
          f"(== q(q+1)(q^3-1): {s['anchor_is_q_qp1_q3m1']})")
    ok = (
        s["n_pairs"] >= 200
        and s["n_integer_product"] > 0
        and s["n_noninteger_product"] > 0
        and s["all_D1_is_zero"]
        and s["all_D0_is_zero"]
        and s["anchor_is_q_qp1_q3m1"]
    )
    print(f"  DATASET OK           : {ok}  "
          f"(pairs={s['n_pairs']}, Dx(1)=0 all rows={s['all_D1_is_zero']}, "
          f"observed Dx(0)={s['observed_D0']})")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
