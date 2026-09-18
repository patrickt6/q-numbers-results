#!/usr/bin/env python3
r"""
Exact addition-deficit dataset from the q-Gosper engine.

For a pair of rationals x, y > 1 the q-Gosper engine (q_gosper.py) gives two
exact rational functions in q, both read off the SAME MGO q-blocks:

    [x]_q + [y]_q  =  q_gosper(x, y, "add")      # bihomographic engine value
    [x+y]_q        =  q_real_rational(x + y)      # single q-real, same q-blocks

The addition deficit is their exact difference

    D_{x,y}(q)  =  [x+y]_q - ([x]_q + [y]_q),

a Laurent (in fact ordinary, since x,y>1) rational function over Z[q,q^{-1}].
The MGO deformation map x|->[x]_q is not additive, so D is generically nonzero;
the structural invariants observed across every pair are

    D(0) = -1        (constant term: 1 from [x+y]_q minus 2 from [x]_q+[y]_q),
    D(1) =  0        (additivity is restored at q=1).

This module builds a dataset of >= 200 such pairs (both integer-sum and
non-integer-sum), recording for each the head Laurent coefficients of D together
with D(1) and D(0). It REUSES the engine entry points in q_gosper.py verbatim
(q_real_rational, q_gosper, laurent_coeffs, q_valuation) -- no q-blocks are
re-derived here, and neither q_gosper.py nor the qreals package is modified.

The independent qreals-vs-engine ground-truth cross-check lives in a separate
verification harness (its positive arm proves q_gosper(.,.,"add") == qreals
[x]_q+[y]_q and its cross-check proves the two qreals paths agree on [x+y]_q);
this module therefore trusts the engine and stays self-contained.

Entry points:
    build_deficit_summary()  -- deterministic, JSON-serialisable summary of the
                                whole dataset (the provenance-tracked entry point).
    write_csv(path)          -- compute and write deficit_dataset.csv.

Run:  python make_deficit_dataset.py          # writes deficit_dataset.csv
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
# >= 6 so the (3/2, 5/2) row carries the full head -1,0,0,1,0,0 of D = q^3 - 1.
HEAD_K = 10

CSV_NAME = "deficit_dataset.csv"


# ----------------------------------------------------------------------------
# deterministic pair generator (x, y > 1; both integer-sum and non-integer-sum)
# ----------------------------------------------------------------------------
def _generate_pairs() -> list[tuple[Fraction, Fraction]]:
    """A fixed, deterministic battery of >= 200 ordered rational pairs.

    Two disjoint families, deduplicated as unordered pairs so each row carries
    distinct mathematical content:

      * integer-sum   -- x + y in Z (same denominator, complementary numerators);
      * non-integer   -- x + y not in Z (assorted denominators).

    The anchor (3/2, 5/2) is emitted first so the check can find it at row 0.
    """
    int_sum: list[tuple[Fraction, Fraction]] = []
    non_sum: list[tuple[Fraction, Fraction]] = []
    seen_unordered: set[frozenset] = set()

    def add(pool: list, x: Fraction, y: Fraction) -> None:
        if x <= 1 or y <= 1:
            return
        key = frozenset((x, y))
        if key in seen_unordered:
            return
        seen_unordered.add(key)
        pool.append((x, y))

    # anchor required by the check (integer sum: 3/2 + 5/2 = 4)
    add(int_sum, Fraction(3, 2), Fraction(5, 2))

    # integer-sum family: common denominator r, numerators p1 <= p2, sum divisible by r
    for r in range(2, 10):
        for p1 in range(r + 1, 5 * r):
            for p2 in range(p1, 5 * r):
                x, y = Fraction(p1, r), Fraction(p2, r)
                if (x + y).denominator == 1:
                    add(int_sum, x, y)

    # non-integer-sum family: assorted denominators/numerators, x+y not integral
    for d1 in range(2, 9):
        for d2 in range(d1, 9):
            for n1 in range(d1 + 1, d1 + 8):
                for n2 in range(d2 + 1, d2 + 8):
                    x, y = Fraction(n1, d1), Fraction(n2, d2)
                    if (x + y).denominator != 1:
                        add(non_sum, x, y)

    # balance the two families (>= 120 each => >= 240 total, comfortably > 200)
    cap = 120
    return int_sum[:cap] + non_sum[:cap]


PAIRS: list[tuple[Fraction, Fraction]] = _generate_pairs()


# ----------------------------------------------------------------------------
# per-pair exact deficit and its recorded fields
# ----------------------------------------------------------------------------
@lru_cache(maxsize=None)
def deficit_expr(x: Fraction, y: Fraction) -> sp.Expr:
    """The exact deficit D_{x,y}(q) = [x+y]_q - ([x]_q + [y]_q), reduced.

    Both terms come from the q-Gosper engine over the same MGO q-blocks:
    [x+y]_q via q_real_rational(x+y), [x]_q+[y]_q via q_gosper(x,y,'add').
    Memoised so the CSV-write and summary passes in one process share the
    (symbolically heavy) computation; the function is pure of its arguments.
    """
    return sp.cancel(q_real_rational(x + y) - q_gosper(x, y, "add"))


def _eval_int_at(expr: sp.Expr, point: int) -> int:
    """Integer value of a rational function in q at q=point (limit fallback)."""
    val = sp.cancel(expr).subs(q, point)
    if val in (sp.zoo, sp.nan, sp.oo, -sp.oo):
        val = sp.limit(expr, q, point)
    return int(sp.nsimplify(val))


def _frac_str(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}"


def deficit_row(x: Fraction, y: Fraction, D: sp.Expr | None = None) -> dict:
    """One JSON-serialisable dataset row for the pair (x, y).

    Fields are integers / strings / bools only, so the summary that aggregates
    them hashes deterministically under the provenance tracker.
    """
    if D is None:
        D = deficit_expr(x, y)
    z = x + y
    val = q_valuation(D)
    # head Laurent coefficients c_0..c_{HEAD_K-1} (lo pinned to 0: x,y>1 => val 0)
    _, head = laurent_coeffs(D, HEAD_K - 1, lo=0)
    return {
        "x": _frac_str(x),
        "y": _frac_str(y),
        "x_plus_y": _frac_str(z),
        "integer_sum": z.denominator == 1,
        "valuation": int(val),
        "head_coeffs": [int(c) for c in head],
        "D_at_q0": _eval_int_at(D, 0),
        "D_at_q1": _eval_int_at(D, 1),
    }


def _iter_rows():
    """Yield (x, y, D, row) for every pair exactly once."""
    for x, y in PAIRS:
        D = deficit_expr(x, y)
        yield x, y, D, deficit_row(x, y, D)


# ----------------------------------------------------------------------------
# provenance-tracked entry point: deterministic dataset summary
# ----------------------------------------------------------------------------
def build_deficit_summary() -> dict:
    """Deterministic, JSON-serialisable summary of the whole deficit dataset.

    This is the function the provenance tracker records: re-running it must
    reproduce the same value bit-for-bit (it is pure -- no RNG, no file I/O), so
    verification over its record returns ok=True.
    """
    rows = [row for *_unused, row in _iter_rows()]
    n_int = sum(1 for r in rows if r["integer_sum"])
    n_non = len(rows) - n_int
    # locate the required anchor row and its head
    anchor = next(
        (r for r in rows if r["x"] == "3/2" and r["y"] == "5/2"), None
    )
    anchor_head6 = anchor["head_coeffs"][:6] if anchor else None
    return {
        "csv_name": CSV_NAME,
        "head_len": HEAD_K,
        "n_pairs": len(rows),
        "n_integer_sum": n_int,
        "n_noninteger_sum": n_non,
        "all_D0_is_minus1": all(r["D_at_q0"] == -1 for r in rows),
        "all_D1_is_zero": all(r["D_at_q1"] == 0 for r in rows),
        "all_valuation_zero": all(r["valuation"] == 0 for r in rows),
        "anchor_3_2__5_2_head6": anchor_head6,
        "anchor_is_q3_minus_1": anchor_head6 == [-1, 0, 0, 1, 0, 0],
        "deficit_definition": "D(q) = [x+y]_q - ([x]_q + [y]_q)",
        "engine_source": "q_gosper.q_real_rational(x+y) - q_gosper.q_gosper(x,y,'add')",
        "rows": rows,
        "sympy_version": sp.__version__,
    }


# ----------------------------------------------------------------------------
# CSV writer (adds the exact rational function as a human-readable column)
# ----------------------------------------------------------------------------
def write_csv(path: str | Path | None = None) -> Path:
    """Compute the dataset and write it to deficit_dataset.csv. Returns the path."""
    out = Path(path) if path is not None else (HERE / CSV_NAME)
    coeff_cols = [f"c{i}" for i in range(HEAD_K)]
    header = (
        ["idx", "x", "y", "x_plus_y", "integer_sum", "valuation"]
        + coeff_cols
        + ["D_at_q0", "D_at_q1", "D_exact"]
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
                    row["x_plus_y"],
                    row["integer_sum"],
                    row["valuation"],
                ]
                + head
                + [row["D_at_q0"], row["D_at_q1"], sp.sstr(sp.expand(D))]
            )
    return out


def main() -> int:
    out = write_csv()
    s = build_deficit_summary()
    print(f"wrote {out}")
    print(f"  pairs                : {s['n_pairs']} "
          f"({s['n_integer_sum']} integer-sum, {s['n_noninteger_sum']} non-integer-sum)")
    print(f"  head coeffs per row  : c0..c{s['head_len'] - 1}")
    print(f"  D(0) = -1 all rows   : {s['all_D0_is_minus1']}")
    print(f"  D(1) =  0 all rows   : {s['all_D1_is_zero']}")
    print(f"  valuation 0 all rows : {s['all_valuation_zero']}")
    print(f"  (3/2,5/2) head[:6]   : {s['anchor_3_2__5_2_head6']}  "
          f"(== q^3 - 1: {s['anchor_is_q3_minus_1']})")
    ok = (
        s["n_pairs"] >= 200
        and s["n_integer_sum"] > 0
        and s["n_noninteger_sum"] > 0
        and s["all_D0_is_minus1"]
        and s["all_D1_is_zero"]
        and s["anchor_is_q3_minus_1"]
    )
    print(f"  DATASET OK           : {ok}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
