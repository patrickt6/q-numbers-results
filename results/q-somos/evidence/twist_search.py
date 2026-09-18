#!/usr/bin/env python3
"""Search for integer twist exponents (a, b) such that the q-Somos-4 recurrence

    x_{n+4} x_n = q^a x_{n+3} x_{n+1} + q^b (x_{n+2})^2

over Z[q, q^{-1}][x_0, x_1, x_2, x_3] produces Laurent polynomial values for
x_4, ..., x_{11}.

A value x_n is Laurent in (x_0, x_1, x_2, x_3) with coefficients in Q(q) iff,
after cancellation to lowest terms num/den, the denominator den is a single
monomial in x_0, x_1, x_2, x_3 (units in Q(q) are ignored). This is exactly
the Laurent phenomenon condition adapted to the q-deformed cluster setting
(Berenstein and Zelevinsky, arXiv:math/0404446; Fomin and Zelevinsky,
arXiv:math/0104151).

Outputs:
  twist_search.csv  : columns a, b, n, is_laurent, denom_degree
  twist_winners.md  : every (a, b) for which x_4..x_11 are all Laurent, with
                      the explicit Laurent x_4 in each case and a q=1 check
                      against integer Somos-4 (OEIS A006720).
"""
from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent

q = sp.Symbol('q')
X = sp.symbols('x0 x1 x2 x3')  # the four initial cluster variables
A_RANGE = range(-3, 4)
B_RANGE = range(-3, 4)
N_MIN = 4
N_MAX = 11


def step(x_prev4, x_prev3, x_prev2, x_prev1, a: int, b: int):
    """Return the next term x_n = (q^a x_{n-1} x_{n-3} + q^b x_{n-2}^2) / x_{n-4}.

    Returned as a sympy expression in q, x0, x1, x2, x3, reduced via cancel."""
    numer = q**a * x_prev1 * x_prev3 + q**b * x_prev2**2
    expr = sp.cancel(numer / x_prev4)
    return expr


def laurent_signature(expr):
    """Test whether expr is a Laurent polynomial in (x0, x1, x2, x3) over Q(q).

    Returns a pair (is_laurent, denom_degree) where denom_degree is the total
    degree (sum of exponents) of the denominator in the four x variables after
    cancellation. For a Laurent expression the denominator is a single
    monomial; denom_degree records the total power of the four x's in that
    monomial. If is_laurent is False, the denominator carries at least two
    distinct x monomials, witnessing a genuine non-Laurent obstruction.
    """
    expr = sp.cancel(expr)
    num, den = sp.fraction(sp.together(expr))
    # Treat q as a unit in the coefficient field Q(q); only the x dependence
    # of the denominator matters.
    try:
        den_poly = sp.Poly(sp.expand(den), *X)
    except (sp.PolynomialError, sp.GeneratorsError):
        return None, -1
    monoms = den_poly.monoms()
    if not monoms:
        return True, 0
    is_laurent = (len(monoms) == 1)
    # Total degree of the (any) denominator monomial in x0..x3.
    denom_deg = sum(monoms[0])
    return is_laurent, denom_deg


def run():
    rows = []
    winners = []
    x4_by_pair = {}

    for a in A_RANGE:
        for b in B_RANGE:
            seq = [X[0], X[1], X[2], X[3]]
            all_laurent = True
            x4_cache = None
            for n in range(N_MIN, N_MAX + 1):
                nxt = step(seq[n-4], seq[n-3], seq[n-2], seq[n-1], a, b)
                seq.append(nxt)
                is_l, dd = laurent_signature(nxt)
                if n == N_MIN:
                    x4_cache = nxt
                if not is_l:
                    all_laurent = False
                rows.append({
                    "a": a, "b": b, "n": n,
                    "is_laurent": bool(is_l),
                    "denom_degree": int(dd),
                })
            x4_by_pair[(a, b)] = x4_cache
            if all_laurent:
                winners.append((a, b))

    # Write twist_search.csv
    csv_path = HERE / "twist_search.csv"
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=["a", "b", "n", "is_laurent", "denom_degree"])
        w.writeheader()
        for r in rows:
            w.writerow(r)

    # Write twist_winners.md
    md_path = HERE / "twist_winners.md"
    md_lines = []
    md_lines.append("# q-Somos-4 Laurent-stable twists")
    md_lines.append("")
    md_lines.append("Search window (a, b) in -3..3 x -3..3; Laurent test on x_4..x_11.")
    md_lines.append("")
    md_lines.append(f"Total pairs tested: {len(A_RANGE) * len(B_RANGE)}.")
    md_lines.append(f"Laurent-stable winners: {len(winners)}.")
    md_lines.append("")

    if winners:
        md_lines.append("## Winners (every x_n for n in 4..11 is Laurent in x_0..x_3 over Q(q))")
        md_lines.append("")
        a006720 = [1, 1, 1, 1, 2, 3, 7, 23, 59, 314, 1529, 8209]  # OEIS A006720
        for (a, b) in winners:
            x4 = x4_by_pair[(a, b)]
            x4_s = sp.cancel(x4)
            x4_q1 = sp.simplify(x4_s.subs(q, 1))
            md_lines.append(f"### (a, b) = ({a}, {b})")
            md_lines.append("")
            md_lines.append("Explicit Laurent polynomial for x_4:")
            md_lines.append("")
            md_lines.append(f"```")
            md_lines.append(f"x_4 = {sp.sstr(x4_s)}")
            md_lines.append(f"```")
            md_lines.append("")
            md_lines.append(f"At q = 1, x_4 specializes to: `{sp.sstr(x4_q1)}`.")
            # Also evaluate at x_0=x_1=x_2=x_3=1 and q=1; should equal A006720[4]=2
            try:
                num_q1_unit = int(sp.simplify(x4_q1.subs({X[0]:1, X[1]:1, X[2]:1, X[3]:1})))
            except (TypeError, ValueError):
                num_q1_unit = None
            target = a006720[4]
            ok = (num_q1_unit == target)
            md_lines.append(f"At x_0=x_1=x_2=x_3=1, q=1: {num_q1_unit} (OEIS A006720(4)={target}, {'match' if ok else 'MISMATCH'}).")
            md_lines.append("")
    else:
        md_lines.append("## No Laurent-stable twist in the searched window")
        md_lines.append("")
        md_lines.append(
            "No (a, b) in -3..3 x -3..3 yields x_4, ..., x_11 all Laurent. "
            "The Laurent property fails for every pair starting at some n in {5, ..., 11}. "
            "The classical (a, b) = (0, 0) case is the integer Somos-4 recurrence, "
            "whose Laurent phenomenon (Fomin-Zelevinsky arXiv:math/0104151) is "
            "recovered at q = 1 by every (a, b), but for symbolic q the q-twisted "
            "recurrence breaks the cluster compatibility unless (a, b) is paired "
            "with a compatible quantum exchange matrix in the Berenstein-Zelevinsky "
            "sense (arXiv:math/0404446)."
        )
        md_lines.append("")
        md_lines.append("### Failure-mode audit for the most-Laurent-looking pair")
        md_lines.append("")
        # Find the pair with the highest count of is_laurent True
        counts = {}
        for r in rows:
            key = (r["a"], r["b"])
            counts[key] = counts.get(key, 0) + (1 if r["is_laurent"] else 0)
        best = max(counts.items(), key=lambda kv: kv[1])
        (ba, bb), bcount = best
        md_lines.append(
            f"Most-Laurent-looking pair: (a, b) = ({ba}, {bb}) with {bcount} of "
            f"{N_MAX - N_MIN + 1} indices Laurent."
        )
        # First failing n
        first_fail = next((r for r in rows if r["a"] == ba and r["b"] == bb and not r["is_laurent"]), None)
        if first_fail is not None:
            md_lines.append(
                f"First failing index: n = {first_fail['n']} with denominator "
                f"total degree {first_fail['denom_degree']} in (x_0, x_1, x_2, x_3)."
            )

    md_path.write_text("\n".join(md_lines), encoding="utf-8")

    # SHA-256 manifests
    def sha256(p: Path) -> str:
        return hashlib.sha256(p.read_bytes()).hexdigest()

    table_sha = sha256(csv_path)
    md_sha = sha256(md_path)

    summary = {
        "rows": len(rows),
        "winners": [list(w) for w in winners],
        "n_winners": len(winners),
        "table_sha256": table_sha,
        "winners_sha256": md_sha,
        "a_range": [A_RANGE.start, A_RANGE.stop - 1],
        "b_range": [B_RANGE.start, B_RANGE.stop - 1],
        "n_range": [N_MIN, N_MAX],
    }
    (HERE / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    return summary


if __name__ == "__main__":
    out = run()
    print(json.dumps(out, indent=2))
