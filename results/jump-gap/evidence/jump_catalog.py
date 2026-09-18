#!/usr/bin/env python3
r"""
The one-sided jump gap of a q-deformed rational, [r/s]_q^+ - [r/s]_q^-.

The Morier-Genoud-Ovsienko (MGO) map x |-> [x]_q is not continuous at the
rationals: a rational r/s has two distinct q-deformations, and the value the
deformation approaches differs depending on the side from which r/s is
approached. Jouteur (arXiv:2503.02122) names the two the *right* and *left*
versions and proves (Proposition 4.8) which one is which limit:

    [r/s]_q^+  (limit from above, x -> r/s with x > r/s) = the RIGHT version,
               which is the original MGO deformation [13];
    [r/s]_q^-  (limit from below, x -> r/s with x < r/s) = the LEFT version,
               defined by Bapat-Becker-Licata [1].

By Jouteur Definition 1.2, both are read off the SAME q-deformed continuant
matrix M_q of the (even-length) regular continued fraction of r/s, only applied
to two different q-deformations of the point at infinity:

    [r/s]_q^+ = M_q . (1, 0)^T          (first column: R/S),
    [r/s]_q^- = M_q . (1, 1 - q)^T      (Jouteur Prop 1.1: 1/(1-q) is the
                                         left version of infinity).

This module builds M_q from the MGO q-continuant blocks, in the *exact*
convention of the qreals package (q_rational), and cross-checks the right
version against qreals.q_rational on every catalogue entry: qreals is the oracle.
The left version is the same matrix on the left infinity point. The jump is

    gap(r/s) = [r/s]_q^+ - [r/s]_q^-.

Engine / oracle:
  - qreals.q_rational               : the exact right version [r/s]_q^+, asserted
                                      equal to the matrix first column for every
                                      catalogue entry.
  - approaching rational sequences  : q_rational of rationals just above / below
                                      r/s stabilise (in Taylor coefficients) to
                                      the right / left versions, directly
                                      realising both one-sided limits with the
                                      engine (Jouteur Prop 4.8). See
                                      stabilisation_check().
  - recurrence.py (modular_atlas)   : the functional-equation Taylor coefficients
                                      of the quadratic constants phi, sqrt2 equal
                                      the stabilised limit of q_rational over
                                      their convergents (Jouteur Prop 4.1),
                                      validating the stabilisation engine the
                                      whole construction rests on. See
                                      recurrence_oracle_check().

The conjectured closed form and its verification on held-out rationals live in
run_jump_catalog().

Run:  python jump_catalog.py            # writes jump_gaps.csv, prints summary
"""
from __future__ import annotations

import csv
import sys
from fractions import Fraction
from math import gcd
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent

# Adjust the import paths below to your local q-numbers engine: the qreals
# package (the oracle) and the recurrence module (the stabilisation oracle).
# They are only read, never modified.
for cand in (
    HERE.parent.parent.parent / "qreals" / "src",
    HERE.parent / "modular_atlas" / "fast_compute",
):
    if cand.is_dir():
        sys.path.insert(0, str(cand))

from qreals.rational import q_rational  # noqa: E402  (the oracle)

q = sp.Symbol("q")


# ============================================================================
# MGO q-integers and the q-continuant block (qreals convention, re-implemented)
# Reproduces qreals.q_rational coefficient for coefficient; asserted below.
# ============================================================================
def q_int(n: int) -> sp.Expr:
    """[n]_q = 1 + q + ... + q^{n-1}."""
    n = int(n)
    if n == 0:
        return sp.Integer(0)
    if n > 0:
        return sum((q**i for i in range(n)), sp.Integer(0))
    return -q_int(-n) / q ** (-n)


def q_int_qinv(n: int) -> sp.Expr:
    """[n]_{1/q} = q^{-(n-1)} [n]_q for n > 0."""
    n = int(n)
    if n == 0:
        return sp.Integer(0)
    if n > 0:
        return q_int(n) / q ** (n - 1)
    return -q_int_qinv(-n) * q ** (-n)


def cf_terms(fr: Fraction) -> list[int]:
    """Regular continued-fraction partial quotients of a rational."""
    return [int(t) for t in sp.continued_fraction(sp.Rational(fr.numerator, fr.denominator))]


def make_even_length(a: list[int]) -> list[int]:
    """Even-length regular-CF representative (qreals convention)."""
    a = list(a)
    if len(a) % 2 == 0:
        return a
    if a[-1] >= 2:
        a[-1] -= 1
        a.append(1)
        return a
    if len(a) >= 2 and a[-1] == 1:
        a.pop()
        a[-1] += 1
        return a
    raise ValueError(f"cannot make even-length CF from {a!r}")


def q_block(i: int, a: int) -> sp.Matrix:
    """MGO 2x2 q-continuant block at 0-indexed position i with digit a.

    Even i (1-indexed odd) carries [a]_q with q^{a} above; odd i carries
    [a]_{1/q} with q^{-a} above. det(block) = -(numerator-above).
    """
    if i % 2 == 0:
        return sp.Matrix([[q_int(a), q**a], [1, 0]])
    return sp.Matrix([[q_int_qinv(a), q ** (-a)], [1, 0]])


def continuant_matrix(fr: Fraction) -> tuple[sp.Matrix, list[int]]:
    """The q-deformed continuant matrix M_q of r/s, and its even-length CF."""
    cf = make_even_length(cf_terms(fr))
    M = sp.eye(2)
    for i, a in enumerate(cf):
        M = M * q_block(i, a)
    return M, cf


# ============================================================================
# The two one-sided limits and the jump gap
# ============================================================================
def right_version(fr: Fraction) -> sp.Expr:
    """[r/s]_q^+ = limit from above = MGO right version = M_q . (1,0)^T."""
    M, _ = continuant_matrix(fr)
    return sp.cancel(M[0, 0] / M[1, 0])


def left_version(fr: Fraction) -> sp.Expr:
    """[r/s]_q^- = limit from below = left version = M_q . (1, 1-q)^T."""
    M, _ = continuant_matrix(fr)
    num = M[0, 0] + (1 - q) * M[0, 1]
    den = M[1, 0] + (1 - q) * M[1, 1]
    return sp.cancel(num / den)


def jump_gap(fr: Fraction) -> sp.Expr:
    """gap(r/s) = [r/s]_q^+ - [r/s]_q^-, an exact rational function of q."""
    M, _ = continuant_matrix(fr)
    right = M[0, 0] / M[1, 0]
    left = (M[0, 0] + (1 - q) * M[0, 1]) / (M[1, 0] + (1 - q) * M[1, 1])
    return sp.cancel(right - left)


def alt_cf_sum(cf: list[int]) -> int:
    """E = (sum of even-position digits) - (sum of odd-position digits)."""
    return sum(a for i, a in enumerate(cf) if i % 2 == 0) - sum(
        a for i, a in enumerate(cf) if i % 2 == 1
    )


# ============================================================================
# The conjectured closed form (function of q and s)
# ============================================================================
def unit_fraction_gap_formula(s: int) -> sp.Expr:
    """Conjectured closed form for the unit-fraction jump, pure in q and s:

        [1/s]_q^+ - [1/s]_q^- = (1 - q) q^{s-1} / ([s]_q (1 + q^2 [s-1]_q)).
    """
    return sp.cancel((1 - q) * q ** (s - 1) / (q_int(s) * (1 + q**2 * q_int(s - 1))))


def predicted_leading_coeff(s: int) -> sp.Rational:
    """Conjectured q->1 leading coefficient of the gap: gap/(q-1) -> -1/s^2."""
    return sp.Rational(-1, s**2)


# ============================================================================
# Engine cross-checks: the two one-sided limits as stabilised q_rational limits
# ============================================================================
def _taylor(expr: sp.Expr, N: int) -> list[sp.Expr]:
    """First N Taylor coefficients of a rational function regular at q=0.

    Manual power-series division; avoids a sympy .series() recursion bug on the
    large q-rationals coming from deep approaching convergents.
    """
    expr = sp.cancel(expr)
    num, den = sp.fraction(expr)
    pn = sp.Poly(sp.expand(num), q)
    pd = sp.Poly(sp.expand(den), q)
    d = [pd.coeff_monomial(q**k) for k in range(pd.degree() + 1)]
    n = [pn.coeff_monomial(q**k) for k in range(N)]
    c: list[sp.Expr] = []
    for k in range(N):
        acc = n[k] if k < len(n) else sp.Integer(0)
        for j in range(1, min(k, len(d) - 1) + 1):
            acc -= d[j] * c[k - j]
        c.append(sp.cancel(acc / d[0]))
    return c


def stabilisation_check(samples: list[tuple[int, int]], N: int = 10, eps_den: int = 997) -> bool:
    """Jouteur Prop 4.8 via the engine: q_rational of rationals just above r/s
    stabilises (first N Taylor coeffs) to the right version, just below to the
    left version. This realises BOTH one-sided limits with qreals directly."""
    for (p, s) in samples:
        x = Fraction(p, s)
        rc = _taylor(right_version(x), N)
        lc = _taylor(left_version(x), N)
        above = x + Fraction(1, eps_den)
        below = x - Fraction(1, eps_den)
        ac = _taylor(q_rational(above.numerator, above.denominator), N)
        bc = _taylor(q_rational(below.numerator, below.denominator), N)
        if any(sp.simplify(ac[i] - rc[i]) != 0 for i in range(N)):
            return False
        if any(sp.simplify(bc[i] - lc[i]) != 0 for i in range(N)):
            return False
    return True


def recurrence_oracle_check(N: int = 12) -> bool:
    """recurrence.py oracle (Jouteur Prop 4.1): the functional-equation Taylor
    coefficients of phi and sqrt2 equal the stabilised q_rational limit over
    their convergents. Validates the engine the one-sided limits are built on."""
    try:
        from recurrence import phi_qreal_coeffs, sqrt2_qreal_coeffs
    except ImportError:
        return False

    def deep_convergent(cf: list[int]) -> Fraction:
        val = Fraction(cf[-1])
        for t in reversed(cf[:-1]):
            val = t + 1 / val
        return val

    phi_conv = deep_convergent([1] + [1] * 24)           # Fibonacci ratio
    sqrt2_conv = deep_convergent([1] + [2] * 24)
    phi_ok = phi_qreal_coeffs(N) == [
        int(c) for c in _taylor(q_rational(phi_conv.numerator, phi_conv.denominator), N)
    ]
    sqrt2_ok = sqrt2_qreal_coeffs(N) == [
        int(c) for c in _taylor(q_rational(sqrt2_conv.numerator, sqrt2_conv.denominator), N)
    ]
    return phi_ok and sqrt2_ok


# ============================================================================
# The catalogue and the held-out verification set (disjoint)
# ============================================================================
def build_catalogue() -> list[tuple[int, int]]:
    """At least 100 reduced rationals r/s: all r/s with s <= 12 and r <= 3s,
    plus the unit fractions 1/s up to s = 30 (the visible q-and-s family)."""
    cat: list[tuple[int, int]] = []
    seen: set[tuple[int, int]] = set()
    for s in range(1, 13):
        for p in range(1, 3 * s + 1):
            if gcd(p, s) != 1:
                continue
            if Fraction(p, s) == 1:
                continue
            key = (p, s)
            if key not in seen:
                seen.add(key)
                cat.append(key)
    for s in range(13, 31):
        if (1, s) not in seen:
            seen.add((1, s))
            cat.append((1, s))
    return cat


def heldout_set() -> list[tuple[int, int]]:
    """Rationals NOT in the catalogue, for closed-form verification:
    unit fractions 1/s with s = 31..45, and general r/s with s = 13,14,15."""
    held: list[tuple[int, int]] = [(1, s) for s in range(31, 46)]
    held += [(5, 13), (7, 13), (11, 13), (4, 15), (8, 15), (11, 14), (3, 14), (9, 13)]
    return held


# ============================================================================
# Row computation and CSV
# ============================================================================
CSV_HEADER = [
    "p", "s", "even_cf", "E_alt_cf_sum",
    "gap_numerator", "gap_denominator",
    "gap_at_q_half", "leading_q1_coeff",
    "right_matches_qreals_oracle", "numerator_is_unit_times_qE",
    "is_unit_fraction", "unit_formula_matches",
]


def row_for(p: int, s: int) -> dict:
    fr = Fraction(p, s)
    M, cf = continuant_matrix(fr)
    right = sp.cancel(M[0, 0] / M[1, 0])
    left = sp.cancel((M[0, 0] + (1 - q) * M[0, 1]) / (M[1, 0] + (1 - q) * M[1, 1]))
    gap = sp.cancel(right - left)
    E = alt_cf_sum(cf)

    # oracle: matrix right version must equal qreals.q_rational
    oracle_ok = sp.simplify(right - q_rational(p, s)) == 0

    num, den = sp.fraction(gap)

    # numerator-is-(1-q)*q^E structural claim: gap / ((1-q) q^E) must be 1/poly
    ratio = sp.cancel(gap / ((1 - q) * q**E))
    rnum, _ = sp.fraction(ratio)
    num_is_unit = len(sp.Poly(sp.expand(rnum), q).terms()) == 1

    # q->1 leading coefficient: gap/(q-1) at q=1
    lead = sp.cancel(gap / (q - 1)).subs(q, 1)

    is_unit = (p == 1 and s >= 2)
    if is_unit:
        unit_ok = bool(sp.simplify(gap - unit_fraction_gap_formula(s)) == 0)
    else:
        unit_ok = None

    return {
        "p": p,
        "s": s,
        "even_cf": "[" + ",".join(str(a) for a in cf) + "]",
        "E_alt_cf_sum": E,
        "gap_numerator": sp.sstr(sp.expand(num)),
        "gap_denominator": sp.sstr(sp.expand(den)),
        "gap_at_q_half": str(sp.nsimplify(gap.subs(q, sp.Rational(1, 2)))),
        "leading_q1_coeff": str(lead),
        "right_matches_qreals_oracle": bool(oracle_ok),
        "numerator_is_unit_times_qE": bool(num_is_unit),
        "is_unit_fraction": is_unit,
        "unit_formula_matches": unit_ok,
    }


def write_csv(rows: list[dict], path: Path) -> None:
    with path.open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=CSV_HEADER)
        w.writeheader()
        for r in rows:
            w.writerow(r)


# ============================================================================
# Deterministic provenance entry point and the script driver
# ============================================================================
def run_jump_catalog() -> dict:
    """Recompute the catalogue + held-out verification. Pure and JSON-able:
    no file I/O here, so re-runs hash-match under the provenance tracker."""
    catalogue = build_catalogue()
    rows = [row_for(p, s) for (p, s) in catalogue]

    oracle_ok = all(r["right_matches_qreals_oracle"] for r in rows)
    numerator_ok = all(r["numerator_is_unit_times_qE"] for r in rows)
    leading_ok = all(
        sp.simplify(sp.sympify(r["leading_q1_coeff"]) - predicted_leading_coeff(r["s"])) == 0
        for r in rows
    )
    unit_rows = [r for r in rows if r["is_unit_fraction"]]
    unit_ok = all(r["unit_formula_matches"] for r in unit_rows)

    # held-out: the conjectured closed form, recomputed from q and s only,
    # versus the engine gap, on rationals not in the catalogue.
    held = heldout_set()
    heldout_results = []
    for (p, s) in held:
        gap = jump_gap(Fraction(p, s))
        is_unit = (p == 1 and s >= 2)
        unit_match = bool(sp.simplify(gap - unit_fraction_gap_formula(s)) == 0) if is_unit else None
        lead_match = bool(
            sp.simplify(sp.cancel(gap / (q - 1)).subs(q, 1) - predicted_leading_coeff(s)) == 0
        )
        E = alt_cf_sum(make_even_length(cf_terms(Fraction(p, s))))
        num_match = len(sp.Poly(sp.expand(sp.fraction(sp.cancel(gap / ((1 - q) * q**E)))[0]), q).terms()) == 1
        heldout_results.append({
            "p": p, "s": s, "is_unit_fraction": is_unit,
            "unit_formula_matches": unit_match,
            "leading_coeff_matches": lead_match,
            "numerator_is_unit_times_qE": num_match,
        })

    heldout_unit = [h for h in heldout_results if h["is_unit_fraction"]]
    heldout_unit_pass = all(h["unit_formula_matches"] for h in heldout_unit)
    heldout_leading_pass = all(h["leading_coeff_matches"] for h in heldout_results)
    heldout_numerator_pass = all(h["numerator_is_unit_times_qE"] for h in heldout_results)

    stab_ok = stabilisation_check([(1, 2), (3, 5), (5, 7), (2, 3), (7, 4)])
    rec_ok = recurrence_oracle_check()

    all_pass = bool(
        oracle_ok and numerator_ok and leading_ok and unit_ok
        and heldout_unit_pass and heldout_leading_pass and heldout_numerator_pass
        and stab_ok and rec_ok
    )

    return {
        "closed_form_unit": "[1/s]_q^+ - [1/s]_q^- = (1-q) q^{s-1} / ([s]_q (1 + q^2 [s-1]_q))",
        "closed_form_universal": "[r/s]_q^+ - [r/s]_q^- = (1-q) q^E / (S^+(q) S^-(q)), "
                                 "E = alt sum of even-length CF digits, S^+/S^- the right/left "
                                 "q-denominators with S^+(1) = S^-(1) = s",
        "leading_term_at_q1": "gap = -(q-1)/s^2 + O((q-1)^2)",
        "jouteur_relation": "arXiv:2503.02122 Def 1.2 + Prop 4.8: [r/s]_q^+ = right version "
                            "(M_q.(1,0)), [r/s]_q^- = left version (M_q.(1,1-q))",
        "catalogue_size": len(rows),
        "right_matches_qreals_oracle_all": oracle_ok,
        "numerator_is_unit_times_qE_all": numerator_ok,
        "leading_coeff_minus_inv_s2_all": leading_ok,
        "unit_formula_matches_in_catalogue": unit_ok,
        "n_unit_fractions_in_catalogue": len(unit_rows),
        "heldout_size": len(heldout_results),
        "heldout_unit_count": len(heldout_unit),
        "heldout_unit_formula_pass": heldout_unit_pass,
        "heldout_leading_pass": heldout_leading_pass,
        "heldout_numerator_pass": heldout_numerator_pass,
        "stabilisation_check_pass": stab_ok,
        "recurrence_oracle_pass": rec_ok,
        "all_pass": all_pass,
        "sympy_version": sp.__version__,
    }


def main() -> int:
    catalogue = build_catalogue()
    rows = [row_for(p, s) for (p, s) in catalogue]
    csv_path = HERE / "jump_gaps.csv"
    write_csv(rows, csv_path)

    summary = run_jump_catalog()

    print("q-rational one-sided jump gap  [r/s]_q^+ - [r/s]_q^-")
    print("Jouteur relation :", summary["jouteur_relation"])
    print()
    print("Conjectured closed form (q and s):")
    print("  unit fractions :", summary["closed_form_unit"])
    print("  leading term   :", summary["leading_term_at_q1"])
    print("  universal form :", summary["closed_form_universal"])
    print()
    print(f"catalogue size                         : {summary['catalogue_size']} rationals")
    print(f"CSV written                            : {csv_path}")
    print(f"right == qreals.q_rational (oracle)     : {summary['right_matches_qreals_oracle_all']}")
    print(f"numerator = (1-q) q^E on all            : {summary['numerator_is_unit_times_qE_all']}")
    print(f"leading coeff = -1/s^2 on all           : {summary['leading_coeff_minus_inv_s2_all']}")
    print(f"unit formula exact in catalogue         : {summary['unit_formula_matches_in_catalogue']}")
    print(f"stabilisation (engine, both limits)     : {summary['stabilisation_check_pass']}")
    print(f"recurrence.py oracle (phi, sqrt2)       : {summary['recurrence_oracle_pass']}")
    print()
    print(f"HELD-OUT rationals                      : {summary['heldout_size']} "
          f"({summary['heldout_unit_count']} unit fractions)")
    print(f"  closed form exact on held-out units   : {summary['heldout_unit_formula_pass']}")
    print(f"  leading -1/s^2 on held-out            : {summary['heldout_leading_pass']}")
    print(f"  numerator (1-q)q^E on held-out        : {summary['heldout_numerator_pass']}")
    print()
    print(f"ALL PASS : {summary['all_pass']}")
    return 0 if summary["all_pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
