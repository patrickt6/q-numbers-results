#!/usr/bin/env python3
r"""
The rational jump gap as a fully explicit function of the continued fraction.

This generalises the shipped jump-gap closed form (jump_catalog.py) so that
every ingredient of

    [r/s]_q^+ - [r/s]_q^-  =  (1 - q) q^E / ( S_+(q) S_-(q) )

is written out as an explicit function of the regular continued fraction of r/s,
valid for ALL rationals -- not only the unit fractions or any fitted family.
The shipped result proved the form holds with E the alternating CF-digit sum and
S_+ / S_- the right / left q-denominators read off the q-continuant matrix. Here
the same three quantities are produced directly from the CF digits, with no
matrix inversion and no per-case fitting:

  E        = (a_0 + a_1 + ... + a_{2m-1}) - 1,   one less than the sum of the
             digits of the even-length regular CF [a_0, ..., a_{2m-1}];
  S_+, S_- = the right / left q-continuant denominators, built by a single
             polynomial recurrence on the digits (continuant_poly below). Both
             are genuine polynomials with S_+(1) = S_-(1) = s.

The two exponents agree through the identity
    E  =  alt_cf_sum  +  2 * (sum of odd-position digits)  -  1,
which is exactly the valuation correction that turns the Laurent q-denominators
of the matrix construction into the polynomials S_+ , S_-:
    v(S_+^raw) = 1 - (sum of odd-position digits),   v(S_-^raw) = -(same sum).

The Jouteur left/right relation is the anchor (arXiv:2503.02122, Definition 1.2
and Proposition 4.8): [r/s]_q^+ is the right version (the MGO / qreals
q_rational, M_q.(1,0)) and [r/s]_q^- is the left version (M_q.(1,1-q)). The
qreals engine is the oracle and is not modified: every held-out rational checks
right_version == qreals.q_rational and S_+ == the reduced qreals denominator.

Verification (run_gap_general): on 37 held-out rationals disjoint from the
jump_catalog catalogue and its held-out set, with denominators spanning 16 to
2584 (small fractions, Fibonacci and Pell convergents, and assorted large
denominators), the CF-built closed form equals the engine jump gap with exactly
zero residual.

Run:  python gap_general.py            # prints the verdict
"""
from __future__ import annotations

import sys
from fractions import Fraction
from math import gcd
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent

# Adjust the import path to your local q-numbers engine (the qreals package, the
# oracle). It is only read, never modified. Mirrors jump_catalog.py.
for cand in (
    HERE.parent.parent.parent / "qreals" / "src",
    HERE.parent / "modular_atlas" / "fast_compute",
):
    if cand.is_dir():
        sys.path.insert(0, str(cand))
sys.path.insert(0, str(HERE))  # so jump_catalog is importable by name

# Reuse the shipped engine verbatim (build on jump_catalog).
from jump_catalog import (  # noqa: E402
    alt_cf_sum,
    build_catalogue,
    cf_terms,
    heldout_set,
    jump_gap,
    make_even_length,
    q,
    q_int,
    right_version,
)
from qreals.rational import q_rational  # noqa: E402  (the oracle)


# ============================================================================
# The explicit CF-only construction of E, S_+ , S_-
# ============================================================================
def continuant_poly(cf: list[int]) -> tuple[sp.Expr, sp.Expr]:
    r"""Bottom row (x, y) of the polynomial q-continuant matrix of the digits.

    The MGO q-continuant matrix is M_q = B_0 B_1 ... B_{2m-1} with blocks

        i even:  B_i = [[ [a_i]_q , q^{a_i} ], [1, 0]]       (already polynomial)
        i odd :  B_i = [[ [a_i]_{1/q} , q^{-a_i} ], [1, 0]]  (Laurent: q^{-a_i})

    Multiplying every odd block by q^{a_i} clears the negative powers and gives
    polynomial blocks

        i even:  [[ [a_i]_q , q^{a_i} ], [1, 0]]
        i odd :  [[ q [a_i]_q , 1 ], [ q^{a_i} , 0 ]]

    so the product is q^{P_odd} M_q with P_odd the sum of the odd-position
    digits. Tracking only the bottom row (x, y) of that polynomial product is
    enough for both denominators. Because the even-length CF always ends on an
    odd-position block, the final x carries one extra factor of q (its constant
    term is zero), which is removed in closed_form_from_cf.
    """
    x, y = sp.Integer(0), sp.Integer(1)          # bottom row of the identity
    for i, a in enumerate(cf):
        if i % 2 == 0:                            # even block
            nx, ny = x * q_int(a) + y, x * q**a
        else:                                     # odd block (cleared of q^{-a})
            nx, ny = x * q * q_int(a) + y * q**a, x
        x, y = sp.expand(nx), sp.expand(ny)
    return x, y


def closed_form_from_cf(cf: list[int]) -> dict:
    r"""E, S_+ , S_- and the gap, all built from the CF digits alone.

        E   = sum(cf) - 1
        S_+ = x / q          (right q-denominator; x is divisible by q)
        S_- = x + (1 - q) y  (left q-denominator)
        gap = (1 - q) q^E / (S_+ S_-)

    No engine call and no fitting: the only inputs are the digits in `cf`.
    """
    x, y = continuant_poly(cf)
    s_plus = sp.expand(sp.cancel(x / q))
    s_minus = sp.expand(x + (1 - q) * y)
    E = sum(cf) - 1
    gap = sp.cancel((1 - q) * q**E / (s_plus * s_minus))
    return {"E": E, "S_plus": s_plus, "S_minus": s_minus, "gap": gap}


def exponent_from_cf(cf: list[int]) -> int:
    """E = (sum of the even-length CF digits) - 1, the clean polynomial exponent."""
    return sum(cf) - 1


def exponent_via_valuation(cf: list[int]) -> int:
    """The same E reached from the shipped alternating-sum exponent plus the
    valuation correction:  E = alt_cf_sum + 2 P_odd - 1, where P_odd is the sum
    of the odd-position (0-indexed) digits. Equals exponent_from_cf identically."""
    p_odd = sum(a for i, a in enumerate(cf) if i % 2 == 1)
    return alt_cf_sum(cf) + 2 * p_odd - 1


# ============================================================================
# The held-out verification set (disjoint from jump_catalog by construction)
# ============================================================================
def _excluded() -> set[tuple[int, int]]:
    """Everything the shipped jump_catalog already verifies."""
    return set(build_catalogue()) | set(heldout_set())


def general_heldout_set() -> list[tuple[int, int]]:
    """At least 30 reduced rationals NOT touched by jump_catalog, with small and
    large denominators. Small: non-unit r/s, s in 16..40. Large: Fibonacci and
    Pell convergents (long CFs, denominators to 2584) and assorted big
    denominators. Every entry has bounded CF digits so the exact symbolic gap
    stays fast; the construction itself does not care about digit size."""
    small = [
        (3, 16), (5, 16), (7, 18), (5, 19), (9, 20), (7, 22), (11, 24),
        (13, 25), (9, 26), (15, 28), (11, 30), (17, 31), (13, 33), (19, 35),
        (23, 37), (17, 40),
    ]
    fibonacci = [
        (13, 21), (21, 34), (34, 55), (55, 89), (89, 144), (144, 233),
        (233, 377), (377, 610), (610, 987), (987, 1597), (1597, 2584),
    ]
    pell = [(12, 29), (29, 70), (70, 169), (169, 408), (408, 985)]
    assorted = [(100, 271), (150, 331), (200, 457), (123, 500), (321, 1000)]

    excluded = _excluded()
    out: list[tuple[int, int]] = []
    for p, s in small + fibonacci + pell + assorted:
        assert gcd(p, s) == 1, f"{p}/{s} not reduced"
        assert (p, s) not in excluded, f"{p}/{s} overlaps jump_catalog"
        out.append((p, s))
    return out


# ============================================================================
# Per-rational verification: closed form (CF only) vs engine gap (oracle)
# ============================================================================
def verify_rational(p: int, s: int) -> dict:
    r"""Recompute the gap two independent ways and confirm zero residual:

      closed form : closed_form_from_cf(CF of r/s)  -- E, S_+, S_- from digits.
      engine gap  : jump_catalog.jump_gap           -- the matrix subtraction
                    R/S_+ - (R + (1-q)R')/S_-, whose right version is asserted
                    equal to qreals.q_rational (the oracle).

    Also confirms, from the CF alone: S_+(1) = S_-(1) = s; S_+ is a genuine
    polynomial (x divisible by q); E from the digit sum equals E from the
    valuation correction; S_+ equals the reduced qreals denominator; and the
    q -> 1 leading coefficient of the gap is -1/s^2.
    """
    fr = Fraction(p, s)
    cf = make_even_length(cf_terms(fr))
    cfd = closed_form_from_cf(cf)
    E, s_plus, s_minus, gap = cfd["E"], cfd["S_plus"], cfd["S_minus"], cfd["gap"]

    # 1. zero-residual agreement with the engine gap
    residual = sp.cancel(gap - jump_gap(fr))
    gap_matches = residual == 0

    # 2. oracle: the engine right version is exactly qreals.q_rational
    oracle_ok = sp.simplify(right_version(fr) - q_rational(p, s)) == 0

    # 3. both q-denominators are q-analogues of s
    denom_shape_ok = bool(s_plus.subs(q, 1) == s and s_minus.subs(q, 1) == s)

    # 4. S_+ is a genuine polynomial (constant term present, not Laurent)
    s_plus_poly = sp.Poly(s_plus, q)
    s_plus_is_poly = all(e >= 0 for (e,) in s_plus_poly.monoms())

    # 5. the two exponent formulas agree
    exponent_ok = (E == exponent_from_cf(cf) == exponent_via_valuation(cf))

    # 6. S_+ equals the reduced qreals (right-version) denominator, up to the
    #    overall constant normalisation sympy may choose
    rden = sp.fraction(sp.cancel(q_rational(p, s)))[1]

    def _monic_const(poly: sp.Expr) -> sp.Expr:
        pc = sp.Poly(poly, q)
        return sp.expand(poly / pc.all_coeffs()[-1])  # divide by constant term

    s_plus_matches_engine = sp.expand(_monic_const(s_plus) - _monic_const(rden)) == 0

    # 7. q -> 1 leading coefficient is -1/s^2 (depends only on s)
    leading = sp.cancel(gap / (q - 1)).subs(q, 1)
    leading_ok = bool(sp.simplify(leading - sp.Rational(-1, s**2)) == 0)

    ok = bool(
        gap_matches and oracle_ok and denom_shape_ok and s_plus_is_poly
        and exponent_ok and s_plus_matches_engine and leading_ok
    )
    return {
        "p": p, "s": s, "E": E, "cf_len": len(cf), "max_digit": max(cf),
        "gap_matches": bool(gap_matches),
        "oracle_ok": bool(oracle_ok),
        "denom_shape_ok": denom_shape_ok,
        "s_plus_is_poly": bool(s_plus_is_poly),
        "exponent_ok": bool(exponent_ok),
        "s_plus_matches_engine": bool(s_plus_matches_engine),
        "leading_ok": leading_ok,
        "ok": ok,
    }


# ============================================================================
# Deterministic provenance entry point
# ============================================================================
def run_gap_general() -> dict:
    """Recompute the held-out verification. Pure and JSON-able (fixed held-out
    set, no RNG, no file I/O), so re-runs hash-match under the provenance tracker."""
    held = general_heldout_set()
    results = [verify_rational(p, s) for (p, s) in held]

    gap_all = all(r["gap_matches"] for r in results)
    oracle_all = all(r["oracle_ok"] for r in results)
    denom_all = all(r["denom_shape_ok"] for r in results)
    poly_all = all(r["s_plus_is_poly"] for r in results)
    exponent_all = all(r["exponent_ok"] for r in results)
    engine_den_all = all(r["s_plus_matches_engine"] for r in results)
    leading_all = all(r["leading_ok"] for r in results)

    # The exponent identity E = sum-1 = alt_cf_sum + 2 P_odd - 1 on the full
    # shipped catalogue too (cheap integer check; subsumes the shipped E form).
    catalogue_exponent_ok = all(
        exponent_from_cf(make_even_length(cf_terms(Fraction(p, s))))
        == exponent_via_valuation(make_even_length(cf_terms(Fraction(p, s))))
        for (p, s) in build_catalogue()
    )

    denominators = sorted(s for (_, s) in held)
    all_pass = bool(
        gap_all and oracle_all and denom_all and poly_all and exponent_all
        and engine_den_all and leading_all and catalogue_exponent_ok
        and len(held) >= 30
    )

    return {
        "closed_form": "[r/s]_q^+ - [r/s]_q^- = (1-q) q^E / (S_+(q) S_-(q))",
        "exponent_formula": "E = (sum of even-length CF digits) - 1",
        "exponent_identity": "E = alt_cf_sum + 2*(sum of odd-position digits) - 1",
        "denominator_construction": "S_+ = x/q, S_- = x + (1-q) y, with (x,y) the "
                                    "bottom row of the polynomial q-continuant of the CF "
                                    "(continuant_poly); S_+(1) = S_-(1) = s",
        "jouteur_relation": "arXiv:2503.02122 Def 1.2 + Prop 4.8: [r/s]_q^+ = right "
                            "version (qreals q_rational, M_q.(1,0)); [r/s]_q^- = left "
                            "version (M_q.(1,1-q))",
        "base_record": "generalises jump_catalog; engine unchanged",
        "heldout_size": len(held),
        "heldout_min_denominator": denominators[0],
        "heldout_max_denominator": denominators[-1],
        "gap_zero_residual_all": gap_all,
        "right_version_is_qreals_oracle_all": oracle_all,
        "denominators_collapse_to_s_all": denom_all,
        "s_plus_is_genuine_polynomial_all": poly_all,
        "exponent_two_formulas_agree_all": exponent_all,
        "s_plus_equals_qreals_denominator_all": engine_den_all,
        "leading_coeff_minus_inv_s2_all": leading_all,
        "exponent_identity_on_catalogue": catalogue_exponent_ok,
        "all_pass": all_pass,
        "sympy_version": sp.__version__,
    }


def main() -> int:
    held = general_heldout_set()
    summary = run_gap_general()

    print("Rational jump gap, generalised closed form (all rationals)")
    print("  form     :", summary["closed_form"])
    print("  exponent :", summary["exponent_formula"])
    print("           :", summary["exponent_identity"])
    print("  denoms   :", summary["denominator_construction"])
    print("  Jouteur  :", summary["jouteur_relation"])
    print()
    print(f"held-out rationals (disjoint from jump_catalog) : {summary['heldout_size']}")
    print(f"  denominator range                             : "
          f"{summary['heldout_min_denominator']}..{summary['heldout_max_denominator']}")
    print(f"  gap == engine, zero residual (all)            : {summary['gap_zero_residual_all']}")
    print(f"  right version == qreals.q_rational (oracle)   : {summary['right_version_is_qreals_oracle_all']}")
    print(f"  S_+(1) = S_-(1) = s (all)                      : {summary['denominators_collapse_to_s_all']}")
    print(f"  S_+ genuine polynomial (all)                  : {summary['s_plus_is_genuine_polynomial_all']}")
    print(f"  E = sum-1 = alt+2P_odd-1 (all)                : {summary['exponent_two_formulas_agree_all']}")
    print(f"  S_+ == reduced qreals denominator (all)       : {summary['s_plus_equals_qreals_denominator_all']}")
    print(f"  q->1 leading coeff = -1/s^2 (all)             : {summary['leading_coeff_minus_inv_s2_all']}")
    print(f"  exponent identity on shipped catalogue        : {summary['exponent_identity_on_catalogue']}")
    print()
    print(f"ALL PASS : {summary['all_pass']}")

    # per-rational table for the record
    print()
    print(f"{'r/s':>10}  {'E':>4}  {'cf_len':>6}  {'maxdig':>6}  ok")
    for (p, s) in held:
        r = verify_rational(p, s)
        print(f"{p:>4}/{s:<5} {r['E']:>4}  {r['cf_len']:>6}  {r['max_digit']:>6}  {r['ok']}")

    return 0 if summary["all_pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
