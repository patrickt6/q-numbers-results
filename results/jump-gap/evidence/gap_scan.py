#!/usr/bin/env python3
r"""
Closed-form scanner for the q-rational jump gap.

For every reduced rational r/s up to a denominator ceiling, recompute the
one-sided jump gap two independent ways and confirm they agree:

  1. engine gap  : [r/s]_q^+ - [r/s]_q^- as the difference of the two full
                   q-continuant matrix ratios (jump_catalog.jump_gap), i.e. the
                   subtraction R/S^+ - (R + (1-q)R') / S^-.
  2. closed form : (1 - q) q^E / (S^+ S^-), rebuilt from q and the even-length
                   continued fraction alone. E is the alternating CF-digit sum
                   (jump_catalog.alt_cf_sum); S^+ = S and S^- = S + (1-q)S' are
                   the right / left q-denominators read off the continuant bottom
                   row. The numerator (1 - q) q^E is a single monomial in q.

The two expressions are algebraically equal iff det(M_q) = q^E (the telescoping
identity), so this scan re-derives that identity rational by rational through two
unrelated arithmetic paths: a subtraction of ratios against a monomial over a
product.

Speed: the exact symbolic gap (sympy cancel) slows down for large denominators,
so the wide sweep checks the closed form at several sampled numeric values of q
(exact Fractions), while the existing jump_catalog catalogue is kept as the small
exact-symbolic subset. Every rational records which check it received.

Per rational the scan also confirms the predicted shapes that the closed form
rests on:
  - E shape           : det(M_q) = q^E (q a sampled value, E from alt_cf_sum);
  - denominator shape : S^+(1) = S^-(1) = s (the q-denominators are q-analogues
                        of the classical denominator s).

Any rational where the two ways disagree, or where E or a denominator departs
from the predicted shape, is logged as an offender.

Run:
    python gap_scan.py                # asks one question: the denominator ceiling
    python gap_scan.py 80             # non-interactive: ceiling given as argument

Writes nothing but the companion note gap_scan.md; prints one verdict line then
the offenders. The qreals package is not touched.
"""
from __future__ import annotations

import sys
from fractions import Fraction
from math import gcd
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))  # so jump_catalog is importable by name

# Reuse the catalogue engine verbatim. Nothing here is redefined.
from jump_catalog import (  # noqa: E402
    alt_cf_sum,
    build_catalogue,
    cf_terms,
    continuant_matrix,
    heldout_set,
    jump_gap,
    make_even_length,
    q,
    unit_fraction_gap_formula,
)

DEFAULT_CEILING = 80

# Sampled values of q for the numeric check. All lie strictly in (0, 1): there
# every q-integer and both q-denominators S^+, S^- are sums of positive terms,
# so no sampled denominator is ever zero and no guard is needed. Several distinct
# samples make accidental agreement between two unequal rational functions of q
# vanishingly unlikely.
Q_SAMPLES = [
    Fraction(1, 2),
    Fraction(1, 3),
    Fraction(2, 3),
    Fraction(2, 5),
    Fraction(3, 7),
    Fraction(4, 9),
]


# ============================================================================
# Numeric continuant in exact Fractions (fast; no sympy in the hot loop)
# ============================================================================
def _nq_int(n: int, qv: Fraction) -> Fraction:
    """[n]_q at a numeric q. CF digits are >= 0 (only a_0 can be 0)."""
    if n <= 0:
        return Fraction(0)
    acc = Fraction(0)
    p = Fraction(1)
    for _ in range(n):
        acc += p
        p *= qv
    return acc


def _nq_int_qinv(n: int, qv: Fraction) -> Fraction:
    """[n]_{1/q} = q^{-(n-1)} [n]_q at a numeric q (odd positions, n >= 1)."""
    if n <= 0:
        return Fraction(0)
    return _nq_int(n, qv) / qv ** (n - 1)


def _numeric_continuant(cf: list[int], qv: Fraction) -> tuple[Fraction, Fraction, Fraction, Fraction]:
    """Bottom-and-top of M_q at numeric q: returns (R, R', S, S')."""
    m00, m01 = Fraction(1), Fraction(0)
    m10, m11 = Fraction(0), Fraction(1)
    for i, a in enumerate(cf):
        if i % 2 == 0:
            b00, b01 = _nq_int(a, qv), qv ** a
        else:
            b00, b01 = _nq_int_qinv(a, qv), qv ** (-a)
        # right-multiply by [[b00, b01], [1, 0]]
        n00 = m00 * b00 + m01
        n01 = m00 * b01
        n10 = m10 * b00 + m11
        n11 = m10 * b01
        m00, m01, m10, m11 = n00, n01, n10, n11
    return m00, m01, m10, m11


def _classical_denominator(cf: list[int]) -> int:
    """S^+(1) = S^-(1): the continuant bottom-left at q = 1, i.e. s."""
    _, _, s_plus_at_1, _ = _numeric_continuant(cf, Fraction(1))
    return int(s_plus_at_1)


# ============================================================================
# The two-way checks
# ============================================================================
def numeric_two_way(p: int, s: int) -> dict:
    """Numeric closed-form check at every sampled q. Returns a verdict dict with
    any mismatch noted. Cheap enough for large denominators."""
    fr = Fraction(p, s)
    cf = make_even_length(cf_terms(fr))
    E = alt_cf_sum(cf)
    denom_at_1 = _classical_denominator(cf)

    mismatches: list[str] = []

    # denominator shape: both q-denominators collapse to s at q = 1
    if denom_at_1 != s:
        mismatches.append(f"denominator shape: S^+(1)={denom_at_1}, expected s={s}")

    for qv in Q_SAMPLES:
        R, Rp, S, Sp = _numeric_continuant(cf, qv)
        s_plus = S
        s_minus = S + (1 - qv) * Sp
        engine = R / s_plus - (R + (1 - qv) * Rp) / s_minus
        closed = (1 - qv) * qv ** E / (s_plus * s_minus)
        det = R * Sp - Rp * S
        if engine != closed:
            mismatches.append(f"gap mismatch at q={qv}: engine {engine} vs closed {closed}")
        if det != qv ** E:
            mismatches.append(f"E shape at q={qv}: det {det} vs q^E {qv ** E} (E={E})")

    return {"p": p, "s": s, "E": E, "cf": cf, "ok": not mismatches, "mismatches": mismatches}


def symbolic_two_way(p: int, s: int) -> dict:
    """Exact symbolic closed-form check: the sympy-cancelled engine gap against
    the (1-q) q^E / (S^+ S^-) closed form rebuilt from the continuant. Slow, run
    only on the representative subset."""
    fr = Fraction(p, s)
    M, cf = continuant_matrix(fr)
    E = alt_cf_sum(cf)
    s_plus = M[1, 0]
    s_minus = M[1, 0] + (1 - q) * M[1, 1]
    closed = sp.cancel((1 - q) * q ** E / (s_plus * s_minus))
    engine = jump_gap(fr)
    det = sp.cancel(M.det())

    mismatches: list[str] = []
    if sp.cancel(engine - closed) != 0:
        mismatches.append("gap mismatch (symbolic): cancel(engine - closed) != 0")
    if sp.cancel(det - q ** E) != 0:
        mismatches.append(f"E shape (symbolic): det != q^E (E={E})")
    if _classical_denominator(cf) != s:
        mismatches.append(f"denominator shape: S^+(1) != s={s}")
    # unit fractions: the general closed form must collapse to the pure q-and-s
    # unit-fraction form (1-q) q^{s-1} / ([s]_q (1 + q^2 [s-1]_q)).
    if p == 1 and s >= 2 and sp.cancel(closed - unit_fraction_gap_formula(s)) != 0:
        mismatches.append("unit-fraction shape: closed form != (1-q)q^{s-1}/([s]_q(1+q^2[s-1]_q))")

    return {"p": p, "s": s, "E": E, "cf": cf, "ok": not mismatches, "mismatches": mismatches}


# ============================================================================
# The sweep set
# ============================================================================
def wide_set(ceiling: int) -> list[tuple[int, int]]:
    """Every reduced rational in (0, 1) up to the denominator ceiling, i.e. the
    Farey interior: r/s with 2 <= s <= ceiling, 1 <= r < s, gcd(r, s) = 1. The
    catalogue's r/s > 1 and integer cases are added so they too get a numeric
    check; the union is what the numeric pass sweeps."""
    seen: set[tuple[int, int]] = set()
    out: list[tuple[int, int]] = []
    for s in range(2, ceiling + 1):
        for r in range(1, s):
            if gcd(r, s) == 1 and (r, s) not in seen:
                seen.add((r, s))
                out.append((r, s))
    for (p, s) in build_catalogue() + heldout_set():
        if (p, s) not in seen:
            seen.add((p, s))
            out.append((p, s))
    out.sort(key=lambda ps: (ps[1], ps[0]))
    return out


def representative_subset() -> list[tuple[int, int]]:
    """The existing jump_catalog catalogue: the small exact-symbolic subset."""
    return build_catalogue()


# ============================================================================
# The scan
# ============================================================================
def run_scan(ceiling: int) -> dict:
    """Symbolic check on the representative subset, numeric check on every
    reduced rational up to the ceiling. Returns a JSON-able verdict."""
    sym_set = representative_subset()
    num_set = wide_set(ceiling)

    sym_keys = set(sym_set)
    offenders: list[dict] = []

    # exact symbolic on the representative subset
    sym_results = [symbolic_two_way(p, s) for (p, s) in sym_set]
    for r in sym_results:
        if not r["ok"]:
            offenders.append({
                "p": r["p"], "s": r["s"], "check": "symbolic",
                "detail": "; ".join(r["mismatches"]),
            })

    # numeric on the wide sweep
    num_results = [numeric_two_way(p, s) for (p, s) in num_set]
    for r in num_results:
        if not r["ok"]:
            offenders.append({
                "p": r["p"], "s": r["s"],
                "check": "numeric (also symbolic)" if (r["p"], r["s"]) in sym_keys else "numeric",
                "detail": "; ".join(r["mismatches"]),
            })

    all_keys = sorted(set(sym_set) | set(num_set), key=lambda ps: (ps[1], ps[0]))
    n_total = len(all_keys)
    n_both = len([k for k in all_keys if k in sym_keys])
    n_numeric_only = n_total - n_both

    agree = not offenders
    if agree:
        verdict = (f"agreement on all {n_total} rationals "
                   f"({n_both} exact-symbolic, {n_numeric_only} numeric-sampled)")
    else:
        verdict = f"exceptions found: {len(offenders)} of {n_total} rationals disagree"

    return {
        "ceiling": ceiling,
        "q_samples": [str(x) for x in Q_SAMPLES],
        "symbolic_subset_size": len(sym_set),
        "numeric_set_size": len(num_set),
        "n_total": n_total,
        "n_both": n_both,
        "n_numeric_only": n_numeric_only,
        "agree": agree,
        "verdict": verdict,
        "offenders": offenders,
    }


def write_md(result: dict, path: Path) -> None:
    lines = [
        "# Closed-form scan of the q-rational jump gap",
        "",
        "`gap_scan.py` sweeps every reduced rational up to a denominator ceiling and",
        "recomputes the one-sided jump gap two independent ways, flagging any",
        "disagreement. The two ways are:",
        "",
        "1. **engine gap** `[r/s]_q^+ - [r/s]_q^-`, the difference of the two full",
        "   q-continuant matrix ratios (`jump_catalog.jump_gap`):",
        "   `R/S^+ - (R + (1-q)R') / S^-`.",
        "2. **closed form** `(1 - q) q^E / (S^+ S^-)`, rebuilt from `q` and the",
        "   even-length continued fraction alone: `E` is the alternating CF-digit sum",
        "   (`alt_cf_sum`), and `S^+ = S`, `S^- = S + (1-q)S'` are the right / left",
        "   q-denominators read off the continuant bottom row.",
        "",
        "The two are algebraically equal iff `det(M_q) = q^E`, so the scan re-derives",
        "that telescoping identity rational by rational through two unrelated",
        "arithmetic paths: a subtraction of ratios against a monomial over a product.",
        "",
        "## Verdict",
        "",
        f"**{result['verdict']}**",
        "",
        "## Ranges checked",
        "",
        f"- Denominator ceiling: `s <= {result['ceiling']}`.",
        f"- Total distinct rationals: {result['n_total']}.",
        f"- Exact symbolic (representative subset, the `jump_catalog` catalogue): "
        f"{result['n_both']} rationals. Each gets `cancel(engine - closed) == 0`, the",
        "  symbolic `det(M_q) = q^E` check, and the `S^+(1) = s` denominator-shape check.",
        f"- Numeric-sampled (the wide sweep, every reduced `r/s` in `(0,1)` up to the",
        f"  ceiling plus the catalogue and held-out sets): {result['numeric_set_size']} "
        f"rationals, of which {result['n_numeric_only']} are numeric-only.",
        f"- Sampled values of `q`: {', '.join(result['q_samples'])} (all in `(0,1)`, where",
        "  every q-denominator is a sum of positive terms, so none vanishes).",
        "- Per rational the numeric pass checks, at each sampled `q`: `engine == closed`,",
        "  `det(M_q) == q^E` (E shape), and `S^+(1) == s` (denominator shape).",
        "",
        "## Which check each rational received",
        "",
        "- Rationals in both sets: exact symbolic and numeric-sampled.",
        "- Rationals only in the wide sweep: numeric-sampled.",
        "- The representative subset is kept exact-symbolic so the identity is",
        "  confirmed symbolically on a fixed, reproducible set; the wide numeric pass",
        "  extends the same two-way check to large denominators without the sympy",
        "  cancellation cost.",
        "",
        "## Exceptions",
        "",
    ]
    if not result["offenders"]:
        lines.append("None. The two ways agree, and `E` and both q-denominators match the")
        lines.append("predicted shape, on every rational checked.")
    else:
        lines.append("| r/s | check | mismatch |")
        lines.append("|---|---|---|")
        for o in result["offenders"]:
            lines.append(f"| {o['p']}/{o['s']} | {o['check']} | {o['detail']} |")
    lines.append("")
    lines.append("## Reproduce")
    lines.append("")
    lines.append("```")
    lines.append("python gap_scan.py        # asks for the ceiling")
    lines.append(f"python gap_scan.py {result['ceiling']}      # ceiling as argument")
    lines.append("```")
    lines.append("")
    lines.append("Built on `jump_catalog.py` (reuses `build_catalogue`, `heldout_set`,")
    lines.append("`jump_gap`, `unit_fraction_gap_formula`, `alt_cf_sum`, `cf_terms`,")
    lines.append("`make_even_length`, `continuant_matrix`). The qreals package is not touched.")
    lines.append("")
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    if len(sys.argv) >= 2:
        ceiling = int(sys.argv[1])
        print(f"Denominator ceiling: {ceiling} (from argument)")
    else:
        raw = input(f"Denominator ceiling for the sweep [default {DEFAULT_CEILING}]: ").strip()
        ceiling = int(raw) if raw else DEFAULT_CEILING

    if ceiling < 2:
        print("The denominator ceiling must be at least 2.", file=sys.stderr)
        return 2

    result = run_scan(ceiling)

    print()
    print("q-rational jump gap: two-way closed-form scan")
    print("  way 1 (engine) : R/S^+ - (R + (1-q)R') / S^-   [jump_catalog.jump_gap]")
    print("  way 2 (closed) : (1 - q) q^E / (S^+ S^-)        [E, S^+, S^- from the CF]")
    print()
    print(f"  denominator ceiling          : s <= {result['ceiling']}")
    print(f"  exact-symbolic subset        : {result['n_both']} rationals "
          f"(the jump_catalog catalogue)")
    print(f"  numeric-sampled set          : {result['numeric_set_size']} rationals "
          f"({result['n_numeric_only']} numeric-only)")
    print(f"  sampled q values             : {', '.join(result['q_samples'])}")
    print(f"  per rational also checked    : det(M_q) = q^E, and S^+(1) = S^-(1) = s")
    print()
    print(f"VERDICT: {result['verdict']}")
    print()

    if result["offenders"]:
        print("Offenders (rational, check, mismatch):")
        for o in result["offenders"]:
            print(f"  {o['p']}/{o['s']}  [{o['check']}]  {o['detail']}")
    else:
        print("No offenders: every rational agrees both ways, and E and both")
        print("q-denominators match the predicted shape.")

    write_md(result, HERE / "gap_scan.md")
    print()
    print(f"wrote {HERE / 'gap_scan.md'}")
    return 0 if result["agree"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
