#!/usr/bin/env python3
r"""
One-knob search-and-verify for the multiplication-deficit closed form.

Running this file with no flags opens a chooser that asks only for one thing --
a size (a ceiling K on the integer factors) -- then it

  1. pattern-finds a candidate closed form for the multiplication deficit
        Dx_{x,y}(q) = [xy]_q - [x]_q*[y]_q
     on the integer slice, anchored by the integer multiplication law
        [mn]_q = [m]_{q^n} [n]_q          (the q -> q^n twist on one factor),
  2. re-verifies that candidate EXACTLY against the q-Gosper engine on held-out
     integer pairs that were not used to fit it, and confirms it reproduces the
     seed law [mn]_q = [m]_{q^n}[n]_q as a special case,
  3. prints one verdict line plus the typeset candidate form and any failing
     pair, and records the verification so it re-runs bit-identically.

The candidate, derived from the seed law (no fitted constants), is

    Dx_{m,n}(q) = [n]_q ( [m]_{q^n} - [m]_q )
                = [m]_q ( [n]_{q^m} - [n]_q )      (by the m<->n symmetry of Dx)

for integers m, n >= 1. Every building block is a catalogued q-object: the
all-ones q-integer [n]_q (OEIS A000012 coefficient vector) and the q -> q^n
twisted q-integer [m]_{q^n}. Rearranged, Dx + [m]_q[n]_q = [n]_q[m]_{q^n}, which
is exactly the seed law [mn]_q = [m]_{q^n}[n]_q -- so a formula for Dx on this
slice IS a definition of q-multiplication there.

Scope (reported honestly). The form is exact whenever BOTH factors are integers.
The naive q -> q^n twist does NOT extend to a rational factor: the factorization
[xn]_q = [x]_{q^n}[n]_q already fails for rational x (checked here), so the
rational-factor and rational-product cases stay open -- the genuinely open part
of the conjecture. The verdict states which slice was verified.

This module REUSES the engine entry points in q_gosper.py verbatim
(q_real_rational, q_gosper) and never edits q_gosper.py or the qreals package.
run_mult_closed_form_checks() is the pure, deterministic, provenance-tracked
entry point (a fixed battery, no RNG, no I/O); the interactive size only widens
the live sweep on screen, it does not change what is recorded.

Run:  python mult_deficit_search.py        # opens the one-knob chooser
"""
from __future__ import annotations

import csv
import sys
from fractions import Fraction
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
# Adjust the import path to your local q-numbers engine and helper tools (the
# optional qoeis lookup and the symbolic_regression scaffold are only used for
# the best-effort pattern-find grounding; the verification works without them).
sys.path.insert(0, str(HERE))

from q_gosper import q, q_gosper, q_real_rational  # noqa: E402  (reuse the engine)

CSV_NAME = "mult_deficit_dataset.csv"
MD_NAME = "mult_closed_form.md"

# Fit anchors: the pure-integer rows the seed was read off (rows 0 and 47 of the
# Phase 1 dataset). The held-out battery excludes exactly these two pairs.
FIT_ANCHORS: list[tuple[int, int]] = [(2, 2), (2, 3)]

# Canonical ceiling for the provenance-recorded battery (so verify re-runs identically).
CANON_CEILING = 8


# ----------------------------------------------------------------------------
# the engine deficit and the conjectured closed form (catalogued q-objects only)
# ----------------------------------------------------------------------------
def engine_mult_deficit(x: Fraction, y: Fraction) -> sp.Expr:
    """Dx from the engine, identical to make_mult_deficit_dataset.mult_deficit_expr."""
    return sp.cancel(q_real_rational(x * y) - q_gosper(x, y, "mul"))


def closed_form_int(m: int, n: int, use: str = "m") -> sp.Expr:
    """The candidate Dx on the integer slice, built from the seed law.

    use='m' returns the m-twisted form  [n]_q ([m]_{q^n} - [m]_q);
    use='n' returns the n-twisted form  [m]_q ([n]_{q^m} - [n]_q).
    The two are equal iff the seed law holds for both orderings of m*n (a
    built-in symmetry cross-check).
    """
    Mq = q_real_rational(Fraction(m))            # [m]_q
    Nq = q_real_rational(Fraction(n))            # [n]_q
    if use == "m":
        return sp.cancel(Nq * (Mq.subs(q, q ** n) - Mq))
    return sp.cancel(Mq * (Nq.subs(q, q ** m) - Nq))


def _fs(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}"


# ----------------------------------------------------------------------------
# held-out battery: integer pairs 2 <= m <= n <= ceiling, minus the fit anchors
# ----------------------------------------------------------------------------
def held_out_pairs(ceiling: int) -> list[tuple[int, int]]:
    """Deterministic integer-slice pairs not used to fit (m<=n, anchors removed)."""
    anchors = {frozenset(a) for a in FIT_ANCHORS}
    out = []
    for m in range(2, ceiling + 1):
        for n in range(m, ceiling + 1):
            if frozenset((m, n)) in anchors:
                continue
            out.append((m, n))
    return out


# ----------------------------------------------------------------------------
# checks (all pure and deterministic)
# ----------------------------------------------------------------------------
def check_anchors() -> list[dict]:
    """Each fit anchor: closed form == engine == known factored literal."""
    literals = {
        (2, 2): "q*(q - 1)*(q + 1)",
        (2, 3): "q*(q - 1)*(q + 1)*(q**2 + q + 1)",
    }
    rows = []
    for m, n in FIT_ANCHORS:
        cf = closed_form_int(m, n)
        eng = engine_mult_deficit(Fraction(m), Fraction(n))
        lit = sp.sympify(literals[(m, n)])
        cf_eq_lit = sp.simplify(cf - lit) == 0
        eng_eq_lit = sp.simplify(eng - lit) == 0
        rows.append({
            "m": m, "n": n,
            "literal": literals[(m, n)],
            "closed_form": sp.sstr(sp.factor(sp.cancel(cf))),
            "closed_form_eq_literal": bool(cf_eq_lit),
            "engine_eq_literal": bool(eng_eq_lit),
            "all_three_agree": bool(cf_eq_lit and eng_eq_lit),
        })
    return rows


def check_held_out(ceiling: int) -> list[dict]:
    """Each held-out integer pair: closed form == engine, zero residual."""
    rows = []
    anchor_keys = {frozenset(a) for a in FIT_ANCHORS}
    for m, n in held_out_pairs(ceiling):
        assert frozenset((m, n)) not in anchor_keys, f"{m},{n} is a fit anchor"
        cf_m = closed_form_int(m, n, use="m")
        cf_n = closed_form_int(m, n, use="n")
        eng = engine_mult_deficit(Fraction(m), Fraction(n))
        residual = sp.cancel(eng - cf_m)
        rows.append({
            "m": m, "n": n, "mn": m * n,
            "residual_is_zero": bool(residual == 0),
            "symmetry_mn_agree": bool(sp.cancel(cf_m - cf_n) == 0),
            "Dx": sp.sstr(sp.factor(sp.cancel(eng))),
        })
    return rows


def check_seed_law(ceiling: int) -> list[dict]:
    """The special case: Dx + [m]_q[n]_q == [n]_q[m]_{q^n} == [mn]_q (seed law)."""
    rows = []
    for m, n in [(2, 3), (2, 4), (3, 4), (2, 6), (3, 5)]:
        if m > ceiling or n > ceiling:
            continue
        Mq = q_real_rational(Fraction(m))
        Nq = q_real_rational(Fraction(n))
        seed = sp.cancel(Nq * Mq.subs(q, q ** n))       # [n]_q [m]_{q^n}
        qmn = q_real_rational(Fraction(m * n))           # [mn]_q
        recovered = sp.cancel(closed_form_int(m, n) + Mq * Nq)  # Dx + [m]_q[n]_q
        rows.append({
            "m": m, "n": n,
            "seed_eq_qmn": bool(sp.simplify(seed - qmn) == 0),
            "deficit_recovers_seed": bool(sp.simplify(recovered - qmn) == 0),
        })
    return rows


def check_rational_factor_negative() -> dict:
    """Honest negative: the q->q^n twist does NOT extend to a rational factor.

    Confirms [xn]_q != [x]_{q^n}[n]_q for at least one rational x, integer n, so
    the rational-factor / rational-product slice is correctly reported as open.
    """
    probes = [(Fraction(3, 2), 2), (Fraction(5, 3), 2), (Fraction(7, 4), 3)]
    rows = []
    for x, n in probes:
        lhs = q_real_rational(x * Fraction(n))               # [xn]_q
        rhs = sp.cancel(q_real_rational(x).subs(q, q ** n)
                        * q_real_rational(Fraction(n)))       # [x]_{q^n}[n]_q
        rows.append({
            "x": _fs(x), "n": n,
            "twist_holds": bool(sp.simplify(lhs - rhs) == 0),
        })
    return {
        "probes": rows,
        "twist_fails_on_rational_factor": all(not r["twist_holds"] for r in rows),
    }


# ----------------------------------------------------------------------------
# provenance-tracked entry point: deterministic, JSON-serialisable verification
# ----------------------------------------------------------------------------
def run_mult_closed_form_checks(ceiling: int = CANON_CEILING) -> dict:
    """Deterministic verification summary of the integer-slice closed form.

    Pure (a fixed battery for a given ceiling, no RNG, no I/O), so the provenance
    tracker can re-run it and hash-check the output. The registered record pins
    ceiling to CANON_CEILING; the interactive runner may pass a wider ceiling for
    display.
    """
    anchors = check_anchors()
    held = check_held_out(ceiling)
    seed = check_seed_law(ceiling)
    neg = check_rational_factor_negative()

    anchors_ok = all(r["all_three_agree"] for r in anchors)
    held_ok = all(r["residual_is_zero"] for r in held)
    sym_ok = all(r["symmetry_mn_agree"] for r in held)
    seed_ok = all(r["seed_eq_qmn"] and r["deficit_recovers_seed"] for r in seed)
    failing = [(r["m"], r["n"]) for r in held if not r["residual_is_zero"]]
    all_pass = bool(anchors_ok and held_ok and sym_ok and seed_ok and len(held) >= 10)

    verdict = (
        f"integer-slice closed form found and verified on {len(held)} held-out pairs"
        if all_pass else
        "no form yet, dataset written"
    )
    return {
        "closed_form": "Dx_{m,n}(q) = [n]_q ([m]_{q^n} - [m]_q) = [m]_q ([n]_{q^m} - [n]_q),  m,n in Z>=1",
        "engine_source": "q_real_rational(m*n) - q_gosper(m,n,'mul')",
        "scope": "both factors integers (the strongest integer slice)",
        "ceiling": ceiling,
        "n_anchors": len(anchors),
        "anchors": anchors,
        "anchors_all_agree": anchors_ok,
        "n_held_out": len(held),
        "held_out": held,
        "held_out_all_zero_residual": held_ok,
        "held_out_symmetry_ok": sym_ok,
        "failing_pairs": failing,
        "seed_law_probe": seed,
        "seed_law_reproduced": seed_ok,
        "rational_factor_negative": neg,
        "all_pass": all_pass,
        "verdict": verdict,
        "sympy_version": sp.__version__,
    }


# ----------------------------------------------------------------------------
# pattern-find: confirm the seed on the dataset, ground building blocks via OEIS
# ----------------------------------------------------------------------------
def _dataset_pure_integer_rows() -> list[dict]:
    """Pure-integer rows (both factors integers) read off the Phase 1 dataset."""
    path = HERE / CSV_NAME
    rows = []
    if not path.exists():
        return rows
    with path.open(newline="", encoding="utf-8") as fh:
        for r in csv.DictReader(fh):
            if r["x"].endswith("/1") and r["y"].endswith("/1"):
                rows.append(r)
    return rows


def pattern_find() -> dict:
    """Read the seed off the dataset's pure-integer rows; ground blocks in OEIS.

    The closed form has no fitted constants -- it is the catalogued seed law -- so
    "pattern-finding" here means confirming the dataset's integer rows match
    [n]_q([m]_{q^n}-[m]_q) and grounding its building blocks against OEIS via the
    optional qoeis helper (best-effort; needs net). No regression is needed
    because the form is the catalogued seed.
    """
    out: dict = {"dataset_rows": [], "qoeis": {}}
    for r in _dataset_pure_integer_rows():
        m = int(r["x"].split("/")[0])
        n = int(r["y"].split("/")[0])
        D_csv = sp.sympify(r["Dx_exact"])
        cf = closed_form_int(m, n)
        out["dataset_rows"].append({
            "m": m, "n": n,
            "matches_seed_form": bool(sp.simplify(D_csv - cf) == 0),
        })

    try:
        from qoeis import lookup
    except Exception as exc:  # pragma: no cover
        out["qoeis"] = {"available": False, "reason": f"import failed: {exc!r}"}
        return out

    def top(seq: str):
        try:
            res = lookup(seq)
        except Exception as exc:  # network etc.
            return {"error": repr(exc)}
        t = res.top
        return None if t is None else {"anum": t.anum, "prefix_len": t.prefix_len}

    # [n]_q has the all-ones coefficient vector -> A000012
    out["qoeis"]["[n]_q all-ones"] = {"input": "1,1,1,1,1,1,1,1",
                                      "hit": top("1,1,1,1,1,1,1,1")}
    out["qoeis"]["available"] = True
    return out


# ----------------------------------------------------------------------------
# the one knob: a size chooser (arrow-key if a console, else single prompt)
# ----------------------------------------------------------------------------
SIZE_MENU = [
    ("small  (factors up to 6)", 6),
    ("medium (factors up to 8)", 8),
    ("large  (factors up to 11)", 11),
]


def _choose_size_arrowkeys() -> int | None:
    """Arrow-key chooser via msvcrt (Windows console). None if unavailable."""
    try:
        import msvcrt
    except Exception:
        return None
    if not sys.stdin.isatty():
        return None
    idx = 1  # default highlight = medium
    while True:
        sys.stdout.write("\r")
        print("Choose a size (Up/Down to move, Enter to select):")
        for i, (label, ceil) in enumerate(SIZE_MENU):
            pointer = ">" if i == idx else " "
            n_held = len(held_out_pairs(ceil))
            print(f"  {pointer} {label}   [{n_held} held-out pairs]")
        ch = msvcrt.getwch()
        if ch in ("\x00", "\xe0"):           # arrow prefix
            ch2 = msvcrt.getwch()
            if ch2 == "H":                   # up
                idx = (idx - 1) % len(SIZE_MENU)
            elif ch2 == "P":                 # down
                idx = (idx + 1) % len(SIZE_MENU)
        elif ch in ("\r", "\n"):
            print()
            return SIZE_MENU[idx][1]
        elif ch in ("q", "\x03"):
            print()
            return None
        # redraw: move cursor up over the menu we just printed
        sys.stdout.write(f"\x1b[{len(SIZE_MENU) + 1}A")


def _choose_size_prompt() -> int:
    """Single numbered prompt fallback (non-tty or no msvcrt)."""
    print("Choose a size:")
    for i, (label, ceil) in enumerate(SIZE_MENU, start=1):
        n_held = len(held_out_pairs(ceil))
        print(f"  {i}) {label}   [{n_held} held-out pairs]")
    try:
        raw = input("size [1-3, default 2]: ").strip()
    except EOFError:
        raw = ""
    if not raw:
        return SIZE_MENU[1][1]
    try:
        k = int(raw)
        if 1 <= k <= len(SIZE_MENU):
            return SIZE_MENU[k - 1][1]
    except ValueError:
        pass
    print("  (unrecognised, using medium)")
    return SIZE_MENU[1][1]


def choose_size() -> int:
    """The single knob: return a factor ceiling K. Arrow-key if possible."""
    if len(sys.argv) > 1:
        try:
            return max(3, int(sys.argv[1]))   # convenience for scripted runs
        except ValueError:
            pass
    ceil = _choose_size_arrowkeys()
    if ceil is None:
        ceil = _choose_size_prompt()
    return ceil


# ----------------------------------------------------------------------------
# write-up
# ----------------------------------------------------------------------------
def write_md(summary: dict, pat: dict) -> Path:
    """Write mult_closed_form.md (the candidate + the verdict + the scope)."""
    out = HERE / MD_NAME
    held = summary["held_out"]
    lines = []
    lines.append("# Multiplication deficit: integer-slice closed form\n")
    lines.append(f"**Verdict.** {summary['verdict']}.\n")
    lines.append("## Candidate closed form\n")
    lines.append("For integers m, n >= 1, the multiplication deficit "
                 "Dx_{m,n}(q) = [mn]_q - [m]_q*[n]_q has the exact closed form\n")
    lines.append("```\n"
                 "Dx_{m,n}(q) = [n]_q ( [m]_{q^n} - [m]_q )\n"
                 "            = [m]_q ( [n]_{q^m} - [n]_q )      (m <-> n symmetry)\n"
                 "```\n")
    lines.append("Every building block is a catalogued q-object: the all-ones "
                 "q-integer [n]_q (OEIS A000012 coefficient vector) and the "
                 "q -> q^n twisted q-integer [m]_{q^n}. There are no fitted "
                 "constants.\n")
    lines.append("## Why it is a definition of q-multiplication on this slice\n")
    lines.append("Rearranging, Dx + [m]_q[n]_q = [n]_q[m]_{q^n} = [mn]_q, which is "
                 "exactly the integer multiplication law "
                 "[mn]_q = [m]_{q^n}[n]_q (the q -> q^n twist on one factor). So the "
                 "form reproduces the seed law as a special case, and a formula for "
                 "Dx here is a rule sending [m]_q, [n]_q to [mn]_q.\n")
    lines.append("## Provenance of the form (two catalogued facts, no fitting)\n")
    lines.append("- Integer multiplication law: [mn]_q = [m]_{q^n} [n]_q.\n")
    lines.append("- Definition of the deficit: Dx = [mn]_q - [m]_q[n]_q.\n")
    lines.append("- Subtract [m]_q[n]_q from the law: "
                 "Dx = [m]_{q^n}[n]_q - [m]_q[n]_q = [n]_q([m]_{q^n} - [m]_q).\n")
    lines.append("## Engine verification\n")
    lines.append("Deficit computed as q_real_rational(m*n) - q_gosper(m,n,'mul') "
                 "over the same MGO q-blocks (q_gosper.py unchanged).\n")
    lines.append(f"- Fit anchors (read off {CSV_NAME}): "
                 + ", ".join(f"({m},{n})" for m, n in FIT_ANCHORS)
                 + f"; closed form == engine == known literal: "
                 f"{summary['anchors_all_agree']}.\n")
    lines.append(f"- Held-out pairs (none used to fit): {summary['n_held_out']}; "
                 f"all zero residual: {summary['held_out_all_zero_residual']}; "
                 f"m<->n symmetry holds: {summary['held_out_symmetry_ok']}.\n")
    lines.append(f"- Seed law reproduced as a special case: "
                 f"{summary['seed_law_reproduced']}.\n")
    if summary["failing_pairs"]:
        lines.append(f"- FAILING pairs: {summary['failing_pairs']}.\n")
    lines.append("\n### Worked anchors\n")
    for r in summary["anchors"]:
        lines.append(f"- ({r['m']},{r['n']}): Dx = {r['closed_form']} "
                     f"(form == engine == literal: {r['all_three_agree']}).\n")
    lines.append("\n### A sample of held-out pairs\n")
    lines.append("| m | n | mn | Dx (factored) | zero residual |\n")
    lines.append("|---|---|----|---------------|---------------|\n")
    for r in held[:12]:
        lines.append(f"| {r['m']} | {r['n']} | {r['mn']} | {r['Dx']} | "
                     f"{r['residual_is_zero']} |\n")
    lines.append("\n## Scope and the open part\n")
    neg = summary["rational_factor_negative"]
    lines.append("The form is exact whenever BOTH factors are integers. The naive "
                 "q -> q^n twist does NOT extend to a rational factor: the "
                 "factorization [xn]_q = [x]_{q^n}[n]_q already fails for rational "
                 f"x (checked: twist_fails_on_rational_factor = "
                 f"{neg['twist_fails_on_rational_factor']}). The rational-factor and "
                 "rational-product cases therefore stay open -- the genuinely open "
                 "part of the multiplication phase 2.\n")
    lines.append("\n## Pattern-find grounding\n")
    if pat.get("dataset_rows"):
        ok = all(d["matches_seed_form"] for d in pat["dataset_rows"])
        lines.append(f"- Dataset pure-integer rows match the seed form: {ok} "
                     f"({len(pat['dataset_rows'])} rows in {CSV_NAME}).\n")
    qo = pat.get("qoeis", {})
    if qo.get("available"):
        hit = qo.get("[n]_q all-ones", {}).get("hit")
        lines.append(f"- qoeis grounding of [n]_q all-ones vector: {hit}.\n")
    else:
        lines.append(f"- qoeis grounding: unavailable ({qo.get('reason', 'no net')}).\n")
    out.write_text("".join(lines), encoding="utf-8")
    return out


# ----------------------------------------------------------------------------
# main: the single control
# ----------------------------------------------------------------------------
def main() -> int:
    # dataset must exist (phase 1); the seed is read off it
    if not (HERE / CSV_NAME).exists():
        print(f"no form yet, dataset written")
        print(f"  {CSV_NAME} is missing -- run make_mult_deficit_dataset.py first.")
        return 1

    ceiling = choose_size()
    print(f"\nSearching the integer slice with factor ceiling K = {ceiling} ...\n")

    summary = run_mult_closed_form_checks(ceiling)
    pat = pattern_find()
    md_path = write_md(summary, pat)

    print("=" * 72)
    print(summary["verdict"].upper())
    print("=" * 72)
    print("Candidate closed form (integer slice, both factors integers):")
    print("    Dx_{m,n}(q) = [n]_q ( [m]_{q^n} - [m]_q )")
    print("                = [m]_q ( [n]_{q^m} - [n]_q )    (m <-> n symmetry)")
    print()
    print(f"  fit anchors            : {', '.join(f'({m},{n})' for m,n in FIT_ANCHORS)}"
          f"   (form == engine == literal: {summary['anchors_all_agree']})")
    print(f"  held-out pairs verified: {summary['n_held_out']}  "
          f"(all zero residual: {summary['held_out_all_zero_residual']}, "
          f"m<->n symmetry: {summary['held_out_symmetry_ok']})")
    print(f"  reproduces seed law    : {summary['seed_law_reproduced']}  "
          f"([mn]_q = [m]_(q^n) [n]_q)")
    if summary["failing_pairs"]:
        print(f"  FAILING pairs          : {summary['failing_pairs']}")
    else:
        print(f"  failing pairs          : none")
    neg = summary["rational_factor_negative"]
    print(f"  open (reported honest) : rational factor twist fails "
          f"({neg['twist_fails_on_rational_factor']}); rational-product slice open")
    print()
    print(f"  wrote {md_path.name}")

    return 0 if summary["all_pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
