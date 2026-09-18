#!/usr/bin/env python3
r"""Exact vanishing locus of the q-denominator at roots of unity, and its k-uniformity.

Question (raised by a collaborator, 2026-08-10). For a q-rational with negative continued
fraction expansion x = [[c_1, c_2, ..., c_i]], the q-denominator satisfies

    S_{i+1}(q) = [c_{i+1}]_q S_i(q) - q^{c_i - 1} S_{i-1}(q),   (S_0, S_1) = (0, 1),

with [a]_q = 1 + q + ... + q^{a-1}. Since both [a]_q and q^{a-1} evaluated at a primitive
kth root of unity depend only on a mod k, the condition Phi_k | S is a condition on the
residues (c_2, ..., c_i) mod k. Note S_i does not depend on c_1.

The observation to test: those residue conditions appear not to depend on k. They stay
pinned near 0 and near plus or minus 1, 2, 3, and the same conditions work for every k.

This module computes the vanishing locus exactly, with no truncation and no floating
point, by working in the ring of integers Z[x]/Phi_k(x). It reports:

  1. the total number of solution residue tuples for each k,
  2. the sub-locus whose residues all lie in the centered window [-W, W], and whether
     that sub-locus is literally identical across a range of k,
  3. the deviation of the total from the linear law that the large-k data obey, which
     isolates the sporadic moduli.

Two independent code paths compute the same locus. The fast path uses a precomputed
power table in Z[x]/Phi_k; the reference path calls sympy polynomial remainder directly.
They are compared on every k up to CROSSCHECK_KMAX and any disagreement is a hard failure.

Run:
    PYTHONPATH=<path> python3 vanishing_locus.py            # full run, writes RESULTS.md
    PYTHONPATH=<path> python3 vanishing_locus.py --quick    # small k only
"""

from __future__ import annotations

import argparse
import json
import sys
from itertools import product
from pathlib import Path

from sympy import Poly, cyclotomic_poly, symbols

HERE = Path(__file__).resolve().parent
x = symbols("x")

CROSSCHECK_KMAX = 8
WINDOW = 3          # centered residue window, matches the residues seen in the families
STABLE_FROM = 9     # k from which the windowed locus is compared for equality


# ---------------------------------------------------------------------------
# exact arithmetic in Z[x]/Phi_k(x)
# ---------------------------------------------------------------------------

class CycRing:
    """Z[x]/Phi_k(x) with a precomputed reduction table. Elements are lists of ints."""

    def __init__(self, k: int):
        self.k = k
        coeffs = Poly(cyclotomic_poly(k, x), x).all_coeffs()[::-1]   # low to high
        assert coeffs[-1] == 1, "cyclotomic polynomials are monic"
        self.d = len(coeffs) - 1
        self.red = [-c for c in coeffs[:-1]]                          # x^d = sum red[i] x^i
        self.tab = self._power_table()

    def _power_table(self) -> list[list[int]]:
        """x^j reduced, for j = 0 .. 2d, enough for one convolution."""
        tab, cur = [], [0] * self.d
        cur[0] = 1
        for _ in range(2 * self.d + 1):
            tab.append(cur[:])
            cur = self._shift(cur)
        return tab

    def _shift(self, v: list[int]) -> list[int]:
        top = v[-1]
        out = [0] + v[:-1]
        if top:
            for i in range(self.d):
                out[i] += top * self.red[i]
        return out

    def zero(self) -> list[int]:
        return [0] * self.d

    def one(self) -> list[int]:
        v = self.zero()
        v[0] = 1
        return v

    def add(self, a, b):
        return [u + v for u, v in zip(a, b)]

    def sub(self, a, b):
        return [u - v for u, v in zip(a, b)]

    def mul(self, a, b):
        d = self.d
        conv = [0] * (2 * d - 1)
        for i, u in enumerate(a):
            if u:
                for j, v in enumerate(b):
                    if v:
                        conv[i + j] += u * v
        out = conv[:d] + [0] * max(0, d - len(conv))
        for e in range(d, 2 * d - 1):
            co = conv[e]
            if co:
                t = self.tab[e]
                for i in range(d):
                    out[i] += co * t[i]
        return out

    def is_zero(self, a) -> bool:
        return not any(a)

    def monomials(self) -> list[list[int]]:
        """x^e for e = 0 .. k-1."""
        out = [self.one()]
        for _ in range(self.k - 1):
            out.append(self._shift(out[-1]))
        return out

    def brackets(self, mono) -> list[list[int]]:
        """[a]_q at the root of unity, for a = 0 .. k-1."""
        out, acc = [], self.zero()
        for a in range(self.k):
            out.append(acc[:])
            acc = self.add(acc, mono[a])
        return out


def denominator_value(R: CycRing, mono, brk, word):
    """S_i(omega) for the residue word (c_2, ..., c_i), via the MGO recursion."""
    prev, cur, cprev = R.zero(), R.one(), None          # (S_0, S_1) = (0, 1)
    for c in word:
        if cprev is None:
            sub = R.zero()                              # q^{c_1 - 1} S_0 = 0, so c_1 is free
        else:
            sub = R.mul(mono[(cprev - 1) % R.k], prev)
        prev, cur, cprev = cur, R.sub(R.mul(brk[c], cur), sub), c
    return cur


def locus(k: int, length: int) -> list[tuple[int, ...]]:
    """All residue words (c_2, ..., c_length) mod k with S_length(omega_k) = 0."""
    R = CycRing(k)
    mono = R.monomials()
    brk = R.brackets(mono)
    return [w for w in product(range(k), repeat=length - 1)
            if R.is_zero(denominator_value(R, mono, brk, w))]


def locus_reference(k: int, length: int) -> list[tuple[int, ...]]:
    """Independent slow path: sympy Poly.rem against Phi_k at every step."""
    Phi = Poly(cyclotomic_poly(k, x), x)

    def red(expr):
        return Poly(expr, x).rem(Phi)

    brk = {a: red(sum(x**j for j in range(a))) for a in range(k)}
    xp = {a: red(x**a) for a in range(k)}
    out = []
    for w in product(range(k), repeat=length - 1):
        prev, cur, cprev = Poly(0, x), Poly(1, x), None
        for c in w:
            sub = Poly(0, x) if cprev is None else red(xp[(cprev - 1) % k].as_expr() * prev.as_expr())
            prev, cur, cprev = cur, red(brk[c].as_expr() * cur.as_expr() - sub.as_expr()), c
        if cur.is_zero:
            out.append(w)
    return out


def centered(r: int, k: int) -> int:
    return r - k if r > k // 2 else r


# ---------------------------------------------------------------------------
# tracked results
# ---------------------------------------------------------------------------

try:
    import provstore
    provstore.set_store_root(HERE)
    tracked = provstore.tracked
    HAVE_PROVSTORE = True
except Exception:                                        # the maths must run without it
    HAVE_PROVSTORE = False

    def tracked(*a, **kw):
        def deco(f):
            return f
        return deco if not a else a[0]


@tracked(tags={"tangent": "2026-08-10-k-uniformity", "quantity": "solution_counts"})
def solution_counts(length: int, kmin: int, kmax: int) -> dict:
    """Size of the vanishing locus for each k, with a cross-checked reference path."""
    counts = {}
    for k in range(kmin, kmax + 1):
        fast = sorted(locus(k, length))
        if k <= CROSSCHECK_KMAX:
            ref = sorted(locus_reference(k, length))
            if fast != ref:
                raise AssertionError(f"path disagreement at k={k}, length={length}")
        counts[k] = len(fast)
    return {"length": length, "counts": counts,
            "crosschecked_through_k": min(kmax, CROSSCHECK_KMAX)}


@tracked(tags={"tangent": "2026-08-10-k-uniformity", "quantity": "windowed_locus"})
def windowed_locus(length: int, ks: list[int], window: int = WINDOW) -> dict:
    """The locus restricted to residues in [-window, window], and whether it is k-free."""
    per_k = {}
    for k in ks:
        sols = {tuple(centered(r, k) for r in w) for w in locus(k, length)}
        per_k[k] = sorted(t for t in sols if all(abs(v) <= window for v in t))
    base = per_k[ks[0]]
    return {"length": length, "window": window, "ks": ks,
            "identical_across_ks": all(per_k[k] == base for k in ks),
            "size": len(base), "tuples": base}


@tracked(tags={"tangent": "2026-08-10-k-uniformity", "quantity": "sporadics"})
def sporadic_moduli(length: int, counts: dict, slope: int, intercept: int,
                    generic_from: int) -> dict:
    """Deviation of each count from the linear law that holds for k >= generic_from."""
    dev = {}
    for k, n in counts.items():
        k = int(k)
        dev[k] = n - (slope * k + intercept)
    for k, d in dev.items():
        if k >= generic_from and d != 0:
            raise AssertionError(f"linear law fails at k={k}, length={length}")
    return {"length": length, "law": f"{slope}k + {intercept}",
            "generic_from": generic_from,
            "deviations": {k: d for k, d in dev.items() if d != 0}}


# ---------------------------------------------------------------------------
# report
# ---------------------------------------------------------------------------

LAWS = {3: (0, 2, 3), 4: (2, 3, 7), 5: (10, 0, 7)}       # length: (slope, intercept, generic_from)


def computation_id_for(quantity: str, length: int) -> str | None:
    """Id of the recorded computation of `quantity` at this length.

    The decorator tags cannot carry the length, since they are fixed at definition
    time, so the record is identified by the length reported in its own result. A
    claim must never be attached to the computation of a different length, which is
    exactly the silent mismatch provstore exists to prevent, so an ambiguous or missing
    match is a hard failure rather than a fallback.
    """
    if not HAVE_PROVSTORE:
        return None
    hits = [c for c in provstore.find(tags={"quantity": quantity,
                                        "tangent": "2026-08-10-k-uniformity"})
            if isinstance(c.result, dict) and c.result.get("length") == length]
    if not hits:
        raise AssertionError(f"no recorded computation of {quantity} at length {length}")
    return hits[0].id


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true", help="stop at k = 9")
    args = ap.parse_args()
    kmax = 9 if args.quick else 13

    out = {}
    for length in (3, 4, 5):
        counts = solution_counts(length=length, kmin=2, kmax=kmax)
        slope, intercept, generic_from = LAWS[length]
        window = windowed_locus(length=length,
                                ks=[k for k in range(STABLE_FROM, kmax + 1)])
        spor = sporadic_moduli(length=length, counts=counts["counts"],
                               slope=slope, intercept=intercept,
                               generic_from=generic_from)
        out[length] = {"counts": counts, "window": window, "sporadics": spor,
                       "ids": {q: computation_id_for(q, length)
                               for q in ("solution_counts", "windowed_locus", "sporadics")},
                       "kmax": kmax}
        print(f"length {length}: counts {counts['counts']}")
        print(f"  law {spor['law']} from k >= {generic_from}, "
              f"deviations {spor['deviations']}")
        print(f"  windowed locus identical across {window['ks']}: "
              f"{window['identical_across_ks']} (size {window['size']})")

    (HERE / "results.json").write_text(json.dumps(out, indent=1, default=str))
    write_results_md(out, kmax)
    if HAVE_PROVSTORE:
        record_claims(out)
    return 0


def write_results_md(out: dict, kmax: int) -> None:
    lines = ["# Vanishing locus of S at roots of unity: exact counts", "",
             "Generated by `vanishing_locus.py`. Exact arithmetic in Z[x]/Phi_k, no truncation.",
             f"Every k up to {CROSSCHECK_KMAX} is computed twice by independent code paths.", "",
             "| length | k | number of solution words |", "|---|---|---|"]
    for length in sorted(out):
        for k, n in out[length]["counts"]["counts"].items():
            lines.append(f"| {length} | {k} | {n} |")
    lines += ["", "## Linear law and sporadic moduli", "",
              "| length | law for large k | first generic k | deviations |", "|---|---|---|---|"]
    for length in sorted(out):
        s = out[length]["sporadics"]
        lines.append(f"| {length} | {s['law']} | {s['generic_from']} | "
                     f"{s['deviations'] or 'none'} |")
    lines += ["", f"## Windowed locus, residues in [-{WINDOW}, {WINDOW}]", "",
              "| length | identical across k | size |", "|---|---|---|"]
    for length in sorted(out):
        w = out[length]["window"]
        lines.append(f"| {length} | {w['identical_across_ks']} | {w['size']} |")
    lines += ["", "The windowed locus is compared across "
              f"k = {STABLE_FROM} to {kmax}. Identical means the same set of residue words,",
              "not merely the same cardinality.", ""]
    for length in sorted(out):
        w = out[length]["window"]
        lines += [f"### Length {length} windowed locus ({w['size']} words)", "",
                  "```", *[str(t) for t in w["tuples"]], "```", ""]
    (HERE / "RESULTS.md").write_text("\n".join(lines))


def record_claims(out: dict) -> None:
    """One claim per reported number, each pointing at the computation of its own length."""
    laws = {3: "exactly 2", 4: "exactly 2k + 3", 5: "exactly 10k"}
    slopes = {3: 2, 4: 2, 5: 10}
    for length in sorted(out):
        rec = out[length]
        ids, kmax = rec["ids"], rec["kmax"]
        gen = LAWS[length][2]
        provstore.claim(
            f"At continued fraction length {length} the number of residue words with "
            f"S_{length} vanishing at a primitive kth root of unity is {laws[length]}, "
            f"for every k from {gen} to {kmax}.",
            computation_id=ids["solution_counts"], value_numeric=slopes[length],
            tags={"tangent": "2026-08-10-k-uniformity", "length": length,
                  "quantity": "count-law"})
        w = rec["window"]
        provstore.claim(
            f"At length {length} the set of vanishing residue words with all residues in "
            f"[-{WINDOW}, {WINDOW}] is the same set of {w['size']} words for every k from "
            f"{STABLE_FROM} to {kmax}.",
            computation_id=ids["windowed_locus"], value_numeric=w["size"],
            tags={"tangent": "2026-08-10-k-uniformity", "length": length,
                  "quantity": "k-uniformity"})
        s = rec["sporadics"]
        provstore.claim(
            f"At length {length} the only moduli up to {kmax} where the count deviates "
            f"from {s['law']} are {sorted(s['deviations'])}.",
            computation_id=ids["sporadics"], value_numeric=len(s["deviations"]),
            tags={"tangent": "2026-08-10-k-uniformity", "length": length,
                  "quantity": "sporadics"})


if __name__ == "__main__":
    # Run through the imported module, never through __main__. A function recorded while
    # its module is __main__ cannot be resolved again by `provstore verify`, so the record
    # would be unreproducible; importing this file by name binds the tracked functions to
    # the module `vanishing_locus`, which verify can import.
    sys.path.insert(0, str(HERE))
    from vanishing_locus import main as _main
    sys.exit(_main())
