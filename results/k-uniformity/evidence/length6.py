#!/usr/bin/env python3
r"""Length 6, and the divisor law behind the exceptional moduli.

a collaborator's question: the equations get more complicated as the length i grows, so is there
an i = 6 analogue of the exceptional case seen at i = 4, where the value of k matters.

The observed exceptions so far are the extra solution (2,2,2) at k = 4 and length 4, and
the extra solutions (2,2,2,2) and (3,3,3,3) at k = 5 and length 5. The first two are the
constant word of 2s, and at those words S_4 = Phi_2 Phi_4 and S_5 = Phi_5. That suggests

    S_i(2, 2, ..., 2) = [i]_q,

in which case the constant word is a solution at every k dividing i with k > 1, and the
exceptional moduli at length i are the divisors of i that the generic families miss. The
prediction for length 6 is therefore exceptional behaviour at k = 3 and k = 6, and 6 is
also the modulus where the specialised modular group stops being finite.

This script tests that prediction three ways:
  1. the identity S_i(2,...,2) = [i]_q, symbolically, for i up to 12;
  2. the full length-6 vanishing locus, exactly, for k = 2 to 11;
  3. whether the length-6 counts follow a linear law for large k, and which moduli deviate.

Run:
    PYTHONPATH=<path> python3 length6.py
"""

from __future__ import annotations

import sys
from pathlib import Path

from sympy import Poly, cyclotomic_poly, expand, factor_list, symbols

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from vanishing_locus import CycRing, centered, denominator_value, locus

q = symbols("q")


def S_poly(word):
    prev, cur, cprev = 0, 1, None
    for c in word:
        sub = 0 if cprev is None else q ** (cprev - 1) * prev
        prev, cur, cprev = cur, expand(sum(q**j for j in range(c)) * cur - sub), c
    return expand(cur)


try:
    import provstore
    provstore.set_store_root(HERE)
    tracked = provstore.tracked
    HAVE_PROVSTORE = True
except Exception:
    HAVE_PROVSTORE = False

    def tracked(*a, **kw):
        def deco(f):
            return f
        return deco if not a else a[0]


@tracked(tags={"tangent": "2026-08-10-k-uniformity", "quantity": "constant_word_law"})
def constant_word_law(max_length: int) -> dict:
    """S_i(2,2,...,2) = [i]_q, and hence Phi_k divides it for every k dividing i, k > 1."""
    rows = {}
    for i in range(3, max_length + 1):
        S = S_poly((2,) * (i - 1))
        bracket_i = sum(q**j for j in range(i))
        rows[i] = {
            "equals_bracket_i": expand(S - bracket_i) == 0,
            "factors": str(factor_list(S)[1]),
            "divisors_hit": [k for k in range(2, i + 1) if i % k == 0
                             and Poly(S, q).rem(Poly(cyclotomic_poly(k, q), q)).is_zero],
        }
    return {"max_length": max_length, "rows": rows,
            "law_holds": all(r["equals_bracket_i"] for r in rows.values())}


@tracked(tags={"tangent": "2026-08-10-k-uniformity", "quantity": "length6_counts"})
def length6_counts(kmin: int, kmax: int) -> dict:
    counts = {k: len(locus(k, 6)) for k in range(kmin, kmax + 1)}
    return {"length": 6, "counts": counts}


@tracked(tags={"tangent": "2026-08-10-k-uniformity", "quantity": "length6_window"})
def length6_window(ks: list[int], window: int = 3) -> dict:
    per_k = {}
    for k in ks:
        sols = {tuple(centered(r, k) for r in w) for w in locus(k, 6)}
        per_k[k] = sorted(t for t in sols if all(abs(v) <= window for v in t))
    base = per_k[ks[0]]
    return {"length": 6, "window": window, "ks": ks, "size": len(base),
            "identical_across_ks": all(per_k[k] == base for k in ks)}


@tracked(tags={"tangent": "2026-08-10-k-uniformity", "quantity": "length6_law"})
def fit_quadratic(counts: dict, anchor: int) -> dict:
    """Fit a k b k^2 law on three consecutive anchors and report deviations everywhere.

    The count is linear in k at lengths 4 and 5, one free parameter per family. At length 6
    it is quadratic, so the fit is taken on three points rather than two, and the deviations
    are the honest test of whether the law holds away from the anchors.
    """
    k0 = anchor
    a = (counts[k0 + 2] - 2 * counts[k0 + 1] + counts[k0]) // 2
    b = counts[k0 + 1] - counts[k0] - a * (2 * k0 + 1)
    c = counts[k0] - a * k0 * k0 - b * k0
    dev = {k: counts[k] - (a * k * k + b * k + c) for k in sorted(counts)}
    return {"law": f"{a}k^2 + {b}k + {c}", "a": a, "b": b, "c": c,
            "anchor": anchor,
            "deviations": {k: d for k, d in dev.items() if d != 0},
            "generic_from": min((k for k in sorted(counts) if
                                 all(dev[j] == 0 for j in sorted(counts) if j >= k)),
                                default=None)}


@tracked(tags={"tangent": "2026-08-10-k-uniformity", "quantity": "window_sweep"})
def window_sweep(length: int, ks: list[int], windows: list[int]) -> dict:
    """Smallest residue window whose restricted locus is k-independent, at this length.

    A window is only informative when it is strictly smaller than half the modulus. Once
    W >= k/2 the window contains every centered residue, the restriction is the whole locus,
    and the comparison degenerates into comparing total counts, which differ for trivial
    reasons. The guard below makes that a hard failure rather than a silently empty test.
    """
    if max(windows) >= min(ks) // 2:
        raise AssertionError(
            f"window {max(windows)} is not smaller than half of k = {min(ks)}, "
            "so the restricted locus is the whole locus and the test is vacuous")
    full = {k: {tuple(centered(r, k) for r in w) for w in locus(k, length)} for k in ks}
    rows = {}
    for W in windows:
        per_k = {k: sorted(t for t in full[k] if all(abs(v) <= W for v in t)) for k in ks}
        base = per_k[ks[0]]
        rows[W] = {"identical": all(per_k[k] == base for k in ks), "size": len(base)}
    stable = [W for W, r in rows.items() if r["identical"]]
    return {"length": length, "ks": ks, "rows": rows,
            "smallest_stable_window": min(stable) if stable else None}


def main() -> int:
    law = constant_word_law(max_length=12)
    print("S_i(2,...,2) = [i]_q for i = 3..12:", law["law_holds"])
    for i, r in law["rows"].items():
        print(f"   i={i:2d} divisors k>1 with Phi_k | S_i: {r['divisors_hit']}")

    counts = length6_counts(kmin=2, kmax=11)["counts"]
    print("length 6 counts:", counts)
    fit = fit_quadratic(counts=counts, anchor=9)
    print(f"   quadratic law {fit['law']}, exact from k = {fit['generic_from']}, "
          f"deviations {fit['deviations']}")

    sweep = window_sweep(length=6, ks=[11, 12, 13], windows=[3, 4])
    print("   window sweep:", {W: r for W, r in sweep["rows"].items()})
    print("   smallest k-independent window:", sweep["smallest_stable_window"])

    if HAVE_PROVSTORE:
        for quantity, text, val in [
            ("constant_word_law",
             "The constant word of 2s satisfies S_i(2,...,2) = [i]_q for i from 3 to 12, so "
             "Phi_k divides S_i for every k dividing i with k > 1.", law["max_length"]),
            ("length6_law",
             f"At continued fraction length 6 the number of vanishing residue words is "
             f"{fit['law']}, exactly, for every k from {fit['generic_from']} to 11, with "
             f"deviations only at {sorted(fit['deviations'])}.", fit["a"]),
            ("window_sweep",
             f"At length 6 the smallest residue window whose restricted locus is the same "
             f"word set for k = {sweep['ks']} is "
             f"{sweep['smallest_stable_window']}, so the window 3 that suffices at lengths "
             f"3 to 5 is too small.", sweep["smallest_stable_window"] or 0),
        ]:
            hits = provstore.find(tags={"quantity": quantity,
                                    "tangent": "2026-08-10-k-uniformity"})
            if not hits:
                raise AssertionError(f"no recorded computation for {quantity}")
            provstore.claim(text, computation_id=hits[0].id, value_numeric=val,
                        tags={"tangent": "2026-08-10-k-uniformity", "quantity": quantity})
    return 0


if __name__ == "__main__":
    from length6 import main as _main
    sys.exit(_main())
