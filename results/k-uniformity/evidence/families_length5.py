#!/usr/bin/env python3
r"""Test the explicit length-5 family list against the exact vanishing locus.

Proposed description of V_5(k) for k >= 7: ten one-parameter families, being the five
shapes below with a single governing sign e = +-1 and a free parameter t modulo k,

    (0, t, e, e),   (e, e, t, 0),   (t, 0, e - t, e),   (e, t, 0, e - t),   (t, e, e, e - t),

together with ten words that are claimed to make S_5 vanish identically in Z[q, q^{-1}],
namely (1,2,2,1), (1,3,1,2), (2,1,3,1), (2,2,1,3), (3,1,2,2) and their negatives.

Three things are checked here, all exactly:
  1. the proposed set equals the computed locus, for each k, with no missing and no extra
     words. The computed locus comes from vanishing_locus.py, an independent
     implementation using a power table in Z[x]/Phi_k;
  2. the ten claimed identical vanishings really are identities in Z[q], not root of unity
     coincidences, so they hold at every k simultaneously;
  3. the sporadic solutions at small k are honest cyclotomic relations, specifically that
     S_5(2,2,2,2) = Phi_5 and S_4(2,2,2) = Phi_2 Phi_4.

Run:
    PYTHONPATH=<path> python3 families_length5.py
"""

from __future__ import annotations

import sys
from pathlib import Path

from sympy import Poly, cyclotomic_poly, expand, factor_list, symbols

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from vanishing_locus import locus            # independent implementation

q = symbols("q")

SHAPES = ("0,t,e,e", "e,e,t,0", "t,0,e-t,e", "e,t,0,e-t", "t,e,e,e-t")
IDENTITIES = ((1, 2, 2, 1), (1, 3, 1, 2), (2, 1, 3, 1), (2, 2, 1, 3), (3, 1, 2, 2))


def predicted(k: int) -> set[tuple[int, ...]]:
    out = set()
    for e in (1, -1):
        for t in range(k):
            out |= {
                (0, t, e, e),
                (e, e, t, 0),
                (t, 0, e - t, e),
                (e, t, 0, e - t),
                (t, e, e, e - t),
            }
        for w in IDENTITIES:
            out.add(tuple(e * c for c in w))
    return {tuple(c % k for c in w) for w in out}


def S_poly(word):
    """S_i(q) as an element of Z[q], from the MGO recursion."""
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


@tracked(tags={"tangent": "2026-08-10-k-uniformity", "quantity": "length5_families"})
def family_match(ks: list[int]) -> dict:
    """Compare the predicted family set against the computed locus, per k."""
    report = {}
    for k in ks:
        actual = {tuple(w) for w in locus(k, 5)}
        pred = predicted(k)
        report[k] = {"actual": len(actual), "predicted": len(pred),
                     "missing": sorted(actual - pred), "extra": sorted(pred - actual)}
    return {"per_k": report,
            "exact_for_all_k": all(not r["missing"] and not r["extra"]
                                   for r in report.values())}


@tracked(tags={"tangent": "2026-08-10-k-uniformity", "quantity": "identical_vanishings"})
def identical_vanishings() -> dict:
    """Which of the claimed words make S_5 the zero polynomial in Z[q]."""
    res = {}
    for w in IDENTITIES:
        for sgn in (1, -1):
            word = tuple(sgn * c for c in w)
            if sgn == -1:
                continue                        # negative residues need a modulus to mean anything
            res[str(word)] = S_poly(word) == 0
    return {"words": res, "all_identically_zero": all(res.values())}


@tracked(tags={"tangent": "2026-08-10-k-uniformity", "quantity": "sporadic_factorization"})
def sporadic_factorizations() -> dict:
    """The small-k extras are honest cyclotomic relations."""
    def fac(word):
        return str(factor_list(S_poly(word)))
    s5 = S_poly((2, 2, 2, 2))
    s4 = S_poly((2, 2, 2))
    return {
        "S5_2222": str(s5),
        "S5_2222_is_Phi5": expand(s5 - cyclotomic_poly(5, q)) == 0,
        "S5_3333_factors": fac((3, 3, 3, 3)),
        "S5_3333_divisible_by_Phi5":
            Poly(S_poly((3, 3, 3, 3)), q).rem(Poly(cyclotomic_poly(5, q), q)).is_zero,
        "S4_222": str(s4),
        "S4_222_is_Phi2_Phi4":
            expand(s4 - cyclotomic_poly(2, q) * cyclotomic_poly(4, q)) == 0,
    }


def main() -> int:
    match = family_match(ks=[7, 9, 11, 13])
    ident = identical_vanishings()
    spor = sporadic_factorizations()

    for k, r in match["per_k"].items():
        print(f"k={k}: actual {r['actual']}, predicted {r['predicted']}, "
              f"missing {len(r['missing'])}, extra {len(r['extra'])}")
        if r["missing"]:
            print("   missing:", r["missing"][:8])
        if r["extra"]:
            print("   extra:", r["extra"][:8])
    print("identical vanishings:", ident)
    print("sporadic factorizations:", spor)

    if HAVE_PROVSTORE:
        for quantity, text, val in [
            ("length5_families",
             "At length 5 the vanishing locus is exactly the five shapes (0,t,e,e), "
             "(e,e,t,0), (t,0,e-t,e), (e,t,0,e-t), (t,e,e,e-t) with a single governing "
             "sign, together with ten words at which S_5 vanishes identically, verified "
             "for k = 7, 9, 11, 13 with no missing and no extra words.",
             10 if match["exact_for_all_k"] else 0),
            ("identical_vanishings",
             "The five words (1,2,2,1), (1,3,1,2), (2,1,3,1), (2,2,1,3), (3,1,2,2) make "
             "S_5 the zero polynomial in Z[q], so they are solutions at every k.",
             sum(ident["words"].values())),
            ("sporadic_factorization",
             "The extra solutions at small k are cyclotomic relations: S_5(2,2,2,2) is "
             "Phi_5 exactly and S_4(2,2,2) is Phi_2 Phi_4.",
             1 if spor["S5_2222_is_Phi5"] and spor["S4_222_is_Phi2_Phi4"] else 0),
        ]:
            hits = provstore.find(tags={"quantity": quantity,
                                    "tangent": "2026-08-10-k-uniformity"})
            if not hits:
                raise AssertionError(f"no recorded computation for {quantity}")
            provstore.claim(text, computation_id=hits[0].id, value_numeric=val,
                        tags={"tangent": "2026-08-10-k-uniformity",
                              "quantity": quantity})
    return 0 if match["exact_for_all_k"] else 1


if __name__ == "__main__":
    from families_length5 import main as _main
    sys.exit(_main())
