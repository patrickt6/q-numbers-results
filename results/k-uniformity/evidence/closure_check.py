#!/usr/bin/env python3
r"""Downward closure as a consequence of k-independent congruences.

a collaborator's argument, in his own terms: the conditions characterising S_i(omega_k) = 0 are
congruences modulo k with fixed integer constants, so if a word satisfies them modulo k it
satisfies them modulo l for every divisor l of k, and therefore Phi_k | S_i should force
Phi_l | S_i. The residues +-2 and +-3 appearing in the conditions do not obstruct this,
since reduction modulo l carries the constant 2 to 2 and 3 to 3.

That argument is only as good as the premise that the conditions really are k-independent
congruences. At length 5 the premise is now available: every family is an identity of
Laurent polynomials rather than a root of unity coincidence, so membership in a family is
preserved by reduction. This script checks the conclusion directly and unconditionally, by
reducing every solution word modulo every divisor and testing it again:

    for every k, for every l > 1 dividing k, for every word w in V_i(k),
    is (w mod l) in V_i(l)?

A single failure would refute downward closure at that length. The test does not assume the
classification, so it is independent evidence for it.

Run:
    PYTHONPATH=<path> python3 closure_check.py
"""

from __future__ import annotations

import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from vanishing_locus import locus

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


def divisors_above_one(k: int) -> list[int]:
    return [l for l in range(2, k) if k % l == 0]


@tracked(tags={"tangent": "2026-08-10-k-uniformity", "quantity": "downward_closure"})
def closure_scan(length: int, kmax: int) -> dict:
    """Reduce every solution modulo every proper divisor and retest."""
    loci = {k: {tuple(w) for w in locus(k, length)} for k in range(2, kmax + 1)}
    instances = violations = 0
    failures = []
    for k in range(2, kmax + 1):
        for l in divisors_above_one(k):
            for w in loci[k]:
                instances += 1
                if tuple(c % l for c in w) not in loci[l]:
                    violations += 1
                    if len(failures) < 20:
                        failures.append({"k": k, "l": l, "word": list(w)})
    return {"length": length, "kmax": kmax, "instances": instances,
            "violations": violations, "failures": failures}


def main() -> int:
    out = {}
    for length, kmax in ((3, 16), (4, 14), (5, 12), (6, 9)):
        r = closure_scan(length=length, kmax=kmax)
        out[length] = r
        print(f"length {length}: k up to {r['kmax']}, {r['instances']} instances, "
              f"{r['violations']} violations")
        if r["failures"]:
            print("   first failures:", r["failures"][:5])

    if HAVE_PROVSTORE:
        for length, r in out.items():
            hits = [c for c in provstore.find(tags={"quantity": "downward_closure",
                                                "tangent": "2026-08-10-k-uniformity"})
                    if isinstance(c.result, dict) and c.result.get("length") == length]
            if not hits:
                raise AssertionError(f"no downward closure record at length {length}")
            provstore.claim(
                f"At continued fraction length {length}, reducing every vanishing residue "
                f"word modulo every proper divisor l > 1 of k and retesting gives "
                f"{r['instances']} instances for k up to {r['kmax']} with "
                f"{r['violations']} violations.",
                computation_id=hits[0].id, value_numeric=r["violations"],
                tags={"tangent": "2026-08-10-k-uniformity", "length": length,
                      "quantity": "downward_closure"})
    return 0 if all(r["violations"] == 0 for r in out.values()) else 1


if __name__ == "__main__":
    from closure_check import main as _main
    sys.exit(_main())
