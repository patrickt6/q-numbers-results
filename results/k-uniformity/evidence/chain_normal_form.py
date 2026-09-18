#!/usr/bin/env python3
r"""Independent check of the chain normal form for the q-denominator.

Claim under test (a collaborator's chain reformulation, carried to general length). Define
T_0 = 0, T_1 = 1 and

    T_j = [c_j]_{q^{(-1)^j}} T_{j-1} - w_{j-1} T_{j-2},
    w_{j-1} = 1                  if j-1 is even,
    w_{j-1} = q^{c_{j-1} - c_j}  if j-1 is odd,

so even-indexed quotients are evaluated at q^{-1} and odd-indexed ones at q. Then

    S_j = q^{E_j} T_j,     E_j = sum of (c_l - 1) over even l with 2 <= l <= j.

Since q^{E_j} and every weight are units at a root of unity, S_i(omega) = 0 iff
T_i(omega) = 0. At length 3 this is the identity [c_3]_q [c_2]_{1/q} = 1.

Also tested: the reversal symmetry q^N S_i(1/q; c_2,...,c_i) = S_i(q; c_i,...,c_2) with
N = deg S_i, which is what the conjugate-and-subtract step of the length-4 proof uses.

This file is deliberately a separate implementation from vanishing_locus.py. It uses
sympy rational function arithmetic rather than a power table in Z[x]/Phi_k, so agreement
between the two is evidence about the mathematics and not about one piece of code.

Run:
    PYTHONPATH=<path> python3 chain_normal_form.py
"""

from __future__ import annotations

import sys
from itertools import product
from pathlib import Path

from sympy import Poly, cancel, cyclotomic_poly, expand, simplify, symbols

HERE = Path(__file__).resolve().parent
q = symbols("q")
x = symbols("x")


def bracket(a, var):
    """[a]_var for a >= 0."""
    return sum(var**j for j in range(a))


def S_direct(word):
    """S_i(q) from the MGO recursion, for word = (c_2, ..., c_i)."""
    prev, cur, cprev = 0, 1, None
    for c in word:
        sub = 0 if cprev is None else q ** (cprev - 1) * prev
        prev, cur, cprev = cur, expand(bracket(c, q) * cur - sub), c
    return expand(cur)


def T_chain(word):
    """T_i(q) from the chain recursion, and the exponent E_i."""
    prev, cur = 0, 1
    E = 0
    for idx, c in enumerate(word):
        j = idx + 2                                  # this quotient is c_j
        var = 1 / q if j % 2 == 0 else q
        if idx == 0:
            w = 0                                    # T_0 = 0, weight irrelevant
        elif (j - 1) % 2 == 0:
            w = 1
        else:
            w = q ** (word[idx - 1] - c)
        prev, cur = cur, cancel(bracket(c, var) * cur - w * prev)
        if j % 2 == 0:
            E += c - 1
    return cancel(cur), E


def check_identity(words) -> dict:
    """S_j = q^{E_j} T_j, symbolically, at every prefix of every word."""
    bad = []
    for word in words:
        for cut in range(1, len(word) + 1):
            pre = word[:cut]
            T, E = T_chain(pre)
            if simplify(S_direct(pre) - q**E * T) != 0:
                bad.append(pre)
    return {"words_tested": len(words), "prefixes_tested":
            sum(len(w) for w in words), "failures": bad}


def check_reversal(words) -> dict:
    """q^N S_i(1/q; word) = S_i(q; reversed word), N = deg S_i."""
    bad = []
    for word in words:
        S = S_direct(word)
        N = Poly(S, q).degree()
        if simplify(q**N * S.subs(q, 1 / q) - S_direct(tuple(reversed(word)))) != 0:
            bad.append(word)
    return {"words_tested": len(words), "failures": bad}


def check_at_roots(kmax: int, lengths, entries) -> dict:
    """Vanishing of S_i and of T_i agree at every primitive kth root, k = 2..kmax."""
    total = vanishing = 0
    bad = []
    for k in range(2, kmax + 1):
        Phi = Poly(cyclotomic_poly(k, x), x)
        for length in lengths:
            for word in product(entries, repeat=length - 1):
                S = Poly(S_direct(word).subs(q, x), x).rem(Phi)
                T, _ = T_chain(word)
                num = Poly(cancel(T * q ** _clear(word)).subs(q, x), x).rem(Phi)
                total += 1
                sz, tz = S.is_zero, num.is_zero
                if sz != tz:
                    bad.append((k, word))
                vanishing += int(sz)
    return {"cases": total, "vanishing": vanishing, "kmax": kmax, "failures": bad}


def _clear(word) -> int:
    """A power of q large enough to clear the negative powers in T."""
    return sum(word)


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


check_identity = tracked(tags={"tangent": "2026-08-10-k-uniformity",
                               "quantity": "chain_identity"})(check_identity)
check_reversal = tracked(tags={"tangent": "2026-08-10-k-uniformity",
                               "quantity": "reversal_symmetry"})(check_reversal)
check_at_roots = tracked(tags={"tangent": "2026-08-10-k-uniformity",
                               "quantity": "chain_at_roots"})(check_at_roots)


WORDS = [(2, 3), (4, 2, 5), (3, 3, 3), (2, 5, 3, 4), (6, 2, 2, 6), (5, 4, 3, 2, 6),
         (2, 2, 2, 2, 2), (7, 3, 5, 2, 4), (3, 6, 2, 5, 3, 4)]


def main() -> int:
    ident = check_identity(words=WORDS)
    rev = check_reversal(words=WORDS)
    roots = check_at_roots(kmax=7, lengths=(3, 4, 5), entries=tuple(range(1, 6)))
    print("chain identity S_j = q^{E_j} T_j:", ident)
    print("reversal symmetry:", rev)
    print("agreement at roots of unity:", {k: v for k, v in roots.items() if k != "failures"},
          "failures:", roots["failures"][:5])
    ok = not (ident["failures"] or rev["failures"] or roots["failures"])
    if HAVE_PROVSTORE and ok:
        for quantity, text, val in [
            ("chain_identity",
             "The chain normal form S_j = q^{E_j} T_j, with even-indexed quotients "
             "evaluated at q inverse and odd-indexed at q, holds identically on every "
             f"prefix of {len(WORDS)} test words up to length 7.", ident["prefixes_tested"]),
            ("reversal_symmetry",
             "The q-denominator satisfies q^N S(1/q; word) = S(q; reversed word) with "
             f"N its degree, on {len(WORDS)} test words.", rev["words_tested"]),
            ("chain_at_roots",
             "Vanishing of the chain form and of the q-denominator agree at every "
             f"primitive kth root of unity for k up to 7, over {roots['cases']} words.",
             roots["cases"]),
        ]:
            hits = provstore.find(tags={"quantity": quantity,
                                    "tangent": "2026-08-10-k-uniformity"})
            if not hits:
                raise AssertionError(f"no recorded computation for {quantity}")
            provstore.claim(text, computation_id=hits[0].id, value_numeric=val,
                        tags={"tangent": "2026-08-10-k-uniformity",
                              "quantity": quantity})
    return 0 if ok else 1


if __name__ == "__main__":
    sys.path.insert(0, str(HERE))
    from chain_normal_form import main as _main
    sys.exit(_main())
