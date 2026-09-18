#!/usr/bin/env python3
r"""
Impossibility search: is [x+y]_q a bihomographic function of [x]_q and [y]_q?

This module decides, exactly, whether the q-deformed real-sum [x+y]_q can be
written as a single bilinear-fractional (bihomographic) function

    z(X, Y) = (a XY + b X + c Y + d) / (e XY + f X + g Y + h),   X=[x]_q, Y=[y]_q,

with coefficients a..h in the field Q(q). That is exactly the value class a
classical Gosper bihomographic transducer can emit after fully ingesting the
q-continued-fraction digits of x and y (the engine in `q_gosper.py` carries
precisely this 2x4 state). The verdict is a clean NEGATIVE, with the addition
deficit D = [x+y]_q - ([x]_q + [y]_q) as the obstruction object.

Nothing here modifies `q_gosper.py`; it only imports the engine entry points
`q_real_rational` and `q_gosper`. The whole battery is deterministic (fixed
pairs, fixed q-values, no RNG), so `run_impossibility_checks()` re-runs
bit-identically and is the provstore entry point (see `register_impossibility.py`).

Three independent arms, all driven by the engine:

  ARM 1  EXACT bihomographic kernel over Q(q) (degree-unbounded; the proof).
         Stack one row per test pair of the 8-wide relation
             [ XY, X, Y, 1, -T XY, -T X, -T Y, -T ],   T = [x+y]_q,
         a kernel vector of which is a bihomographic law for T. The rank over
         Q(q) is computed by exact rational specialization at several q0 (the
         specialized rank is a lower bound on the Q(q)-rank, and there are only
         8 columns, so rank 8 at any q0 proves the kernel is trivial -> NO law).
         Control: feeding the engine's own [x]_q+[y]_q gives rank 7 (a genuine
         1-dimensional kernel), so the test detects a real bihomographic form.

  ARM 2  EXPLICIT finite bounded-degree scan (records the literal search bound).
         For each q-degree band W = 0,1,...,W_MAX, search every bihomographic
         form whose 8 coefficients are Laurent polynomials with q-exponents in
         [-W, +W] and rational coefficients of any magnitude. This is a finite
         homogeneous linear system (8*(2W+1) unknowns) solved exactly by
         specialization at distinct integer q-values reduced modulo a large
         prime; a trivial kernel certifies no such form exists in that band.
         The result is subsumed by ARM 1 (which covers all W at once) but pins
         down the concrete (state count, degree range) the question asks for.

  ARM 3  REVERSAL obstruction (names the mechanism behind D). For integer sums
         N = x+y the deficit has the closed form D = q^{N-1}[x]_{1/q} - [x]_q,
         exposing the q-reversal [x]_q -> [x]_{1/q} (the q |-> 1/q involution).
         We certify that [x]_{1/q} is not even a single Mobius function of [x]_q
         (rank 4), whereas the genuine MGO shift [x+1]_q = q[x]_q + 1 IS Mobius
         and is recovered exactly as (A,B,C,D) = (q,1,0,1) (rank 3). So the
         deficit's dependence on the q-involution is the precise reason no
         fixed-coefficient bilinear-fractional law in [x]_q,[y]_q yields [x+y]_q.
"""
from __future__ import annotations

from fractions import Fraction

import sympy as sp

from q_gosper import q, q_gosper, q_real_rational

# ---------------------------------------------------------------------------
# engine wrappers (exact rational functions of q; no engine edits)
# ---------------------------------------------------------------------------
def Xq(x: Fraction) -> sp.Expr:           # [x]_q
    return sp.cancel(q_real_rational(Fraction(x)))


def Xq_inv(x: Fraction) -> sp.Expr:       # [x]_{1/q}  (the q-reversal)
    return sp.cancel(q_real_rational(Fraction(x)).subs(q, 1 / q))


def Tq(x: Fraction, y: Fraction) -> sp.Expr:   # [x+y]_q  (single q-real of the sum)
    return sp.cancel(q_real_rational(Fraction(x) + Fraction(y)))


def add_value(x: Fraction, y: Fraction) -> sp.Expr:   # engine value = [x]_q + [y]_q
    return sp.cancel(q_gosper(Fraction(x), Fraction(y), "add"))


# ---------------------------------------------------------------------------
# fixed, deterministic test data
# ---------------------------------------------------------------------------
# Generic pairs, deliberately mostly NON-integer sums (the hard case): the
# bihomographic question is non-trivial precisely when x+y is not an integer.
KERNEL_PAIRS = [
    (Fraction(3, 2), Fraction(7, 3)),   # 23/6
    (Fraction(5, 3), Fraction(7, 4)),   # 41/12
    (Fraction(7, 4), Fraction(9, 5)),   # 71/20
    (Fraction(9, 5), Fraction(11, 6)),  # 109/30
    (Fraction(11, 6), Fraction(13, 7)), # 155/42
    (Fraction(4, 3), Fraction(8, 5)),   # 44/15
    (Fraction(5, 2), Fraction(8, 3)),   # 31/6
    (Fraction(7, 5), Fraction(12, 7)),  # 109/35
    (Fraction(13, 8), Fraction(10, 3)), # 119/24
    (Fraction(9, 4), Fraction(11, 5)),  # 89/20
]

# q-values for ARM 1 exact specialization (small, distinct, off the poles).
Q0_EXACT = [sp.Rational(1, 7), sp.Rational(1, 5), sp.Rational(2, 9)]

# ARM 2 scan: degree bands and the prime + integer q-samples for the mod-p solve.
W_MAX = 8
BOUNDED_PAIRS = KERNEL_PAIRS[:5]
BOUNDED_PRIMES = (2_000_003, 2_000_029)
BOUNDED_QSAMPLES = list(range(2, 52))        # 50 distinct integer q-values

# ARM 3: single-variable arguments for the reversal / shift Mobius tests.
REVERSAL_XS = [Fraction(3, 2), Fraction(5, 3), Fraction(7, 4), Fraction(9, 5),
               Fraction(4, 3), Fraction(7, 5), Fraction(11, 6), Fraction(13, 8),
               Fraction(8, 5), Fraction(5, 2)]

# ARM "negative cells": integer-sum pairs whose deficit the engine reproduces,
# matching both the closed form and the reversal identity.
INTEGER_SUM_CELLS = [
    (Fraction(3, 2), Fraction(5, 2)), (Fraction(4, 3), Fraction(5, 3)),
    (Fraction(5, 4), Fraction(7, 4)), (Fraction(7, 3), Fraction(8, 3)),
    (Fraction(9, 5), Fraction(11, 5)), (Fraction(2, 1), Fraction(3, 1)),
    (Fraction(7, 4), Fraction(9, 4)),
]


# ---------------------------------------------------------------------------
# ARM 1 -- exact bihomographic kernel over Q(q)
# ---------------------------------------------------------------------------
def _relation_row(Xv, Yv, Tv):
    """One row of the 8-wide bihomographic relation P - T*Q = 0."""
    return [sp.cancel(Xv * Yv), Xv, Yv, sp.Integer(1),
            sp.cancel(-Tv * Xv * Yv), sp.cancel(-Tv * Xv),
            sp.cancel(-Tv * Yv), -Tv]


def kernel_rank_at(target, q0, pairs=KERNEL_PAIRS):
    """Rank of the relation matrix specialized at q=q0 (exact rational)."""
    rows = []
    for x, y in pairs:
        Xv = sp.nsimplify(Xq(x).subs(q, q0))
        Yv = sp.nsimplify(Xq(y).subs(q, q0))
        if target == "sum":
            Tv = sp.nsimplify(Tq(x, y).subs(q, q0))
        elif target == "engine_add":
            Tv = sp.nsimplify(add_value(x, y).subs(q, q0))
        else:
            raise ValueError(target)
        rows.append(_relation_row(Xv, Yv, Tv))
    return sp.Matrix(rows).rank()


def arm1_exact_kernel():
    """[x+y]_q gives rank 8 (no law); engine [x]_q+[y]_q gives rank 7 (control)."""
    sum_ranks = {str(q0): int(kernel_rank_at("sum", q0)) for q0 in Q0_EXACT}
    control_rank = int(kernel_rank_at("engine_add", Q0_EXACT[0]))
    return {
        "columns": 8,
        "n_pairs": len(KERNEL_PAIRS),
        "q0_values": [str(q0) for q0 in Q0_EXACT],
        "sum_ranks": sum_ranks,                       # expect all 8
        "sum_kernel_trivial": all(r == 8 for r in sum_ranks.values()),
        "control_add_rank": control_rank,             # expect 7
        "control_detects_bihomographic": control_rank == 7,
    }


# ---------------------------------------------------------------------------
# ARM 2 -- explicit finite bounded-degree scan (mod-p exact linear algebra)
# ---------------------------------------------------------------------------
def _rank_mod_p(rows, p):
    """Exact rank of an integer matrix over GF(p) by Gaussian elimination."""
    M = [list(r) for r in rows]
    nrows = len(M)
    ncols = len(M[0]) if M else 0
    rank = 0
    for col in range(ncols):
        piv = next((r for r in range(rank, nrows) if M[r][col] % p), None)
        if piv is None:
            continue
        M[rank], M[piv] = M[piv], M[rank]
        inv = pow(M[rank][col] % p, p - 2, p)
        M[rank] = [(v * inv) % p for v in M[rank]]
        for r in range(nrows):
            if r != rank and M[r][col] % p:
                f = M[r][col] % p
                M[r] = [(M[r][c] - f * M[rank][c]) % p for c in range(ncols)]
        rank += 1
        if rank == nrows:
            break
    return rank


def _rat_mod_p(value: sp.Rational, p: int):
    """A sympy Rational reduced mod p (None if the denominator is 0 mod p)."""
    num, den = sp.fraction(sp.nsimplify(value))
    num, den = int(num), int(den)
    if den % p == 0:
        return None
    return (num % p) * pow(den % p, p - 2, p) % p


def bounded_degree_scan(w_max=W_MAX, primes=BOUNDED_PRIMES):
    """For each band W, certify NO bihomographic form of q-degree <= W exists.

    Unknowns: coefficient of q^e (e in -W..W) in each of the 8 slots
    {XY, X, Y, 1, -T XY, -T X, -T Y, -T}. Each (pair, integer q-sample) gives one
    linear equation; rank == #unknowns over GF(p) (for every prime tried)
    certifies the only solution is 0, i.e. no degree-<=W form. Sound for the
    negative: any genuine form would satisfy every sampled equation and survive.
    """
    # Pre-evaluate the 8 slot values at every (pair, q-sample), as exact rationals.
    slot_vals = {}  # (pi, qs) -> [8 rationals]
    for pi, (x, y) in enumerate(BOUNDED_PAIRS):
        Xe, Ye, Te = Xq(x), Xq(y), Tq(x, y)
        for qs in BOUNDED_QSAMPLES:
            Xv = sp.nsimplify(Xe.subs(q, qs))
            Yv = sp.nsimplify(Ye.subs(q, qs))
            Tv = sp.nsimplify(Te.subs(q, qs))
            slot_vals[(pi, qs)] = [Xv * Yv, Xv, Yv, sp.Integer(1),
                                   -Tv * Xv * Yv, -Tv * Xv, -Tv * Yv, -Tv]

    per_band = []
    all_trivial = True
    for W in range(0, w_max + 1):
        exps = list(range(-W, W + 1))
        n_unknowns = 8 * len(exps)
        band_trivial = True
        band_ranks = {}
        for p in primes:
            rows = []
            for pi, (x, y) in enumerate(BOUNDED_PAIRS):
                for qs in BOUNDED_QSAMPLES:
                    vals = slot_vals[(pi, qs)]
                    row = []
                    ok = True
                    # q^e factors mod p
                    qe = {}
                    for e in exps:
                        if e >= 0:
                            qe[e] = pow(qs, e, p)
                        else:
                            qe[e] = pow(pow(qs, -e, p), p - 2, p)
                    for s in range(8):
                        mv = _rat_mod_p(vals[s], p)
                        if mv is None:
                            ok = False
                            break
                        for e in exps:
                            row.append((mv * qe[e]) % p)
                    if ok:
                        rows.append(row)
            r = _rank_mod_p(rows, p)
            band_ranks[p] = r
            if r != n_unknowns:
                band_trivial = False
        per_band.append({"W": W, "n_unknowns": n_unknowns,
                         "ranks": band_ranks, "trivial_kernel": band_trivial})
        all_trivial = all_trivial and band_trivial

    return {
        "state": "one 2x4 bihomographic state (8 coefficient cells)",
        "degree_range_scanned": f"q-exponents [-{w_max}, +{w_max}]",
        "w_max": w_max,
        "n_pairs": len(BOUNDED_PAIRS),
        "n_q_samples": len(BOUNDED_QSAMPLES),
        "primes": list(primes),
        "per_band": per_band,
        "all_bands_negative": all_trivial,
    }


# ---------------------------------------------------------------------------
# ARM 3 -- the reversal obstruction (mechanism behind D)
# ---------------------------------------------------------------------------
def _mobius_rank(value_fn, target_fn, q0):
    """Rank of rows [V, 1, -W*V, -W] (a kernel vector => W is Mobius in V)."""
    rows = []
    for x in REVERSAL_XS:
        V = sp.nsimplify(value_fn(x).subs(q, q0))
        W = sp.nsimplify(target_fn(x).subs(q, q0))
        rows.append([V, sp.Integer(1), -W * V, -W])
    M = sp.Matrix(rows)
    return M, int(M.rank())


def arm3_reversal_obstruction():
    """[x]_{1/q} is not Mobius in [x]_q (rank 4); shift [x+1]_q is (rank 3)."""
    rev_ranks = {}
    for q0 in (sp.Rational(1, 7), sp.Rational(2, 9)):
        _, r = _mobius_rank(Xq, Xq_inv, q0)
        rev_ranks[str(q0)] = r

    # control: [x+1]_q = q[x]_q + 1 is Mobius, recover (A,B,C,D)=(q,1,0,1).
    def shift(x):
        return sp.cancel(q_real_rational(Fraction(x) + 1))

    Mc, rc = _mobius_rank(Xq, shift, sp.Rational(1, 7))
    ker = Mc.nullspace()
    recovered = None
    if rc == 3 and len(ker) == 1:
        v = ker[0]
        v = v / v[1]            # normalise B = 1
        recovered = [sp.nsimplify(e) for e in v]   # expect [1/7, 1, 0, 1] at q=1/7

    return {
        "reversal_ranks": rev_ranks,                      # expect all 4
        "reversal_not_mobius": all(r == 4 for r in rev_ranks.values()),
        "shift_control_rank": rc,                         # expect 3
        "shift_is_mobius": rc == 3,
        "shift_recovered_vector_at_q=1/7": [str(e) for e in recovered] if recovered else None,
    }


# ---------------------------------------------------------------------------
# Engine negative cells: the deficit D the engine reproduces, pair by pair
# ---------------------------------------------------------------------------
def engine_negative_cells():
    """Every integer-sum cell: engine deficit nonzero, == closed form == reversal."""
    cells = []
    all_ok = True
    for x, y in INTEGER_SUM_CELLS:
        N = int(x + y)
        D_engine = sp.cancel(Tq(x, y) - add_value(x, y))       # engine deficit
        D_closed = sp.cancel(q ** (N - 1) * Xq_inv(x) - Xq(x))  # closed form
        nonzero = D_engine != 0
        closed_ok = sp.cancel(D_engine - D_closed) == 0
        # reversal identity: [x+y]_q == [y]_q + q^{N-1}[x]_{1/q}
        rev_ok = sp.cancel(Tq(x, y) - (Xq(y) + q ** (N - 1) * Xq_inv(x))) == 0
        ok = bool(nonzero and closed_ok and rev_ok)
        all_ok = all_ok and ok
        cells.append({"x": str(x), "y": str(y), "N": N,
                      "deficit": str(sp.cancel(D_engine)),
                      "nonzero": bool(nonzero), "matches_closed_form": bool(closed_ok),
                      "matches_reversal_identity": bool(rev_ok)})
    return {"cells": cells, "n_cells": len(cells), "all_cells_reproduced": all_ok}


# ---------------------------------------------------------------------------
# deterministic top-level checker (provstore entry point)
# ---------------------------------------------------------------------------
def run_impossibility_checks():
    """Full deterministic battery -> JSON-able summary. No RNG; reproducible."""
    arm1 = arm1_exact_kernel()
    arm2 = bounded_degree_scan()
    arm3 = arm3_reversal_obstruction()
    neg = engine_negative_cells()

    verdict_negative = (
        arm1["sum_kernel_trivial"]
        and arm1["control_detects_bihomographic"]
        and arm2["all_bands_negative"]
        and arm3["reversal_not_mobius"]
        and arm3["shift_is_mobius"]
        and neg["all_cells_reproduced"]
    )
    return {
        "question": "Is [x+y]_q a bihomographic function of [x]_q and [y]_q?",
        "verdict": "NO (clean negative)" if verdict_negative else "INCONCLUSIVE",
        "verdict_negative": bool(verdict_negative),
        "arm1_exact_kernel": arm1,
        "arm2_bounded_scan": arm2,
        "arm3_reversal_obstruction": arm3,
        "engine_negative_cells": neg,
    }


if __name__ == "__main__":
    import json

    summary = run_impossibility_checks()
    print(json.dumps(summary, indent=2))
    print("\nVERDICT:", summary["verdict"])
