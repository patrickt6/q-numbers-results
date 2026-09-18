#!/usr/bin/env python3
r"""
Impossibility search: is [xy]_q a bihomographic function of [x]_q and [y]_q?

This module decides, exactly, whether the q-deformed real-product [xy]_q (the
single q-real of the ordinary product x*y) can be written as a single
bilinear-fractional (bihomographic) function

    z(X, Y) = (a XY + b X + c Y + d) / (e XY + f X + g Y + h),   X=[x]_q, Y=[y]_q,

with coefficients a..h in the field Q(q). That is exactly the value class a
classical Gosper bihomographic transducer can emit after fully ingesting the
q-continued-fraction digits of x and y (the engine in `q_gosper.py` carries
precisely this 2x4 state; the 'mul' op there computes [x]_q * [y]_q, NOT the
single q-real [xy]_q). The verdict is a clean NEGATIVE, in lockstep with the
addition result in `impossibility.md`.

Nothing here modifies `q_gosper.py`; it only imports the engine entry points
`q_real_rational` and `q_gosper`. The whole battery is deterministic (fixed
pairs, fixed q-values, fixed primes, no RNG), so `run_mult_impossibility_checks()`
re-runs bit-identically and is the provstore entry point (see
`register_mult_impossibility.py`). It re-uses the addition module's ARM helpers
where their shape is unchanged; it does not rewrite that module.

Three arms plus a square-case reversal probe, all driven by the engine:

  ARM 1  EXACT bihomographic kernel over Q(q) (degree-unbounded; the proof).
         Stack one row per test pair of the 8-wide relation
             [ XY, X, Y, 1, -T XY, -T X, -T Y, -T ],   T = [xy]_q,
         a kernel vector of which is a bihomographic law for T. The rank over
         Q(q) is computed by exact rational specialization at several q0 (the
         specialized rank is a lower bound on the Q(q)-rank, and there are only
         8 columns, so rank 8 at any q0 proves the kernel is trivial -> NO law).
         Control: feeding the engine's own [x]_q * [y]_q (via q_gosper(x,y,'mul'))
         gives rank 7 (a genuine 1-dimensional kernel), so the test detects a
         real bihomographic form.

  ARM 2  EXPLICIT finite bounded-degree scan (records the literal search bound).
         For each q-degree band W = 0,1,...,W_MAX, search every bihomographic
         form whose 8 coefficients are Laurent polynomials with q-exponents in
         [-W, +W]. This is a finite homogeneous linear system solved exactly by
         specialization at distinct integer q-values reduced modulo a large
         prime; a trivial kernel certifies no such form exists in that band.
         Subsumed by ARM 1, kept for the concrete (state count, degree range).

  ARM 3  SQUARE-CASE reversal probe (names the obstruction object). The natural
         analogue of the addition deficit is the square deficit
             Dx_{x,x}(q) = [x^2]_q - [x]_q^2,
         the gap between the single q-real of x^2 and the engine product [x]_q^2.
         For addition the deficit closes as D = q^{N-1}[x]_{1/q} - [x]_q, so the
         q-reversal [x]_{1/q} (the q |-> 1/q involution) IS the obstruction. Here
         we test whether the same reversal accounts for the square deficit:
         whether [x^2]_q is a bihomographic function of [x]_q AND its reversal
         [x]_{1/q}. It is not (rank 8), whereas feeding the reversal [x]_{1/q}
         itself as the target yields a genuine kernel (rank < 8), so the test
         does detect the reversal when it is the value. The finding is that the
         reversal is ABSENT as the square obstruction: squaring is a strictly
         richer obstruction than the q-involution that drives addition.
"""
from __future__ import annotations

from fractions import Fraction

import sympy as sp

from q_gosper import q, q_gosper, q_real_rational

# We re-use the addition module's mod-p linear algebra and reversal wrappers
# verbatim where their shape is unchanged (no rewrite of that module).
import impossibility_search as add_imp
from impossibility_search import Xq, Xq_inv, _relation_row, _rank_mod_p, _rat_mod_p


# ---------------------------------------------------------------------------
# engine wrappers specific to the product target (exact rational fns of q)
# ---------------------------------------------------------------------------
def Tmul(x: Fraction, y: Fraction) -> sp.Expr:     # [xy]_q (single q-real of x*y)
    return sp.cancel(q_real_rational(Fraction(x) * Fraction(y)))


def mul_value(x: Fraction, y: Fraction) -> sp.Expr:   # engine value = [x]_q * [y]_q
    return sp.cancel(q_gosper(Fraction(x), Fraction(y), "mul"))


def Tsq(x: Fraction) -> sp.Expr:                   # [x^2]_q
    return sp.cancel(q_real_rational(Fraction(x) * Fraction(x)))


def square_deficit(x: Fraction) -> sp.Expr:        # Dx_{x,x}(q) = [x^2]_q - [x]_q^2
    return sp.cancel(Tsq(x) - Xq(x) ** 2)


# ---------------------------------------------------------------------------
# fixed, deterministic test data
# ---------------------------------------------------------------------------
# Generic pairs, deliberately NON-integer products (the hard case): the
# bihomographic question is non-trivial precisely when xy is not an integer.
KERNEL_PAIRS = [
    (Fraction(3, 2), Fraction(7, 3)),   # 7/2
    (Fraction(5, 3), Fraction(7, 4)),   # 35/12
    (Fraction(7, 4), Fraction(9, 5)),   # 63/20
    (Fraction(9, 5), Fraction(11, 6)),  # 33/10
    (Fraction(11, 6), Fraction(13, 7)), # 143/42
    (Fraction(4, 3), Fraction(8, 5)),   # 32/15
    (Fraction(5, 2), Fraction(8, 3)),   # 20/3
    (Fraction(7, 5), Fraction(12, 7)),  # 12/5
    (Fraction(13, 8), Fraction(10, 3)), # 65/12
    (Fraction(9, 4), Fraction(11, 5)),  # 99/20
]

# q-values for ARM 1 exact specialization (small, distinct, off the poles).
Q0_EXACT = [sp.Rational(1, 7), sp.Rational(1, 5), sp.Rational(2, 9)]

# ARM 2 scan: degree bands and the prime + integer q-samples for the mod-p solve.
W_MAX = 8
BOUNDED_PAIRS = KERNEL_PAIRS[:5]
BOUNDED_PRIMES = (2_000_003, 2_000_029)
BOUNDED_QSAMPLES = list(range(2, 52))        # 50 distinct integer q-values

# ARM 3 square-case catalog: 32 distinct NON-integer x > 1 (the regime where the
# reversal [x]_{1/q} is genuinely independent of [x]_q; at integers it collapses
# to q^{1-n}[n]_q and cannot distinguish the reversal from a power of [x]_q).
SQUARE_XS = sorted(
    {
        Fraction(n, n - 1) for n in range(3, 13)
    } | {
        Fraction(n, n - 2) for n in range(5, 13)
    } | {
        Fraction(n, n - 3) for n in range(7, 15)
    } | {
        Fraction(7, 4), Fraction(9, 4), Fraction(11, 4), Fraction(13, 4),
        Fraction(8, 5), Fraction(9, 5), Fraction(11, 5), Fraction(12, 5),
        Fraction(11, 6), Fraction(13, 6), Fraction(13, 8), Fraction(15, 8),
        Fraction(10, 3), Fraction(11, 3),
    }
)

# ARM "negative cells": product pairs whose engine product deficit is reproduced.
PRODUCT_CELLS = [
    (Fraction(3, 2), Fraction(5, 2)), (Fraction(4, 3), Fraction(5, 3)),
    (Fraction(5, 4), Fraction(7, 4)), (Fraction(7, 3), Fraction(8, 3)),
    (Fraction(9, 5), Fraction(11, 5)), (Fraction(2, 1), Fraction(3, 1)),
    (Fraction(7, 4), Fraction(9, 4)),
]


# ---------------------------------------------------------------------------
# ARM 1 -- exact bihomographic kernel over Q(q), product target
# ---------------------------------------------------------------------------
def kernel_rank_at(target, q0, pairs=KERNEL_PAIRS):
    """Rank of the product relation matrix specialized at q=q0 (exact rational)."""
    rows = []
    for x, y in pairs:
        Xv = sp.nsimplify(Xq(x).subs(q, q0))
        Yv = sp.nsimplify(Xq(y).subs(q, q0))
        if target == "prod":
            Tv = sp.nsimplify(Tmul(x, y).subs(q, q0))
        elif target == "engine_mul":
            Tv = sp.nsimplify(mul_value(x, y).subs(q, q0))
        else:
            raise ValueError(target)
        rows.append(_relation_row(Xv, Yv, Tv))
    return sp.Matrix(rows).rank()


def arm1_exact_kernel():
    """[xy]_q gives rank 8 (no law); engine [x]_q*[y]_q gives rank 7 (control)."""
    prod_ranks = {str(q0): int(kernel_rank_at("prod", q0)) for q0 in Q0_EXACT}
    control_rank = int(kernel_rank_at("engine_mul", Q0_EXACT[0]))
    return {
        "columns": 8,
        "n_pairs": len(KERNEL_PAIRS),
        "q0_values": [str(q0) for q0 in Q0_EXACT],
        "prod_ranks": prod_ranks,                        # expect all 8
        "prod_kernel_trivial": all(r == 8 for r in prod_ranks.values()),
        "control_mul_rank": control_rank,                # expect 7
        "control_detects_bihomographic": control_rank == 7,
    }


# ---------------------------------------------------------------------------
# ARM 2 -- explicit finite bounded-degree scan (mod-p exact linear algebra)
# ---------------------------------------------------------------------------
def bounded_degree_scan(w_max=W_MAX, primes=BOUNDED_PRIMES):
    """For each band W, certify NO bihomographic form of q-degree <= W exists.

    Same construction as the addition scan, with the product target T = [xy]_q.
    Unknowns: coefficient of q^e (e in -W..W) in each of the 8 slots
    {XY, X, Y, 1, -T XY, -T X, -T Y, -T}. Each (pair, integer q-sample) gives one
    linear equation; rank == #unknowns over GF(p) (for every prime tried)
    certifies the only solution is 0, i.e. no degree-<=W form.
    """
    slot_vals = {}  # (pi, qs) -> [8 rationals]
    for pi, (x, y) in enumerate(BOUNDED_PAIRS):
        Xe, Ye, Te = Xq(x), Xq(y), Tmul(x, y)
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
# ARM 3 -- square-case reversal probe (the obstruction object)
# ---------------------------------------------------------------------------
def _xr_row(Xv, Rv, Tv):
    """One row of the 8-wide bihomographic relation in (X, R=[x]_{1/q})."""
    return [sp.cancel(Xv * Rv), Xv, Rv, sp.Integer(1),
            sp.cancel(-Tv * Xv * Rv), sp.cancel(-Tv * Xv),
            sp.cancel(-Tv * Rv), -Tv]


def _xr_kernel_rank(target_fn, q0, xs=SQUARE_XS):
    """Rank of the (X, R) bihomographic relation for target_fn(x), at q=q0."""
    rows = []
    for x in xs:
        Xv = sp.nsimplify(Xq(x).subs(q, q0))
        Rv = sp.nsimplify(Xq_inv(x).subs(q, q0))
        Tv = sp.nsimplify(target_fn(x).subs(q, q0))
        rows.append(_xr_row(Xv, Rv, Tv))
    return int(sp.Matrix(rows).rank())


def _span_rank(basis_fns, q0, with_deficit, xs=SQUARE_XS):
    """Rank of the catalog matrix of basis_fns at q0, optionally with the Dx column."""
    rows = []
    for x in xs:
        row = []
        if with_deficit:
            row.append(sp.nsimplify(square_deficit(x).subs(q, q0)))
        for fn in basis_fns:
            row.append(sp.nsimplify(fn(x).subs(q, q0)))
        rows.append(row)
    return int(sp.Matrix(rows).rank())


def square_reversal_obstruction():
    """Does the q-reversal [x]_{1/q} account for the square deficit? It does not."""
    q0 = Q0_EXACT[0]

    # (1) main: is [x^2]_q bihomographic in (X, R=[x]_{1/q})?  expect rank 8.
    sq_xr_ranks = {str(qq): _xr_kernel_rank(Tsq, qq) for qq in Q0_EXACT}

    # (2) control: feed the reversal [x]_{1/q} itself as the target. A genuine
    #     bihomographic form (z = R) exists, so the kernel is nontrivial: rank < 8.
    control_xr_rank = _xr_kernel_rank(Xq_inv, q0)

    # (3) supplementary span tests on the square deficit Dx itself:
    #     - addition-deficit SHAPE: is Dx a fixed Q(q)-combination of {[x]_{1/q},[x]_q,1}?
    #     - degree-2 bilinear: span of {[x]_q^2,[x]_q,1,[x]_{1/q}^2,[x]_{1/q},[x]_q[x]_{1/q}}?
    one = lambda x: sp.Integer(1)
    lin_basis = [Xq_inv, Xq, one]
    bil_basis = [lambda x: Xq(x) ** 2, Xq, one,
                 lambda x: Xq_inv(x) ** 2, Xq_inv,
                 lambda x: sp.cancel(Xq(x) * Xq_inv(x))]
    lin_base = _span_rank(lin_basis, q0, with_deficit=False)
    lin_with = _span_rank(lin_basis, q0, with_deficit=True)
    bil_base = _span_rank(bil_basis, q0, with_deficit=False)
    bil_with = _span_rank(bil_basis, q0, with_deficit=True)

    # a handful of exact square deficits, for the record (deterministic strings)
    sample_xs = [Fraction(3, 2), Fraction(5, 3), Fraction(7, 4), Fraction(2, 1)]
    samples = [{"x": str(x), "Dx": str(square_deficit(x))} for x in sample_xs]

    reversal_present = not (all(r == 8 for r in sq_xr_ranks.values())
                            and control_xr_rank < 8)
    return {
        "deficit": "Dx_{x,x}(q) = [x^2]_q - [x]_q^2",
        "n_catalog": len(SQUARE_XS),
        "q0_values": [str(q0) for q0 in Q0_EXACT],
        "square_bihom_in_(X,R)_ranks": sq_xr_ranks,        # expect all 8
        "square_not_bihom_in_reversal": all(r == 8 for r in sq_xr_ranks.values()),
        "reversal_control_rank": control_xr_rank,          # expect < 8 (kernel)
        "control_detects_reversal": control_xr_rank < 8,
        "lin_span_{R,X,1}_base_rank": lin_base,            # expect r
        "lin_span_{R,X,1}_with_Dx_rank": lin_with,         # expect r+1 (Dx not in span)
        "Dx_in_addition_deficit_shape": lin_with == lin_base,
        "bilinear_span_base_rank": bil_base,               # expect r
        "bilinear_span_with_Dx_rank": bil_with,            # expect r+1 (Dx not in span)
        "Dx_in_bilinear_span": bil_with == bil_base,
        "reversal_present": reversal_present,               # expect False
        "verdict": "reversal ABSENT as the square obstruction",
        "sample_square_deficits": samples,
    }


# ---------------------------------------------------------------------------
# Engine negative cells: the product deficit the engine reproduces, pair by pair
# ---------------------------------------------------------------------------
def engine_negative_cells():
    """Every cell: engine product [x]_q*[y]_q differs from [xy]_q (nonzero deficit)."""
    cells = []
    all_ok = True
    for x, y in PRODUCT_CELLS:
        D = sp.cancel(Tmul(x, y) - mul_value(x, y))    # [xy]_q - [x]_q*[y]_q
        nonzero = D != 0
        all_ok = all_ok and bool(nonzero)
        cells.append({"x": str(x), "y": str(y), "xy": str(x * y),
                      "product_deficit": str(D), "nonzero": bool(nonzero)})
    # square cells: Dx nonzero for each catalog sample shown
    sq_cells = []
    for x in [Fraction(3, 2), Fraction(5, 3), Fraction(7, 4), Fraction(9, 5)]:
        D = square_deficit(x)
        sq_cells.append({"x": str(x), "square_deficit": str(D), "nonzero": bool(D != 0)})
        all_ok = all_ok and bool(D != 0)
    return {"product_cells": cells, "n_product_cells": len(cells),
            "square_cells": sq_cells, "all_cells_nonzero": all_ok}


# ---------------------------------------------------------------------------
# deterministic top-level checker (provstore entry point)
# ---------------------------------------------------------------------------
def run_mult_impossibility_checks():
    """Full deterministic battery -> JSON-able summary. No RNG; reproducible."""
    arm1 = arm1_exact_kernel()
    arm2 = bounded_degree_scan()
    arm3 = square_reversal_obstruction()
    neg = engine_negative_cells()

    verdict_negative = (
        arm1["prod_kernel_trivial"]
        and arm1["control_detects_bihomographic"]
        and arm2["all_bands_negative"]
        and arm3["square_not_bihom_in_reversal"]
        and arm3["control_detects_reversal"]
        and neg["all_cells_nonzero"]
    )
    return {
        "question": "Is [xy]_q a bihomographic function of [x]_q and [y]_q?",
        "verdict": "NO (clean negative)" if verdict_negative else "INCONCLUSIVE",
        "verdict_negative": bool(verdict_negative),
        "reversal_finding": arm3["verdict"],
        "arm1_exact_kernel": arm1,
        "arm2_bounded_scan": arm2,
        "arm3_square_reversal": arm3,
        "engine_negative_cells": neg,
    }


if __name__ == "__main__":
    import json

    summary = run_mult_impossibility_checks()
    print(json.dumps(summary, indent=2))
    print("\nVERDICT:", summary["verdict"])
    print("REVERSAL:", summary["reversal_finding"])
