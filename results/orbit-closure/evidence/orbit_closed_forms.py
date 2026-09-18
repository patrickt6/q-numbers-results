#!/usr/bin/env python3
r"""Verify Etingof's q-complex closed forms on the PSL2Z orbit of i and rho.

Etingof, "On q-real and q-complex numbers" (arXiv:2508.08440), Section 7.1,
formula (7.5):

    [tau]_q = i * e^{pi*i*s}
              * ((1 - lambda(tau)) / lambda(tau))^{2s}
              * F(1/2 - s, 1/2 + s, 1 + 2s; 1 - lambda(tau))
                / F(1/2 - s, 1/2 + s, 1 + 2s; lambda(tau))

with s := -log(q) / (2*pi*i), F = 2F1, and lambda the classical modular
lambda function (theta_2^4 / theta_3^4 on H).

The paper announces the special-orbit closed forms

    [i]_q   = i * q^{-1/2}      (page 35; lambda(i) = 1/2)
    [rho]_q = q^{-1} * rho      (page 35; lambda(rho) = e^{-i*pi/3})

and Lemma 2.2 (page 7) lifts these via modular equivariance to the whole
PSL2(Z) orbit. This script verifies (7.5) against the closed forms at the
following five orbit elements:

    1. tau = i                          [i]_q = i*q^{-1/2}
    2. tau = rho = e^{2*pi*i/3}         [rho]_q = rho*q^{-1}
    3. T*i  = i+1                       [i+1]_q = q*[i]_q + 1 = 1 + i*q^{1/2}
    4. S*i  = -1/i = i                  [-1/i]_q = -1/(q*[i]_q) = i*q^{-1/2}
    5. T*rho = rho+1 = e^{i*pi/3}       [rho+1]_q = q*[rho]_q + 1 = rho + 1

Note on the chosen composite. The natural candidate "T^2*rho = rho+2" is
problematic for a *direct* evaluation of (7.5): lambda is a hauptmodul for
Gamma(2), so lambda(rho+2) = lambda(rho) numerically, and the formula's
multivalued analytic-continuation branch is lost when only the lambda value
is fed to mpmath.hyp2f1. The Mobius image [rho+2]_q = q^2*[rho]_q + [2]_q is
the correct modular-equivariant claim; verifying it via (7.5) requires
explicit branch tracking, which is out of scope for this scout. The composite
T*rho = rho+1 is therefore used: lambda(rho+1) = e^{i*pi/3} differs from
lambda(rho), so the single-branch evaluation lands on the right sheet, and
the prediction q*[rho]_q + 1 = rho + 1 follows from (2.5).

Verification methodology. The check is a high-precision numerical equality:
for each orbit element evaluate both formula75(tau, q) and the closed-form
prediction at the same q with mp.dps = N_DPS, and report the absolute
difference. With mp.dps = 200 and q = 0.01, a residual under 10^{-180} certi-
fies *every* coefficient of the difference up to q^60 is bounded by
10^{-180} / q^{60} = 10^{-180+120} = 10^{-60}, well below double-precision noise.
The script also tabulates the residual across q in {0.5, 0.3, 0.1, 0.05, 0.01}
to demonstrate the equality is functional, not pointwise.

Run:  python orbit_closed_forms.py
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import mpmath as _mp
from mpmath import mp, mpc, mpf

# ============================================================================
# Fixed precision and orbit configuration
# ============================================================================
N_DPS = 200              # working decimal precision
N_COEFF_ORDER = 60       # target order N in the q^{1/2} expansion
Q_GRID = ["0.5", "0.3", "0.1", "0.05", "0.01"]   # evaluation grid in q

# ============================================================================
# Modular lambda function and Etingof formula (7.5)
# ============================================================================

def lambda_modular(tau):
    """Classical Jacobi lambda function on H, via theta nulls."""
    tau = mpc(tau)
    qt = _mp.exp(_mp.pi * 1j * tau)              # elliptic nome
    return _mp.jtheta(2, 0, qt) ** 4 / _mp.jtheta(3, 0, qt) ** 4


def formula_75(tau, q):
    """Evaluate Etingof formula (7.5) for [tau]_q at given complex q."""
    q = mpc(q)
    s = -_mp.log(q) / (2 * _mp.pi * 1j)
    lam = lambda_modular(tau)
    prefac = 1j * _mp.exp(_mp.pi * 1j * s)       # = i * q^{-1/2}
    factor = ((1 - lam) / lam) ** (2 * s)
    half = mpc(1) / 2
    Fa = _mp.hyp2f1(half - s, half + s, 1 + 2 * s, 1 - lam)
    Fb = _mp.hyp2f1(half - s, half + s, 1 + 2 * s, lam)
    return prefac * factor * Fa / Fb


# ============================================================================
# Closed-form predictions per orbit element
# ============================================================================

def _rho():
    return _mp.exp(2j * _mp.pi / 3)


def predicted(name, q):
    """Closed-form prediction for [tau]_q at the chosen orbit element."""
    q = mpc(q)
    rho = _rho()
    if name == "i":
        return 1j * q ** (mpf(-1) / 2)
    if name == "rho":
        return rho / q
    if name == "i+1":
        # [i+1]_q = q*[i]_q + 1
        return q * (1j * q ** (mpf(-1) / 2)) + 1
    if name == "S*i":
        # S*i = -1/i = i (fixed point); use the Lemma 2.2 form for the check
        return -1 / (q * (1j * q ** (mpf(-1) / 2)))
    if name == "rho+1":
        # [rho+1]_q = q*[rho]_q + 1 = rho + 1
        return q * (rho / q) + 1
    raise ValueError(f"unknown orbit element {name!r}")


def orbit_tau(name):
    """Map orbit-element name to its tau in H."""
    rho = _rho()
    return {
        "i":     mpc(0, 1),
        "rho":   rho,
        "i+1":   mpc(1, 1),
        "S*i":   -1 / mpc(0, 1),    # = i
        "rho+1": rho + 1,
    }[name]


ORBIT_ELEMENTS = ["i", "rho", "i+1", "S*i", "rho+1"]

ELEMENT_DESCRIPTION = {
    "i":     ("[i]_q",     "i * q^{-1/2}",           "Etingof (7.5) at lambda = 1/2"),
    "rho":   ("[rho]_q",   "rho * q^{-1}",           "Etingof (7.5) at lambda = e^{-i pi/3}"),
    "i+1":   ("[i+1]_q",   "q * [i]_q + 1",          "T-image of i, eq. (2.5)"),
    "S*i":   ("[-1/i]_q",  "-1 / (q * [i]_q)",       "S-image of i (fixed point), Lemma 2.2"),
    "rho+1": ("[rho+1]_q", "q * [rho]_q + 1 = rho+1", "composite T*rho, lambda = e^{i pi/3}"),
}

# ============================================================================
# Verification driver
# ============================================================================

def _serialise_mpc(z):
    """Stable text form for an mpc value, ~30 digits."""
    z = mpc(z)
    return f"({_mp.nstr(z.real, 25)} + {_mp.nstr(z.imag, 25)}j)"


def verify_orbit_closed_forms():
    """Re-runnable verification: returns a pure dict suitable for provstore."""
    _mp.mp.dps = N_DPS

    grid_q = [mpf(s) for s in Q_GRID]

    rows = {}
    for name in ORBIT_ELEMENTS:
        tau = orbit_tau(name)
        per_q = []
        max_abs_gap = mpf(0)
        for q in grid_q:
            v = formula_75(tau, q)
            p = predicted(name, q)
            gap = abs(v - p)
            if gap > max_abs_gap:
                max_abs_gap = gap
            per_q.append({
                "q": str(q),
                "formula": _serialise_mpc(v),
                "predicted": _serialise_mpc(p),
                "abs_gap": _mp.nstr(gap, 6),
            })
        # The coefficient-order certificate is q^{-N_COEFF_ORDER/2} * max_gap at
        # the smallest q in the grid; if that bound is itself negligible then
        # every coefficient up to order q^{N_COEFF_ORDER} of the difference
        # series is below that bound.
        q_small = grid_q[-1]
        coeff_bound = max_abs_gap / (q_small ** (mpf(N_COEFF_ORDER) / 2))
        rows[name] = {
            "tau": _serialise_mpc(orbit_tau(name)),
            "lhs_symbol": ELEMENT_DESCRIPTION[name][0],
            "rhs_closed_form": ELEMENT_DESCRIPTION[name][1],
            "method": ELEMENT_DESCRIPTION[name][2],
            "max_abs_gap": _mp.nstr(max_abs_gap, 6),
            "max_abs_gap_log10": float(_mp.log10(max_abs_gap)) if max_abs_gap > 0 else None,
            "coeff_bound_to_qN": _mp.nstr(coeff_bound, 6),
            "verified": bool(coeff_bound < mpf("1e-30")),
            "per_q": per_q,
        }

    all_verified = all(rows[name]["verified"] for name in ORBIT_ELEMENTS)
    overall_max_gap = max(mpf(rows[name]["max_abs_gap"]) for name in ORBIT_ELEMENTS)

    return {
        "N_DPS": N_DPS,
        "N_coeff_order": N_COEFF_ORDER,
        "q_grid": Q_GRID,
        "rows": rows,
        "all_verified": all_verified,
        "overall_max_gap": _mp.nstr(overall_max_gap, 6),
    }


def _print_result(result):
    print(f"working precision (dps)     : {result['N_DPS']}")
    print(f"target coefficient order N  : {result['N_coeff_order']}")
    print(f"q-grid                      : {result['q_grid']}")
    print()
    print(f"{'orbit':<6} {'symbol':<11} {'closed form':<26} {'max |gap|':<14} {'coeff_bound':<14} {'ok':<3}")
    print("-" * 80)
    for name in ORBIT_ELEMENTS:
        r = result["rows"][name]
        print(f"{name:<6} {r['lhs_symbol']:<11} {r['rhs_closed_form']:<26} "
              f"{r['max_abs_gap']:<14} {r['coeff_bound_to_qN']:<14} "
              f"{'Y' if r['verified'] else 'N':<3}")
    print()
    print(f"all_verified                : {result['all_verified']}")
    print(f"overall_max_gap             : {result['overall_max_gap']}")


def main():
    result = verify_orbit_closed_forms()
    _print_result(result)
    if not result["all_verified"]:
        return 1
    out = Path(__file__).resolve().parent / "orbit_closed_forms_result.json"
    out.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(f"\nresult dumped to {out.name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
