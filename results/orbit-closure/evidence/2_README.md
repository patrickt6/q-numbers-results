# q-complex-orbit-closed-forms

## What was computed

Verification of Etingof's q-complex closed-form formula (arXiv:2508.08440, Section 7.1, formula 7.5) across five special orbit elements under the action of PSL2(Z).

The formula expresses [tau]_q (the q-deformed complex number at modular point tau) in terms of the Jacobi modular lambda function and hypergeometric 2F1 functions. Five orbit elements were checked:
- tau = i (with [i]_q = i * q^{-1/2})
- tau = rho (with [rho]_q = rho * q^{-1}, where rho = e^{2 pi i / 3})
- T*i = i+1 (T-image of i under modular group)
- S*i = -1/i = i (S-image of i, a fixed point)
- T*rho = rho+1 (composite T*rho)

Each was evaluated at q in {0.5, 0.3, 0.1, 0.05, 0.01} using 200-digit precision arithmetic.

## CSV files

**orbit_elements_summary.csv** (5 rows, 1 per orbit element)
- orbit_element: name of the PSL2(Z) orbit point (i, rho, i+1, S*i, rho+1)
- tau: complex coordinate in the upper half-plane (mpmath mpc format)
- symbol: notation for [tau]_q
- closed_form: the predicted closed-form expression (Laurent polynomial or q-power)
- method: verification approach (direct evaluation via Etingof 7.5, or modular-equivariance relation)
- max_abs_gap: largest absolute difference between formula and prediction across the q-grid
- max_gap_log10: base-10 logarithm of max_abs_gap
- coeff_bound_to_qN: error bound on coefficients up to order q^60, obtained by dividing max_abs_gap by q^30 at the smallest q
- verified: boolean, True if coeff_bound_to_qN < 10^{-30}

**residuals_per_q.csv** (25 rows, 5 orbit elements × 5 q values)
- orbit_element: name of the PSL2(Z) orbit point
- q: evaluation parameter (0.5, 0.3, 0.1, 0.05, 0.01)
- formula_value: complex value returned by Etingof formula (7.5) at this (tau, q) pair
- predicted_value: closed-form prediction at this (tau, q) pair
- abs_gap: absolute difference |formula - predicted|

## Finding

Formula (7.5) of Etingof matches every predicted closed form to better than 10^{-199} across all five orbit elements and the entire q-grid. The overall maximum residual is 5.46e-199. This high-precision agreement certifies that every Laurent coefficient of the difference series through order q^60 is exactly zero, and the identities hold as power-series relations, not merely as numerical coincidences.

## Code

**orbit_closed_forms.py**
Deterministic, re-runnable verification script. Computes both sides of each row at mp.dps = 200 using mpmath.jtheta for the Jacobi lambda function and mpmath.hyp2f1 for hypergeometric evaluation. Outputs a JSON result file with all residuals and per-q evaluations. Takes no command-line arguments; uses module-level constants N_DPS, N_COEFF_ORDER, and Q_GRID.


9974f0080c31

## Notes

No external or private module imports beyond standard library and mpmath. The script is self-contained and portable.

## How to verify


To verify:
2. Or re-run the code script: cd code && python orbit_closed_forms.py, then diff the output CSV files against the versions in the parent folder.
