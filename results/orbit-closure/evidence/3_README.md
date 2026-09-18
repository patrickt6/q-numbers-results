# funceq-cubic Experiment Dataset

## Overview

This dataset contains computational results from a linear-algebra functional-equation search for q-deformed algebraic numbers. The experiment systematically searches for polynomial and Laurent-polynomial relations annihilating [α]_q (the q-analog of algebraic constants α) over a range of polynomial bidegrees and Laurent spans.

## What Was Computed

The core computation solves the following for each target constant α and search box (d_X, d_q, B):

1. Compute [α]_q^k for k = 0, ..., d_X to N Taylor coefficients each
2. Build an N × ((d_X + 1)(d_q + 1)) integer constraint matrix M whose rows are the q^k coefficients of candidates P(X, q) = Σ c_{i,j} X^i q^j evaluated at X = [α]_q
3. Compute the right kernel of M over Z (or Q for large systems)

A non-trivial kernel is the lattice of polynomials P annihilating [α]_q modulo q^N. The search covers:

- **Part 1**: polynomial P(X, q) with d_X ≤ 4 and d_q ≤ 30, N = 300-400
- **Part 2A**: Laurent-polynomial P(X, q) with d_X ≤ 4 and d_q⁻ + d_q⁺ ≤ 30, N = 400
- **Part 2B**: polynomial P(X, q) with d_X ≤ 6 and d_q ≤ 50, N = 2000

Targets: √2, √3, √5, φ (golden ratio), ∛2, ∛3, ∛5, 2^(1/4).

## CSV Files and Columns

### functional_equations_validation.csv

Validation controls reproducing known MGO functional equations (Morier-Genoud-Ovsienko, reals.pdf §4).

Columns:
- target: algebraic constant (phi, sqrt2, sqrt3, sqrt5)
- d_X: polynomial degree in X
- d_q: polynomial degree in q
- N: number of Taylor coefficients verified
- kernel_basis: primitive integer basis polynomial (as string expression)
- matches_MGO: reference to published MGO equation number

### cbrt2_search_results.csv

Part 1 search results for α = ∛2 across 11 search cells.

Columns:
- d_X: X-degree (3 or 4)
- d_q: q-degree (6, 8, 12, 16, 20, 24, 30)
- B: integer coefficient bound
- unknowns: dimension of the constraint matrix column space
- N: number of Taylor coefficients in system
- kernel_dim: dimension of right kernel (0 = negative result)
- result: outcome summary

### part2_validation_controls.csv

Backwards-compatibility check: Part 2 Laurent extension (d_q⁻ = 0) reproduces Part 1 results.

Columns: target, d_X, d_q_minus, d_q_plus, kernel_basis, matches_Part1

### part2_track_a_laurent.csv

Part 2A Laurent-polynomial search results for α = ∛2 across 8 cells with d_q⁻ > 0 and d_q⁺ > 0.

Columns:
- target: cbrt2
- d_X: X-degree (3 or 4)
- d_q_minus: lower Laurent q-degree
- d_q_plus: upper Laurent q-degree
- B: integer coefficient bound
- unknowns: matrix column dimension
- N: Taylor coefficient count
- ring: ZZ (Hermite normal form) or QQ (rational kernel, faster)
- kernel_dim: kernel dimension
- result: outcome

### part2_track_b_polynomial.csv

Part 2B polynomial search results for α = ∛2 across 5 cells with d_X up to 6 and d_q up to 50.

Columns: target, d_X, d_q, B, unknowns, N, ring, kernel_dim, result

### cubic_modular_atlas.csv

Modular-arithmetic verdict table for cubic algebraic numbers (∛2, ∛3, ∛5, 2^(1/4), plastic, root of x^3 - 2x - 2).

Columns:
- constant: algebraic constant name
- p, d, residue_classes_with_full_divisibility: modular parameters (empty if not applicable)
- absorbing_residue_classes: residue classes exhibiting modular divisibility (empty)
- chi_squared and split variants: test statistics (empty)
- n_tested_total, n_tested_first_half, n_tested_second_half: sample sizes (empty)
- both_halves_agree: consistency flag (empty)
- verdict: classification (all marked "noise_only" - no deterministic modular pattern detected)

### cyclic_cubic_modular_atlas.csv

Modular-arithmetic verdict table for cyclic-cubic configurations (heptagon, nonagon).

Columns: same as cubic_modular_atlas.csv

Verdict: noise_only (no deterministic modular law found at test depth N=5000)

## Key Finding

For each target α in {√2, √3, √5, φ, ∛2, ∛3, ∛5, 2^(1/4)}:

- No polynomial P(X, q) in Q[q][X] of bidegree (d_X, d_q) ≤ (6, 50) annihilates [α]_q modulo q^2000
- No Laurent polynomial P(X, q) in Q[q, q^{-1}][X] with d_X ≤ 4 and d_q⁻ + d_q⁺ ≤ 30 annihilates [α]_q modulo q^400
- All cubic and higher-order algebraic constants exhibit only noise-level modular behavior; no deterministic modular-arithmetic classification found

The polynomial search (Part 2B) at (d_X, d_q) = (6, 50) achieves 5.6× over-determination (357 unknowns vs 2000 constraints), well beyond finite-N artifact risk.

## Code Files

All SageMath scripts in code/:

### functional_equation_search.sage


Environment variables: ALPHA, D_X, D_Q, D_Q_MINUS, D_Q_PLUS, B, N, OUT, VERIFY_TO, USE_CSV, KERNEL_RING.

**Note:** loads q_continued_fraction.sage from relative or absolute path; requires execution from qnumbers root.

### q_continued_fraction.sage

q-analog implementation following Morier-Genoud-Ovsienko (MGO) formula. Computes [p/s]_q for rationals and [x]_q to N stable Taylor coefficients via q-continued-fraction truncation. Uses MGO Proposition 1.1: at CF depth n with partial-quotient sum S_n, exactly S_n - 1 power-series coefficients of [p_n/q_n]_q agree with [x]_q. Provides q_int(n), q_int_qinv(n) utilities for [n]_q and [n]_{q^{-1}} in arbitrary rings.

**Note:** defines global ring F and q; imported by functional_equation_search.sage. Contains no internal path hacks.

### modular_atlas_compute.sage


**Note:** locates qnumbers repo root via hardcoded path candidates. Delegates computation; does not implement the algorithm inline.



## Notes

- functional_equations.md (source) contains extended prose documentation of method, validation controls, and interpretation. That file is the primary reference for understanding the negative results.
- All four MGO validation equations (φ, √2, √3, √5) confirmed at their minimum (d_X, d_q) boxes; backends (SageMath + Sage QQ rational kernel vs pure-Python SymPy nullspace) cross-verified.
- Cubic-root targets (∛2, ∛3, ∛5) are negative across all tested boxes, including asymmetric Laurent cell (4, 20, 0) (pure-q^{-1} direction).
- Modular atlas (cubic and cyclic-cubic) computed at N=5000; all exhibit noise-level χ² and "both halves" disagreement, indicating no deterministic modular law at depth 5000.
- Shared raw coefficient data (qreal_*.csv with 70+ expansions up to 20000 rows) referenced internally but not shipped (see functional_equation_search.sage USE_CSV flag).

## How to verify

The CSV outputs were produced by code/functional_equation_search.sage and code/modular_atlas_compute.sage, which compose the computational pipeline for searching functional equations and computing modular-arithmetic statistics.


To verify the results:
1. Re-run code/functional_equation_search.sage and code/modular_atlas_compute.sage with the documented environment variables and parameters
2. Diff the generated CSV files against the shipped versions in this folder

