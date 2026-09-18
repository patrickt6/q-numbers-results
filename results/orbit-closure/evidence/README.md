# cubic-modular-atlas - Orbit-closure dichotomy results

## What was computed

This folder contains results from the analysis of q-deformed cyclic cubics to test an orbit-closure dichotomy. The core question: does a q-polynomial functional equation (Ovsienko-Ustinov rigid form) exist for the two cyclic-cubic examples (heptagon and nonagon) but not for the S_3 cubics?

Two main findings:
1. On the q-polynomial-equation axis, the dichotomy holds: cyclic cubics satisfy a degree-three q-equation with infinite Laurent-series coefficients, while S_3 cubics admit no finite functional equation.
2. On the modular-pattern axis at N=5000, both classes show no detectable modular structure (noise-only), so modular patterns do not separate them at this resolution.

## CSV files and column meanings

**cubic_modular_atlas.csv** (6 rows)
- Contains: modular-atlas scanner results for the six S_3 cubics (cbrt2, cbrt3, cbrt5, plastic, root_x3_2x_2) and one quartic (qrt2).
- All entries have empty cells for the detail columns and verdict='noise_only', indicating no modular pattern detected.

**cyclic_cubics.csv** (2 rows)
- Contains: basic metadata for the two orbit-closed cyclic cubics.
- The two constants are heptagon (2cos(2*pi/7)) and nonagon (2cos(2*pi/9)), both with Galois group C_3 (cyclic, totally real).

**modular_atlas_results.csv** (8 rows)
- Contains: combined modular-atlas results for both cyclic cubics and all S_3 nulls.

**finite_kernel_search.csv** (2 rows)
- Contains: results of the polynomial functional equation kernel search for the cyclic cubics.
- Columns: `constant`, `finite_kernel_boxes_searched` (list of bidegree boxes tested), `result` (outcome: kernel dimension 0 in every box).
- This shows that cyclic cubics, like S_3 cubics, admit no finite q-polynomial functional equation, consistent with the Ovsienko-Ustinov theory.

**galois_conjugate_verification.csv** (2 rows)
- Contains: verification that the recovered q-trace equals the sum of q-deformations of the three real Galois conjugates.
- Columns: `constant`, `real_roots` (number of real roots; both cubics have 3), `recovered_B_q_equals_X1_X2_X3` (whether the recovered Laurent series equals the q-trace; both confirmed over q^[-5,160)), `OU_residual` (residual error of the recovered equation; 0 over q^[-5,4950) for both).

**dichotomy_summary.csv** (5 rows)
- Contains: comparison of properties between orbit-closed cyclic cubics and orbit-not-closed S_3 cubics.
- Columns: `property` (property being tested), `cyclic_cubics_heptagon_nonagon` (value for cyclic case), `s3_cubics_cbrt2_cbrt3_cbrt5_plastic_root_x3_2x_2_and_quartic_qrt2` (value for S_3 case).
- Properties include: Galois orbit closure, existence of q-trace, existence of q-polynomial equation, finite functional equation, and modular pattern detection.

## The finding

The orbit-closure dichotomy holds on the q-polynomial-equation axis (cyclic cubics recover the Ovsienko-Ustinov degree-three q-equation; S_3 cubics do not), but the modular-pattern conjunct shares a null at N=5000 (both are noise-only). This suggests the separation is carried by functional equations, not modular patterns at this computational resolution.

## Code files

**cubic_atlas_compute.sage**
- Purpose: compute q-continued-fraction expansions [alpha]_q for algebraic constants.
- Key function: `compute_constant(slug, N)` computes the first N stable Taylor coefficients of [constant]_q.
- Input: slug (constant identifier, e.g. "heptagon") and N (number of coefficients, default 5000).
- Output: CSV file with columns `n` (index) and `coefficient` (the q-coefficient at index n).
- Dependencies: imports `q_continued_fraction.sage` (internal Sage q-deformation engine). The script is provided here for reference; to run it, the internal engine must be available in the project directory structure.


- q-real computes: heptagon `81d5c043353abecb0649b059d2a4fb3f`, nonagon `b119dfb61d613de0f5596494471086b4`.
- Modular scan (cyclic + S_3 nulls): `b5a58395ec0e03735c65e578db9464d8`.
- Functional-equation kernel search and Ovsienko-Ustinov recovery: `c8690ab46766897ee8eae880784e7682`.

## How to verify


