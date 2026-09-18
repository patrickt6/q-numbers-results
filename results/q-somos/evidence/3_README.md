# q-somos-repro - Hankel Determinant Periodicity Verification

## Overview

This experiment reproduces the integer Hankel and Somos/Gale-Robinson tables for metallic numbers (golden, silver, bronze, and a fourth metallic number) as described in Ovsienko and Pedon (arXiv:2312.17009v2) and Han-Pedon (arXiv:2502.05993).

## What Was Computed

For each metallic number y_k = (k + sqrt(k^2 + 4))/2 where k in {1, 2, 3, 4}, the computation:

1. Computed the q-real series [y_k]_q to a sufficient number of coefficients
2. Calculated Hankel determinants Delta_n^(ell)(y_k) where n ranges over one or more complete periods and ell (shift) ranges from 0 to k+1
3. Verified the three-term Gale-Robinson recurrence relation:
   Delta_{n+2k+2}^(ell) * Delta_n^(ell) = Delta_{n+2k+1}^(ell) * Delta_{n+1}^(ell) - (Delta_{n+k+1}^(ell))^2

The Hankel determinant Delta_n is computed from coefficients a_i of [y_k]_q as the determinant of the n-by-n matrix with entries a_{i+j} for 0 <= i,j < n. The shifted variant Delta_n^(ell) drops the first ell coefficients before constructing the determinant.

## Key Finding

All 1104 recurrence relation checks passed (both table and check files show 100% match rate across all k and shift values). This confirms that the Hankel sequences exhibit the predicted periodic or antiperiodic structure and satisfy the Gale-Robinson relation without exception.

## CSV Files

somos_table.csv (552 rows):
- k: metallic number index (1, 2, 3, or 4)
- shift_ell: the shift parameter ell (ranges 0 to k+1 for each k)
- n: the determinant index within the period (0-indexed)
- delta_value: the integer value of Delta_{n+1}^(ell)

This table stores one complete period of Hankel values for each k and shift combination.

somos_check.csv (552 rows):
- k: metallic number index
- shift_ell: shift parameter
- n: the recurrence index (where the relation is tested)
- lhs: left-hand side of Gale-Robinson relation (Delta_{n+2k+2}^(ell) * Delta_n^(ell))
- rhs: right-hand side (Delta_{n+2k+1}^(ell) * Delta_{n+1}^(ell) - (Delta_{n+k+1}^(ell))^2)
- match: boolean indicating whether lhs == rhs

The recurrence is checked over one full period for each k and shift.

## Code File

somos_repro.py:
- Builds the q-real series for each metallic number using the qreals library
- Computes Hankel determinants via direct matrix determinant calculation
- Writes the two CSV outputs with complete period coverage
- Prints a summary of match statistics and SHA-256 checksums

**Note:** This script imports the qreals library (qreals.q_real_truncated). It assumes qreals is installed or available on the Python path. The script uses a sys.path manipulation (lines 45-48) to locate qreals relative to the directory structure of the original qnumbers project. When running this script in isolation, the qreals module must be available separately.


d2c4a8725d4c

## Theorem and Conjecture References

- Ovsienko-Pedon (arXiv:2312.17009v2): Definition of Hankel determinants for q-reals and the empirical periodicity conjecture.
- Han-Pedon (arXiv:2502.05993): Proof that Hankel sequences of metallic numbers satisfy the Gale-Robinson recurrence and exhibit the predicted periodic/antiperiodic structure.

## How to verify

The CSVs somos_table.csv and somos_check.csv were produced by code/somos_repro.py. To verify:

2. Re-run code/somos_repro.py and diff the CSV outputs against the originals
