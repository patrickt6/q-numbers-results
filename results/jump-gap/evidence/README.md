# jump-gap experiment

## Summary

This folder contains the catalogue and computations of the one-sided jump gap of q-deformed rationals: the discontinuity between the left and right versions of [r/s]_q at every rational r/s.


## What was computed

The Morier-Genoud-Ovsienko (MGO) q-deformation x |-> [x]_q is not continuous at the rationals. Each rational r/s has two distinct q-deformations: the right version (limit from above) and the left version (limit from below). This computation evaluates the exact jump gap,

    gap(r/s) = [r/s]_q^+ - [r/s]_q^-

over a catalogue of 155 reduced rationals and derives a closed-form expression.

## Data files

### jump_gaps.csv

155 rows of rationals (p, s) and their jump gap properties. Columns:

- **p, s**: numerator and denominator (always coprime, s >= 1)
- **even_cf**: even-length regular continued fraction of p/s as a list [a0, a1, ...]
- **E_alt_cf_sum**: the alternating sum of CF digits (even positions minus odd positions). This equals D, the exponent of the q-Wronskian det M_q = q^D, and it is what this column stores. It is distinct from the numerator exponent E = (sum of all CF digits) - 1 used in the closed form below; the two are related by E = D + 2(sum of odd-position digits) - 1. The column name predates that distinction, so read it as the alternating sum D, not E.
- **gap_numerator**: numerator polynomial of the gap, as a string in q
- **gap_denominator**: denominator polynomial of the gap, as a string in q
- **gap_at_q_half**: gap evaluated at q = 1/2 (rational value)
- **leading_q1_coeff**: leading coefficient as q -> 1, always equals -1/s^2
- **right_matches_qreals_oracle**: boolean flag (True on all rows)
- **numerator_is_unit_times_qE**: boolean flag checking numerator = (1-q) * q^E * unit (True on all)
- **is_unit_fraction**: boolean (True if p = 1)
- **unit_formula_matches**: boolean for unit fractions; exact match of closed form (True on all units)

## The finding

Two main results:

1. **Closed form for unit fractions** (all 1/s in the catalogue):

   [1/s]_q^+ - [1/s]_q^- = (1 - q) q^{s-1} / ([s]_q (1 + q^2 [s-1]_q))

   where [s]_q = 1 + q + ... + q^{s-1} is the q-integer.

2. **Universal form** (all rationals):

   [r/s]_q^+ - [r/s]_q^- = (1 - q) q^E / (S^+(q) S^-(q))

   where E = (sum of the even-length CF digits) - 1, and S^+, S^- are the right and left q-denominators (both equal s at q = 1). The single power of q traces back to the q-Wronskian det M_q = q^D, where D is the alternating CF sum (even positions minus odd positions); after the raw Laurent denominators are cleared to honest polynomials the numerator exponent becomes E = D + 2(sum of odd-position digits) - 1 = (sum of all digits) - 1. So E (numerator exponent) and D (determinant exponent, stored in the CSV column E_alt_cf_sum) are different quantities. See gap_meaning.md in the source project for the derivation.

**Leading behaviour at q = 1:**

   gap(r/s) = -(q - 1) / s^2 + O((q - 1)^2)

This shows the jump shrinks like 1/s^2 as denominators grow.

## Verification

The catalogue was verified on two disjoint sets:

- **Training set** (155 rationals in the CSV): all checks pass (oracle agreement, numerator structure, leading term, unit formula)
- **Held-out set** (23 rationals not in the catalogue): unit fractions 1/s for s = 31..45, and general fractions 5/13, 7/13, 11/13, 9/13, 4/15, 8/15, 3/14, 11/14. The closed forms recomputed from q and s only match the engine gap exactly on all held-out entries.

## Code files

### jump_catalog.py

Main computation script. Builds the q-continuant matrix M_q from the MGO blocks, reads off the two one-sided limits (right and left versions), and computes the jump gap for each rational. Also implements the unit-fraction closed form and verifies it against a qreals oracle (q_rational function).

**Note on imports**: This file uses sys.path.insert to load qreals.rational and recurrence modules from parent directories (lines 68-75). In isolation, these imports will fail. The file is designed to run within the original project structure. The computation logic (q-continuant blocks, closed-form formulas, verification logic) is complete and self-contained; only the oracle cross-checks (stabilisation_check, recurrence_oracle_check) require the parent modules.

## References

- P. Jouteur, Symmetries of the q-deformed real projective line, arXiv:2503.02122. Definition 1.2 and Proposition 1.1 (right and left versions), Proposition 4.8 (one-sided limits).
- S. Morier-Genoud, V. Ovsienko, q-deformed rationals and q-continued fractions, Forum Math. Sigma 8 (2020), e13.
- A. Bapat, L. Becker, A. Licata (left version definition).

## How to verify


To verify the results:

2. Alternatively, re-run code/jump_catalog.py and diff the output jump_gaps.csv against the stored version.
