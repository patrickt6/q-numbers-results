# q-Somos-4 Laurent-stable twists (q-somos-twist)

## What was computed

A systematic search over integer twist exponents (a, b) in the range -3 to 3 testing whether the q-twisted Somos-4 recurrence

    x_{n+4} x_n = q^a x_{n+3} x_{n+1} + q^b (x_{n+2})^2

produces Laurent polynomial values for x_4 through x_11 when computed over Z[q, q^{-1}][x_0, x_1, x_2, x_3]. The search tested 49 pairs total.

## CSV files and columns

### twist_search.csv
Main result table: 392 rows (49 pairs × 8 iterations from n=4 to n=11).

- **a, b**: twist exponent pair
- **n**: iteration index
- **is_laurent**: true if x_n is a Laurent polynomial in (x_0, x_1, x_2, x_3) over the coefficient field Q(q)
- **denom_degree**: total degree of the denominator monomial in the four x variables after cancellation (0 for Laurent)

### laurent_examples.csv
Representative Laurent polynomials for x_4 from each winning pair: 49 rows.

- **a, b**: twist exponent pair
- **x4_laurent_expression**: explicit symbolic form of x_4 for this (a, b)
- **oeis_a006720_value**: integer Somos-4 value at x_0 = x_1 = x_2 = x_3 = 1, q = 1 (all 49 pairs specialize to 2)

### summary.csv
High-level metadata: 9 rows (parameter ranges and summary statistics).

- **rows**: total data rows in twist_search.csv (392)
- **n_winners**: count of (a, b) pairs with all x_4..x_11 Laurent (49)
- **a_range_start, a_range_end, b_range_start, b_range_end, n_range_start, n_range_end**: search window bounds
- **winners_list**: comma-separated list of all 49 winning (a, b) pairs

### proof_check.csv
Verification summary: 12 rows.

- **cells_checked**: 392 (one cell per (a, b) pair and n index)
- **support_failures**: 0 (Laurent support is identical across all 49 pairs)
- **q1_coefficient_failures**: 0 (q-coefficients reduce correctly at q = 1)
- **a006720_failures**: 0 (all pairs specialize to OEIS A006720 values)
- **all_pass**: true (all 392 cells pass verification)
- **A006720_values**: the 8 values A006720(4) through A006720(11) = 2,3,7,23,59,314,1529,8209

## The finding

All 49 pairs in the search window produce Laurent sequences. Specifically, the (a, b) exponent does not affect whether x_n remains Laurent in the initial variables, but it modulates the q-power distribution across the numerator and denominator. The denominator support (the monomial in x_0..x_3) remains fixed across all pairs. When q = 1 and initial variables are set to 1, every pair recovers the integer Somos-4 sequence (OEIS A006720). This indicates that the Laurent phenomenon (a property of cluster algebras) extends robustly to the q-twisted setting, at least for this recurrence and parameter range.

## Code files

### twist_search.py
Exhaustive pair search. Iterates over the (a, b) grid, computes x_n for n = 4..11 using the q-twisted recurrence, tests each term for the Laurent polynomial property, and outputs the results table and winner list. Dependencies: sympy.

### twist_proof_check.py
Symbolic verification. For each of the 392 cells (a, b, n), checks three properties: (1) Laurent support stability (the numerator/denominator monomial structure matches the classical (0, 0) case), (2) q-coefficient agreement at q = 1, and (3) OEIS A006720 agreement at q = 1 and unit initial conditions. All 392 cells pass. Dependencies: sympy.



## Notes

The recurrence and Laurent phenomenon are classical from the cluster algebra literature (Berenstein-Zelevinsky arXiv:math/0404446; Fomin-Zelevinsky arXiv:math/0104151; Gale-Robinson). The q-twist introduces a parameter into what was originally an integer sequence definition, and this study confirms that the cluster-like Laurent property persists across all tested parameter choices.

## How to verify


Reproduce by re-running `code/twist_search.py` and diffing the regenerated CSV against the committed CSV.
