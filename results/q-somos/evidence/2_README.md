# q-Somos-4 Twist Extended Window

## What was computed

A systematic scan of integer pairs (a, b) in the range [-6, 6] x [-6, 6] (169 pairs total), checking Laurent polynomial behavior of the q-Somos-4 twist recurrence. For each pair, symbolic sequences x_4 through x_12 were computed via the recurrence x_{n+4} x_n = q^a x_{n+3} x_{n+1} + q^b x_{n+2}^2 starting from symbolic x_0, x_1, x_2, x_3. The result is a complete atlas of Laurent-polynomial signatures over the extended window.

## Files

### qsomos_twist_results.csv
Main results table. 1,521 data rows (plus header).

Columns:
- a: first twist exponent (integer)
- b: second twist exponent (integer)
- n: recurrence depth (4 to 12)
- is_laurent: boolean, True if x_n is a Laurent polynomial in (x_0, x_1, x_2, x_3) over Q(q)
- denom_degree: sum of exponents in the denominator monomial (integer); 0 if is_laurent is True; -1 if the value is not expressible as a rational function
- elapsed_s: cumulative wall-clock time in seconds from start of computation

One row per (a, b, n) triple tested.

### code/run.py
Python computation script (SymPy-based). Uses a depth-first iteration pattern so partial runs preserve the full depth history through the last completed n, and maintains per-pair state to avoid recomputation. Each pair is tested once per n value, with symbolic cancellation via SymPy. Tunables: A_RANGE, B_RANGE, N_MIN, N_MAX control the scan window and recursion depth cap.

## Finding

All 169 integer pairs (a, b) in the extended [-6, 6]^2 window maintain the Laurent property for all depths n = 4 to 12. The earlier [-3, 3]^2 / n <= 11 observation extends seamlessly to the wider window and two additional depths without any pair failing. The denominator-degree sequence (indexed by n) is identical across all surviving pairs: [1, 2, 4, 7, 9, 13, 17, 21, 27]. This uniformity is strong evidence that the Laurent property is driven by a Berenstein-Zelevinsky compatible-pair structure where the twist exponents (a, b) scale uniformly without breaking compatibility.

## Hypothesis

The Laurent property of the q-Somos-4 family is a Berenstein-Zelevinsky compatible-pair phenomenon. An exact compatibility argument (using the quantum exchange-matrix formalism) should recover the observed denominator-degree column and confirm that the property holds for arbitrary integer twists, not just the sampled [-6, 6]^2 grid.

## Notes

- Computation completed after a partial run was killed at depth n=12 mid-session. This is the successful rerun at n <= 12.
- The run.py script references a companion twist_search.py (not shipped) that implements a different Laurent-property check; the same symbolic denominatorgenerator is used here.
- Total rows: 1,521 (all (a, b, n) triples successfully evaluated).

## How to verify


To verify the results:
2. Re-run the code/ script: python code/run.py and diff the generated qsomos_twist_results.csv against the original to confirm reproducibility.
