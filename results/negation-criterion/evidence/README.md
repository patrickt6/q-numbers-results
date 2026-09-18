# negation-finiteness

## Summary

For every squarefree D in [2, 200], this experiment determines whether the q-negation sum
V_D(q) = [sqrt(D)]_q + [-sqrt(D)]_q is a finite Laurent polynomial in q or an infinite
series. Of the 121 squarefree D in this range, 63 give a finite Laurent polynomial and 58
give an infinite series. Being trace-zero (a pure square root) is necessary but NOT
sufficient for finiteness: sqrt(19), sqrt(43), sqrt(46), and sqrt(53) are all trace-zero
yet yield infinite sums. A clean if-and-only-if criterion in terms of the continued
fraction of sqrt(D) remains open.

## What was computed

The q-negation [-x]_q is the Jouteur arXiv:2503.02122 equation (2) negation. The routine
negation_sum(x, N) returns the Laurent series of [x]_q + [-x]_q to order N. The control
case is [sqrt(2)]_q + [-sqrt(2)]_q = (q^3 - 1)/q^2 (valuation -2, coefficients -1 at q^-2
and +1 at q).

Finiteness is decided by a two-order stability test rather than a fragile low-order
trailing-zero heuristic. The series is computed at two truncation orders N1 = 140 and
N2 = 420. The sum is called finite when the index of the last nonzero coefficient is
identical at both orders and sits well below N1; it is called infinite when that index
keeps growing with N. A set of anchors (D = 2, 3, 5, 6, 7, 13 finite; 19, 43, 46, 53
infinite) is required to reproduce before any row is trusted.

For each squarefree D the script also records the classical continued fraction of
sqrt(D): the integer part a0, the period, the period length and its parity, the
palindrome check on the period body, the central element of the period, and the Pell /
fundamental-unit norm (+1 for even period length, -1 for odd).

Two continued-fraction conditions are each sufficient on this scan, with zero
counterexamples, though neither is necessary:

- period length <= 2 implies finite, and
- maximum partial quotient of the period <= 7 implies finite.

## Data files

negation_table.csv -- one row per squarefree D in [2, 200], 121 rows.

- D: squarefree integer, the radicand
- finite: True if V_D(q) is a finite Laurent polynomial, False if infinite
- lastnz_N1: index of the last nonzero coefficient at truncation order N1 = 140
- lastnz_N2: index of the last nonzero coefficient at truncation order N2 = 420
- cf_a0: integer part of the continued fraction of sqrt(D)
- period: continued-fraction period of sqrt(D), space-separated partial quotients
- period_len: length of the continued-fraction period
- period_parity: "even" or "odd" parity of the period length
- palindrome: True if the period body (period minus its last element) is a palindrome
- central: central element of the period body when it has odd length, else blank
- pell_norm: fundamental-unit norm, +1 for even period length, -1 for odd
- reduced_sum: when finite, the Laurent polynomial V_D(q) as a string; blank when infinite

## The finding

Across the 121 squarefree D in [2, 200], 63 negation sums are finite and 58 are infinite.
Trace-zero (pure square root) status is necessary but not sufficient for finiteness: the
trace-zero cases sqrt(19), sqrt(43), sqrt(46), sqrt(53) all give infinite sums. On this
scan two continued-fraction conditions are each sufficient with zero counterexamples but
neither is necessary: period length <= 2, and maximum partial quotient of the period <= 7.
The control identity [sqrt(2)]_q + [-sqrt(2)]_q = (q^3 - 1)/q^2 holds. A clean
if-and-only-if period criterion that separates the finite from the infinite cases remains
open.

## Provenance

reproduced by re-running code/negation_scan.py (which calls qreals.arithmetic.negation_sum)
and diffing the regenerated negation_table.csv against the committed copy.
