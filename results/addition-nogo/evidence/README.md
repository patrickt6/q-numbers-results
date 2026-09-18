# q-Gosper Engine

## What was computed

A q-deformed bihomographic continued-fraction engine extending the classical integer-state machine (2x4 state matrix for bilinear functions) to the MGO q-parameter setting. The engine computes a 2x4 Laurent-polynomial state by right-multiplying with Kronecker-factored q-block products derived from the regular-continued-fraction representation of rational inputs x and y. The engine ingests partial quotients from the even-length regular CFs of both x and y to compute the output of bilinear operations (addition, subtraction, multiplication, division) on the q-real series [x]_q and [y]_q.

The headline result: the engine computes [x]_q + [y]_q exactly (verified against the qreals package to order q^23 on all 24 rational-pair test cases), but provably does not compute [x+y]_q (the q-deformation of the arithmetic sum), with clean divergence at q^0 and well-characterized deficit D_{x,y}(q) = [x+y]_q - ([x]_q + [y]_q).

## Files in this folder

**deficit_closed_forms.csv**
- Extracted table of closed-form expressions for the addition deficit on four rational pairs where x+y is an integer.
- Columns: x, y, x_plus_y (the integer sum), D_of_q (the deficit as a symbolic expression in q).
- The symbolic expressions use q-integer notation (e.g., [k]_q means the q-integer (1-q^k)/(1-q)).
- Examples show patterns like (q^m - 1)/[k]_q on the integer-sum family; the closed-form closed form for rational x,y remains an open question.

**code/q_gosper.py**
- The main q-engine implementation.
- Key functions:
  - `q_int(n)`, `q_int_qinv(n)`: q-integer [n]_q and [n]_{1/q}.
  - `cf_terms(fr)`, `make_even_length(a)`, `q_cf(fr)`: even-length regular-continued-fraction extraction matching the qreals package convention.
  - `q_block(i, a)`: the 2x2 MGO q-continuant block at position i with digit a; alternates between [a]_q,q^a and [a]_{1/q},q^{-a} to match the qreals recursion exactly.
  - `q_real_rational(fr)`: [x]_q as a rational function in q via the q-block product.
  - `state_matrix(op)`: the 2x4 coefficient matrix for operations (add, sub, mul, div).
  - `q_gosper_state(x, y, op)`: the full 2x4 q-state after ingesting the CFs of x and y.
  - `q_gosper(x, y, op)`: the bilinear value (first-column ratio) of the q-state; for op='add' this is [x]_q + [y]_q, NOT [x+y]_q.
  - `laurent_coeffs(expr, hi, lo)`: extracts integer Laurent coefficients of a q-rational from exponent lo to hi.
  - `taylor_coeffs(expr, N)`: first N Taylor coefficients.
- Dependencies: sympy (symbolic algebra).
- This is a pure-computation script with no external project dependencies (qreals is used only in the verification harness verify_q_gosper.py, not here).

## What the engine does and does not do

**Positive arm:** The engine computes z([x]_q, [y]_q) exactly for any bilinear operation z, matching the qreals package coefficient-for-coefficient. Over 24 test rational pairs to order q^23, the addition output [x]_q + [y]_q is bit-identical to qreals.q_rational expanded via qreals.q_real_truncated. Multiplication [x]_q * [y]_q is also exact on all 24 pairs.

**Negative arm:** The engine does NOT compute [x+y]_q, the q-deformed series of the arithmetic sum. For any pair (x, y) with x, y > 1, the engine returns [x]_q + [y]_q (sum of two separate q-series, each with constant term 1) whereas [x+y]_q is a single q-series with constant term 1. They diverge at q^0: the deficit D has D(0) = -1 always.

**Why this is not a bug:** The MGO deformation map x |-> [x]_q is not additive. The continuous-fraction proof skeleton (Kronecker factorization, Lemma 1, commutation, tensor structure) carries over to the q-case perfectly; the engine computes what the proof provides, which is the bilinear form in [x]_q and [y]_q, not their sum's deformation.

## The deficit invariants

The deficit D_{x,y}(q) = [x+y]_q - ([x]_q + [y]_q) satisfies two universal identities:

1. D(1) = 0 always, because at q=1 the deformation specializes to the identity: [x]_1 = x, so [x+y]_1 = x+y = [x]_1 + [y]_1.
2. D(0) = -1 for all x, y > 1, the leading-order divergence: [x]_q has constant term 1, so [x]_q + [y]_q has constant term 2, while [x+y]_q has constant term 1.

The CSV deficit_closed_forms.csv lists four pairs with integer sums; all show clean factorizations like (q^k - 1)/[m]_q, suggesting structure worth probing at scale across larger rational-pair families (integer slice, then rational denominators). The engine is the tool to map D on the full family and search for a closed-form pattern.

## How to use the code

```python
from fractions import Fraction
from q_gosper import q_gosper, taylor_coeffs

# Compute [x]_q + [y]_q for x=3/2, y=5/2
x, y = Fraction(3, 2), Fraction(5, 2)
result = q_gosper(x, y, op='add')

# Extract the first 12 Taylor coefficients
coeffs = taylor_coeffs(result, 12)
print(coeffs)  # [2, 1, 1, 0, 0, 0, -1, -1, -1, -1, -1, -1]
```

The script has no external project imports; only sympy is required.

## What was tested

Verification harness verify_q_gosper.py (not shipped in this folder) tests the engine on 24 rational pairs (x, y) with x, y > 1 and x, y <= 20 denominator. Two arms:

1. **Positive:** [x]_q + [y]_q matches qreals.q_rational(...).series(...) and qreals.q_real_truncated(...) to order q^23 on all 24 pairs. Result: 24/24 pass.
2. **Negative:** [x+y]_q (computed via qreals) diverges from the engine's [x]_q + [y]_q on all 24 pairs, with first divergence at q^0 on all pairs. Deficit D is clean Laurent polynomial in q.

Result: OVERALL PASS. The engine computes what the proof gives (the bilinear form in q-reals), and does not compute the deformed sum (a genuinely different object).


924bb610

## References


## How to verify


To verify:
2. Or re-run the code/q_gosper.py script and diff the CSV outputs against deficit_closed_forms.csv
