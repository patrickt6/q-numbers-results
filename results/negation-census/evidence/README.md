# negation-census-d6000

Exact census of the negation sum F(d) = [sqrt(d)]_q + [-sqrt(d)]_q for every nonsquare
integer d with 2 <= d <= 6000 (5923 values). This is the dataset behind the finiteness
statistics quoted in the negation-sum writeups (1064 finite, 4859 infinite) and the
computational evidence surrounding the quadratic-irrational conjecture.

## Background, in three sentences

For each nonsquare d, the sum F(d) is a single rational function of q: writing (r_d, s_d)
for the fundamental solution of Pell's equation r^2 - d s^2 = 1 and Lambda_q for the
q-deformation of the automorph matrix [[r_d, d s_d], [s_d, r_d]], one has
F(d) = (A - D)/C where A, C, D are entries of Lambda_q. F(d) is a finite Laurent
polynomial exactly when C divides A - D in Z[q, q^{-1}] up to a monomial; otherwise it is
an infinite power series. Every row of the census performs this divisibility test
exactly, no floating point anywhere.

## What "coefficients" means here (read this if the columns are confusing)

Two different polynomial objects appear, and they live on different sides of the test.

1. The SERIES coefficients: F(d), expanded as a Laurent series in q, has integer
   coefficients c_j (F(d) = sum c_j q^j). "F(d) finite" means all but finitely many c_j
   are zero. The census does NOT store these coefficients; it stores the exact verdict.

2. The CORE polynomial: when F(d) is infinite, write F(d) = N(q)/D(q) in lowest terms.
   The denominator D(q) factors as (monomial) x (cyclotomic factors) x (one remaining
   factor). That remaining non-cyclotomic, non-monomial factor is called the INFINITE
   CORE. Its survival in the denominator is exactly what makes the series infinite, and
   the last two columns describe it. Example: for d = 19 the core is
   q^6 + 2q^5 + 2q^4 + 3q^3 + 2q^2 + 2q + 1, an irreducible palindromic sextic.

## Columns

| column | meaning |
|---|---|
| d | the nonsquare integer, 2 <= d <= 6000 |
| squarefree | whether d is squarefree (True/False); finiteness does NOT require it (d = 8, 18, 32 are finite) |
| r_d | numerator of the fundamental Pell solution: smallest r with r^2 - d s^2 = 1, s >= 1 |
| s_d | denominator of the fundamental Pell solution |
| cf_period_length | period length of the regular continued fraction of sqrt(d) |
| cf_period_parity | parity of that period (odd iff the negative Pell equation x^2 - d y^2 = -1 is solvable) |
| is_finite | exact verdict: True iff C divides A - D up to a monomial, i.e. F(d) is a finite Laurent polynomial |
| S_is_cyc_squarefree_product | True iff the q-denominator S of [r_d/s_d]_q is a squarefree product of cyclotomic polynomials |
| infinite_core_palindromic | infinite rows only: True iff the core polynomial is palindromic (coefficients read the same in both directions); empty for finite rows |
| infinite_core_degree | infinite rows only: degree of the core polynomial; empty for finite rows |

## Headline facts contained in this table

- 1064 of 5923 values are finite; 4859 are infinite. Finiteness is not sparse.
- All 4859 infinite cores are palindromic, without exception.
- Core degree tracks the continued-fraction period length almost linearly.
- Finiteness does not require d squarefree: 8 = 2*2^2, 18 = 2*3^2, 32 = 2*4^2 are finite.

## Reproducing

The test per d: compute the fundamental Pell solution (r_d, s_d); express the automorph
as a word in the modular generators R = [[1,1],[0,1]] and S = [[0,-1],[1,0]]; substitute
the q-deformed generators R_q = [[q,1],[0,1]], S_q = [[0,-q^{-1}],[1,0]]; read off
A, C, D; perform exact polynomial division of A - D by C in Z[q, q^{-1}]. Everything is
integer arithmetic on polynomial coefficients.
