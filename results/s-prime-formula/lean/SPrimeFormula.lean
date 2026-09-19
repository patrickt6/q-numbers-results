-- statement_only: the statement compiles, the proof is `sorry`. The result is already published (see header), so only the statement is formalised.
import Mathlib

/-!
# s-prime-formula: `2 S'(1) = d deg S + a^-1 - a` for the reduced denominator of `[a/d]_q`

Status: STATEMENT ONLY (`lean.state = "statement_only"`); no proof attempted.

PUBLISHED SOURCE (as recorded in `results.json` for this id): this formula is already
known: Lasker, arXiv:2309.10819, Lemma 6.1 and Corollary 6.2.  It was derived
independently and found afterwards to be published.

Source statement: `results/s-prime-formula/statement.tex`.

```
x = a/d,  0 < a < d,  gcd(a, d) = 1
S = reduced monic denominator of [x]_q
2 S'(1) = d deg S + a^{-1} - a          (a^{-1} in (0, d) the inverse of a mod d)
```

## Formalisation choices (all recorded)

* `[a/d]_q` is the Morier-Genoud-Ovsienko q-rational: choose a word `w` in
  `R = [[1,1],[0,1]]`, `L = [[1,0],[1,1]]` whose classical product `M` has first column
  `(a, d)` (so `M . infinity = a/d`); then `[a/d]_q = A / C` with `(A, C)` the first column
  of the product of `R_q = [[q,1],[0,1]]` and `L_q = [[1,0],[1,q^-1]]` over the same word.
  The ratio does not depend on the choice of `w` (any two choices differ by right
  factors `R^k`, which multiply the first column by `q^k`) nor on the unit ambiguity.
* "Reduced monic denominator" `S`: a monic `S` in `Z[q]` with `R` in `Z[q]` such that
  `A / C = R / S` (as `A * S = C * R` in `Z[q, q^-1]`) and `R`, `S` coprime over `Q[q]`.
  The theorem is stated for every such pair `(R, S)`; that such a pair exists with `S`
  monic (i.e. that the reduced denominator is monic) is part of the published statement and
  is NOT asserted separately here.  Uniqueness of `S` is automatic (reduced fraction with
  monic denominator).
* `a^{-1}`: an integer `b` with `0 < b < d` and `a b = 1 (mod d)`.
* `S'(1)` is the derivative of the polynomial `S` evaluated at `1`; `deg S` is `natDegree`.
* Numerical sanity check outside Lean: with these conventions the formula holds for every
  coprime `0 < a < d <= 25` (recorded in the running report).

## Not expressed

* Existence of a monic reduced denominator (see above).
* Lasker's other statements in the same section.
-/

open LaurentPolynomial

namespace SPrimeFormula
noncomputable section

abbrev LP := LaurentPolynomial ℤ

/-- Letters: `true` is `R`, `false` is `L`.  Classical matrices. -/
def letterZ : Bool → Matrix (Fin 2) (Fin 2) ℤ
  | true => !![1, 1; 0, 1]
  | false => !![1, 0; 1, 1]

/-- q-deformed letters: `R_q = [[q, 1], [0, 1]]`, `L_q = [[1, 0], [1, q^-1]]`. -/
def letterQ : Bool → Matrix (Fin 2) (Fin 2) LP
  | true => !![T 1, 1; 0, 1]
  | false => !![1, 0; 1, T (-1)]

/-- Classical product of a word. -/
def prodc (w : List Bool) : Matrix (Fin 2) (Fin 2) ℤ := (w.map letterZ).prod

/-- The q-deformed product of the same word. -/
def prodq (w : List Bool) : Matrix (Fin 2) (Fin 2) LP := (w.map letterQ).prod

/-- **The `S'(1)` formula** (Lasker, arXiv:2309.10819, Lemma 6.1 and Corollary 6.2). -/
theorem s_prime_formula {a d : ℤ} (ha : 0 < a) (had : a < d) (hcop : IsCoprime a d)
    (w : List Bool) (hw1 : prodc w 0 0 = a) (hw2 : prodc w 1 0 = d)
    (R S : Polynomial ℤ) (hS : S.Monic)
    (hRS : IsCoprime (R.map (Int.castRingHom ℚ)) (S.map (Int.castRingHom ℚ)))
    (hfrac : prodq w 0 0 * Polynomial.toLaurent S = prodq w 1 0 * Polynomial.toLaurent R)
    (b : ℤ) (hb0 : 0 < b) (hbd : b < d) (hab : a * b ≡ 1 [ZMOD d]) :
    2 * (Polynomial.derivative S).eval 1 = d * S.natDegree + b - a := by
  sorry

end
end SPrimeFormula

#print axioms SPrimeFormula.s_prime_formula
