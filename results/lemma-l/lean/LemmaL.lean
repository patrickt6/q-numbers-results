-- statement_only: the statement compiles, the proof is `sorry` (the source proof needs Lemma L at primes, the monomial law and a cited first-jet identity).
import Mathlib

/-!
# lemma-l: Lemma L at odd prime powers follows from downward closure (DC) alone

Status: STATEMENT ONLY (`lean.state = "statement_only"`).  The single theorem below ends in
`sorry`.  The argument in the source is short to read but is not elementary to formalise: it
uses Lemma L at the prime `n = p` (a separate proved lemma), the universal monomial law
(Kronecker's theorem on algebraic integers with all conjugates of modulus 1), the first jet
`(A - D)'(1) = (d+1) s` (a cited result), Kummer valuations of binomial coefficients, and a
valuation computation in `Z[zeta_{p^a}]`.

Source statement: `results/lemma-l/statement.tex`.  Source argument: the proof of Theorem A
and Corollary B in the write-up for this result (odd prime powers, pi-adic route).

```
p odd prime, a >= 1, Lambda_q = [[A,B],[C,D]]
(DC):  Phi_{p^a} | C  =>  Phi_{p^j} | C     (1 <= j < a)
(DC)  =>  ( Phi_{p^a} | C  =>  A = D  (mod Phi_{p^a}) )
```

## What Lambda_q is (formalised choices)

* `d` is a nonsquare integer, `(r, s)` its FUNDAMENTAL Pell solution (`r, s >= 1`,
  `r^2 - d s^2 = 1`, `s` minimal among positive solutions), and
  `Lambda = [[r, d s], [s, r]]` the fundamental automorph.  This is the setting of the
  write-up section on the Pell automorph, where `Lambda_q = rho(Lambda)`.
* `rho` is the q-deformation on nonnegative `SL(2, Z)` matrices, defined through the unique
  word in `R = [[1,1],[0,1]]` and `L = [[1,0],[1,1]]` with classical product `Lambda`
  (`R_q = [[q,1],[0,1]]`, `L_q = [[1,0],[1,q^-1]]`).  The statement quantifies over every
  word `w` with classical product `Lambda` (there is exactly one; uniqueness is not needed
  here).  `Lambda_q` is `prodq w`.
* `rho(Lambda)` is defined only up to a unit `+- q^j` in the write-up (its "sign
  convention" paragraph).  Both `Phi | C` and `Phi | A - D` are invariant under
  multiplying the whole matrix by a unit, so the statement does not depend on that choice.
* Divisibility and congruences are in `Z[q, q^-1] = LaurentPolynomial Z`; `Phi_n` is the
  image of `Polynomial.cyclotomic n Z`.  `A = D (mod Phi)` is `Phi | A - D`.
* Downward closure (DC) is a HYPOTHESIS `hDC` on this particular `Lambda_q`, as in the source
  ("stated relative to DC").  It is a statement about `C` only.

## Hypothesis mapping

* "`p` odd prime": `hp : p.Prime`, `hp2 : p ≠ 2`.  "`a >= 1`": `ha : 1 ≤ a`.
* `(DC)`: `hDC`, quantified over `j` with `1 <= j < a` and conditional on `Phi_{p^a} | C`.
* conclusion: `Phi_{p^a} | C` implies `Phi_{p^a} | A - D`.

## Not expressed

* Nothing dropped from `statement.tex`.  Note (for review) that the source argument also
  uses Lemma L at the prime level as a proved input; the statement here does not assume it,
  so it asserts that too (this is what `a = 1` says).
-/

open LaurentPolynomial

namespace LemmaL
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

/-- Classical product of a word, left to right. -/
def prodc (w : List Bool) : Matrix (Fin 2) (Fin 2) ℤ := (w.map letterZ).prod

/-- The q-deformed product of the same word: `rho` of the classical product. -/
def prodq (w : List Bool) : Matrix (Fin 2) (Fin 2) LP := (w.map letterQ).prod

/-- "`Phi_n` divides `f`" in `Z[q, q^-1]`. -/
def CycDvd (n : ℕ) (f : LP) : Prop := Polynomial.toLaurent (Polynomial.cyclotomic n ℤ) ∣ f

/-- **Lemma L at odd prime powers from downward closure.** -/
theorem lemma_L_prime_power {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 1 ≤ a)
    {d r s : ℤ} (hd : 0 < d) (hns : ¬ IsSquare d) (hr : 0 < r) (hs : 0 < s)
    (hpell : r ^ 2 - d * s ^ 2 = 1)
    (hfund : ∀ r' s' : ℤ, 0 < r' → 0 < s' → r' ^ 2 - d * s' ^ 2 = 1 → s ≤ s')
    (w : List Bool) (hw : prodc w = !![r, d * s; s, r])
    (hDC : CycDvd (p ^ a) (prodq w 1 0) →
      ∀ j : ℕ, 1 ≤ j → j < a → CycDvd (p ^ j) (prodq w 1 0)) :
    CycDvd (p ^ a) (prodq w 1 0) → CycDvd (p ^ a) (prodq w 0 0 - prodq w 1 1) := by
  sorry

end
end LemmaL
