-- statement_only: the statement compiles; the cited convergence-and-equation theorem for the q-real sqrt 2 is `sorry`. The final law is proved relative to it.
import Mathlib

/-!
# sqrt2-mod2: `n = 1 (mod 3)` implies `c_n` even, for `[sqrt 2]_q = sum c_n q^n`

Status: STATEMENT ONLY in the sense of `lean.state = "statement_only"`: the one `sorry`
is `mgo_qsqrt2`, the cited fact that the q-real `[sqrt 2]_q` exists as a power series in
`Z[[q]]` and satisfies `q^2 y^2 - (q^3 - 1) y - (q^2 + 1) = 0`.  Everything else is proved
(axioms propext, Classical.choice, Quot.sound), in particular the arithmetic core
`even_of_equation`, which does NOT use an automaton.

Source statement: `results/sqrt2-mod2/statement.tex`.
Source argument: Christol's theorem plus an 11-state automaton checked with a theorem
prover for automatic sequences (evidence folder, files `C2.txt`, `walnut_commands.txt`).

```
[sqrt 2]_q = sum_{n>=0} c_n q^n
n = 1 (mod 3)  ==>  c_n = 0 (mod 2)      (all n >= 0)
```

## The sequence `c_n`, exactly as defined here

* `[x]_q` of a rational `x` is the Morier-Genoud-Ovsienko q-rational: for the (even-length)
  regular continued fraction word `R^{a_1} L^{a_2} R^{a_3} ... L^{a_{2j}}` (with `R = [[1,1],[0,1]]`,
  `L = [[1,0],[1,1]]`, so `x` is the image of `infinity` under the product), `[x]_q = A / C`,
  the ratio of the first column of the product of `R_q = [[q,1],[0,1]]` and
  `L_q = [[1,0],[1,q^-1]]` over the same word.  This ratio does not depend on the unit
  `+- q^j` ambiguity of the matrix.
* `sqrt 2 = [1; 2, 2, 2, ...]`.  The convergents `3/2, 17/12, 99/70, ...` (odd indices, so
  even-length words) are `R L^2 (R^2 L^2)^m`; `wordSqrt2 m` is this word and `qConv m` is
  `[p_m/q_m]_q` in the field of Laurent series `Q((q))`.
* `[sqrt 2]_q` is the coefficientwise limit of `qConv m` (`IsQSqrt2 f`): for every integer
  `n` the coefficient of `q^n` in `qConv m` is eventually equal to that of `f`.  This is
  the Morier-Genoud-Ovsienko definition (q-adic limit of convergents).  `IsQSqrt2.unique`
  proves the limit is unique.
* Numerical check outside Lean: with this word and these matrices the convergents for
  `m = 2, 4, 6` agree with the solution of the equation through `q^9`, `q^17`, `q^25`
  (the first differing coefficients are at `q^10`, `q^18`, `q^26`).

## Hypothesis mapping

* "all `n >= 0`, `n = 1 mod 3`": `n : N`, `n % 3 = 1`.
* "`c_n` even": `exists z : Z, f.coeff n = 2 * z` (integrality and evenness together).
* Any `f` with `IsQSqrt2 f` is covered; the theorem `mgo_qsqrt2` supplies that such an
  `f` exists and satisfies the equation, so the final statement is not vacuous.

## What is cited, not proved (`mgo_qsqrt2`)

That the limit exists in `Z[[q]]` and satisfies the quadratic equation is Proposition 4.5
of the Morier-Genoud-Ovsienko paper on q-deformed real numbers (the source cites it as such
in its evidence folder, `algebraic_equation_F2q.md`).  It is stated here as one `sorry`.

## Finite-range check by computation

Lean cannot compute the `Q((q))` object `qConv m` (Finsupp and Hahn series are not
executable).  What Lean can and does check by computation is a separate finite-range lemma
`finite_range_recurrence`, labelled as such: for the sequence `csList` defined by the
integer recurrence that the equation forces, `c_n` is even for every `n = 1 mod 3` with
`n < 40`.  That lemma is about `csList`, not about the q-real itself, and is subsumed by
`even_of_equation`, which proves the law for all `n`.  It is kept only as a computation
that is independent of the induction, and `csList` is compared with the first coefficients
from the external computation (`csList_head`).

## Not expressed

* The Christol-Walnut automaton argument itself is not formalised; the proof here is a
  direct induction on the reduction mod 2 of the recurrence.  (The source proves the same
  statement with an automaton; the two proofs are different.)
* `[sqrt 2]_q` is fixed by the even-length convergent sequence above.  The full sequence
  of convergents would give the same limit (Morier-Genoud-Ovsienko), not formalised.
-/

open LaurentPolynomial PowerSeries Finset
namespace Sqrt2Mod2
noncomputable section

theorem rec_int (y : PowerSeries ℤ) (h : X^2 * y^2 - (X^3 - 1) * y - (X^2 + 1) = 0) (k : ℕ) :
    (if 2 ≤ k then ∑ p ∈ antidiagonal (k-2), coeff p.1 y * coeff p.2 y else 0)
    - ((if 3 ≤ k then coeff (k-3) y else 0) - coeff k y)
    - ((if k = 2 then 1 else 0) + (if k = 0 then 1 else 0)) = (0:ℤ) := by
  have h' : (X^2 * (y * y) - (X^3 * y - y) - (X^2 + 1) : PowerSeries ℤ) = 0 := by
    rw [← h]; ring
  have := congrArg (coeff k) h'
  rw [map_sub, map_sub, map_sub, map_add, coeff_X_pow_mul', coeff_X_pow_mul', coeff_mul,
    coeff_X_pow, coeff_one, map_zero] at this
  simpa using this

/-- Parity of a convolution: in `ZMod 2` the sum over the antidiagonal is the diagonal term. -/
theorem conv_zmod2 (a : ℕ → ZMod 2) (m : ℕ) :
    ∑ p ∈ antidiagonal m, a p.1 * a p.2 = if Even m then a (m / 2) else 0 := by
  have hsq : ∀ x : ZMod 2, x * x = x := by decide
  have hadd : ∀ x : ZMod 2, x + x = 0 := by decide
  rw [← Finset.sum_filter_add_sum_filter_not (antidiagonal m) (fun p => p.1 = p.2)]
  have h2 : ∑ p ∈ (antidiagonal m).filter (fun p => ¬ p.1 = p.2), a p.1 * a p.2 = 0 := by
    apply Finset.sum_involution (fun p _ => (p.2, p.1))
    · intro p _; rw [mul_comm (a p.2) (a p.1)]; exact hadd _
    · intro p hp _ h
      simp only [Finset.mem_filter] at hp
      exact hp.2 (by simpa [Prod.ext_iff, eq_comm] using h)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp ⊢
      exact ⟨by omega, fun h => hp.2 h.symm⟩
    · intro p _; rfl
  rw [h2, add_zero]
  by_cases hm : Even m
  · obtain ⟨t, ht⟩ := hm
    have hF : (antidiagonal m).filter (fun p => p.1 = p.2) = {(t, t)} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_singleton, Prod.ext_iff]
      omega
    rw [hF, Finset.sum_singleton, if_pos ⟨t, ht⟩, hsq]
    congr 1; omega
  · have hF : (antidiagonal m).filter (fun p => p.1 = p.2) = ∅ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.notMem_empty, iff_false]
      rintro ⟨h1, h2⟩
      exact hm ⟨p.1, by omega⟩
    rw [hF, Finset.sum_empty, if_neg hm]

/-- **Part A.**  Any power series `y ∈ Z[[q]]` solving the equation
`q^2 y^2 - (q^3 - 1) y - (q^2 + 1) = 0` has `c_n` even for every `n ≡ 1 (mod 3)`. -/
theorem even_of_equation (y : PowerSeries ℤ)
    (h : X^2 * y^2 - (X^3 - 1) * y - (X^2 + 1) = 0) :
    ∀ n : ℕ, n % 3 = 1 → 2 ∣ coeff n y := by
  set a : ℕ → ZMod 2 := fun n => ((coeff n y : ℤ) : ZMod 2) with ha
  have hneg : ∀ x : ZMod 2, -x = x := by decide
  have hE : ∀ k : ℕ, (if 2 ≤ k then (if Even (k - 2) then a ((k - 2) / 2) else 0) else 0)
      - ((if 3 ≤ k then a (k - 3) else 0) - a k)
      - ((if k = 2 then 1 else 0) + (if k = 0 then 1 else 0)) = 0 := by
    intro k
    have h0 := congrArg (Int.cast : ℤ → ZMod 2) (rec_int y h k)
    simp only [Int.cast_sub, Int.cast_add, Int.cast_ite, Int.cast_zero, Int.cast_one, Int.cast_sum,
      Int.cast_mul] at h0
    have hc : ∑ p ∈ Finset.antidiagonal (k - 2), ((coeff p.1 y : ℤ) : ZMod 2) * ((coeff p.2 y : ℤ) : ZMod 2)
        = if Even (k - 2) then a ((k - 2) / 2) else 0 := conv_zmod2 a (k - 2)
    rw [hc] at h0
    simpa [ha] using h0
  have key : ∀ n : ℕ, n % 3 = 1 → a n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      have hEn := hE n
      by_cases h1 : n = 1
      · subst h1
        simpa using hEn
      · have h4 : 4 ≤ n := by omega
        have e2 : ¬ n = 2 := by omega
        have e0 : ¬ n = 0 := by omega
        have h3 : a (n - 3) = 0 := ih (n - 3) (by omega) (by omega)
        have hX : (if 2 ≤ n then (if Even (n - 2) then a ((n - 2) / 2) else 0) else 0) = 0 := by
          rw [if_pos (by omega)]
          by_cases he : Even (n - 2)
          · rw [if_pos he]
            obtain ⟨t, ht⟩ := he
            exact ih ((n - 2) / 2) (by omega) (by omega)
          · rw [if_neg he]
        rw [hX, if_pos (by omega), h3, if_neg e2, if_neg e0] at hEn
        simpa using hEn
  intro n hn
  have := key n hn
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp this

abbrev LP := LaurentPolynomial ℤ

def letterQ : Bool → Matrix (Fin 2) (Fin 2) LP
  | true => !![T 1, 1; 0, 1]
  | false => !![1, 0; 1, T (-1)]

def prodq (w : List Bool) : Matrix (Fin 2) (Fin 2) LP := (w.map letterQ).prod

def qvar : (LaurentSeries ℚ)ˣ := Units.mk0 (HahnSeries.single (1 : ℤ) (1 : ℚ)) (by simp)

def toLS : LP →+* LaurentSeries ℚ := LaurentPolynomial.eval₂ (Int.castRingHom _) qvar

def wordSqrt2 (m : ℕ) : List Bool := [true, false, false] ++ (List.replicate m [true, true, false, false]).flatten

def qConv (m : ℕ) : LaurentSeries ℚ :=
  toLS (prodq (wordSqrt2 m) 0 0) / toLS (prodq (wordSqrt2 m) 1 0)

def IsQSqrt2 (f : LaurentSeries ℚ) : Prop :=
  ∀ n : ℤ, ∃ M : ℕ, ∀ m ≥ M, f.coeff n = (qConv m).coeff n

theorem IsQSqrt2.unique {f g : LaurentSeries ℚ} (hf : IsQSqrt2 f) (hg : IsQSqrt2 g) : f = g := by
  ext n
  obtain ⟨M1, h1⟩ := hf n
  obtain ⟨M2, h2⟩ := hg n
  rw [h1 (max M1 M2) (le_max_left _ _), h2 (max M1 M2) (le_max_right _ _)]

theorem mgo_qsqrt2 : ∃ y : PowerSeries ℤ,
    IsQSqrt2 ((PowerSeries.map (Int.castRingHom ℚ) y : PowerSeries ℚ) : LaurentSeries ℚ) ∧
    PowerSeries.X ^ 2 * y ^ 2 - (PowerSeries.X ^ 3 - 1) * y - (PowerSeries.X ^ 2 + 1) = 0 := by
  sorry


/-- **Final statement** (relative to `mgo_qsqrt2`): for `f = [sqrt 2]_q`, `c_n` is an even
integer whenever `n = 1 (mod 3)`. -/
theorem sqrt2_mod2 (f : LaurentSeries ℚ) (hf : IsQSqrt2 f) (n : ℕ) (hn : n % 3 = 1) :
    ∃ z : ℤ, f.coeff (n : ℤ) = 2 * z := by
  obtain ⟨y, hy, heq⟩ := mgo_qsqrt2
  have hfy := hf.unique hy
  obtain ⟨z, hz⟩ := even_of_equation y heq n hn
  refine ⟨z, ?_⟩
  rw [hfy, PowerSeries.coeff_coe]
  simp [hz]

end

/-! ### Finite-range check by computation (about the recurrence, NOT the full result) -/

/-- The next coefficient forced by the equation `q^2 y^2 - (q^3-1) y - (q^2+1) = 0`,
given the coefficients `c_0, ..., c_{k-1}` (integer recurrence, with the convolution). -/
def nextC (l : List ℤ) : ℤ :=
  (if l.length = 0 then 1 else 0) + (if l.length = 2 then 1 else 0)
    + (if 3 ≤ l.length then l.getD (l.length - 3) 0 else 0)
    - (if 2 ≤ l.length then
        ∑ i ∈ Finset.range (l.length - 1), l.getD i 0 * l.getD (l.length - 2 - i) 0 else 0)

def csList : ℕ → List ℤ
  | 0 => []
  | n + 1 => csList n ++ [nextC (csList n)]

/-- The first coefficients agree with an external computation of `[sqrt 2]_q`. -/
theorem csList_head : csList 12 = [1, 0, 0, 1, 0, -2, 1, 4, -5, -7, 18, 7] := by decide +kernel

/-- **Finite-range lemma, about the recurrence-defined sequence only**: `c_n` even for
`n = 1 mod 3`, `n < 40`. -/
theorem finite_range_recurrence :
    ∀ n : Fin 40, (n : ℕ) % 3 = 1 → (csList 40).getD n 0 % 2 = 0 := by decide +kernel

end Sqrt2Mod2

#print axioms Sqrt2Mod2.even_of_equation
#print axioms Sqrt2Mod2.sqrt2_mod2
#print axioms Sqrt2Mod2.finite_range_recurrence
#print axioms Sqrt2Mod2.csList_head
