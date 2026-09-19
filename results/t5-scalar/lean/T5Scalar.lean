import Mathlib

/-!
# t5-scalar: the scalar identity `q (A - D) = (q - 1) (q B + C)`

Source statement: `results/t5-scalar/statement.tex`.

```
Lambda_q = ( A  B )
           ( C  D )
q (A - D) = (q - 1) (q B + C)
C | B  <->  C | (A - D)
```

## What is formalised (read this before trusting the theorem)

* The ring is `LP = LaurentPolynomial ℤ = ℤ[q, q⁻¹]` with `q = T 1`.
  Divisibility `C ∣ B` is divisibility in this ring, so it is automatically
  "up to monomials" (monomials `± q^k` are the units).
* The q-deformation `rho` is the one of the write-up: `R_q = [[q,1],[0,1]]`,
  `S_q = [[0,-1/q],[1,0]]`, and `L_q = S_q R_q⁻¹ S_q⁻¹ = [[1,0],[1,1/q]]`
  (this last equality is the Lean theorem `Sq_mul_Rqinv_mul_Sqinv`).
* `rho` is used only on matrices with nonnegative entries.  Such a matrix in
  `SL(2, ℤ)` is a product of `R = [[1,1],[0,1]]` and `L = [[1,0],[1,1]]` in
  exactly one way (`exists_word`, `prodc_injective`, both proved here), and
  `rho` of that product is the product of `R_q` and `L_q` in the same order
  (`prodq`).  The fundamental Pell automorph `Lambda = [[r, d s],[s, r]]` with
  `r, s ≥ 1`, `d ≥ 1` has nonnegative entries, so this covers it.
* The theorem quantifies over every word `w` with classical product `Lambda`,
  and every such word is the same word (`prodc_injective`).  So `Lambda_q` in
  the theorem is `prodq w` for that word.  The write-up's `rho(Lambda)` is
  defined only up to a unit `± q^j`; property (P) is homogeneous, and
  divisibility is unit invariant, so this choice of representative does not
  affect either conclusion.

Hypothesis mapping, statement.tex line by line:

* `Lambda = [[r, d s],[s, r]]`, `r² - d s² = 1`:  hypotheses `hdet`, with
  `0 < r`, `0 < s`, `0 < d`.  (Fundamental / minimal `s` is NOT used; the
  result holds for every positive solution.  This is a generalisation of the
  write-up, recorded in status.json.)
* `Lambda_q = [[A,B],[C,D]]`:  `X = prodq w`, `A = X 0 0`, `B = X 0 1`,
  `C = X 1 0`, `D = X 1 1`.
* `q (A - D) = (q - 1) (q B + C)`:  first conjunct of `t5_scalar`.
* `C | B ↔ C | (A - D)`:  second conjunct of `t5_scalar`.

The proof follows the write-up: property (P) holds for `I`, `R_q`, `L_q`
(Lemma 1), is preserved by `X ↦ R_q X R_q` and `X ↦ L_q X L_q` (Lemma 3 with
`k = 1`), and the R,L word of an equal-diagonal matrix is a palindrome
(Lemma 4, proved by `prodc_injective` and a transpose/reversal identity).
Only the case `k = 1` of Lemma 3 is needed because palindromes are peeled one
letter at a time.  Lemma 2 (symmetries) and Theorem 6 (general `t`) are NOT
formalised, since they are not needed for positive equal-diagonal matrices.
-/

open LaurentPolynomial

namespace T5Scalar

/-! ### Generic part: any commutative ring `R` with `q * qi = 1`

Everything about `R_q`, `L_q` and property (P) is proved once, over an
arbitrary commutative ring, and then used twice: over `ℤ[q, q⁻¹]` (the
q-deformation) and over `ℤ` with `q = qi = 1` (the classical matrices). -/

section Generic

variable {R : Type*} [CommRing R]

/-- `R_q = [[q, 1], [0, 1]]`. -/
def RG (q : R) : Matrix (Fin 2) (Fin 2) R := !![q, 1; 0, 1]

/-- `L_q = [[1, 0], [1, q⁻¹]]`, with `qi` standing for `q⁻¹`. -/
def LG (qi : R) : Matrix (Fin 2) (Fin 2) R := !![1, 0; 1, qi]

/-- Property (P) of the write-up: `q (A - D) = (q - 1) (q B + C)`,
for `X = [[A, B], [C, D]]`. -/
def PG (q : R) (X : Matrix (Fin 2) (Fin 2) R) : Prop :=
  q * (X 0 0 - X 1 1) = (q - 1) * (q * X 0 1 + X 1 0)

theorem PG_mk (q a b c d : R) :
    PG q !![a, b; c, d] ↔ q * (a - d) = (q - 1) * (q * b + c) := by
  simp [PG]

theorem PG_one (q : R) : PG q (1 : Matrix (Fin 2) (Fin 2) R) := by
  simp [PG]

theorem PG_R (q : R) : PG q (RG q) := by
  simp [PG, RG]; ring

theorem PG_L (q qi : R) (hq : q * qi = 1) : PG q (LG qi) := by
  simp [PG, LG]; linear_combination (-1 : R) * hq

/-- Lemma 3 of the write-up, `k = 1`, `R` case. -/
theorem PG_RXR (q : R) (X : Matrix (Fin 2) (Fin 2) R) (h : PG q X) :
    PG q (RG q * X * RG q) := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, X = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two X⟩
  rw [PG_mk] at h
  simp only [RG, Matrix.mul_fin_two, PG_mk]
  linear_combination q * h

/-- Lemma 3 of the write-up, `k = 1`, `L` case. -/
theorem PG_LXL (q qi : R) (hq : q * qi = 1) (X : Matrix (Fin 2) (Fin 2) R) (h : PG q X) :
    PG q (LG qi * X * LG qi) := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, X = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two X⟩
  rw [PG_mk] at h
  simp only [LG, Matrix.mul_fin_two, PG_mk]
  linear_combination qi * h - (a + b + d * qi) * hq

/-- Letters: `true` is `R`, `false` is `L`. -/
def gG (q qi : R) : Bool → Matrix (Fin 2) (Fin 2) R
  | true => RG q
  | false => LG qi

/-- Product of the letters of a word, left to right. -/
def prodG (q qi : R) (w : List Bool) : Matrix (Fin 2) (Fin 2) R :=
  (w.map (gG q qi)).prod

@[simp] theorem prodG_nil (q qi : R) : prodG q qi [] = 1 := by simp [prodG]

@[simp] theorem prodG_cons (q qi : R) (x : Bool) (w : List Bool) :
    prodG q qi (x :: w) = gG q qi x * prodG q qi w := by simp [prodG]

theorem prodG_append (q qi : R) (v w : List Bool) :
    prodG q qi (v ++ w) = prodG q qi v * prodG q qi w := by simp [prodG]

/-- Property (P) holds for the product of every palindromic word
(Proposition 5 of the write-up, in the positive case). -/
theorem PG_prodG_palin (q qi : R) (hq : q * qi = 1) :
    ∀ (n : ℕ) (w : List Bool), w.length ≤ n → w.reverse = w → PG q (prodG q qi w) := by
  intro n
  induction n with
  | zero =>
    intro w hw _
    have : w = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    simpa using PG_one q
  | succ n ih =>
    intro w hw hpal
    match w with
    | [] => simpa using PG_one q
    | x :: rest =>
      rcases List.eq_nil_or_concat rest with hr | ⟨m, y, hr⟩
      · subst hr
        cases x
        · simpa [gG] using PG_L q qi hq
        · simpa [gG] using PG_R q
      · subst hr
        simp only [List.concat_eq_append] at hw hpal ⊢
        have hrev : (x :: (m ++ [y])).reverse = y :: (m.reverse ++ [x]) := by simp
        rw [hrev] at hpal
        have hxy : y = x := by
          have := congrArg List.head? hpal
          simpa using this
        subst hxy
        have hm : m.reverse = m := by
          have := congrArg List.tail hpal
          simpa using this
        have hmlen : m.length ≤ n := by simp at hw; omega
        have := ih m hmlen hm
        have hp : prodG q qi (y :: (m ++ [y])) = gG q qi y * (prodG q qi m * gG q qi y) := by
          simp [prodG_append]
        rw [hp, ← mul_assoc]
        cases y
        · exact PG_LXL q qi hq _ this
        · exact PG_RXR q _ this

theorem map_prodG {S : Type*} [CommRing S] (f : R →+* S) (q qi : R) (w : List Bool) :
    (prodG q qi w).map f = prodG (f q) (f qi) w := by
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [prodG_cons, prodG_cons, Matrix.map_mul, ih]
    congr 1
    cases x <;> (ext i j; fin_cases i <;> fin_cases j <;> simp [gG, RG, LG])

end Generic

/-! ### The classical (integer) side -/

section Classical

/-- 2 by 2 integer matrices. -/
abbrev IMat := Matrix (Fin 2) (Fin 2) ℤ

/-- The classical product of a word in `R = [[1,1],[0,1]]` and `L = [[1,0],[1,1]]`. -/
def prodc (w : List Bool) : IMat := prodG (1 : ℤ) 1 w

/-- `J M^T J = [[d, b], [c, a]]` for `M = [[a, b], [c, d]]`. -/
def flipM (M : IMat) : IMat := !![M 1 1, M 0 1; M 1 0, M 0 0]

theorem flipM_mul (M N : IMat) : flipM (M * N) = flipM N * flipM M := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, M = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two M⟩
  obtain ⟨e, f, g, h, rfl⟩ : ∃ a b c d, N = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two N⟩
  simp only [flipM, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

theorem flipM_one : flipM 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [flipM]

theorem flipM_gG (x : Bool) : flipM (gG (1 : ℤ) 1 x) = gG (1 : ℤ) 1 x := by
  cases x <;> (ext i j; fin_cases i <;> fin_cases j <;> simp [flipM, gG, RG, LG])

/-- Transposition-and-swap reverses the word (Lemma 4 (ii), the identity part). -/
theorem flipM_prodc (w : List Bool) : flipM (prodc w) = prodc w.reverse := by
  induction w with
  | nil => simpa [prodc] using flipM_one
  | cons x w ih =>
    have h1 : prodc (x :: w) = gG (1 : ℤ) 1 x * prodc w := by simp [prodc]
    rw [h1, flipM_mul, ih, flipM_gG]
    simp [prodc, prodG_append]

/-- Nonnegative entries and determinant one. -/
def Good (M : IMat) : Prop :=
  0 ≤ M 0 0 ∧ 0 ≤ M 0 1 ∧ 0 ≤ M 1 0 ∧ 0 ≤ M 1 1 ∧ M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1

theorem good_one : Good 1 := by simp [Good]

theorem RG_mul (a b c d : ℤ) :
    RG (1 : ℤ) * !![a, b; c, d] = !![a + c, b + d; c, d] := by
  simp only [RG, Matrix.mul_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp

theorem LG_mul (a b c d : ℤ) :
    LG (1 : ℤ) * !![a, b; c, d] = !![a, b; a + c, b + d] := by
  simp only [LG, Matrix.mul_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp

theorem good_prodc (w : List Bool) : Good (prodc w) := by
  induction w with
  | nil => simpa [prodc] using good_one
  | cons x w ih =>
    have h1 : prodc (x :: w) = gG (1 : ℤ) 1 x * prodc w := by simp [prodc]
    rw [h1]
    obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d, prodc w = !![a, b; c, d] :=
      ⟨_, _, _, _, Matrix.eta_fin_two _⟩
    rw [hM] at ih ⊢
    obtain ⟨h0, hb, h2, h3, h4⟩ := ih
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at h0 hb h2 h3 h4
    cases x
    · simp only [gG, LG_mul, Good, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      refine ⟨h0, hb, by linarith, by linarith, by linarith⟩
    · simp only [gG, RG_mul, Good, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      refine ⟨by linarith, by linarith, h2, h3, by linarith⟩

/-- Existence half of Lemma 4 (i): a nonnegative matrix of determinant one is a
product of `R` and `L`. -/
theorem exists_word_aux : ∀ (n : ℕ) (a b c d : ℤ), a + b + c + d ≤ n → 0 ≤ a → 0 ≤ b →
    0 ≤ c → 0 ≤ d → a * d - b * c = 1 → ∃ w, prodc w = !![a, b; c, d] := by
  intro n
  induction n with
  | zero =>
    intro a b c d hs ha hb hc hd hdet
    have hb0 : b = 0 := by omega
    have hc0 : c = 0 := by omega
    have ha0 : a = 0 := by omega
    subst hb0; subst hc0; subst ha0; simp at hdet
  | succ n ih =>
    intro a b c d hs ha hb hc hd hdet
    by_cases hR : c ≤ a ∧ d ≤ b
    · obtain ⟨hca, hdb⟩ := hR
      have hcd : 0 < c + d := by
        by_contra hcon
        have hc0 : c = 0 := by omega
        have hd0 : d = 0 := by omega
        subst hc0; subst hd0; simp at hdet
      obtain ⟨w, hw⟩ := ih (a - c) (b - d) c d (by omega) (by omega) (by omega) hc hd
        (by linarith)
      refine ⟨true :: w, ?_⟩
      have : prodc (true :: w) = RG (1 : ℤ) * prodc w := by simp [prodc, gG]
      rw [this, hw, RG_mul]
      congr 1 <;> simp
    · by_cases hL : a ≤ c ∧ b ≤ d
      · obtain ⟨hac, hbd⟩ := hL
        have hab : 0 < a + b := by
          by_contra hcon
          have ha0 : a = 0 := by omega
          have hb0 : b = 0 := by omega
          subst ha0; subst hb0; simp at hdet
        obtain ⟨w, hw⟩ := ih a b (c - a) (d - b) (by omega) ha hb (by omega) (by omega)
          (by linarith)
        refine ⟨false :: w, ?_⟩
        have : prodc (false :: w) = LG (1 : ℤ) * prodc w := by simp [prodc, gG]
        rw [this, hw, LG_mul]
        congr 1 <;> simp
      · -- neither `R` nor `L` peels: only `M = 1` is possible
        have hcases : (a < c ∨ b < d) ∧ (c < a ∨ d < b) := by
          constructor
          · by_contra hh; push Not at hh; exact hL ⟨by omega, by omega⟩
          · by_contra hh; push Not at hh; exact hR ⟨by omega, by omega⟩
        rcases hcases with ⟨h1 | h1, h2 | h2⟩
        · omega
        · exfalso
          nlinarith [mul_nonneg (show 0 ≤ c - 1 - a by omega) hd,
            mul_nonneg (show 0 ≤ b - 1 - d by omega) (show 0 ≤ c - 1 by omega)]
        · have hb0 : b = 0 := by
            nlinarith [mul_nonneg (show 0 ≤ a - c - 1 by omega) hd,
              mul_nonneg (show 0 ≤ d - b - 1 by omega) (show 0 ≤ c by omega)]
          have hc0 : c = 0 := by
            nlinarith [mul_nonneg (show 0 ≤ a - c - 1 by omega) hd,
              mul_nonneg (show 0 ≤ d - b - 1 by omega) (show 0 ≤ c by omega)]
          subst hb0; subst hc0
          have ha1 : a = 1 := by nlinarith
          have hd1 : d = 1 := by nlinarith
          subst ha1; subst hd1
          exact ⟨[], by
            ext i j; fin_cases i <;> fin_cases j <;> simp [prodc]⟩
        · omega

theorem exists_word (M : IMat) (hM : Good M) : ∃ w, prodc w = M := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, M = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two M⟩
  obtain ⟨h0, h1, h2, h3, h4⟩ := hM
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at h0 h1 h2 h3 h4
  exact exists_word_aux (a + b + c + d).toNat a b c d (by omega) h0 h1 h2 h3 h4

theorem gc_mul_cancel (x : Bool) (M N : IMat) (h : gG (1 : ℤ) 1 x * M = gG (1 : ℤ) 1 x * N) :
    M = N := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, M = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two M⟩
  obtain ⟨e, f, g, k, rfl⟩ : ∃ a b c d, N = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two N⟩
  cases x
  · simp only [gG, LG_mul] at h
    have := congrArg (fun X : IMat => (X 0 0, X 0 1, X 1 0, X 1 1)) h
    simp at this
    obtain ⟨h1, h2, h3, h4⟩ := this
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> omega
  · simp only [gG, RG_mul] at h
    have := congrArg (fun X : IMat => (X 0 0, X 0 1, X 1 0, X 1 1)) h
    simp at this
    obtain ⟨h1, h2, h3, h4⟩ := this
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> omega

/-- `R M₁ ≠ L M₂` for nonnegative determinant-one `M₁, M₂`: the first letter of the
word is determined (uniqueness half of Lemma 4 (i)). -/
theorem R_ne_L (M₁ M₂ : IMat) (h₁ : Good M₁) (h₂ : Good M₂) :
    gG (1 : ℤ) 1 true * M₁ ≠ gG (1 : ℤ) 1 false * M₂ := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, M₁ = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two M₁⟩
  obtain ⟨e, f, g, k, rfl⟩ : ∃ a b c d, M₂ = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two M₂⟩
  obtain ⟨h0, h1, h2, h3, h4⟩ := h₁
  obtain ⟨j0, j1, j2, j3, j4⟩ := h₂
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at h0 h1 h2 h3 h4 j0 j1 j2 j3 j4
  intro h
  simp only [gG, RG_mul, LG_mul] at h
  have := congrArg (fun X : IMat => (X 0 0, X 0 1, X 1 0, X 1 1)) h
  simp at this
  obtain ⟨k1, k2, k3, k4⟩ := this
  have ha : a = 0 := by omega
  have hb : b = 0 := by omega
  subst ha; subst hb
  simp at h4

theorem prodc_ne_one_cons (x : Bool) (w : List Bool) : prodc (x :: w) ≠ 1 := by
  intro h
  have h1 : prodc (x :: w) = gG (1 : ℤ) 1 x * prodc w := by simp [prodc]
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d, prodc w = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hg := good_prodc w
  rw [hM] at hg h1
  obtain ⟨h0, hb, h2, h3, h4⟩ := hg
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at h0 hb h2 h3 h4
  rw [h1] at h
  cases x
  · simp only [gG, LG_mul] at h
    have := congrArg (fun X : IMat => (X 0 0, X 0 1, X 1 0, X 1 1)) h
    simp at this
    omega
  · simp only [gG, RG_mul] at h
    have := congrArg (fun X : IMat => (X 0 0, X 0 1, X 1 0, X 1 1)) h
    simp at this
    omega

/-- Uniqueness half of Lemma 4 (i): distinct words have distinct classical products. -/
theorem prodc_injective : ∀ (w₁ w₂ : List Bool), prodc w₁ = prodc w₂ → w₁ = w₂ := by
  intro w₁
  induction w₁ with
  | nil =>
    intro w₂ h
    cases w₂ with
    | nil => rfl
    | cons y w => exact absurd (by simpa [prodc] using h.symm) (prodc_ne_one_cons y w)
  | cons x w ih =>
    intro w₂ h
    cases w₂ with
    | nil => exact absurd (by simpa [prodc] using h) (prodc_ne_one_cons x w)
    | cons y v =>
      have e1 : prodc (x :: w) = gG (1 : ℤ) 1 x * prodc w := by simp [prodc]
      have e2 : prodc (y :: v) = gG (1 : ℤ) 1 y * prodc v := by simp [prodc]
      rw [e1, e2] at h
      by_cases hxy : x = y
      · subst hxy
        have := gc_mul_cancel x _ _ h
        rw [ih v this]
      · exfalso
        cases x <;> cases y
        · exact hxy rfl
        · exact R_ne_L _ _ (good_prodc v) (good_prodc w) h.symm
        · exact R_ne_L _ _ (good_prodc w) (good_prodc v) h
        · exact hxy rfl

end Classical

/-! ### The q-deformation over `ℤ[q, q⁻¹]` -/

noncomputable section

/-- `ℤ[q, q⁻¹]`. -/
abbrev LP := LaurentPolynomial ℤ

/-- 2 by 2 matrices over `ℤ[q, q⁻¹]`. -/
abbrev Mat := Matrix (Fin 2) (Fin 2) LP

theorem T_one_mul_T_neg_one : (T 1 : LP) * T (-1) = 1 := by
  rw [← T_add]; simp

/-- `R_q = [[q,1],[0,1]]`. -/
def Rq : Mat := RG (T 1)
/-- `L_q = [[1,0],[1,q⁻¹]]`. -/
def Lq : Mat := LG (T (-1))
/-- `S_q = [[0,-1/q],[1,0]]`. -/
def Sq : Mat := !![0, -T (-1); 1, 0]
/-- `R_q⁻¹ = [[1/q, -1/q],[0,1]]`. -/
def Rqinv : Mat := !![T (-1), -T (-1); 0, 1]
/-- `S_q⁻¹ = [[0,1],[-q,0]]`. -/
def Sqinv : Mat := !![0, 1; -T 1, 0]

theorem generic_R_inv {R : Type*} [CommRing R] (q qi : R) (hq : q * qi = 1) :
    RG q * !![qi, -qi; 0, 1] = 1 := by
  simp only [RG, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;>
    first | linear_combination hq | linear_combination (-1 : R) * hq

theorem generic_S_inv {R : Type*} [CommRing R] (q qi : R) (hq : q * qi = 1) :
    !![0, -qi; 1, 0] * !![0, 1; -q, 0] = (1 : Matrix (Fin 2) (Fin 2) R) := by
  simp only [Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> linear_combination hq

theorem generic_SRS {R : Type*} [CommRing R] (q qi : R) (hq : q * qi = 1) :
    !![0, -qi; 1, 0] * !![qi, -qi; 0, 1] * !![0, 1; -q, 0] = LG qi := by
  simp only [LG, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;>
    linear_combination hq

/-- `L_q = S_q R_q⁻¹ S_q⁻¹`, the definition used in the write-up. -/
theorem Sq_mul_Rqinv_mul_Sqinv : Sq * Rqinv * Sqinv = Lq :=
  generic_SRS (T 1) (T (-1)) T_one_mul_T_neg_one

/-- `Rqinv` is the inverse of `Rq`. -/
theorem Rq_mul_Rqinv : Rq * Rqinv = 1 := generic_R_inv (T 1) (T (-1)) T_one_mul_T_neg_one

/-- `Sqinv` is the inverse of `Sq`. -/
theorem Sq_mul_Sqinv : Sq * Sqinv = 1 := generic_S_inv (T 1) (T (-1)) T_one_mul_T_neg_one

/-- The q-deformation `rho` of a word in `R, L`: the same product with `R_q, L_q`. -/
def prodq (w : List Bool) : Mat := prodG (T 1 : LP) (T (-1)) w

/-- Specialisation `q ↦ 1`, a ring homomorphism `ℤ[q, q⁻¹] → ℤ`. -/
def spec : LP →+* ℤ := LaurentPolynomial.eval₂ (RingHom.id ℤ) 1

theorem spec_toLaurent (p : Polynomial ℤ) : spec (Polynomial.toLaurent p) = p.eval 1 := by
  simp [spec, eval₂_toLaurent]

theorem spec_T (n : ℤ) : spec (T n) = 1 := by
  simp [spec, eval₂_T]

/-- Setting `q = 1` in the q-deformed word product gives the classical product. -/
theorem map_prodq (w : List Bool) : (prodq w).map spec = prodc w := by
  rw [prodq, map_prodG, spec_T, spec_T]; rfl

theorem T_one_sub_eq : (T 1 - 1 : LP) = Polynomial.toLaurent (Polynomial.X - Polynomial.C 1) := by
  simp [Polynomial.toLaurent_X]

theorem T_one_sub_ne : (T 1 - 1 : LP) ≠ 0 := by
  rw [T_one_sub_eq]
  intro h
  exact Polynomial.X_sub_C_ne_zero (1:ℤ) (Polynomial.toLaurent_injective (by simpa using h))

/-- A Laurent polynomial that vanishes at `q = 1` is divisible by `q - 1`. -/
theorem exists_factor (F : LP) (hF : spec F = 0) : ∃ G : LP, F = (T 1 - 1) * G := by
  obtain ⟨n, f', hf'⟩ := exists_T_pow F
  have h1 : spec (Polynomial.toLaurent f') = 0 := by
    rw [hf', map_mul, hF, zero_mul]
  rw [spec_toLaurent] at h1
  have h2 : Polynomial.X - Polynomial.C 1 ∣ f' := Polynomial.dvd_iff_isRoot.mpr h1
  obtain ⟨g, hg⟩ := h2
  refine ⟨Polynomial.toLaurent g * T (-(n:ℤ)), ?_⟩
  have h3 : F = Polynomial.toLaurent f' * T (-(n:ℤ)) := by
    rw [hf', mul_assoc, ← T_add]; simp
  rw [h3, hg, map_mul, ← T_one_sub_eq]
  ring

/-- If `C(1) ≠ 0` then `C ∣ (q - 1) B` implies `C ∣ B`. -/
theorem dvd_of_dvd_mul (C B : LP) (hC : spec C ≠ 0) (h : C ∣ (T 1 - 1) * B) : C ∣ B := by
  obtain ⟨F, hF⟩ := h
  have h0 : spec C * spec F = 0 := by
    rw [← map_mul, ← hF, map_mul, map_sub, spec_T, map_one, sub_self, zero_mul]
  have hF0 : spec F = 0 := (mul_eq_zero.mp h0).resolve_left hC
  obtain ⟨G, hG⟩ := exists_factor F hF0
  refine ⟨G, ?_⟩
  apply mul_left_cancel₀ T_one_sub_ne
  rw [hF, hG]; ring

/-- `q` is a unit, so dividing `q * X` is the same as dividing `X`. -/
theorem dvd_T_one_mul_iff (C X : LP) : C ∣ T 1 * X ↔ C ∣ X := by
  have hu : IsUnit (T 1 : LP) := isUnit_T 1
  exact hu.dvd_mul_left

/-! ### The theorem -/

/-- The Pell automorph `Lambda = [[r, d s], [s, r]]`. -/
def Lambda (d r s : ℤ) : IMat := !![r, d * s; s, r]

/-- `Lambda` (with `d, r, s ≥ 1`) is a nonnegative determinant-one matrix, so it is the
classical product of a word in `R, L`. -/
theorem good_Lambda {d r s : ℤ} (hd : 0 < d) (hr : 0 < r) (hs : 0 < s)
    (h : r ^ 2 - d * s ^ 2 = 1) : Good (Lambda d r s) := by
  simp only [Good, Lambda, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  refine ⟨hr.le, by positivity, hs.le, hr.le, by linarith⟩

/-- **t5-scalar.**  Let `r² - d s² = 1` with `d, r, s ≥ 1` and `Lambda = [[r, d s],[s, r]]`.
Then `Lambda` is the classical product of some word `w` in `R, L`, and for every such word
the q-deformation `Lambda_q = prodq w = [[A, B],[C, D]]` satisfies

* `q (A - D) = (q - 1) (q B + C)`, and
* `C ∣ B ↔ C ∣ (A - D)` in `ℤ[q, q⁻¹]`.

(Hypothesis mapping is in the header of this file.) -/
theorem t5_scalar {d r s : ℤ} (hd : 0 < d) (hr : 0 < r) (hs : 0 < s)
    (h : r ^ 2 - d * s ^ 2 = 1) :
    (∃ w, prodc w = Lambda d r s) ∧
    ∀ w, prodc w = Lambda d r s →
      (T 1 * (prodq w 0 0 - prodq w 1 1) = (T 1 - 1) * (T 1 * prodq w 0 1 + prodq w 1 0)) ∧
      (prodq w 1 0 ∣ prodq w 0 1 ↔ prodq w 1 0 ∣ prodq w 0 0 - prodq w 1 1) := by
  refine ⟨exists_word _ (good_Lambda hd hr hs h), ?_⟩
  intro w hw
  -- the word is a palindrome
  have hpal : w.reverse = w := by
    apply prodc_injective
    rw [← flipM_prodc, hw]
    ext i j; fin_cases i <;> fin_cases j <;> simp [flipM, Lambda]
  have hP : PG (T 1 : LP) (prodq w) :=
    PG_prodG_palin (T 1 : LP) (T (-1)) T_one_mul_T_neg_one w.length w le_rfl hpal
  have hid : T 1 * (prodq w 0 0 - prodq w 1 1) = (T 1 - 1) * (T 1 * prodq w 0 1 + prodq w 1 0) :=
    hP
  refine ⟨hid, ?_⟩
  -- C(1) = s ≠ 0
  have hC : spec (prodq w 1 0) ≠ 0 := by
    have := congrArg (fun X : IMat => X 1 0) (map_prodq w)
    simp only [Matrix.map_apply] at this
    rw [this, hw]
    simp [Lambda]; omega
  constructor
  · intro hCB
    -- C ∣ B, so C ∣ (q-1)(qB + C) = q (A - D)
    have h1 : prodq w 1 0 ∣ T 1 * (prodq w 0 0 - prodq w 1 1) := by
      rw [hid]
      exact Dvd.dvd.mul_left (dvd_add (Dvd.dvd.mul_left hCB _) dvd_rfl) _
    exact (dvd_T_one_mul_iff _ _).mp h1
  · intro hCA
    -- C ∣ (q-1) * (q B) , so C ∣ q B, so C ∣ B
    have h1 : prodq w 1 0 ∣ (T 1 - 1) * (T 1 * prodq w 0 1) := by
      have h2 : prodq w 1 0 ∣ T 1 * (prodq w 0 0 - prodq w 1 1) := Dvd.dvd.mul_left hCA _
      rw [hid, mul_add] at h2
      exact (dvd_add_left (Dvd.dvd.mul_left dvd_rfl _)).mp h2
    have h3 : prodq w 1 0 ∣ T 1 * ((T 1 - 1) * prodq w 0 1) := by
      have : T 1 * ((T 1 - 1) * prodq w 0 1) = (T 1 - 1) * (T 1 * prodq w 0 1) := by ring
      rw [this]; exact h1
    exact dvd_of_dvd_mul _ _ hC ((dvd_T_one_mul_iff _ _).mp h3)

/-- Smoke test on a concrete instance: `d = 3`, `(r, s) = (2, 1)`, `Lambda = R L R`. -/
example : prodc [true, false, true] = Lambda 3 2 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [prodc, prodG, gG, RG, LG, Lambda, Matrix.mul_apply, Fin.sum_univ_two]

end

end T5Scalar

#print axioms T5Scalar.t5_scalar
