/-
  GosperCF.JumpGapDet
  ===================

  The q-Wronskian (determinant) identity that discharges the `hdet` hypothesis of
  `GosperCF.JumpGap.gap_closed_form`.  Folded in 2026-06-02 from an independent
  re-derivation and re-verification of the rational jump-gap proof (symbolic on 173
  rationals; this Lean core checked axiom-clean, zero `sorry`, against
  Lean 4.29 + Mathlib).

  Main results:
    * `det_qcontinuant` - determinant of an even-length product of continuant
      transfer blocks is the single power `q ^ (Sigma exponents)`, with NO sign.
    * `det_continuant`  - the same, with the exponent identified as the
      ALTERNATING SUM of the continued-fraction digits  a0 - a1 + a2 - ... .
      This is the hypothesis the jump-gap closed form was conditional on.
    * `gap_telescope`   - the telescoping identity that turns the determinant into
      the gap:  right - left = (1-q) * det M / (S_+ S_-).

  Correction this file records.  The q-Wronskian is `q ^ (alternating sum)`, NOT
  `q ^ (sum of digits - 1)`.  The "sum - 1" exponent of the lab report is the
  exponent of the *numerator after normalising* the raw denominators into honest
  q-deformations of s; it is not the determinant.  The determinant exponent and the
  numerator exponent are related by  E = D + 2 P_odd - 1  (P_odd = sum of the
  odd-position digits).  See `<path>`.

  NOTE: this module uses `import Mathlib`; run `lake build GosperCF.JumpGapDet` to
  re-confirm it compiles in-project (it was checked axiom-clean at origin).
-/
import Mathlib
open Matrix

namespace GosperCF.JumpGapDet
variable {K : Type*} [Field K]

/-! ### The continuant transfer block -/

/-- A continuant-style transfer block: top-left entry arbitrary, top-right `q ^ e`,
bottom row `(1, 0)`.  The actual q-continuant uses `[a]_q` or `[a]_{1/q}` in the
top-left slot, but that entry sits above a `0` and never affects the determinant. -/
def blk (q : K) (p : K × ℤ) : Matrix (Fin 2) (Fin 2) K := !![p.1, q ^ p.2; 1, 0]

@[simp] lemma det_blk (q : K) (p : K × ℤ) : (blk q p).det = - q ^ p.2 := by
  simp [blk, Matrix.det_fin_two_of]

/-! ### Determinant of a product of blocks -/

/-- Signed determinant of a product of continuant blocks (any length). -/
lemma det_prod_blk (q : K) (hq : q ≠ 0) (L : List (K × ℤ)) :
    (L.map (blk q)).prod.det = (-1) ^ L.length * q ^ ((L.map Prod.snd).sum) := by
  induction L with
  | nil => simp
  | cons p t ih =>
      rw [List.map_cons, List.prod_cons, Matrix.det_mul, det_blk, ih,
          List.map_cons, List.sum_cons, List.length_cons, zpow_add₀ hq]
      ring

/-- **Determinant identity (signed-exponent form).** For an *even-length* product of
continuant blocks the determinant is the single power `q ^ (Sigma exponents)`, with
no sign: the even-length convention is exactly what forces the `(-1)^length` to
vanish. -/
theorem det_qcontinuant (q : K) (hq : q ≠ 0) (L : List (K × ℤ))
    (hlen : Even L.length) :
    (L.map (blk q)).prod.det = q ^ ((L.map Prod.snd).sum) := by
  rw [det_prod_blk q hq L, hlen.neg_one_pow, one_mul]

/-! ### From signed exponents to the alternating digit sum -/

/-- Attach continuant signs: digit at an even index keeps exponent `+a`, at an odd
index gets `-a`.  `signExp [a0,a1,a2,a3] = [a0, -a1, a2, -a3]`. -/
def signExp : List ℤ → List ℤ
  | [] => []
  | a :: t => a :: (signExp t).map (- ·)

@[simp] lemma signExp_length (a : List ℤ) : (signExp a).length = a.length := by
  induction a with
  | nil => rfl
  | cons x t ih => simp [signExp, ih]

lemma sum_map_neg (l : List ℤ) : (l.map (- ·)).sum = - l.sum := by
  induction l with
  | nil => simp
  | cons x t ih => simp [ih]; ring

@[simp] lemma signExp_sum (a : List ℤ) : (signExp a).sum = a.alternatingSum := by
  induction a with
  | nil => simp [signExp]
  | cons x t ih =>
      simp only [signExp, List.sum_cons, List.alternatingSum_cons, sum_map_neg, ih]
      ring

/-- **Determinant identity (alternating-sum form).** The determinant of the
even-length q-continuant built from CF digit list `a` (top-left entries `c`
arbitrary, top-right entries `q^{±aᵢ}` with sign alternating by position) equals the
single power `q ^ (a0 - a1 + a2 - ...)`, the alternating sum of the digits. -/
theorem det_continuant (q : K) (hq : q ≠ 0) (c : K) (a : List ℤ)
    (hlen : Even a.length) :
    (((signExp a).map (fun e => blk q (c, e))).prod).det = q ^ a.alternatingSum := by
  have h := det_qcontinuant (K := K) q hq ((signExp a).map (fun e => (c, e)))
    (by simpa using hlen)
  simpa [List.map_map, Function.comp, signExp_sum] using h

/-! ### The telescoping identity -/

/-- **Telescoping closed form.** For any 2×2 matrix `M` over a field, the difference
of the two seed-vector ratios - the right value `M·(1,0)` and the left value
`M·(1,1-q)` - equals `(1-q)·det M` over the product of the two denominators.
Combined with `det_continuant` this gives  gap = (1-q) q^(alt sum) / (S_+ S_-). -/
lemma gap_telescope (q : K) (M : Matrix (Fin 2) (Fin 2) K)
    (h0 : M 1 0 ≠ 0) (h1 : M 1 0 + (1 - q) * M 1 1 ≠ 0) :
    M 0 0 / M 1 0 - (M 0 0 + (1 - q) * M 0 1) / (M 1 0 + (1 - q) * M 1 1)
      = (1 - q) * M.det / (M 1 0 * (M 1 0 + (1 - q) * M 1 1)) := by
  rw [Matrix.det_fin_two]
  field_simp
  ring

end GosperCF.JumpGapDet

-- Axiom audit (should print only propext, Classical.choice, Quot.sound):
#print axioms GosperCF.JumpGapDet.det_continuant
#print axioms GosperCF.JumpGapDet.gap_telescope
