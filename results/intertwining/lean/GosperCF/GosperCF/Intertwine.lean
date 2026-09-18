/-
  GosperCF.Intertwine
  ===================

  Theorem 4.1 of `gap-a-note.tex` (`thm:char`, the intertwining
  characterization), formalized in the part that is pure algebra.

  Paper statement (verbatim, `thm:char`):

    "For a real quadratic irrational `x`, the following are equivalent: some
     automorph `M` of `x` satisfies `JMJ = M⁻¹`; every automorph of `x` does;
     `x + x^sigma = 0`; and `x = v sqrt D` for some `v` in `Q \ {0}` and some
     squarefree integer `D > 1`."

  and the load-bearing content the paper itself isolates in its scopebox:

    "The equivalence rests on `JMJ = !![m1, -m2; -m3, m4]` against
     `M⁻¹ = !![m4, -m2; -m3, m1]`: these agree entrywise exactly when
     `m1 = m4`, and identity (eq:trace), that `m1 - m4 = (x + x^sigma) m3`,
     makes `m1 = m4` exactly `x + x^sigma = 0`."

  WHAT IS COVERED HERE
  --------------------

  * `intertwine_iff_diag_eq` : over any commutative ring, for
    `M = !![m1, m2; m3, m4]` with `det M = 1`,
    `J * M * J = M⁻¹` if and only if `m1 = m4`.
    This is the first-to-second-and-third equivalence's algebraic core and it
    is proved with no side hypotheses beyond `det M = 1`.

  * `no_neg_intertwine` : over the integers there is no `M` in `SL(2, Z)` with
    `J * M * J = -M⁻¹`.  The paper disposes of this projective sign case by
    saying it "would force `m2 = m3 = 0`, giving `M = ±I`, excluded".  The
    statement proved here is strictly stronger than what the paper needs: over
    `Z` with determinant one the sign case is outright impossible, so nothing
    has to be excluded by hand.

  * `automorph_quadratic` : clearing denominators in `(m1 x + m2)/(m3 x + m4) = x`
    gives `m3 x^2 + (m4 - m1) x - m2 = 0`, the paper's displayed quadratic.

  * `trace_identity` : the paper's identity (eq:trace), `m1 - m4 = (x + x^sigma) m3`,
    PROVED (not assumed) by Vieta from the fact that `x` and `x^sigma` are the two
    distinct roots of that quadratic.

  * `intertwine_iff_trace_zero` : the full link, over the reals,
    `J * M * J = M⁻¹` if and only if `x + x^sigma = 0`.

  WHAT IS NOT COVERED HERE
  ------------------------

  * The fourth item of `thm:char`, that trace zero is equivalent to
    `x = v sqrt D` with `v` rational and `D > 1` squarefree.  That is a
    statement about reduced forms of rationals, not matrix algebra, and it is
    not formalized here.

  * "Every automorph does" is captured only in the sense that the criterion
    `m1 = m4` is shown equivalent to a property of `x` alone (`x + x^sigma = 0`)
    that does not mention `M`.  There is no formalization here of the set of
    automorphs of a given `x`, so the quantified "some / every" phrasing itself
    is not stated as a Lean proposition.

  * Nothing about q-deformation, negation sums, or finiteness.

  NOTHING IS ASSUMED THAT THE PAPER PROVES.  In particular the trace identity
  (eq:trace) is derived here, not taken as a hypothesis.
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

namespace GosperCF.Intertwine

open Matrix

/-- `J = diag(-1, 1)`, the reflection matrix of `gap-a-note.tex` Section 4.
Conjugation by `J` sends the Mobius action of `M` at `x` to its action at `-x`. -/
def J (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![-1, 0; 0, 1]

/-- `J` is an involution. -/
@[simp] theorem J_mul_J (R : Type*) [CommRing R] : J R * J R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

/-- The adjugate formula for the inverse of a `2 x 2` matrix of determinant one. -/
theorem inv_of_det_one {R : Type*} [CommRing R] {m1 m2 m3 m4 : R}
    (hdet : m1 * m4 - m2 * m3 = 1) :
    (!![m1, m2; m3, m4])⁻¹ = !![m4, -m2; -m3, m1] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;>
    first
      | ring1
      | linear_combination hdet

/-- Conjugation of `M` by `J` swaps the signs of the two off-diagonal entries. -/
theorem J_conj {R : Type*} [CommRing R] (m1 m2 m3 m4 : R) :
    J R * !![m1, m2; m3, m4] * J R = !![m1, -m2; -m3, m4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- **Theorem 4.1 of `gap-a-note.tex`, matrix core.**

For `M = !![m1, m2; m3, m4]` of determinant one over any commutative ring,
`J M J = M⁻¹` if and only if the two diagonal entries agree, `m1 = m4`.

This is exactly the comparison the paper's scopebox calls load bearing:
`J M J = !![m1, -m2; -m3, m4]` against `M⁻¹ = !![m4, -m2; -m3, m1]`, which
share their off-diagonal entries and differ only by the order of the diagonal.

Covered: the equivalence as stated, over an arbitrary commutative ring, with no
hypothesis other than `det M = 1`.  Not covered: the projective (`PSL`) reading
of the equation; see `no_neg_intertwine` for the sign case over `Z`. -/
theorem intertwine_iff_diag_eq {R : Type*} [CommRing R] {m1 m2 m3 m4 : R}
    (hdet : m1 * m4 - m2 * m3 = 1) :
    J R * !![m1, m2; m3, m4] * J R = (!![m1, m2; m3, m4])⁻¹ ↔ m1 = m4 := by
  rw [J_conj, inv_of_det_one hdet]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simpa using h00
  · intro h
    subst h
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- **The projective sign case, over the integers.**

The paper's proof of `thm:char` remarks that "equality up to the sign `-I` would
force `m2 = m3 = 0`, giving `M = ±I`, excluded since no automorph of an
irrational is `±I`".  Over `Z` with determinant one the situation is sharper:
the equation `J M J = -M⁻¹` has no solution at all, because it forces
`m1 = -m4` and `m2 = m3 = 0`, hence `-m1^2 = 1`.

So this theorem proves more than the paper needs, and nothing has to be
excluded by appeal to irrationality of `x`. -/
theorem no_neg_intertwine {m1 m2 m3 m4 : ℤ} (hdet : m1 * m4 - m2 * m3 = 1) :
    J ℤ * !![m1, m2; m3, m4] * J ℤ ≠ -(!![m1, m2; m3, m4])⁻¹ := by
  rw [J_conj, inv_of_det_one hdet]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  simp at h00 h01 h10
  -- `h00 : m1 = -m4`, `h01 : -m2 = m2`, `h10 : -m3 = m3`
  have hm2 : m2 = 0 := by omega
  have hm3 : m3 = 0 := by omega
  subst hm2
  subst hm3
  rw [h00] at hdet
  nlinarith [sq_nonneg m4]

section Trace

variable {m1 m2 m3 m4 x xs : ℝ}

/-- Clearing denominators in the fixed-point equation `(m1 x + m2)/(m3 x + m4) = x`
gives the quadratic `m3 x^2 + (m4 - m1) x - m2 = 0` of `gap-a-note.tex`, eq. above
(eq:trace).  The hypothesis is the cleared form, so no nonvanishing of the
denominator is needed. -/
theorem automorph_quadratic (h : m1 * x + m2 = x * (m3 * x + m4)) :
    m3 * x ^ 2 + (m4 - m1) * x - m2 = 0 := by linear_combination -h

/-- **Identity (eq:trace) of `gap-a-note.tex`:** `m1 - m4 = (x + x^sigma) m3`.

Proved here by Vieta from the hypothesis that `x` and `xs` are two distinct
roots of the automorph quadratic `m3 z^2 + (m4 - m1) z - m2`.  This identity is
PROVED, not assumed. -/
theorem trace_identity (hx : m3 * x ^ 2 + (m4 - m1) * x - m2 = 0)
    (hxs : m3 * xs ^ 2 + (m4 - m1) * xs - m2 = 0) (hne : x ≠ xs) :
    m1 - m4 = (x + xs) * m3 := by
  have key : (x - xs) * (m3 * (x + xs) + (m4 - m1)) = 0 := by
    linear_combination hx - hxs
  have h2 : m3 * (x + xs) + (m4 - m1) = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  linear_combination -h2

/-- **Theorem 4.1 of `gap-a-note.tex`, the link to Galois trace zero.**

For a real quadratic irrational `x` with automorph `M = !![m1, m2; m3, m4]` in
`SL(2, Z)` (here: real entries with determinant one), Galois conjugate `xs`,
and `m3 ≠ 0`:

    `J M J = M⁻¹`  if and only if  `x + x^sigma = 0`.

The automorph hypothesis is supplied in the cleared quadratic form: `x` and `xs`
are the two distinct roots of `m3 z^2 + (m4 - m1) z - m2`.  The trace identity
(eq:trace) used in the proof is `trace_identity` above, which is proved here.

Not covered: the passage from `x + x^sigma = 0` to `x = v sqrt D` with `D`
squarefree, which is item four of `thm:char`. -/
theorem intertwine_iff_trace_zero (hdet : m1 * m4 - m2 * m3 = 1) (hm3 : m3 ≠ 0)
    (hx : m3 * x ^ 2 + (m4 - m1) * x - m2 = 0)
    (hxs : m3 * xs ^ 2 + (m4 - m1) * xs - m2 = 0) (hne : x ≠ xs) :
    J ℝ * !![m1, m2; m3, m4] * J ℝ = (!![m1, m2; m3, m4])⁻¹ ↔ x + xs = 0 := by
  rw [intertwine_iff_diag_eq hdet]
  have htr : m1 - m4 = (x + xs) * m3 := trace_identity hx hxs hne
  constructor
  · intro h
    have : (x + xs) * m3 = 0 := by rw [← htr, h]; ring
    exact (mul_eq_zero.mp this).resolve_right hm3
  · intro h
    have : m1 - m4 = 0 := by rw [htr, h]; ring
    linarith

end Trace

/-- Conjugation by an involution `P` commutes with taking powers.
Used in `GosperCF.Pell` to pass from `J M J = M⁻¹` to `J M^k J = M⁻ᵏ`. -/
theorem conj_pow {R : Type*} [CommRing R] {A P : Matrix (Fin 2) (Fin 2) R}
    (hP : P * P = 1) : ∀ k : ℕ, P * A ^ k * P = (P * A * P) ^ k := by
  intro k
  induction k with
  | zero => simpa using hP
  | succ n ih =>
      have h1 : (P * A * P) ^ (n + 1) = (P * A ^ n * P) * (P * A * P) := by
        rw [pow_succ, ih]
      have h2 : (P * A ^ n * P) * (P * A * P) = P * A ^ n * (P * P) * A * P := by
        simp only [Matrix.mul_assoc]
      rw [h1, h2, hP, Matrix.mul_one, pow_succ]
      simp only [Matrix.mul_assoc]

end GosperCF.Intertwine
