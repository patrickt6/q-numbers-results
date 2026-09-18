/-
  GosperCF.Negation
  =================

  The quadratic q-negation-finiteness result (Phase 3 of
  `<path>`, provenance record [id removed]), answering Ovsienko's Example 6.4 on the
  scanned catalogue: for which `x` is `[x]_q + [-x]_q` a finite Laurent
  polynomial?

  `[-x]_q` is Jouteur's PGL₂(ℤ) negation (arXiv:2503.02122, eq. (2)).

  What is formalized here, honestly:

  * `jneg_sum_identity` - **identity (*)**:
      `A + [-x]_q = ((q-1)A² + (1 - q⁻¹)) / ((q-1)A + 1)`,  `A = [x]_q`.
    A pure field identity, exactly the `sympy.cancel` check in the note.  Fully
    proved.

  * `vieta_sum` - for distinct roots `A, A'` of `αX² + βX + γ` over a field,
    `A + A' = -β/α`.  Fully proved.

  * `neg_sum_pure_sqrt` - the **(⇐) direction's algebraic content**: when `x` is a
    pure square root, the MGO/Jouteur framework makes `[-x]_q` the algebraic
    conjugate root `A'` of the quadratic satisfied by `A = [x]_q` (q-Vieta,
    Jouteur §5).  Then `[x]_q + [-x]_q = -β/α`, the q-trace - a radical-free
    field element, hence (the note's structural input) a Laurent polynomial.

  NOT formalized (open / PRD, flagged in the note and the collaborator packet): the
  Laurent-series *finiteness/infiniteness* analysis itself - that `-β/α` reduces
  to a polynomial exactly for trace-zero quadratics (needs palindromicity of
  q-traces, Jouteur §2.3) and that the trace-nonzero / rational / transcendental
  cases retain a non-terminating `√Δ` series.  The `iff` is engine-verified on the
  catalogue, not proved from axioms.

  Author: (removed)
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

namespace GosperCF

variable {K : Type*} [Field K]

/-- Jouteur's PGL₂(ℤ) q-negation (arXiv:2503.02122, eq. (2)), as a function of
    `A = [x]_q`:  `[-x]_q = (-A + 1 - q⁻¹) / ((q-1)·A + 1)`. -/
def jneg (q A : K) : K := (-A + 1 - q⁻¹) / ((q - 1) * A + 1)

/-- **Identity (*).**  The q-negation sum collapses to a single fraction:
    `[x]_q + [-x]_q = ((q-1)·A² + (1 - q⁻¹)) / ((q-1)·A + 1)`, with `A = [x]_q`.
    Holds for every `A` with `(q-1)A + 1 ≠ 0`; no quadratic hypothesis on `x`. -/
theorem jneg_sum_identity (q A : K) (hden : (q - 1) * A + 1 ≠ 0) :
    A + jneg q A = ((q - 1) * A ^ 2 + (1 - q⁻¹)) / ((q - 1) * A + 1) := by
  unfold jneg
  rw [eq_div_iff hden, add_mul, div_mul_cancel₀ _ hden]
  ring

/-- **Vieta sum.**  If `A` and `A'` are distinct roots of `αX² + βX + γ` over a
    field with `α ≠ 0`, then `A + A' = (-β) / α`. -/
theorem vieta_sum (α β γ A A' : K) (hα : α ≠ 0)
    (hA : α * A ^ 2 + β * A + γ = 0) (hA' : α * A' ^ 2 + β * A' + γ = 0)
    (hne : A ≠ A') :
    A + A' = (-β) / α := by
  have hsub : α * (A ^ 2 - A' ^ 2) + β * (A - A') = 0 := by linear_combination hA - hA'
  have hfac : (A - A') * (α * (A + A') + β) = 0 := by linear_combination hsub
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · rw [eq_div_iff hα]; linear_combination h

/-- **(⇐) direction, algebraic content.**  When `x` is a pure square root, the
    Jouteur negation `[-x]_q` is the algebraic-conjugate root `A'` of the
    quadratic `αA² + βA + γ = 0` satisfied by `A = [x]_q` (q-Vieta, Jouteur §5).
    Then the negation sum equals the q-trace `-β/α`, a radical-free element of the
    field. -/
theorem neg_sum_pure_sqrt (q α β γ A A' : K) (hα : α ≠ 0)
    (hA : α * A ^ 2 + β * A + γ = 0) (hA' : α * A' ^ 2 + β * A' + γ = 0)
    (hne : A ≠ A') (hconj : jneg q A = A') :
    A + jneg q A = (-β) / α := by
  rw [hconj]; exact vieta_sum α β γ A A' hα hA hA' hne

/-- **False variant of identity (*)** (buildout 37 statement-correctness gate):
    flipping the sign of `q⁻¹` in the numerator (`1 - q⁻¹` ↦ `1 + q⁻¹`) is
    refutable.  At `q = 2`, `A = 1` the true sum is `3/4` but the flipped form
    gives `5/4`. -/
theorem jneg_sum_false_variant :
    ¬ (∀ (q A : ℚ), (q - 1) * A + 1 ≠ 0 →
        A + jneg q A = ((q - 1) * A ^ 2 + (1 + q⁻¹)) / ((q - 1) * A + 1)) := by
  intro h
  have := h 2 1 (by norm_num)
  norm_num [jneg] at this

end GosperCF
