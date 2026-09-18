/-
  GosperCF.Pell
  =============

  The matrix algebra behind the Pell reduction,
  `<path>`, Theorem
  (note:thm-pell).

  Paper statement (verbatim):

    "For every nonsquare `d`,  `F(d) = G(r/s) = (A - D)/C`  as an identity of
     rational functions in `q`."

  where `(r, s)` is the fundamental solution of `r^2 - d s^2 = 1`,

      `Lambda = !![r, d*s; s, r]`  in  `SL(2, Z)`,

  and `Lambda_q = !![A, B; C, D]` is its q-deformation.

  WHAT IS COVERED HERE
  --------------------

  Exactly the three algebraic steps the task and the paper's proof turn on.

  * `Lambda_det`, `Lambda_inv` : `Lambda` lies in `SL(2, Z)` and its inverse is
    `!![r, -(d*s); -s, r]`.

  * `N_conj_Lambda` : with `N = diag(-1, 1)`,  `N * Lambda * N = Lambda⁻¹`.
    The proof is literally `(intertwine_iff_diag_eq _).mpr rfl`: the criterion
    from `GosperCF.Intertwine` is "the two diagonal entries are equal", and for
    `Lambda` those entries are both `r`, so the `rfl` IS the equal-diagonal
    hypothesis.  The paper stresses that this step fails for a general
    quadratic irrational, whose automorph has unequal diagonal entries; that
    failure is visible here as the fact that
    `GosperCF.Intertwine.intertwine_iff_diag_eq` is an if-and-only-if, so
    `m1 ≠ m4` gives `N M N ≠ M⁻¹` outright.  `general_automorph_fails` below
    records that direction, with `M = !![5, 2; 2, 1]`, the automorph of
    `1 + sqrt 2`, as a concrete witness (`automorph_one_add_sqrt_two_fails`).

  * `N_conj_Lambda_pow` : `N * Lambda^k * N = (Lambda^k)⁻¹` for every `k : ℕ`.

  * `pow_two_two` and its corollaries `pow_diag_diff` and `pow_lower_left` :
    the Cayley-Hamilton step.  Writing `M = !![A, B; C, D]` over any
    commutative ring, `t = A + D`, `δ = A*D - B*C`, and `u` for the
    Chebyshev-type sequence `u 0 = 0`, `u 1 = 1`, `u (n+2) = t * u (n+1) - δ * u n`,

        `M^(n+1) = !![u(n+1)*A - δ*u n, u(n+1)*B; u(n+1)*C, u(n+1)*D - δ*u n]`

    from which the paper's two read-off relations follow:

        `A_k - D_k = u k * (A - D)`     (`pow_diag_diff`)
        `C_k = u k * C`                 (`pow_lower_left`)

  * `ratio_indep_of_pow` : the division-free form of what the paper actually
    concludes from those two relations, namely that `(A_k - D_k)/C_k` does not
    depend on `k`:

        `(A_k - D_k) * C = (A - D) * C_k`.

    It is stated cross-multiplied on purpose: `C` and `C_k` may vanish in an
    arbitrary commutative ring, and the paper's own `u_k` cancellation is
    exactly this identity.

  WHAT IS NOT COVERED HERE
  ------------------------

  * The MGO limit passage.  The paper's final step, `r_k/s_k -> sqrt d` and the
    stabilization of Taylor coefficients giving `F(d) = lim_k G(r_k/s_k)`, is
    analysis and is deliberately out of scope.  NOTHING in this file says
    anything about `F(d)`, about `[x]_q`, about q-deformation, or about limits.

  * The passage from rational convergents to `sqrt d`, likewise out of scope.

  * The q-equivariance and reversal facts of the paper's Section (note:setup),
    which supply the interpretation of `N M N` as the automorph of `-x`.  They
    are not restated here; this file is the matrix algebra those facts are
    applied to.

  So: this file proves the algebraic skeleton of Theorem (note:thm-pell), not
  the theorem.  The theorem's own statement, an identity of rational functions
  in `q`, is not formalized.
-/
import GosperCF.Intertwine
import Mathlib.Tactic

namespace GosperCF.Pell

open Matrix
open GosperCF.Intertwine

section Automorph

variable {d r s : ℤ}

/-- The fundamental automorph `Lambda = !![r, d*s; s, r]` of `sqrt d`,
`02-pell.tex`. -/
def Lambda (d r s : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![r, d * s; s, r]

/-- `Lambda` has determinant one, from `r^2 - d s^2 = 1`. -/
theorem Lambda_det (h : r ^ 2 - d * s ^ 2 = 1) : (Lambda d r s).det = 1 := by
  simp [Lambda, Matrix.det_fin_two_of]
  linear_combination h

/-- The determinant condition in the entrywise shape used by
`GosperCF.Intertwine.intertwine_iff_diag_eq`. -/
private theorem Lambda_det' (h : r ^ 2 - d * s ^ 2 = 1) :
    r * r - (d * s) * s = 1 := by linear_combination h

/-- The inverse of the Pell automorph. -/
theorem Lambda_inv (h : r ^ 2 - d * s ^ 2 = 1) :
    (Lambda d r s)⁻¹ = !![r, -(d * s); -s, r] :=
  inv_of_det_one (Lambda_det' h)

/-- **The intertwining step of `02-pell.tex`:** with `N = diag(-1, 1)`,

    `N * Lambda * N = Lambda⁻¹`.

The paper: "A direct computation gives `N Lambda N = Lambda⁻¹`; this uses that
the two diagonal entries of `Lambda` are equal, which holds because `Lambda` is
the automorph of a *pure* square root."

That dependence is visible in the proof term: the criterion supplied by
`intertwine_iff_diag_eq` is precisely `m1 = m4`, and the proof discharges it by
`rfl`, both entries of `Lambda` being `r`.  Nothing else about `d`, `r`, `s` is
used beyond the determinant. -/
theorem N_conj_Lambda (h : r ^ 2 - d * s ^ 2 = 1) :
    J ℤ * Lambda d r s * J ℤ = (Lambda d r s)⁻¹ :=
  (intertwine_iff_diag_eq (Lambda_det' h)).mpr rfl

/-- The converse half, which is what the paper means by "this step fails for a
general quadratic irrational": if the diagonal entries of an `SL(2, Z)` matrix
differ, then conjugation by `N` does not give the inverse. -/
theorem general_automorph_fails {m1 m2 m3 m4 : ℤ} (hdet : m1 * m4 - m2 * m3 = 1)
    (hne : m1 ≠ m4) :
    J ℤ * !![m1, m2; m3, m4] * J ℤ ≠ (!![m1, m2; m3, m4])⁻¹ :=
  fun h => hne ((intertwine_iff_diag_eq hdet).mp h)

/-- Concrete witness for `general_automorph_fails`: `M = !![5, 2; 2, 1]`, the
automorph of `1 + sqrt 2` used as a counter-instance in `gap-a-note.tex`, has
`m1 = 5 ≠ 1 = m4`, so `N M N ≠ M⁻¹`. -/
theorem automorph_one_add_sqrt_two_fails :
    J ℤ * !![(5 : ℤ), 2; 2, 1] * J ℤ ≠ (!![(5 : ℤ), 2; 2, 1])⁻¹ :=
  general_automorph_fails (by norm_num) (by norm_num)

/-- **Powers, `02-pell.tex`:** `N * Lambda^k * N = (Lambda^k)⁻¹` for all `k : ℕ`.

The paper writes this as `sigma(Lambda_q^k . infinity) = Lambda_q^(-k) . infinity`;
the matrix content is exactly the identity below. -/
theorem N_conj_Lambda_pow (h : r ^ 2 - d * s ^ 2 = 1) (k : ℕ) :
    J ℤ * (Lambda d r s) ^ k * J ℤ = ((Lambda d r s) ^ k)⁻¹ := by
  have hinvpow : (Lambda d r s) ^ k * ((Lambda d r s)⁻¹) ^ k = 1 := by
    have hcomm : (Lambda d r s) * (Lambda d r s)⁻¹ = 1 := by
      rw [Lambda_inv h]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Lambda, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;>
        first
          | ring1
          | linear_combination h
    induction k with
    | zero => simp
    | succ n ih =>
        have e : (Lambda d r s) ^ (n + 1) * ((Lambda d r s)⁻¹) ^ (n + 1)
            = (Lambda d r s) ^ n * ((Lambda d r s) * (Lambda d r s)⁻¹)
                * ((Lambda d r s)⁻¹) ^ n := by
          rw [pow_succ, pow_succ']
          simp only [Matrix.mul_assoc]
        rw [e, hcomm, Matrix.mul_one, ih]
  rw [conj_pow (J_mul_J ℤ) k, N_conj_Lambda h]
  exact (Matrix.inv_eq_right_inv hinvpow).symm

end Automorph

section CayleyHamilton

variable {R : Type*} [CommRing R]

/-- The Chebyshev-type sequence of `02-pell.tex`:
`u 0 = 0`, `u 1 = 1`, `u (n+2) = t * u (n+1) - δ * u n`, where `t` is the trace
and `δ` the determinant. -/
def cheb (t δ : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | (n + 2) => t * cheb t δ (n + 1) - δ * cheb t δ n

@[simp] theorem cheb_zero (t δ : R) : cheb t δ 0 = 0 := rfl
@[simp] theorem cheb_one (t δ : R) : cheb t δ 1 = 1 := rfl
theorem cheb_succ_succ (t δ : R) (n : ℕ) :
    cheb t δ (n + 2) = t * cheb t δ (n + 1) - δ * cheb t δ n := rfl

/-- **The Cayley-Hamilton step of `02-pell.tex`, entrywise.**

"Since `Lambda_q` satisfies its own characteristic equation,
`Lambda_q^k = u_k Lambda_q - det(Lambda_q) u_(k-1) I`."

Stated here over an arbitrary commutative ring, with the entries written out so
that no scalar-action lemmas are needed. -/
theorem pow_two_two (A B C D : R) (n : ℕ) :
    (!![A, B; C, D]) ^ (n + 1) =
      !![cheb (A + D) (A * D - B * C) (n + 1) * A
           - (A * D - B * C) * cheb (A + D) (A * D - B * C) n,
         cheb (A + D) (A * D - B * C) (n + 1) * B;
         cheb (A + D) (A * D - B * C) (n + 1) * C,
         cheb (A + D) (A * D - B * C) (n + 1) * D
           - (A * D - B * C) * cheb (A + D) (A * D - B * C) n] := by
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
      rw [pow_succ, ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ, cheb_succ_succ] <;> ring

/-- Read-off relation one, `02-pell.tex`: `A_k - D_k = u_k (A - D)`. -/
theorem pow_diag_diff (A B C D : R) (n : ℕ) :
    ((!![A, B; C, D]) ^ (n + 1)) 0 0 - ((!![A, B; C, D]) ^ (n + 1)) 1 1
      = cheb (A + D) (A * D - B * C) (n + 1) * (A - D) := by
  rw [pow_two_two]
  simp
  ring

/-- Read-off relation two, `02-pell.tex`: `C_k = u_k C`. -/
theorem pow_lower_left (A B C D : R) (n : ℕ) :
    ((!![A, B; C, D]) ^ (n + 1)) 1 0 = cheb (A + D) (A * D - B * C) (n + 1) * C := by
  rw [pow_two_two]
  simp

/-- **"Cayley-Hamilton removes `k`", `02-pell.tex`, in division-free form.**

The paper concludes from `A_k - D_k = u_k (A - D)` and `C_k = u_k C` that "`u_k`
cancels and `G(r_k/s_k) = (A - D)/C` for every `k >= 1`: the value is the same
at the fundamental solution and at every power of it."

Cross-multiplied, that statement is exactly

    `(A_k - D_k) * C = (A - D) * C_k`,

which is what is proved here.  The division `(A_k - D_k)/C_k` itself is not
formed: in a general commutative ring `C` and `C_k` need not be invertible, and
the cancellation of `u_k` the paper performs is precisely this identity. -/
theorem ratio_indep_of_pow (A B C D : R) (n : ℕ) :
    (((!![A, B; C, D]) ^ (n + 1)) 0 0 - ((!![A, B; C, D]) ^ (n + 1)) 1 1) * C
      = (A - D) * ((!![A, B; C, D]) ^ (n + 1)) 1 0 := by
  rw [pow_diag_diff, pow_lower_left]
  ring

end CayleyHamilton

end GosperCF.Pell
