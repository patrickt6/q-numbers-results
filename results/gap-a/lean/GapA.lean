/-
  GapA: the closed step of Example 6.4 (the "reflection chain"), matrix core.

  SCOPE, stated first.  This file does NOT construct the q-deformation of
  SL(2,Z) and does NOT define the mismatch ratio from q-deformed matrices.  What
  it proves is:
    (1) the integer-matrix identity behind the chain, in full, for all
        automorphs whose trace is an integer:
            R^m N M N R^(-m) = M^(-1),     m = (a - d)/c            (dihedral_loop)
        and its link to the real quadratic irrational x through the trace
        identity of GosperCF.Intertwine (loop_of_trace);
    (2) the arithmetic equivalence  c | a - d  <->  c | a^2 - 1  for
        a d - b c = 1                                               (dvd_sub_iff_dvd_sq_sub_one);
    (3) a REDUCTION: for ANY function r on integer matrices satisfying the four
        transformation laws listed in `MismatchLaws` (assumed, NOT proved here),
            r(M)^2 = q^(2m),   and   r(M) = +-1  <->  a = d,
        and, for a real quadratic irrational x with Galois conjugate xs,
            r(M) = +-1  <->  x + xs = 0.
  Non-vacuity: `toy_laws` shows the laws are satisfiable (a toy real-valued
  model, not the q-deformed ratio), so the reduction is not about an empty class.

  The four laws are the ones the source write-up proves for the q-deformed
  mismatch ratio r(M) = q^(mu+1) conj(C)/C.  Here they are hypotheses of the
  structure `MismatchLaws`; nothing is postulated globally.  The sign step r(M) = +q^m (excluding
  -q^m) is not formalised; it is not needed for the "+-1" statement.

  MAP TO results/gap-a/statement.tex (2nd line of the display):
      kappa(x) = q^(mu+1) conj(C)/C           <->  r M   (r is the paper's kappa;
                                                   the write-up calls it r)
      kappa(x) = +-1  <=>  x + x^sigma = 0    <->  `example64_step_iff`
      t = x + x^sigma in Z  ==>  kappa(x) = q^t   <->  `sq_eq` (gives kappa^2 = q^(2t);
                                                    the sign is the unformalised step)
  Hypotheses of `example64_step_iff` and their meaning in the statement:
      hdet  : a d - b c = 1          M = [[a,b],[c,d]] is in SL(2,Z)
      hc    : c <> 0                 M fixes no rational point, x irrational
      hx,hxs: c x^2 + (d-a) x - b = 0 (and the same at xs)
                                     x, xs are the two roots of the automorph
                                     quadratic, i.e. M x = x and M xs = xs
      hne   : x <> xs                x is a quadratic irrational, xs its conjugate
      L     : MismatchLaws q r       the four assumed laws (see below)
  Conclusion: (r M = 1 or r M = -1) <-> x + xs = 0.

  THE ASSUMED LAWS (structure MismatchLaws), each with its source name:
      inv     r(M^(-1)) = r(M)                 automorph invariance (I1)
      neg     r(N M N)  = r(M)^(-1)            negation law (I2)
      shift   r(R^n M R^(-n)) = q^(2n) r(M)    translation law (I3)
      mono_one  r(M) = +-1 => c | a - d        the k = 0 case of the monomial
                                               dichotomy (I4)
      plus q <> 0, q^n = 1 => n = 0 (q is not a root of unity), r(M) <> 0.
  N = diag(1,-1), R^n = [[1,n],[0,1]].  (GosperCF.Intertwine.J = diag(-1,1) = -N;
  conjugation by -N and by N agree, so N M N = J M J.)

  Statement changes from the paper: none.  The only reading choice is that the
  laws are asked for matrices with lower-left entry c <> 0 only.
-/
import GosperCF.Intertwine
import Mathlib.Tactic

namespace GapA

open Matrix

/-- `N = diag(1, -1)`, the reflection `x -> -x`. -/
def N : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]

/-- `R^n = [[1, n], [0, 1]]`, the translation `x -> x + n`. -/
def Rn (n : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, n; 0, 1]

theorem N_conj (a b c d : ℤ) :
    N * !![a, b; c, d] * N = !![a, -b; -c, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N, Matrix.mul_apply, Fin.sum_univ_succ]

/-- **The dihedral loop** (Lemma 1 of the source write-up).
For `M = [[a,b],[c,d]]` of determinant one with `a - d = m c`,
`R^m (N M N) R^(-m) = M^(-1)`. -/
theorem dihedral_loop {a b c d m : ℤ} (hdet : a * d - b * c = 1) (hm : a - d = m * c) :
    Rn m * (N * !![a, b; c, d] * N) * Rn (-m) = (!![a, b; c, d])⁻¹ := by
  rw [N_conj, GosperCF.Intertwine.inv_of_det_one hdet]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rn, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    first
      | ring1
      | linear_combination hm
      | linear_combination (-1 : ℤ) * hm
      | linear_combination (-m) * hm

/-- **Lemma 2 (arithmetic core).** For `a d - b c = 1`, `c` divides `a - d` exactly
when `c` divides `a^2 - 1`. -/
theorem dvd_sub_iff_dvd_sq_sub_one {a b c d : ℤ} (hdet : a * d - b * c = 1) :
    c ∣ a - d ↔ c ∣ a ^ 2 - 1 := by
  have hcop : IsCoprime a c := ⟨d, -b, by linear_combination hdet⟩
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨a * k + b, by linear_combination a * hk + hdet⟩
  · intro h
    have h1 : c ∣ a * (a - d) := by
      have : c ∣ a ^ 2 - 1 - b * c := dvd_sub h (dvd_mul_left c b)
      have e : a * (a - d) = a ^ 2 - 1 - b * c := by linear_combination (-1 : ℤ) * hdet
      rw [e]; exact this
    exact (hcop.symm.dvd_of_dvd_mul_left h1)

/-- **Trace link.** A real quadratic irrational `x` with conjugate `xs`, both roots
of the automorph quadratic of `M = [[a,b],[c,d]]`, whose trace
`x + xs` is the integer `m`, gives `a - d = m c`, hence the dihedral loop. -/
theorem loop_of_trace {a b c d m : ℤ} {x xs : ℝ}
    (hdet : a * d - b * c = 1)
    (hx : (c : ℝ) * x ^ 2 + ((d : ℝ) - a) * x - b = 0)
    (hxs : (c : ℝ) * xs ^ 2 + ((d : ℝ) - a) * xs - b = 0)
    (hne : x ≠ xs) (htr : x + xs = m) :
    Rn m * (N * !![a, b; c, d] * N) * Rn (-m) = (!![a, b; c, d])⁻¹ := by
  have h := GosperCF.Intertwine.trace_identity (m1 := (a : ℝ)) (m2 := b) (m3 := c)
    (m4 := d) hx hxs hne
  rw [htr] at h
  have h' : a - d = m * c := by exact_mod_cast h
  exact dihedral_loop hdet h'

/-- The transformation laws of the mismatch ratio `r(M) = q^(mu+1) conj(C)/C`,
imported from the source write-up and ASSUMED here (as hypotheses of this
structure, not as global postulates).
`r` is any function on integer matrices with values in a field `K`. -/
structure MismatchLaws {K : Type*} [Field K] (q : K)
    (r : Matrix (Fin 2) (Fin 2) ℤ → K) : Prop where
  q_ne_zero : q ≠ 0
  /-- `q` is not a root of unity. -/
  q_not_root : ∀ n : ℤ, q ^ n = 1 → n = 0
  /-- `r(M) <> 0` whenever the lower-left entry `c` is nonzero. -/
  ne_zero : ∀ M, M.det = 1 → M 1 0 ≠ 0 → r M ≠ 0
  /-- automorph invariance (I1) -/
  inv : ∀ M, M.det = 1 → M 1 0 ≠ 0 → r M⁻¹ = r M
  /-- negation law (I2) -/
  neg : ∀ M, M.det = 1 → M 1 0 ≠ 0 → r (N * M * N) = (r M)⁻¹
  /-- translation law (I3) -/
  shift : ∀ (n : ℤ) M, M.det = 1 → M 1 0 ≠ 0 →
    r (Rn n * M * Rn (-n)) = q ^ (2 * n) * r M
  /-- the `k = 0` case of the monomial dichotomy (I4):
  `r(M) = +-1` forces `c ∣ a - d`. -/
  mono_one : ∀ M, M.det = 1 → M 1 0 ≠ 0 → (r M = 1 ∨ r M = -1) → M 1 0 ∣ M 0 0 - M 1 1

theorem det_mk {a b c d : ℤ} : (!![a, b; c, d]).det = a * d - b * c := by
  simp [Matrix.det_fin_two_of]

theorem det_N_conj {a b c d : ℤ} (h : a * d - b * c = 1) :
    (N * !![a, b; c, d] * N).det = 1 := by
  rw [N_conj, det_mk]; linear_combination h

theorem Rn_conj_det {n : ℤ} {M : Matrix (Fin 2) (Fin 2) ℤ} (h : M.det = 1) :
    (Rn n * M * Rn (-n)).det = 1 := by
  have hR : ∀ k : ℤ, (Rn k).det = 1 := fun k => by rw [Rn, det_mk]; ring
  rw [Matrix.det_mul, Matrix.det_mul, hR, hR, h]; ring

theorem Rn_conj_ll {n : ℤ} (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (Rn n * M * Rn (-n)) 1 0 = M 1 0 := by
  rw [Matrix.eta_fin_two M]
  simp [Rn, Matrix.mul_apply, Fin.sum_univ_succ]

/-- **Loop closure.** Under the laws, `r(M)^2 = q^(2m)` whenever `a - d = m c`. -/
theorem sq_eq {K : Type*} [Field K] {q : K} {r : Matrix (Fin 2) (Fin 2) ℤ → K}
    (L : MismatchLaws q r) {a b c d m : ℤ} (hdet : a * d - b * c = 1) (hc : c ≠ 0)
    (hm : a - d = m * c) : r !![a, b; c, d] ^ 2 = q ^ (2 * m) := by
  have hM : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by rw [det_mk]; exact hdet
  have hMc : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ≠ 0 := by simpa using hc
  have hNM := det_N_conj (a := a) (b := b) (c := c) (d := d) hdet
  have hNMc : (N * !![a, b; c, d] * N) 1 0 ≠ 0 := by
    rw [N_conj]; simpa using hc
  have loop := dihedral_loop hdet hm
  have e1 : r (!![a, b; c, d])⁻¹ = r !![a, b; c, d] := L.inv _ hM hMc
  have e2 := L.shift m (N * !![a, b; c, d] * N) hNM hNMc
  have e3 := L.neg _ hM hMc
  rw [loop, e1, e3] at e2
  have hr : r !![a, b; c, d] ≠ 0 := L.ne_zero _ hM hMc
  field_simp at e2
  linear_combination e2

/-- **`r = +-q^m`.** -/
theorem eq_pm {K : Type*} [Field K] {q : K} {r : Matrix (Fin 2) (Fin 2) ℤ → K}
    (L : MismatchLaws q r) {a b c d m : ℤ} (hdet : a * d - b * c = 1) (hc : c ≠ 0)
    (hm : a - d = m * c) :
    r !![a, b; c, d] = q ^ m ∨ r !![a, b; c, d] = -q ^ m := by
  have h := sq_eq L hdet hc hm
  have h2 : (q ^ m) ^ 2 = q ^ (2 * m) := by
    rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  rw [← h2] at h
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h

/-- **The closed step (matrix form).** Under the laws, for `M = [[a,b],[c,d]]`
in `SL(2,Z)` with `c <> 0`:  `r(M) = +-1  <->  a = d`. -/
theorem pm_one_iff_diag {K : Type*} [Field K] {q : K} {r : Matrix (Fin 2) (Fin 2) ℤ → K}
    (L : MismatchLaws q r) {a b c d : ℤ} (hdet : a * d - b * c = 1) (hc : c ≠ 0) :
    (r !![a, b; c, d] = 1 ∨ r !![a, b; c, d] = -1) ↔ a = d := by
  have hM : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by rw [det_mk]; exact hdet
  have hMc : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ≠ 0 := by simpa using hc
  constructor
  · intro hp
    have hdvd := L.mono_one _ hM hMc hp
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at hdvd
    obtain ⟨m, hm⟩ := hdvd
    have hm' : a - d = m * c := by rw [hm]; ring
    have hsq := sq_eq L hdet hc hm'
    have hone : r !![a, b; c, d] ^ 2 = 1 := by
      rcases hp with h | h <;> rw [h] <;> norm_num
    rw [hone] at hsq
    have : (2 * m) = 0 := L.q_not_root _ hsq.symm
    have hm0 : m = 0 := by omega
    rw [hm0] at hm'
    linarith
  · intro had
    have hm' : a - d = 0 * c := by rw [had]; ring
    have hsq := sq_eq L hdet hc hm'
    simp only [mul_zero, zpow_zero] at hsq
    rw [pow_two] at hsq
    exact mul_self_eq_one_iff.mp hsq

/-- **Example 6.4, the closed step, for a real quadratic irrational.**
`x`, `xs` are the two roots of the automorph quadratic of `M = [[a,b],[c,d]]`
(so `x` is a quadratic irrational with conjugate `xs`); under the assumed laws,
`r(M) = +-1` holds exactly when the trace `x + xs` is zero. -/
theorem example64_step_iff {K : Type*} [Field K] {q : K}
    {r : Matrix (Fin 2) (Fin 2) ℤ → K} (L : MismatchLaws q r) {a b c d : ℤ} {x xs : ℝ}
    (hdet : a * d - b * c = 1) (hc : c ≠ 0)
    (hx : (c : ℝ) * x ^ 2 + ((d : ℝ) - a) * x - b = 0)
    (hxs : (c : ℝ) * xs ^ 2 + ((d : ℝ) - a) * xs - b = 0) (hne : x ≠ xs) :
    (r !![a, b; c, d] = 1 ∨ r !![a, b; c, d] = -1) ↔ x + xs = 0 := by
  rw [pm_one_iff_diag L hdet hc]
  have h := GosperCF.Intertwine.trace_identity (m1 := (a : ℝ)) (m2 := b) (m3 := c)
    (m4 := d) hx hxs hne
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  constructor
  · intro had
    have : (a : ℝ) - d = 0 := by exact_mod_cast sub_eq_zero.mpr had
    rw [this] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hcR
  · intro htr
    rw [htr, zero_mul] at h
    exact_mod_cast sub_eq_zero.mp h

/-- **`t in Z  ==>  r^2 = q^(2t)`** for a real quadratic irrational whose trace is the
integer `t` (the source states `r = q^t`; the sign is the unformalised step). -/
theorem sq_eq_of_trace {K : Type*} [Field K] {q : K}
    {r : Matrix (Fin 2) (Fin 2) ℤ → K} (L : MismatchLaws q r) {a b c d t : ℤ} {x xs : ℝ}
    (hdet : a * d - b * c = 1) (hc : c ≠ 0)
    (hx : (c : ℝ) * x ^ 2 + ((d : ℝ) - a) * x - b = 0)
    (hxs : (c : ℝ) * xs ^ 2 + ((d : ℝ) - a) * xs - b = 0) (hne : x ≠ xs)
    (htr : x + xs = t) : r !![a, b; c, d] ^ 2 = q ^ (2 * t) := by
  have h := GosperCF.Intertwine.trace_identity (m1 := (a : ℝ)) (m2 := b) (m3 := c)
    (m4 := d) hx hxs hne
  rw [htr] at h
  have h' : a - d = t * c := by exact_mod_cast h
  exact sq_eq L hdet hc h'

/-! ### Non-vacuity of the assumed laws

`MismatchLaws` is satisfiable, so the reduction theorems above are not vacuous.
The toy model below is NOT the q-deformed mismatch ratio.  It takes `K = R`,
`q = 2` and `r(M) = 2^((a-d)/c)` with a real exponent; it obeys all the laws
because `(a-d)/c` is negated by `N`-conjugation, fixed by inversion, and shifts by
`+2n` under `R^n`-conjugation. -/

/-- The toy model. -/
noncomputable def toy (M : Matrix (Fin 2) (Fin 2) ℤ) : ℝ :=
  (2 : ℝ) ^ (((M 0 0 : ℝ) - M 1 1) / M 1 0)

theorem toy_mk (a b c d : ℤ) :
    toy !![a, b; c, d] = (2 : ℝ) ^ (((a : ℝ) - d) / c) := by
  simp [toy]

theorem Rn_conj_mk (n a b c d : ℤ) :
    Rn n * !![a, b; c, d] * Rn (-n) =
      !![a + n * c, -n * (a + n * c) + b + n * d; c, -n * c + d] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rn, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem toy_laws : MismatchLaws (2 : ℝ) toy where
  q_ne_zero := by norm_num
  q_not_root := by
    intro n hn
    by_contra hne
    have := (zpow_eq_one_iff_right₀ (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (2:ℝ) ≠ 1)).mp hn
    exact hne this
  ne_zero := by intro M _ _; unfold toy; positivity
  inv := by
    intro M hd hc
    rw [Matrix.eta_fin_two M] at hd hc ⊢
    rw [det_mk] at hd
    rw [GosperCF.Intertwine.inv_of_det_one hd, toy_mk, toy_mk]
    have hc' : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast hc
    congr 1
    push_cast
    field_simp
    ring
  neg := by
    intro M hd hc
    rw [Matrix.eta_fin_two M] at hd hc ⊢
    rw [N_conj, toy_mk, toy_mk]
    have hc' : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast hc
    rw [← Real.rpow_neg (by norm_num)]
    congr 1
    push_cast
    field_simp
  shift := by
    intro n M hd hc
    rw [Matrix.eta_fin_two M] at hd hc ⊢
    rw [Rn_conj_mk, toy_mk, toy_mk]
    have hc' : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast hc
    have : ((2 : ℝ) ^ (2 * n)) = (2 : ℝ) ^ ((2 * (n : ℝ))) := by
      rw [← Real.rpow_intCast]; push_cast; ring_nf
    rw [this, ← Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    field_simp
    ring
  mono_one := by
    intro M hd hc h
    rw [Matrix.eta_fin_two M] at hd hc h ⊢
    rw [toy_mk] at h
    have hc' : (M 1 0 : ℝ) ≠ 0 := by exact_mod_cast hc
    have h0 : (((M 0 0 : ℝ) - M 1 1) / M 1 0) = 0 := by
      rcases h with h | h
      · rcases lt_trichotomy (((M 0 0 : ℝ) - M 1 1) / M 1 0) 0 with hl | hl | hl
        · have := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ) < 2) hl
          linarith
        · exact hl
        · have := Real.one_lt_rpow (by norm_num : (1:ℝ) < 2) hl
          linarith
      · have hpos : (0:ℝ) < (2 : ℝ) ^ (((M 0 0 : ℝ) - M 1 1) / M 1 0) := by positivity
        linarith
    have h1 : ((M 0 0 : ℝ) - M 1 1) = 0 :=
      (div_eq_zero_iff.mp h0).resolve_right hc'
    have h2 : M 0 0 - M 1 1 = 0 := by exact_mod_cast h1
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [h2]; exact dvd_zero _

#print axioms dihedral_loop
#print axioms loop_of_trace
#print axioms dvd_sub_iff_dvd_sq_sub_one
#print axioms sq_eq
#print axioms eq_pm
#print axioms pm_one_iff_diag
#print axioms example64_step_iff
#print axioms sq_eq_of_trace
#print axioms toy_laws

end GapA
