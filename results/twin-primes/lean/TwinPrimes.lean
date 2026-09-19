/-
  TwinPrimes: the difference-of-squares family x = m/(m^2-1) and twin primes.

  Statement formalised (results/twin-primes/statement.tex):
      x = m/(m^2-1):  [x]_q = q^(m-1) [m]_q / ([m-1]_q [m+1]_q),
                      S = [m-1]_q [m+1]_q,
      S = Phi_(m-1) Phi_(m+1)  (two cyclotomic factors)  <=>  m-1 and m+1 both prime.

  PROVED, for EVERY integer m >= 2 (no finite range):
    (a) `family_value`  : with the Morier-Genoud--Ovsienko q-continued fraction
        `qcf` (nested form, defined below) applied to the even-length regular
        continued fraction [0; m-1, 1, m-1] of m/(m^2-1),
            [x]_q = q^(m-1) [m]_q / ([m-1]_q [m+1]_q)
        in any field where q <> 0 and every [k]_q is nonzero.
    (b) `cf_value`      : the classical value of [0; m-1, 1, m-1] is m/(m^2-1).
    (c) `coprime_family`: numerator q^(m-1)[m]_q and denominator [m-1]_q [m+1]_q
        are coprime in Q[q], so the fraction is in lowest terms; the
        denominator is monic, hence S = [m-1]_q [m+1]_q is THE reduced
        q-denominator (`reduced_denominator_unique`).
    (d) `twin_iff`      : [m-1]_q [m+1]_q = Phi_(m-1) Phi_(m+1)  <=>  m-1, m+1 prime.
        Both directions, all m >= 2.  Proof by degrees: deg [k]_q = k-1,
        deg Phi_k = phi(k) <= k-1, with equality iff k is prime.
  `family_twin` bundles (a)-(d), with q the indeterminate of Q(q).

  THE TWO SOURCE DRAFTS DISAGREE, and this file resolves the disagreement for
  the family statement.  The earlier section draft says the factorization
  S = [m-1][m+1] is "verified for 2 <= m <= 30" and not proved for all m, which
  makes its twin theorem conditional.  The later patch in
  results/twin-primes/evidence/patch-twin-primes.tex proves it for all m >= 2
  by continued-fraction telescoping.  `family_value` re-derives that
  computation in Lean, so the all-m statement is machine-checked here with no
  finite-range hypothesis.  NOT formalised: the patch's all-numerators theorem
  (every numerator a coprime to d = p p'), which goes beyond statement.tex.

  READING CHOICES (recorded, not silent):
    * "two cyclotomic factors" is formalised as the equation
      S = Phi_(m-1) Phi_(m+1), the form the source theorem states.  The
      broader reading "S = Phi_a Phi_b for some a, b" is not formalised.
    * `qcf` is the nested MGO formula
        [a1,...,an]_q = [a1]_q + q^a1 / ([a2]_(1/q) + q^(-a2) / ([a3]_q + ...)),
      last term [an]_q or [an]_(1/q) according to the parity of the position.
      Checked outside Lean against the reference q-rational tool at m = 4
      (it returns q^3 [4]/([3][5])) and against an independent computation for
      m = 2..7.
    * [0; m-1, 1, m-1] is the even-length regular continued fraction; for
      m = 2 it is [0;1,1,1] = 2/3.
-/
import Mathlib.Tactic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.FieldTheory.RatFunc.Basic

open Polynomial

namespace TwinPrimes

/-- `[k]_q = 1 + q + ... + q^(k-1)` as a polynomial over `Q`. -/
noncomputable def qnP (k : ℕ) : ℚ[X] := ∑ i ∈ Finset.range k, X ^ i

theorem qnP_monic {k : ℕ} (hk : 1 ≤ k) : (qnP k).Monic :=
  monic_geom_sum_X (by omega)

theorem qnP_ne_zero {k : ℕ} (hk : 1 ≤ k) : qnP k ≠ 0 :=
  (monic_geom_sum_X (by omega)).ne_zero

theorem natDegree_qnP {k : ℕ} (hk : 1 ≤ k) : (qnP k).natDegree = k - 1 := by
  have h : qnP k * (X - 1) = X ^ k - 1 := by
    unfold qnP; exact geom_sum_mul X k
  have h1 : (X ^ k - 1 : ℚ[X]).natDegree = k := by
    have := natDegree_X_pow_sub_C (n := k) (r := (1 : ℚ))
    simpa using this
  have h2 : (qnP k * (X - 1)).natDegree = (qnP k).natDegree + 1 := by
    have hx : (X - 1 : ℚ[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : ℚ)
    have hx1 : (X - 1 : ℚ[X]).natDegree = 1 := by simpa using natDegree_X_sub_C (1 : ℚ)
    rw [natDegree_mul (qnP_ne_zero hk) hx, hx1]
  rw [h, h1] at h2
  omega

theorem qnP_prime {p : ℕ} (hp : p.Prime) : qnP p = cyclotomic p ℚ := by
  haveI := Fact.mk hp
  rw [cyclotomic_prime, qnP]

/-- Two-factor characterisation.  For `m ≥ 2`,
`[m-1]_q [m+1]_q = Phi_(m-1) Phi_(m+1)` iff `m-1` and `m+1` are both prime. -/
theorem twin_iff {m : ℕ} (hm : 2 ≤ m) :
    qnP (m - 1) * qnP (m + 1) = cyclotomic (m - 1) ℚ * cyclotomic (m + 1) ℚ ↔
      (m - 1).Prime ∧ (m + 1).Prime := by
  constructor
  · intro h
    -- compare degrees
    have hne1 : cyclotomic (m - 1) ℚ ≠ 0 := cyclotomic_ne_zero _ _
    have hne2 : cyclotomic (m + 1) ℚ ≠ 0 := cyclotomic_ne_zero _ _
    have hd := congrArg natDegree h
    rw [natDegree_mul (qnP_ne_zero (by omega)) (qnP_ne_zero (by omega)),
      natDegree_mul hne1 hne2, natDegree_qnP (by omega), natDegree_qnP (by omega),
      natDegree_cyclotomic, natDegree_cyclotomic] at hd
    have hm3 : 3 ≤ m := by
      by_contra hlt
      have : m = 2 := by omega
      subst this
      have h3 : Nat.totient 3 = 2 := Nat.totient_prime (by norm_num)
      simp [h3] at hd
    have l1 := Nat.totient_lt (m - 1) (by omega)
    have l2 := Nat.totient_lt (m + 1) (by omega)
    have e1 : (m - 1).totient = m - 1 - 1 := by omega
    have e2 : (m + 1).totient = m + 1 - 1 := by omega
    exact ⟨(Nat.totient_eq_iff_prime (by omega)).mp e1, (Nat.totient_eq_iff_prime (by omega)).mp e2⟩
  · rintro ⟨h1, h2⟩
    rw [qnP_prime h1, qnP_prime h2]


variable {K : Type*} [Field K]

/-- `[k]_q = 1 + q + ... + q^(k-1)` in a field. -/
def qn (q : K) (k : ℕ) : K := ∑ i ∈ Finset.range k, q ^ i

/-- The Morier-Genoud--Ovsienko q-continued fraction, nested form:
`[a1, a2, ..., a_n]_q = [a1]_q + q^a1 / ([a2]_(1/q) + q^(-a2) / ([a3]_q + ...))`,
the flag `s` records whether the current position uses `q` (true) or `1/q` (false). -/
def qcfAux (q : K) : Bool → List ℕ → K
  | _, [] => 0
  | s, [a] => qn (if s then q else q⁻¹) a
  | s, a :: b :: t =>
      qn (if s then q else q⁻¹) a + (if s then q else q⁻¹) ^ a / qcfAux q (!s) (b :: t)

def qcf (q : K) (l : List ℕ) : K := qcfAux q true l

theorem qn_succ (q : K) (k : ℕ) : qn q (k + 1) = qn q k + q ^ k := by
  simp [qn, Finset.sum_range_succ]

theorem qn_succ' (q : K) (k : ℕ) : qn q (k + 1) = 1 + q * qn q k := by
  unfold qn
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm, add_comm]

theorem qn_inv_mul {q : K} (hq : q ≠ 0) (k : ℕ) : qn q⁻¹ (k + 1) * q ^ k = qn q (k + 1) := by
  induction k with
  | zero => simp [qn]
  | succ n ih =>
    have h1 := qn_succ' q (n + 1)
    have e1 : (q⁻¹) ^ (n + 1) * q ^ (n + 1) = 1 := by rw [← mul_pow, inv_mul_cancel₀ hq, one_pow]
    rw [qn_succ, add_mul, pow_succ q n]
    linear_combination q * ih + e1 - h1

/-- `[k]_(1/q) = [k]_q / q^(k-1)` -/
theorem qn_inv {q : K} (hq : q ≠ 0) (k : ℕ) : qn q⁻¹ (k + 1) = qn q (k + 1) / q ^ k := by
  rw [eq_div_iff (pow_ne_zero _ hq)]; exact qn_inv_mul hq k

/-- The value of `[0; m-1, 1, m-1]_q` for `m ≥ 2`. -/
theorem family_value {q : K} (hq : q ≠ 0) (hqn : ∀ k : ℕ, qn q (k + 1) ≠ 0) {m : ℕ} (hm : 2 ≤ m) :
    qcf q [0, m - 1, 1, m - 1] = q ^ (m - 1) * qn q m / (qn q (m - 1) * qn q (m + 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  simp only [show n + 2 - 1 = n + 1 by omega]
  have hA : qn q (n + 1) ≠ 0 := hqn n
  have hB : qn q (n + 2) ≠ 0 := hqn (n + 1)
  have hC : qn q (n + 3) ≠ 0 := hqn (n + 2)
  have hp : q ^ n ≠ 0 := pow_ne_zero _ hq
  have hb : qn q (n + 2) = qn q (n + 1) + q ^ n * q := by rw [qn_succ]; ring
  have hc : qn q (n + 3) = qn q (n + 2) + q ^ n * q * q := by rw [qn_succ]; ring
  simp [qcf, qcfAux, qn_inv hq]
  have hc' : qn q (n + 2 + 1) = 1 + q * qn q (n + 2) := qn_succ' q (n + 2)
  have hb' : qn q (n + 2) = 1 + q * qn q (n + 1) := qn_succ' q (n + 1)
  have h0 : qn q 0 = 0 := by simp [qn]
  have h1 : qn q 1 = 1 := by simp [qn]
  rw [h0, h1]
  generalize qn q (n + 1) = A at *
  generalize qn q (n + 2) = b at *
  generalize qn q (n + 2 + 1) = c at *
  generalize hpp : q ^ n = p at *
  have hbA : b ≠ 0 := hB
  have hcC : c ≠ 0 := hC
  have hpq : q ^ (n + 1) = p * q := by rw [← hpp]; ring
  have hin : 1 + q / (A / p) = b / A := by
    field_simp; linear_combination -hb
  rw [hin, hpq]
  have hmid : A / p + (p * q)⁻¹ / (b / A) = A * c / (p * q * b) := by
    field_simp; linear_combination -hc'
  rw [hmid]
  field_simp
  ring


/-! ### Part C: the family over Q(q) -/

theorem cf_value {m : ℕ} (hm : 2 ≤ m) :
    (0 : ℚ) + 1 / (((m : ℚ) - 1) + 1 / (1 + 1 / ((m : ℚ) - 1))) = m / ((m : ℚ) ^ 2 - 1) := by
  have h2 : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have h1 : (m : ℚ) - 1 ≠ 0 := by linarith
  have h3 : (m : ℚ) + 1 ≠ 0 := by linarith
  have h5 : (m : ℚ) ≠ 0 := by linarith
  have h4 : (m : ℚ) ^ 2 - 1 ≠ 0 := by
    have : (m : ℚ) ^ 2 - 1 = ((m : ℚ) - 1) * ((m : ℚ) + 1) := by ring
    rw [this]; exact mul_ne_zero h1 h3
  have h6 : (1 : ℚ) + 1 / ((m : ℚ) - 1) = m / ((m : ℚ) - 1) := by
    field_simp; ring
  rw [h6]
  have h7 : ((m : ℚ) - 1) + 1 / ((m : ℚ) / ((m : ℚ) - 1)) = ((m : ℚ) ^ 2 - 1) / m := by
    field_simp; ring
  rw [h7]
  field_simp
  ring

theorem qnP_succ' (k : ℕ) : qnP (k + 1) = 1 + X * qnP k := by
  unfold qnP
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm, add_comm]

theorem coprime_X (k : ℕ) : IsCoprime (X : ℚ[X]) (qnP (k + 1)) := by
  refine ⟨-qnP k, 1, ?_⟩
  rw [qnP_succ']; ring

theorem coprime_succ (k : ℕ) : IsCoprime (qnP (k + 2)) (qnP (k + 1)) := by
  refine ⟨1, -X, ?_⟩
  rw [qnP_succ' (k + 1)]; ring

theorem coprime_family {m : ℕ} (hm : 2 ≤ m) :
    IsCoprime (X ^ (m - 1) * qnP m) (qnP (m - 1) * qnP (m + 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have e1 : n + 2 - 1 = n + 1 := by omega
  rw [e1]
  have hX : ∀ k, IsCoprime (X ^ (n + 1) : ℚ[X]) (qnP (k + 1)) :=
    fun k => (coprime_X k).pow_left
  have h_a : IsCoprime (qnP (n + 2)) (qnP (n + 1)) := coprime_succ n
  have h_b : IsCoprime (qnP (n + 2)) (qnP (n + 2 + 1)) := by
    have hpow : IsCoprime (qnP (n + 2)) (X ^ (n + 2) : ℚ[X]) :=
      (coprime_X (n + 1)).symm.pow_right
    have e : qnP (n + 2 + 1) = X ^ (n + 2) + qnP (n + 2) * 1 := by
      unfold qnP
      rw [Finset.sum_range_succ]; ring
    rw [e]
    exact hpow.add_mul_left_right 1
  exact (IsCoprime.mul_right (hX n) (hX (n + 2))).mul_left (IsCoprime.mul_right h_a h_b)

/-- Uniqueness of the reduced form: two coprime representations of the same
rational function with monic denominators have equal denominators. -/
theorem reduced_denominator_unique {n d n' d' : ℚ[X]} (hd : d.Monic) (hd' : d'.Monic)
    (hc : IsCoprime n d) (hc' : IsCoprime n' d')
    (h : (algebraMap ℚ[X] (RatFunc ℚ) n) / algebraMap ℚ[X] (RatFunc ℚ) d =
         (algebraMap ℚ[X] (RatFunc ℚ) n') / algebraMap ℚ[X] (RatFunc ℚ) d') : d = d' := by
  have hd0 : algebraMap ℚ[X] (RatFunc ℚ) d ≠ 0 := by
    simpa using hd.ne_zero
  have hd0' : algebraMap ℚ[X] (RatFunc ℚ) d' ≠ 0 := by
    simpa using hd'.ne_zero
  rw [div_eq_div_iff hd0 hd0'] at h
  have h2 : n * d' = n' * d := by
    apply (RatFunc.algebraMap_injective ℚ)
    simpa using h
  have h3 : d ∣ d' := by
    have : d ∣ n * d' := ⟨n', by rw [h2]; ring⟩
    exact hc.symm.dvd_of_dvd_mul_left this
  have h4 : d' ∣ d := by
    have : d' ∣ n' * d := ⟨n, by rw [← h2]; ring⟩
    exact hc'.symm.dvd_of_dvd_mul_left this
  exact eq_of_monic_of_associated hd hd' (associated_of_dvd_dvd h3 h4)

theorem qn_X_eq (k : ℕ) : qn (RatFunc.X : RatFunc ℚ) k = algebraMap ℚ[X] (RatFunc ℚ) (qnP k) := by
  simp [qn, qnP, map_sum, map_pow, RatFunc.algebraMap_X]

theorem qn_X_ne_zero (k : ℕ) : qn (RatFunc.X : RatFunc ℚ) (k + 1) ≠ 0 := by
  rw [qn_X_eq]
  simpa using qnP_ne_zero (k := k + 1) (by omega)

/-- **The family theorem** for `x = m/(m^2-1)`, all `m ≥ 2`, `q` the indeterminate of `Q(q)`. -/
theorem family_twin {m : ℕ} (hm : 2 ≤ m) :
    -- the continued fraction [0; m-1, 1, m-1] has classical value m/(m^2-1)
    ((0 : ℚ) + 1 / (((m : ℚ) - 1) + 1 / (1 + 1 / ((m : ℚ) - 1))) = m / ((m : ℚ) ^ 2 - 1)) ∧
    -- its q-deformation is q^(m-1)[m]/([m-1][m+1])
    (qcf (RatFunc.X : RatFunc ℚ) [0, m - 1, 1, m - 1] =
        algebraMap ℚ[X] (RatFunc ℚ) (X ^ (m - 1) * qnP m) /
          algebraMap ℚ[X] (RatFunc ℚ) (qnP (m - 1) * qnP (m + 1))) ∧
    -- lowest terms, denominator monic: S = [m-1][m+1]
    IsCoprime (X ^ (m - 1) * qnP m) (qnP (m - 1) * qnP (m + 1)) ∧
    (qnP (m - 1) * qnP (m + 1)).Monic ∧
    -- two cyclotomic factors iff twin primes
    (qnP (m - 1) * qnP (m + 1) = cyclotomic (m - 1) ℚ * cyclotomic (m + 1) ℚ ↔
      (m - 1).Prime ∧ (m + 1).Prime) := by
  refine ⟨cf_value hm, ?_, coprime_family hm, ?_, twin_iff hm⟩
  · have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
    rw [family_value hX qn_X_ne_zero hm]
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
    simp only [map_mul, map_pow, RatFunc.algebraMap_X, qn_X_eq]
  · exact (qnP_monic (by omega)).mul (qnP_monic (by omega))

#print axioms cf_value
#print axioms coprime_family
#print axioms reduced_denominator_unique
#print axioms family_value
#print axioms twin_iff
#print axioms family_twin

/-- **Headline form.**  Whatever coprime representation `n/d` with monic `d` the value
`[x]_q` of `x = m/(m^2-1)` is given, its reduced denominator `d` equals
`Phi_(m-1) Phi_(m+1)` exactly when `m-1` and `m+1` are both prime. -/
theorem reduced_denominator_twin {m : ℕ} (hm : 2 ≤ m) {n d : ℚ[X]} (hd : d.Monic)
    (hc : IsCoprime n d)
    (h : qcf (RatFunc.X : RatFunc ℚ) [0, m - 1, 1, m - 1] =
      algebraMap ℚ[X] (RatFunc ℚ) n / algebraMap ℚ[X] (RatFunc ℚ) d) :
    d = cyclotomic (m - 1) ℚ * cyclotomic (m + 1) ℚ ↔ (m - 1).Prime ∧ (m + 1).Prime := by
  obtain ⟨_, hval, hcop, hmon, hiff⟩ := family_twin hm
  have hdd : d = qnP (m - 1) * qnP (m + 1) :=
    reduced_denominator_unique hd hmon hc hcop (h.symm.trans hval)
  rw [hdd]; exact hiff

#print axioms reduced_denominator_twin

end TwinPrimes
