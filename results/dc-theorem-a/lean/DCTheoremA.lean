import Mathlib

/-!
# dc-theorem-a: downward closure of cyclotomic factors of the q-denominator, bottom index `l ≤ 5`

Source statement: `results/dc-theorem-a/statement.tex`.

```
l ∈ {2,3,4,5},  p prime,  a ≥ 1,  k = p^a l
Φ_k ∣ S  ⟹  Φ_l ∣ S
S = S_i, every i ≥ 1 and every integer word
```

## STATE: statement_only (the case `l = 2` is proved outright; `l = 3, 4, 5` are not)

The write-up's proof has two steps.

* **Step 1 (Frobenius).**  If `ω` is a primitive `k`-th root of unity, `k = p^a l`, then
  `S(ω^{p^a}) ≡ S(ω)^{p^a} (mod p)`, so `Φ_k ∣ S` puts `S(ω_l)`, `ω_l = ω^{p^a}`, in `p`
  times an algebraic integer.  **Proved here, unconditionally** (`frob_ev`, `step1`).
* **Step 2 (finite orbit and content).**  For `l ∈ {2,3,4,5}`, the values `S(ω_l)`
  over all words form a finite set (sizes 3, 7, 9, 31) whose nonzero elements have content 1
  in `ℤ[ω_l]`, so none is divisible by a rational prime; hence `S(ω_l) = 0`.
  **Proved for `l = 2` only** (`step2_two`, by an explicit closure of the 12 reachable states of
  the recurrence at `q = -1`, `P2_closed`, checked by `decide`), so `dc_theorem_a_two`, the
  case `l = 2`, is a complete unconditional proof.  **Not formalised for `l = 3, 4, 5`.**
  It is a finite exact computation in `ℤ[ω_l]` (`12, 72, 96, 600`
  reachable states of the recurrence at `l = 2,3,4,5`, counted by an independent
  computation) and formalising it needs a concrete model of `ℤ[ω_l]`.  It enters this file as
  the named hypothesis `Step2 l`.

`dc_theorem_a` is the full statement of `statement.tex` with `Step2 l` as an explicit
hypothesis, and `dc_of_step2` is its reduction to Step 2.  Because a hypothesis carries the
hard half, the file is `statement_only` and MUST NOT be read as a proof of the theorem.
Only Step 1 is proved.

## Faithfulness of `Step2`

`Step2 l` says: for every prime `p`, every primitive `l`-th root of unity `ζ` in `ℂ`, every
integer word `w`, and every algebraic integer `y`, `S_w(ζ) = p * y` implies `S_w(ζ) = 0`.
The write-up's Step 2 says the nonzero values of `S(ζ_l)` lie in a finite list of elements of
`ℤ[ζ_l]` of content 1, hence outside `p ℤ[ζ_l]`.  Passing from `p ℤ[ζ_l]` to "`p` times an
algebraic integer" uses that `ℤ[ζ_l]` is the full ring of integers of `ℚ(ζ_l)`; this is true
for `l ≤ 5`, and it is what makes Step 1 (which produces an algebraic integer `y`, not an
element of `ℤ[ζ_l]`) connect to Step 2.  The write-up glosses this point ("the congruence being
in `ℤ[ω_l]`"); the Lean form makes it explicit.

## Hypothesis mapping

* `l ∈ {2,3,4,5}`: enters only through `Step2 l`; Step 1 holds for every `l ≥ 1`.
* `p` prime, `a`: `hp : p.Prime`, `a : ℕ` (`a ≥ 1` is not needed; `a = 0` is trivial).
* `k = p^a l`: the modulus is `p ^ a * l`.
* `S = S_i` for every `i`, every integer word: `w : List ℤ`, any length; `S w` is the recurrence
  `S_{i+1} = [c_{i+1}] S_i - q^(c_i - 1) S_{i-1}`, `(S_0,S_1) = (0,1)` in `ℤ[q, q⁻¹]`
  (same definition as in the lemma-n file; the exponent carries the previous quotient).
* `Φ_k ∣ S`: divisibility in `ℤ[q, q⁻¹]` by `Polynomial.cyclotomic k ℤ`.
-/

open LaurentPolynomial

namespace DCTheoremA

noncomputable section

/-- `ℤ[q, q⁻¹]`. -/
abbrev LP := LaurentPolynomial ℤ

/-- `[c]_q` for every integer `c`. -/
def qint : ℤ → LP
  | (n : ℕ) => ∑ i ∈ Finset.range n, T (i : ℤ)
  | Int.negSucc n => -∑ i ∈ Finset.range (n + 1), T (-((i : ℤ) + 1))

theorem qint_zero : qint 0 = 0 := by simp [qint]

theorem qint_succ (c : ℤ) : qint (c + 1) = qint c + T c := by
  rcases c with n | n
  · show qint (Int.ofNat (n + 1)) = qint (Int.ofNat n) + T (Int.ofNat n)
    simp [qint, Finset.sum_range_succ]
  · rcases n with _ | n
    · show qint 0 = qint (Int.negSucc 0) + T (Int.negSucc 0)
      simp [qint]
    · show qint (Int.negSucc n) = qint (Int.negSucc (n + 1)) + T (Int.negSucc (n + 1))
      simp only [qint, Finset.sum_range_succ]
      rw [Int.negSucc_eq (n + 1)]
      ring

theorem T_one_mul_T_neg_one : (T 1 : LP) * T (-1) = 1 := by
  rw [← T_add]; simp

theorem T_one_sub_ne : (T 1 - 1 : LP) ≠ 0 := by
  have h : (T 1 - 1 : LP) = Polynomial.toLaurent (Polynomial.X - Polynomial.C 1) := by
    simp [Polynomial.toLaurent_X]
  rw [h]
  intro h
  exact Polynomial.X_sub_C_ne_zero (1:ℤ) (Polynomial.toLaurent_injective (by simpa using h))

/-- `(q - 1) [c]_q = q^c - 1`. -/
theorem qint_mul (c : ℤ) : (T 1 - 1) * qint c = T c - 1 := by
  induction c using Int.induction_on with
  | zero => simp [qint_zero]
  | succ i ih =>
    rw [qint_succ, mul_add, ih, T_add]; ring
  | pred i ih =>
    have h := qint_succ (-(i:ℤ) - 1)
    have e : -(i:ℤ) - 1 + 1 = -(i:ℤ) := by ring
    rw [e] at h
    have h2 : qint (-(i:ℤ) - 1) = qint (-(i:ℤ)) - T (-(i:ℤ) - 1) := by rw [h]; ring
    rw [h2, mul_sub, ih, T_sub]
    have := T_one_mul_T_neg_one
    linear_combination (-(T (-(i:ℤ)) : LP)) * this



/-- One step of the recurrence `S_{i+1} = [c_{i+1}] S_i - q^{c_i - 1} S_{i-1}`.
The state is `(S_{i-1}, S_i, c_i)`. -/
def step (st : LP × LP × ℤ) (c : ℤ) : LP × LP × ℤ :=
  (st.2.1, qint c * st.2.1 - T (st.2.2 - 1) * st.1, c)

/-- `S_j` for the word `(c_2, ..., c_j)`, given as a list of length `j - 1`,
from `(S_0, S_1) = (0, 1)`.  The third slot of the initial state stands for `c_1`
and never matters, because it is multiplied by `S_0 = 0`. -/
def S (w : List ℤ) : LP := (w.foldl step (0, 1, 0)).2.1

example : S [] = 1 := by simp [S]
example (a : ℤ) : S [a] = qint a := by simp [S, step]
example (a b : ℤ) : S [a, b] = qint b * qint a - T (a - 1) := by simp [S, step]

/-- Smoke test of the convention (exponent carries the previous quotient): on the word
`(2, 2, 2)` the write-up states `S_4 = [4]_q`. -/
example : S [2, 2, 2] = qint 4 := by
  have h1 : (T 1 : LP) * T 1 = T 2 := by rw [← T_add]; rfl
  have h2 : (T 1 : LP) * T 2 = T 3 := by rw [← T_add]; rfl
  have h3 : (T 1 : LP) * T 3 = T 4 := by rw [← T_add]; rfl
  simp only [S, step, List.foldl_cons, List.foldl_nil, qint]
  norm_num [Finset.sum_range_succ, T_zero]
  linear_combination h1 + T 1 * h1 + h2


/-- Evaluation of a Laurent polynomial at a unit `z` of `ℂ`. -/
def ev (z : ℂˣ) : LP →+* ℂ := LaurentPolynomial.eval₂ (Int.castRingHom ℂ) z

theorem ev_T (z : ℂˣ) (n : ℤ) : ev z (T n) = ((z ^ n : ℂˣ) : ℂ) := by
  simp [ev, eval₂_T]

theorem ev_C (z : ℂˣ) (a : ℤ) : ev z (C a) = (a : ℂ) := by
  simp [ev]

theorem ev_invert (z : ℂˣ) (f : LP) : ev z (invert f) = ev z⁻¹ f := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | C_mul_T n a =>
    rw [map_mul, invert_C, invert_T, map_mul, map_mul, ev_C, ev_C, ev_T, ev_T, zpow_neg, inv_zpow]

theorem ev_toLaurent (z : ℂˣ) (p : Polynomial ℤ) :
    ev z (Polynomial.toLaurent p) = Polynomial.aeval (z : ℂ) p := by
  simp [ev, eval₂_toLaurent, Polynomial.aeval_def]

/-- For `ω` a primitive `k`-th root of unity in `ℂ`, `Φ_k` divides a Laurent polynomial
`f` in `ℤ[q, q⁻¹]` exactly when `f(ω) = 0`. -/
theorem cyc_dvd_iff {k : ℕ} (hk : 0 < k) (z : ℂˣ) (hz : IsPrimitiveRoot (z : ℂ) k) (f : LP) :
    Polynomial.toLaurent (Polynomial.cyclotomic k ℤ) ∣ f ↔ ev z f = 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    have : ev z (Polynomial.toLaurent (Polynomial.cyclotomic k ℤ)) = 0 := by
      rw [ev_toLaurent]
      have := hz.isRoot_cyclotomic hk
      simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using this
    rw [map_mul, this, zero_mul]
  · intro h
    obtain ⟨n, p, hp⟩ := exists_T_pow f
    have h1 : ev z (Polynomial.toLaurent p) = 0 := by
      rw [hp, map_mul, h, zero_mul]
    rw [ev_toLaurent] at h1
    have h2 : Polynomial.cyclotomic k ℤ ∣ p := by
      rw [Polynomial.cyclotomic_eq_minpoly hz hk]
      exact minpoly.isIntegrallyClosed_dvd (hz.isIntegral hk) h1
    have h3 : Polynomial.toLaurent (Polynomial.cyclotomic k ℤ) ∣ f * T n := by
      rw [← hp]; exact map_dvd _ h2
    exact (isUnit_T (R := ℤ) n).dvd_mul_right.mp h3


/-! ### Step 1: the Frobenius congruence -/

/-- In `ℤ[X]`, `g^(p^a) - g(X^(p^a))` is `p` times a polynomial. -/
theorem poly_frob {p : ℕ} (hp : p.Prime) (a : ℕ) (g : Polynomial ℤ) :
    ∃ h : Polynomial ℤ, g ^ (p ^ a) - Polynomial.expand ℤ (p ^ a) g = Polynomial.C (p : ℤ) * h := by
  haveI : Fact p.Prime := ⟨hp⟩
  have key : ∀ f : Polynomial (ZMod p), f ^ (p ^ a) = Polynomial.expand (ZMod p) (p ^ a) f := by
    intro f
    induction a with
    | zero => simp
    | succ a ih =>
      rw [pow_succ, pow_mul, ih, ← map_pow, ← ZMod.expand_card f, ← Polynomial.expand_mul]
  have h0 : Polynomial.map (Int.castRingHom (ZMod p))
      (g ^ (p ^ a) - Polynomial.expand ℤ (p ^ a) g) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_pow, key, sub_eq_zero]
    exact (Polynomial.map_expand).symm
  have h1 : Polynomial.C (p : ℤ) ∣ g ^ (p ^ a) - Polynomial.expand ℤ (p ^ a) g := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have := congrArg (fun f => f.coeff i) h0
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp this
  exact h1

/-- **Step 1.**  For a root of unity `z` and any `f ∈ ℤ[q, q⁻¹]`,
`f(z^(p^a)) = f(z)^(p^a) + p * y` with `y` an algebraic integer. -/
theorem frob_ev {p : ℕ} (hp : p.Prime) (a : ℕ) {k : ℕ} (hk : 0 < k) (z : ℂˣ)
    (hz : IsPrimitiveRoot (z : ℂ) k) (f : LP) :
    ∃ y : ℂ, IsIntegral ℤ y ∧ ev (z ^ (p ^ a)) f = (ev z f) ^ (p ^ a) + p * y := by
  obtain ⟨n, g, hg⟩ := exists_T_pow f
  have hf : f = Polynomial.toLaurent g * T (-(n : ℤ)) := by
    rw [hg, mul_assoc, ← T_add]; simp
  obtain ⟨h, hh⟩ := poly_frob hp a g
  have hint : IsIntegral ℤ (z : ℂ) := hz.isIntegral hk
  have hzi : IsPrimitiveRoot (((z⁻¹ : ℂˣ)) : ℂ) k := by simpa using hz.inv
  have hinti : IsIntegral ℤ (((z⁻¹ : ℂˣ)) : ℂ) := hzi.isIntegral hk
  have hmem : Polynomial.aeval (z : ℂ) h ∈ integralClosure ℤ ℂ := by
    have hz' : (z : ℂ) ∈ integralClosure ℤ ℂ := hint
    have : Algebra.adjoin ℤ {(z : ℂ)} ≤ integralClosure ℤ ℂ :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr hz')
    apply this
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨h, rfl⟩
  set u : ℂ := (((z ^ (-(n : ℤ)) : ℂˣ)) : ℂ) with hu
  have hu' : u = ((z⁻¹ : ℂˣ) : ℂ) ^ n := by
    rw [hu, zpow_neg, zpow_natCast, ← inv_pow]; simp
  have huint : IsIntegral ℤ u := by rw [hu']; exact hinti.pow n
  refine ⟨-(Polynomial.aeval (z : ℂ) h) * u ^ (p ^ a), ?_, ?_⟩
  · exact (hmem.neg).mul (huint.pow _) |> fun h => by simpa using h
  · have e1 : ev z f = Polynomial.aeval (z : ℂ) g * u := by
      rw [hf, map_mul, ev_toLaurent, ev_T]
    have e2 : ev (z ^ (p ^ a)) f =
        Polynomial.aeval ((z : ℂ) ^ (p ^ a)) g * u ^ (p ^ a) := by
      have hpw : (z ^ (p ^ a)) ^ (-(n : ℤ)) = (z ^ (-(n : ℤ))) ^ (p ^ a) := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
      rw [hf, map_mul, ev_toLaurent, ev_T, hpw, Units.val_pow_eq_pow_val,
        Units.val_pow_eq_pow_val, ← hu]
    have e3 := congrArg (Polynomial.aeval (z : ℂ)) hh
    rw [map_sub, map_pow, Polynomial.expand_aeval, map_mul, Polynomial.aeval_C] at e3
    rw [e1, e2, mul_pow]
    have e4 : Polynomial.aeval ((z : ℂ) ^ (p ^ a)) g =
        Polynomial.aeval (z : ℂ) g ^ (p ^ a) - (p : ℂ) * Polynomial.aeval (z : ℂ) h := by
      simp only [eq_intCast, Int.cast_natCast, algebraMap_int_eq] at e3
      linear_combination (-1 : ℂ) * e3
    rw [e4]; ring

/-! ### Step 2 as a hypothesis, and the theorem -/

/-- **Step 2 of the write-up, as a hypothesis (NOT proved here).**  For the bottom index `l`,
no value `S_w(ζ)` at a primitive `l`-th root of unity `ζ` is a nonzero multiple of a rational
prime by an algebraic integer. -/
def Step2 (l : ℕ) : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (ζ : ℂˣ), IsPrimitiveRoot (ζ : ℂ) l → ∀ (w : List ℤ) (y : ℂ),
    IsIntegral ℤ y → ev ζ (S w) = (p : ℂ) * y → ev ζ (S w) = 0

/-- Step 1 packaged: `Φ_k ∣ S` with `k = p^a l` makes `S(ω_l)` a multiple of `p` by an
algebraic integer, for `ω_l = ω^(p^a)`.  Proved. -/
theorem step1 {p a l : ℕ} (hp : p.Prime) (hl : 0 < l) (w : List ℤ)
    (hdiv : Polynomial.toLaurent (Polynomial.cyclotomic (p ^ a * l) ℤ) ∣ S w) :
    ∃ (ζ : ℂˣ) (y : ℂ), IsPrimitiveRoot (ζ : ℂ) l ∧ IsIntegral ℤ y ∧
      ev ζ (S w) = (p : ℂ) * y := by
  have hk : 0 < p ^ a * l := Nat.mul_pos (pow_pos hp.pos a) hl
  have hz : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / ((p ^ a * l : ℕ) : ℂ)))
      (p ^ a * l) := Complex.isPrimitiveRoot_exp _ hk.ne'
  let z : ℂˣ := Units.mk0 _ (hz.ne_zero hk.ne')
  have hz' : IsPrimitiveRoot (z : ℂ) (p ^ a * l) := hz
  have h0 : ev z (S w) = 0 := (cyc_dvd_iff hk z hz' (S w)).mp hdiv
  obtain ⟨y, hy, hyeq⟩ := frob_ev hp a hk z hz' (S w)
  refine ⟨z ^ (p ^ a), y, ?_, hy, ?_⟩
  · rw [Units.val_pow_eq_pow_val]
    exact hz'.pow hk rfl
  · rw [hyeq, h0]
    rw [zero_pow (pow_pos hp.pos a).ne', zero_add]

/-- **The theorem of `statement.tex`, given Step 2.** -/
theorem dc_of_step2 {p a l : ℕ} (hp : p.Prime) (hl : 0 < l) (hStep2 : Step2 l) (w : List ℤ)
    (hdiv : Polynomial.toLaurent (Polynomial.cyclotomic (p ^ a * l) ℤ) ∣ S w) :
    Polynomial.toLaurent (Polynomial.cyclotomic l ℤ) ∣ S w := by
  obtain ⟨ζ, y, hζ, hy, hyeq⟩ := step1 hp hl w hdiv
  have h0 := hStep2 p hp ζ hζ w y hy hyeq
  exact (cyc_dvd_iff hl ζ hζ (S w)).mpr h0

/-! ### The case `l = 2`, fully proved (Step 2 by an explicit 12-state closure) -/

/-- The unit `-1 = ω_2`, the primitive square root of unity. -/
def negOne : ℂˣ := -1

theorem ev_negOne_T (n : ℤ) : ev negOne (T n) = if n % 2 = 0 then 1 else -1 := by
  rw [ev_T]
  have : ((negOne ^ n : ℂˣ) : ℂ) = (-1 : ℂ) ^ n := by
    rw [Units.val_zpow_eq_zpow_val]; simp [negOne]
  rw [this]
  split_ifs with h
  · exact Even.neg_one_zpow ⟨n / 2, by omega⟩
  · exact Odd.neg_one_zpow ⟨n / 2, by omega⟩

theorem ev_negOne_qint (c : ℤ) : ev negOne (qint c) = if c % 2 = 0 then 0 else 1 := by
  have h := qint_mul c
  have h2 := congrArg (ev negOne) h
  rw [map_mul, map_sub, ev_T, map_one, map_sub, ev_T, map_one] at h2
  have e : ((negOne ^ (1:ℤ) : ℂˣ) : ℂ) = -1 := by simp [negOne]
  rw [e] at h2
  have h3 := ev_negOne_T c
  rw [ev_T] at h3
  split_ifs at h3 ⊢ with h
  · rw [h3] at h2; linear_combination (-1/2 : ℂ) * h2
  · rw [h3] at h2; linear_combination (-1/2 : ℂ) * h2


/-- The 12 reachable states `(S_{i-1}(-1), S_i(-1), parity of c_i)` of the recurrence at `q = -1`. -/
def P2 : List (ℤ × ℤ × ℤ) :=
  [(0,1,0), (-1,-1,1), (-1,0,0), (-1,0,1), (-1,1,0), (0,-1,0), (0,-1,1), (0,1,1),
   (1,-1,0), (1,0,0), (1,0,1), (1,1,1)]

/-- The recurrence at `q = -1`, on states with the parity of the last quotient. -/
def stepP (st : ℤ × ℤ × ℤ) (r : ℤ) : ℤ × ℤ × ℤ :=
  (st.2.1, r * st.2.1 - (1 - 2 * ((st.2.2 + 1) % 2)) * st.1, r)

theorem P2_closed : ∀ st ∈ P2, ∀ r ∈ [(0 : ℤ), 1], stepP st r ∈ P2 := by decide

theorem P2_vals : ∀ st ∈ P2, st.2.1 = 0 ∨ st.2.1 = 1 ∨ st.2.1 = -1 := by decide

def RelZ (A : LP × LP × ℤ) (st : ℤ × ℤ × ℤ) : Prop :=
  ev negOne A.1 = (st.1 : ℂ) ∧ ev negOne A.2.1 = (st.2.1 : ℂ) ∧ A.2.2 % 2 = st.2.2

theorem step_relZ {A : LP × LP × ℤ} {st : ℤ × ℤ × ℤ} (h : RelZ A st) (c : ℤ) :
    RelZ (step A c) (stepP st (c % 2)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h2, ?_, rfl⟩
  show ev negOne (qint c * A.2.1 - T (A.2.2 - 1) * A.1) = _
  rw [map_sub, map_mul, map_mul, ev_negOne_qint, ev_negOne_T, h1, h2]
  simp only [stepP]
  have hc := Int.emod_two_eq_zero_or_one c
  have hcl := Int.emod_two_eq_zero_or_one A.2.2
  rcases hc with hc | hc <;> rcases hcl with hcl | hcl
  · have : (A.2.2 - 1) % 2 ≠ 0 := by omega
    have h4 : (st.2.2 + 1) % 2 = 1 := by omega
    simp [hc, this, h4]
  · have : (A.2.2 - 1) % 2 = 0 := by omega
    have h4 : (st.2.2 + 1) % 2 = 0 := by omega
    simp [hc, this, h4]
  · have : (A.2.2 - 1) % 2 ≠ 0 := by omega
    have h4 : (st.2.2 + 1) % 2 = 1 := by omega
    simp [hc, this, h4]
  · have : (A.2.2 - 1) % 2 = 0 := by omega
    have h4 : (st.2.2 + 1) % 2 = 0 := by omega
    simp [hc, this, h4]

theorem fold_relZ : ∀ (w : List ℤ) (A : LP × LP × ℤ) (st : ℤ × ℤ × ℤ), RelZ A st → st ∈ P2 →
    ∃ st' ∈ P2, RelZ (w.foldl step A) st' := by
  intro w
  induction w with
  | nil => intro A st h hs; exact ⟨st, hs, h⟩
  | cons c w ih =>
    intro A st h hs
    have hr : c % 2 ∈ [(0 : ℤ), 1] := by
      have := Int.emod_two_eq_zero_or_one c
      rcases this with h | h <;> simp [h]
    exact ih _ _ (step_relZ h c) (P2_closed st hs _ hr)

theorem ev_S_negOne (w : List ℤ) :
    ev negOne (S w) = 0 ∨ ev negOne (S w) = 1 ∨ ev negOne (S w) = -1 := by
  have h0 : RelZ (0, 1, 0) (0, 1, 0) := ⟨by simp, by simp, by simp⟩
  obtain ⟨st, hst, hrel⟩ := fold_relZ w (0, 1, 0) (0, 1, 0) h0 (by simp [P2])
  have hS : ev negOne (S w) = (st.2.1 : ℂ) := hrel.2.1
  rw [hS]
  rcases P2_vals st hst with h | h | h <;> simp [h]


/-- A rational prime is not a unit multiple of an algebraic integer that is `±1 / p`. -/
theorem not_integral_inv (p : ℕ) (hp : p.Prime) (v : ℤ) (hv : v = 1 ∨ v = -1) (y : ℂ)
    (hy : IsIntegral ℤ y) (h : (v : ℂ) = (p : ℂ) * y) : False := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hyq : y = ((v / p : ℚ) : ℂ) := by
    have hp0' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    push_cast
    field_simp
    linear_combination -h
  have hint : IsIntegral ℤ (v / p : ℚ) := by
    rw [hyq] at hy
    exact (isIntegral_algebraMap_iff (A := ℚ) (B := ℂ) (RingHom.injective (algebraMap ℚ ℂ))).mp hy
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  simp only [eq_intCast] at hn
  have : (n : ℚ) * p = v := by rw [hn]; field_simp
  have h2 : n * (p : ℤ) = v := by exact_mod_cast this
  have h3 : (p : ℤ) ∣ v := ⟨n, by linarith⟩
  have h4 : (p : ℤ) ∣ 1 := by
    rcases hv with rfl | rfl
    · exact h3
    · simpa using h3
  have := Int.le_of_dvd one_pos h4
  have := hp.two_le
  omega

/-- **Step 2 for `l = 2`, proved.** -/
theorem step2_two : Step2 2 := by
  intro p hp ζ hζ w y hy h
  have hζ1 : ζ = negOne := by
    apply Units.ext
    have := hζ.eq_neg_one_of_two_right
    simpa [negOne] using this
  subst hζ1
  rcases ev_S_negOne w with h0 | h1 | h1
  · exact h0
  · exfalso
    exact not_integral_inv p hp 1 (Or.inl rfl) y hy (by rw [h1] at h; simpa using h)
  · exfalso
    exact not_integral_inv p hp (-1) (Or.inr rfl) y hy (by rw [h1] at h; simpa using h)


/-- **The theorem of `statement.tex` for `l = 2`, unconditional.**  For `k = 2 p^a`,
`Φ_k ∣ S` implies `Φ_2 ∣ S` (every prime `p`, every `a`, every integer word). -/
theorem dc_theorem_a_two {p a : ℕ} (hp : p.Prime) (w : List ℤ)
    (hdiv : Polynomial.toLaurent (Polynomial.cyclotomic (p ^ a * 2) ℤ) ∣ S w) :
    Polynomial.toLaurent (Polynomial.cyclotomic 2 ℤ) ∣ S w :=
  dc_of_step2 hp (by norm_num) step2_two w hdiv

/-- The statement of `statement.tex` for `l ∈ {2,3,4,5}` with Step 2 as an explicit
hypothesis.  (`Step2 l` is hypothesised for the given `l`; nothing here proves it.) -/
theorem dc_theorem_a {l : ℕ} (hl : l ∈ ({2, 3, 4, 5} : Finset ℕ)) (hStep2 : Step2 l)
    {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (w : List ℤ)
    (hdiv : Polynomial.toLaurent (Polynomial.cyclotomic (p ^ a * l) ℤ) ∣ S w) :
    Polynomial.toLaurent (Polynomial.cyclotomic l ℤ) ∣ S w := by
  have hl0 : 0 < l := by simp at hl; omega
  exact dc_of_step2 hp hl0 hStep2 w hdiv

end

end DCTheoremA

#print axioms DCTheoremA.frob_ev
#print axioms DCTheoremA.step1
#print axioms DCTheoremA.dc_theorem_a
#print axioms DCTheoremA.step2_two
#print axioms DCTheoremA.dc_theorem_a_two
