import Mathlib

/-!
# dc-theorem-a: downward closure of cyclotomic factors of the q-denominator, bottom index `l ≤ 5`

Source statement: `results/dc-theorem-a/statement.tex`.

```
l ∈ {2,3,4,5},  p prime,  a ≥ 1,  k = p^a l
Φ_k ∣ S  ⟹  Φ_l ∣ S
S = S_i, every i ≥ 1 and every integer word
```

## STATE: proved (`l = 2, 3, 4, 5`; the theorem is `dc_theorem_a_all`, with no hypothesis)

The write-up's proof has two steps.

* **Step 1 (Frobenius).**  If `ω` is a primitive `k`-th root of unity, `k = p^a l`, then
  `S(ω^{p^a}) ≡ S(ω)^{p^a} (mod p)`, so `Φ_k ∣ S` puts `S(ω_l)`, `ω_l = ω^{p^a}`, in `p`
  times an algebraic integer.  **Proved here, unconditionally** (`frob_ev`, `step1`).
* **Step 2 (finite orbit and content).**  For `l ∈ {2,3,4,5}`, the values `S(ω_l)`
  over all words form a finite set (sizes 3, 7, 9, 31) whose nonzero elements have content 1
  in `ℤ[ω_l]`, so none is divisible by a rational prime; hence `S(ω_l) = 0`.
  **Proved for `l = 2, 3, 4, 5`** (`step2_two`, `step2_three`, `step2_four`, `step2_five`), giving
  the unconditional theorems `dc_theorem_a_two`, `dc_theorem_a_three`, `dc_theorem_a_four`,
  `dc_theorem_a_five`, and `dc_theorem_a_all` (all four, no hypothesis).
  * `l = 2`: explicit closure of the 12 reachable states of the recurrence at `q = -1`
    (`P2_closed`, checked by `decide`).
  * `l = 3, 4, 5`: states `(S_{i-1}, S_i, c_i mod l)` are stored with
    `S` in integer coordinates over the power basis of `ℤ[ω_l]` (`step_rel` links them to the
    recurrence in `ℤ[q, q⁻¹]` evaluated at `ω_l`); the reachable set is computed by a
    breadth-first search inside Lean (`bfs`, `P3`, `P4`: 72 and 96 states for `l = 3, 4`) and closure under all
    `l` residues of the next quotient is checked by `decide +kernel` (`P3_closed`, `P4_closed`); every
    reachable `S` is `0` or has coordinates of gcd `1` (`P3_vals`).  For `l = 5` (600 states, 31 values
    in the write-up) the set is a candidate given as a search-tree literal `Tr5` (states are stored
    under integer keys `encS`, membership by `KTree.lookup`, `KTree.mem_of_lookup` needs no ordering
    invariant), produced by an external breadth-first search; a search run inside the kernel did not
    finish in reasonable memory.  Soundness does not depend on how the literal was produced: the
    kernel checks that every successor of every listed state, for all five residues, is listed
    (`Pk5_closed`), that the start state is listed (`Pk5_zero`), and that every listed `S` is `0` or
    of gcd `1` (`Pk5_vals`).  **Build cost:** the kernel check of `Pk5_closed` is memory hungry (measured
    in the running report, see `status.json` `build_notes`).  The finishing step
    (`content_coeff`) uses that `ℤ[ζ]` is the integral closure of `ℤ` in `ℚ(ζ)` (Mathlib,
    `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton`) and that `Φ_l` is monic of
    degree `φ(l)`, to show that `S(ζ) = p y` with `y` integral forces `p` to divide every
    power-basis coordinate.  This closes the write-up's remark that Step 1 gives an algebraic
    integer `y`, not an element of `ℤ[ω_l]`.

`dc_theorem_a_all` is the full statement of `statement.tex` with no hypothesis.  `dc_theorem_a` is
the same statement with `Step2 l` as an explicit hypothesis (kept because it is the reduction
`dc_of_step2` in the shape of the statement); `dc_theorem_a_all` supplies `Step2 l` by cases.

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



/-! ### Step 2, general machinery: a finite closed set of coordinate states -/

/-! #### Content: integral multiples of a low-degree cyclotomic integer -/


theorem integral_mem_adjoin {l : ℕ} (hl : 0 < l) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ l)
    (s : Polynomial ℤ) (p : ℕ) (hp : p.Prime) (y : ℂ) (hy : IsIntegral ℤ y)
    (h : Polynomial.aeval ζ s = (p : ℂ) * y) :
    ∃ t : Polynomial ℤ, y = Polynomial.aeval ζ t := by
  haveI : NeZero l := ⟨hl.ne'⟩
  let K := IntermediateField.adjoin ℚ {ζ}
  have hintQ : IsIntegral ℚ ζ := (hζ.isIntegral hl).tower_top
  haveI : IsCyclotomicExtension {l} ℚ K := by
    change IsCyclotomicExtension {l} ℚ (IntermediateField.adjoin ℚ {ζ}).toSubalgebra
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hintQ.isAlgebraic]
    exact hζ.adjoin_isCyclotomicExtension ℚ
  let ζ' : K := IntermediateField.AdjoinSimple.gen ℚ ζ
  have hζ' : IsPrimitiveRoot ζ' l := IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ
  let f : K →ₐ[ℤ] ℂ := IsScalarTower.toAlgHom ℤ K ℂ
  have hf : Function.Injective f := (algebraMap K ℂ).injective
  have hfζ : f ζ' = ζ := rfl
  have e : f (Polynomial.aeval ζ' s) = Polynomial.aeval ζ s := by
    have := Polynomial.aeval_algHom_apply f ζ' s
    rw [hfζ] at this; exact this.symm
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  let y' : K := (p : K)⁻¹ * Polynomial.aeval ζ' s
  have hy'f : f y' = y := by
    have : f y' = (p : ℂ)⁻¹ * f (Polynomial.aeval ζ' s) := by
      simp only [y', map_mul, map_inv₀, map_natCast]
    rw [this, e, h]; field_simp
  have hint : IsIntegral ℤ y' := by
    rw [← isIntegral_algHom_iff f hf, hy'f]; exact hy
  have hcl := IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton hζ'
  obtain ⟨⟨a, ha⟩, hay⟩ := hcl.isIntegral_iff.mp hint
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
  obtain ⟨t, ht⟩ := ha
  refine ⟨t, ?_⟩
  have : f a = y := by rw [← hy'f, ← hay]; rfl
  rw [← this, ← ht]
  have := Polynomial.aeval_algHom_apply f ζ' t
  rw [hfζ] at this
  exact this.symm

theorem content_coeff {l : ℕ} (hl : 0 < l) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ l)
    (s : Polynomial ℤ) (hs : s.natDegree < Nat.totient l) (p : ℕ) (hp : p.Prime) (y : ℂ)
    (hy : IsIntegral ℤ y) (h : Polynomial.aeval ζ s = (p : ℂ) * y) (i : ℕ) :
    (p : ℤ) ∣ s.coeff i := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := integral_mem_adjoin hl ζ hζ s p hp y hy h
  have h0 : Polynomial.aeval ζ (s - Polynomial.C (p : ℤ) * t) = 0 := by
    rw [map_sub, map_mul, h, ht, Polynomial.aeval_C]; simp
  have hd : Polynomial.cyclotomic l ℤ ∣ s - Polynomial.C (p : ℤ) * t := by
    rw [Polynomial.cyclotomic_eq_minpoly hζ hl]
    exact minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hl) h0
  obtain ⟨g, hg⟩ := hd
  have hm : Polynomial.map (Int.castRingHom (ZMod p)) s =
      Polynomial.map (Int.castRingHom (ZMod p)) (Polynomial.cyclotomic l ℤ) *
      Polynomial.map (Int.castRingHom (ZMod p)) g := by
    have := congrArg (Polynomial.map (Int.castRingHom (ZMod p))) hg
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C] at this
    have hp0 : (Int.castRingHom (ZMod p)) (p : ℤ) = 0 := by simp
    rw [hp0] at this
    simpa using this
  have hmon : (Polynomial.map (Int.castRingHom (ZMod p)) (Polynomial.cyclotomic l ℤ)).Monic :=
    (Polynomial.cyclotomic.monic l ℤ).map _
  have hdeg : (Polynomial.map (Int.castRingHom (ZMod p)) (Polynomial.cyclotomic l ℤ)).natDegree
      = Nat.totient l := by
    rw [(Polynomial.cyclotomic.monic l ℤ).natDegree_map, Polynomial.natDegree_cyclotomic]
  have hg0 : Polynomial.map (Int.castRingHom (ZMod p)) g = 0 := by
    by_contra hne
    have h1 := Polynomial.Monic.natDegree_mul' hmon hne
    have h2 : (Polynomial.map (Int.castRingHom (ZMod p)) s).natDegree < Nat.totient l :=
      lt_of_le_of_lt (Polynomial.natDegree_map_le) hs
    rw [hm, h1, hdeg] at h2
    omega
  rw [hg0, mul_zero] at hm
  have := congrArg (fun f => f.coeff i) hm
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp this

/-! #### Reduction of `ev` to residues -/

/-- `ev z (T n)` depends only on `n mod l`, for `z` a primitive `l`-th root of unity. -/
theorem ev_T_mod {l : ℕ} (hl : 0 < l) (z : ℂˣ) (hz : IsPrimitiveRoot (z : ℂ) l) (n : ℤ) :
    ev z (T n) = (z : ℂ) ^ (n % (l : ℤ)).toNat := by
  rw [ev_T]
  have hzl : z ^ (l : ℤ) = 1 := by
    apply Units.ext
    simpa using hz.pow_eq_one
  have hnn : 0 ≤ n % (l : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hl.ne')
  have h1 : n = n % (l : ℤ) + (l : ℤ) * (n / (l : ℤ)) := (Int.emod_add_mul_ediv n l).symm
  have h2 : z ^ n = z ^ (n % (l : ℤ)) := by
    conv_lhs => rw [h1]
    rw [zpow_add, zpow_mul, hzl, one_zpow, mul_one]
  rw [h2]
  have h3 : z ^ (n % (l : ℤ)) = z ^ (((n % (l : ℤ)).toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg hnn]
  rw [h3, zpow_natCast, Units.val_pow_eq_pow_val]

/-- `ev z (qint c)` depends only on `c mod l`. -/
theorem ev_qint_mod {l : ℕ} (hl : 1 < l) (z : ℂˣ) (hz : IsPrimitiveRoot (z : ℂ) l) (c : ℤ) :
    ev z (qint c) = ∑ j ∈ Finset.range (c % (l : ℤ)).toNat, (z : ℂ) ^ j := by
  have h := congrArg (ev z) (qint_mul c)
  rw [map_mul, map_sub, map_sub, map_one, ev_T_mod (by omega) z hz c] at h
  have h1 : ev z (T 1) = (z : ℂ) := by
    rw [ev_T]; simp
  rw [h1] at h
  have hne : (z : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (hz.ne_one hl)
  have hg := geom_sum_mul (z : ℂ) (c % (l : ℤ)).toNat
  apply mul_left_cancel₀ hne
  linear_combination h - hg

section Model

set_option linter.unusedSectionVars false

variable {V : Type} [AddCommGroup V] [DecidableEq V]

/-- multiplication by `ω^j`, `j` times the map `mulW`. -/
def pw (m : V → V) : ℕ → V → V
  | 0, v => v
  | j + 1, v => m (pw m j v)

/-- coordinates of `[r]_ω v = (1 + ω + ... + ω^(r-1)) v`. -/
def qv (m : V → V) : ℕ → V → V
  | 0, _ => 0
  | r + 1, v => qv m r v + pw m r v

/-- One step of the recurrence on coordinate states `(S_{i-1}, S_i, c_i mod l)`. -/
def stepM (l : ℕ) (m : V → V) (st : V × V × ℕ) (r : ℕ) : V × V × ℕ :=
  (st.2.1, qv m r st.2.1 - pw m ((st.2.2 + l - 1) % l) st.1, r)

theorem val_pw (ζ : ℂ) (val : V →+ ℂ) (m : V → V) (hm : ∀ v, val (m v) = ζ * val v) (j : ℕ)
    (v : V) : val (pw m j v) = ζ ^ j * val v := by
  induction j with
  | zero => simp [pw]
  | succ j ih => rw [pw, hm, ih, pow_succ]; ring

theorem val_qv (ζ : ℂ) (val : V →+ ℂ) (m : V → V) (hm : ∀ v, val (m v) = ζ * val v) (r : ℕ)
    (v : V) : val (qv m r v) = (∑ j ∈ Finset.range r, ζ ^ j) * val v := by
  induction r with
  | zero => simp [qv]
  | succ r ih => rw [qv, map_add, ih, val_pw ζ val m hm, Finset.sum_range_succ]; ring

def Rel (l : ℕ) (z : ℂˣ) (val : V →+ ℂ) (A : LP × LP × ℤ) (st : V × V × ℕ) : Prop :=
  ev z A.1 = val st.1 ∧ ev z A.2.1 = val st.2.1 ∧ A.2.2 % (l : ℤ) = (st.2.2 : ℤ)

theorem pred_mod {l : ℕ} (hl : 0 < l) (a : ℤ) (r : ℕ) (hr : a % (l : ℤ) = (r : ℤ)) :
    (a - 1) % (l : ℤ) = (((r + l - 1) % l : ℕ) : ℤ) := by
  have hr1 : 1 ≤ r + l := by omega
  have e : ((((r + l - 1) % l : ℕ)) : ℤ) = ((r : ℤ) + l - 1) % (l : ℤ) := by
    rw [Int.natCast_mod, Nat.cast_sub hr1]; push_cast; ring_nf
  rw [e, ← hr]
  have : (a - 1) - (a % (l : ℤ) + l - 1) = (l : ℤ) * (a / (l : ℤ) - 1) := by
    have := Int.emod_add_mul_ediv a l
    linear_combination (-1 : ℤ) * this
  exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (by rw [this]; exact Int.mul_emod_right _ _)

theorem step_rel {l : ℕ} (hl : 1 < l) (z : ℂˣ) (hz : IsPrimitiveRoot (z : ℂ) l)
    (val : V →+ ℂ) (m : V → V) (hm : ∀ v, val (m v) = (z : ℂ) * val v)
    {A : LP × LP × ℤ} {st : V × V × ℕ} (h : Rel l z val A st) (c : ℤ) :
    Rel l z val (step A c) (stepM l m st (c % (l : ℤ)).toNat) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h2, ?_, ?_⟩
  · show ev z (qint c * A.2.1 - T (A.2.2 - 1) * A.1) = val (qv m _ st.2.1 - pw m _ st.1)
    rw [map_sub, map_mul, map_mul, ev_qint_mod hl z hz, ev_T_mod (by omega) z hz, h1, h2,
      map_sub, val_qv _ val m hm, val_pw _ val m hm, pred_mod (by omega) _ _ h3,
      Int.toNat_natCast]
  · show (c % (l : ℤ)) = ((c % (l : ℤ)).toNat : ℤ)
    exact (Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast (by omega : l ≠ 0)))).symm

end Model

section Model2

variable {V : Type} [AddCommGroup V] [DecidableEq V]

theorem fold_rel {l : ℕ} (hl : 1 < l) (z : ℂˣ) (hz : IsPrimitiveRoot (z : ℂ) l)
    (val : V →+ ℂ) (m : V → V) (hm : ∀ v, val (m v) = (z : ℂ) * val v)
    (P : List (V × V × ℕ)) (hclosed : ∀ st ∈ P, ∀ r ∈ List.range l, stepM l m st r ∈ P) :
    ∀ (w : List ℤ) (A : LP × LP × ℤ) (st : V × V × ℕ), Rel l z val A st → st ∈ P →
      ∃ st' ∈ P, Rel l z val (w.foldl step A) st' := by
  intro w
  induction w with
  | nil => intro A st h hs; exact ⟨st, hs, h⟩
  | cons c w ih =>
    intro A st h hs
    have hr : (c % (l : ℤ)).toNat ∈ List.range l := by
      rw [List.mem_range]
      have h1 := Int.emod_nonneg c (by omega : (l : ℤ) ≠ 0)
      have h2 := Int.emod_lt_of_pos c (by omega : (0 : ℤ) < l)
      omega
    exact ih _ _ (step_rel hl z hz val m hm h c) (hclosed st hs _ hr)

/-- **Step 2 from a finite closed set of coordinate states.** -/
theorem step2_of_closed {l : ℕ} (hl : 1 < l) (m : V → V) (one : V) (cont : V → Bool)
    (P : List (V × V × ℕ)) (hP0 : ((0 : V), one, 0) ∈ P)
    (hclosed : ∀ st ∈ P, ∀ r ∈ List.range l, stepM l m st r ∈ P)
    (hvals : ∀ st ∈ P, st.2.1 = 0 ∨ cont st.2.1 = true)
    (hmodel : ∀ ζ : ℂ, IsPrimitiveRoot ζ l → ∃ (val : V →+ ℂ) (poly : V → Polynomial ℤ),
      (∀ v, val (m v) = ζ * val v) ∧ val one = 1 ∧
      (∀ v, val v = Polynomial.aeval ζ (poly v)) ∧
      (∀ v, (poly v).natDegree < Nat.totient l) ∧
      (∀ v, cont v = true → ∀ p : ℕ, p.Prime → (∀ i, (p : ℤ) ∣ (poly v).coeff i) → False)) :
    Step2 l := by
  intro p hp ζ hζ w y hy h
  obtain ⟨val, poly, hm, hone, hpoly, hdeg, hcont⟩ := hmodel (ζ : ℂ) hζ
  have h0 : Rel l ζ val ((0 : LP), (1 : LP), (0 : ℤ)) ((0 : V), one, 0) := by
    refine ⟨by simp, by simp [hone], by simp⟩
  obtain ⟨st, hst, hrel⟩ := fold_rel hl ζ hζ val m hm P hclosed w _ _ h0 hP0
  have hS : ev ζ (S w) = val st.2.1 := hrel.2.1
  rcases hvals st hst with h1 | h1
  · rw [hS, h1, map_zero]
  · exfalso
    rw [hS, hpoly] at h
    exact hcont _ h1 p hp (fun i => content_coeff (by omega) (ζ : ℂ) hζ _ (hdeg _) p hp y hy h i)

end Model2



section BFS
variable {V : Type} [AddCommGroup V] [DecidableEq V]

/-- Breadth-first closure of the coordinate states under `stepM`. -/
def bfs (l : ℕ) (m : V → V) : ℕ → List (V × V × ℕ) → List (V × V × ℕ) → List (V × V × ℕ)
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | n + 1, fr, seen =>
    let r := (fr.flatMap fun st => (List.range l).map (stepM l m st)).foldl
      (fun (acc : List (V × V × ℕ) × List (V × V × ℕ)) s =>
        if s ∈ acc.1 then acc else (acc.1 ++ [s], acc.2 ++ [s])) (seen, [])
    bfs l m n r.2 r.1

end BFS

/-- Coordinates `(a, b)` stand for `a + b ω` in `Z[ω_3]`; multiplication by `ω`. -/
def mulW3 (v : ℤ × ℤ) : ℤ × ℤ := (-v.2, v.1 - v.2)

def cont2 (v : ℤ × ℤ) : Bool := Int.gcd v.1 v.2 == 1

def P3 : List ((ℤ × ℤ) × (ℤ × ℤ) × ℕ) :=
  bfs 3 mulW3 100 [((0, 0), (1, 0), 0)] [((0, 0), (1, 0), 0)]

theorem P3_card : P3.length = 72 := by decide +kernel

theorem P3_closed : ∀ st ∈ P3, ∀ r ∈ List.range 3, stepM 3 mulW3 st r ∈ P3 := by decide +kernel

theorem P3_vals : ∀ st ∈ P3, st.2.1 = 0 ∨ cont2 st.2.1 = true := by decide +kernel

theorem root3_sum (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 3) : 1 + ζ + ζ ^ 2 = 0 := by
  have h3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hne : ζ - 1 ≠ 0 := sub_ne_zero.mpr (hζ.ne_one (by norm_num))
  apply mul_left_cancel₀ hne
  linear_combination h3

/-- The complex value `a + b ζ` of the coordinates `(a, b)`. -/
noncomputable def val2 (ζ : ℂ) : ℤ × ℤ →+ ℂ :=
  AddMonoidHom.mk' (fun v => (v.1 : ℂ) + (v.2 : ℂ) * ζ) (by
    intro x y; simp only [Prod.fst_add, Prod.snd_add]; push_cast; ring)

noncomputable def poly2 (v : ℤ × ℤ) : Polynomial ℤ := Polynomial.C v.1 + Polynomial.C v.2 * Polynomial.X

theorem poly2_deg (v : ℤ × ℤ) : (poly2 v).natDegree ≤ 1 := by
  unfold poly2; compute_degree

theorem cont2_spec (v : ℤ × ℤ) (h : cont2 v = true) (p : ℕ) (hp : p.Prime)
    (hd : ∀ i, (p : ℤ) ∣ (poly2 v).coeff i) : False := by
  have c0 : (poly2 v).coeff 0 = v.1 := by
    rw [poly2, Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_zero]; ring
  have c1 : (poly2 v).coeff 1 = v.2 := by
    rw [poly2, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_one]; simp
  have h0 := hd 0
  have h1 := hd 1
  rw [c0] at h0
  rw [c1] at h1
  have hg : Int.gcd v.1 v.2 = 1 := by simpa [cont2] using h
  have := Int.dvd_gcd h0 h1
  rw [hg] at this
  exact hp.ne_one (Nat.dvd_one.mp (by exact_mod_cast this))

theorem step2_three : Step2 3 := by
  refine step2_of_closed (by norm_num) mulW3 (1, 0) cont2 P3 (by decide +kernel) P3_closed P3_vals ?_
  intro ζ hζ
  have hΦ := root3_sum ζ hζ
  refine ⟨val2 ζ, poly2, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    simp only [val2, mulW3, AddMonoidHom.mk'_apply]
    push_cast
    linear_combination (-(v.2 : ℂ)) * hΦ
  · simp [val2]
  · intro v; simp [val2, poly2]
  · intro v
    have := poly2_deg v
    have h3 : Nat.totient 3 = 2 := by decide
    omega
  · intro v hv p hp hd; exact cont2_spec v hv p hp hd

theorem dc_theorem_a_three {p a : ℕ} (hp : p.Prime) (w : List ℤ)
    (hdiv : Polynomial.toLaurent (Polynomial.cyclotomic (p ^ a * 3) ℤ) ∣ S w) :
    Polynomial.toLaurent (Polynomial.cyclotomic 3 ℤ) ∣ S w :=
  dc_of_step2 hp (by norm_num) step2_three w hdiv



/-- Coordinates `(a, b)` stand for `a + b i` in `Z[ω_4] = Z[i]`; multiplication by `ω`. -/
def mulW4 (v : ℤ × ℤ) : ℤ × ℤ := (-v.2, v.1)

def P4 : List ((ℤ × ℤ) × (ℤ × ℤ) × ℕ) :=
  bfs 4 mulW4 100 [((0, 0), (1, 0), 0)] [((0, 0), (1, 0), 0)]

theorem P4_card : P4.length = 96 := by decide +kernel

theorem P4_closed : ∀ st ∈ P4, ∀ r ∈ List.range 4, stepM 4 mulW4 st r ∈ P4 := by decide +kernel

theorem P4_vals : ∀ st ∈ P4, st.2.1 = 0 ∨ cont2 st.2.1 = true := by decide +kernel

theorem root4_sq (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 4) : ζ ^ 2 + 1 = 0 := by
  have h4 : ζ ^ 4 = 1 := hζ.pow_eq_one
  have hne : ζ ^ 2 - 1 ≠ 0 :=
    sub_ne_zero.mpr (hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))
  apply mul_left_cancel₀ hne
  linear_combination h4

theorem step2_four : Step2 4 := by
  refine step2_of_closed (by norm_num) mulW4 (1, 0) cont2 P4 (by decide +kernel) P4_closed P4_vals ?_
  intro ζ hζ
  have hΦ := root4_sq ζ hζ
  refine ⟨val2 ζ, poly2, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    simp only [val2, mulW4, AddMonoidHom.mk'_apply]
    push_cast
    linear_combination (-(v.2 : ℂ)) * hΦ
  · simp [val2]
  · intro v; simp [val2, poly2]
  · intro v
    have := poly2_deg v
    have h4 : Nat.totient 4 = 2 := by decide
    omega
  · intro v hv p hp hd; exact cont2_spec v hv p hp hd

theorem dc_theorem_a_four {p a : ℕ} (hp : p.Prime) (w : List ℤ)
    (hdiv : Polynomial.toLaurent (Polynomial.cyclotomic (p ^ a * 4) ℤ) ∣ S w) :
    Polynomial.toLaurent (Polynomial.cyclotomic 4 ℤ) ∣ S w :=
  dc_of_step2 hp (by norm_num) step2_four w hdiv



/-- Coordinates `(a, b, c, d)` stand for `a + b ω + c ω² + d ω³` in `Z[ω_5]`; multiplication by `ω`
(`ω⁴ = -1 - ω - ω² - ω³`). -/
def mulW5 (v : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ := (-v.2.2.2, v.1 - v.2.2.2, v.2.1 - v.2.2.2, v.2.2.1 - v.2.2.2)

def cont4 (v : ℤ × ℤ × ℤ × ℤ) : Bool :=
  Nat.gcd (Nat.gcd (Int.gcd v.1 v.2.1) v.2.2.1.natAbs) v.2.2.2.natAbs == 1

theorem root5_sum (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have hne : ζ - 1 ≠ 0 := sub_ne_zero.mpr (hζ.ne_one (by norm_num))
  apply mul_left_cancel₀ hne
  linear_combination h5

noncomputable def val4 (ζ : ℂ) : ℤ × ℤ × ℤ × ℤ →+ ℂ :=
  AddMonoidHom.mk' (fun v => (v.1 : ℂ) + (v.2.1 : ℂ) * ζ + (v.2.2.1 : ℂ) * ζ ^ 2 + (v.2.2.2 : ℂ) * ζ ^ 3) (by
    intro x y; simp only [Prod.fst_add, Prod.snd_add]; push_cast; ring)

noncomputable def poly4 (v : ℤ × ℤ × ℤ × ℤ) : Polynomial ℤ :=
  Polynomial.C v.1 + Polynomial.C v.2.1 * Polynomial.X + Polynomial.C v.2.2.1 * Polynomial.X ^ 2 +
    Polynomial.C v.2.2.2 * Polynomial.X ^ 3

theorem poly4_deg (v : ℤ × ℤ × ℤ × ℤ) : (poly4 v).natDegree ≤ 3 := by
  unfold poly4; compute_degree

theorem cont4_spec (v : ℤ × ℤ × ℤ × ℤ) (h : cont4 v = true) (p : ℕ) (hp : p.Prime)
    (hd : ∀ i, (p : ℤ) ∣ (poly4 v).coeff i) : False := by
  have c0 : (poly4 v).coeff 0 = v.1 := by
    simp only [poly4, Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_zero, Polynomial.coeff_X_pow]; simp
  have c1 : (poly4 v).coeff 1 = v.2.1 := by
    simp only [poly4, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_one, Polynomial.coeff_X_pow]; simp
  have c2 : (poly4 v).coeff 2 = v.2.2.1 := by
    simp only [poly4, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_X_pow]; simp
  have c3 : (poly4 v).coeff 3 = v.2.2.2 := by
    simp only [poly4, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_X_pow]; simp
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  have h3 := hd 3
  rw [c0] at h0
  rw [c1] at h1
  rw [c2] at h2
  rw [c3] at h3
  have hg : Nat.gcd (Nat.gcd (Int.gcd v.1 v.2.1) v.2.2.1.natAbs) v.2.2.2.natAbs = 1 := by
    simpa [cont4] using h
  have g1 : p ∣ Int.gcd v.1 v.2.1 := by exact_mod_cast Int.dvd_gcd h0 h1
  have g2 : p ∣ Nat.gcd (Int.gcd v.1 v.2.1) v.2.2.1.natAbs := Nat.dvd_gcd g1 (Int.natCast_dvd.mp h2)
  have g3 : p ∣ Nat.gcd (Nat.gcd (Int.gcd v.1 v.2.1) v.2.2.1.natAbs) v.2.2.2.natAbs :=
    Nat.dvd_gcd g2 (Int.natCast_dvd.mp h3)
  rw [hg] at g3
  exact hp.ne_one (Nat.dvd_one.mp g3)

theorem step2_five_of_closed
    (P : List ((ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) × ℕ))
    (hP0 : (((0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)), 0) ∈ P)
    (hclosed : ∀ st ∈ P, ∀ r ∈ List.range 5, stepM 5 mulW5 st r ∈ P)
    (hvals : ∀ st ∈ P, st.2.1 = 0 ∨ cont4 st.2.1 = true) : Step2 5 := by
  refine step2_of_closed (by norm_num) mulW5 (1, 0, 0, 0) cont4 P hP0 hclosed hvals ?_
  intro ζ hζ
  have hΦ := root5_sum ζ hζ
  refine ⟨val4 ζ, poly4, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    simp only [val4, mulW5, AddMonoidHom.mk'_apply]
    push_cast
    linear_combination (-(v.2.2.2 : ℂ)) * hΦ
  · simp [val4]
  · intro v; simp [val4, poly4]
  · intro v
    have := poly4_deg v
    have h5 : Nat.totient 5 = 4 := by decide
    omega
  · intro v hv p hp hd; exact cont4_spec v hv p hp hd


/-! ### The reachable set for `l = 5`, stored by integer keys for fast membership tests -/

/-- Key of a coordinate vector (coordinates in `[-8, 7]`). -/
def enc4 (v : ℤ × ℤ × ℤ × ℤ) : ℕ :=
  (v.1 + 8).toNat + 16 * ((v.2.1 + 8).toNat + 16 * ((v.2.2.1 + 8).toNat + 16 * (v.2.2.2 + 8).toNat))

def dec4 (n : ℕ) : ℤ × ℤ × ℤ × ℤ :=
  (((n % 16 : ℕ) : ℤ) - 8, ((n / 16 % 16 : ℕ) : ℤ) - 8, ((n / 256 % 16 : ℕ) : ℤ) - 8,
    ((n / 4096 % 16 : ℕ) : ℤ) - 8)

def encS (st : (ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) × ℕ) : ℕ :=
  enc4 st.1 + 65536 * (enc4 st.2.1 + 65536 * st.2.2)

def decS (n : ℕ) : (ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) × ℕ :=
  (dec4 (n % 65536), dec4 (n / 65536 % 65536), n / 65536 / 65536)

/-- A binary tree of keys, used only as a fast membership structure (no ordering invariant is needed
for soundness). -/
inductive KTree
  | leaf : KTree
  | node : KTree → ℕ → KTree → KTree

def KTree.toList : KTree → List ℕ
  | .leaf => []
  | .node l k r => l.toList ++ [k] ++ r.toList

def KTree.lookup : KTree → ℕ → Bool
  | .leaf, _ => false
  | .node l x r, k => if k = x then true else if k < x then l.lookup k else r.lookup k

theorem KTree.mem_of_lookup : ∀ (t : KTree) (k : ℕ), t.lookup k = true → k ∈ t.toList
  | .leaf, _, h => by simp [KTree.lookup] at h
  | .node l x r, k, h => by
    simp only [KTree.lookup] at h
    split_ifs at h with h1 h2
    · simp [KTree.toList, h1]
    · have := KTree.mem_of_lookup l k h
      simp [KTree.toList, this]
    · have := KTree.mem_of_lookup r k h
      simp [KTree.toList, this]

/-- The keys of the 600 reachable states, as a search tree literal.  The literal was produced by an
external breadth-first search of the same recurrence (states `(S_{i-1}, S_i, c_i mod 5)` in the
coordinates of `mulW5`, keys as `encS`); it is only a candidate set.  Soundness rests on the
kernel-checked closure `Pk5_closed` and `Pk5_zero` below: every key decodes and re-encodes to
itself, every successor of every state lies in the set, and the start state does. -/
def Tr5 : KTree :=
  (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 1987545497 KTree.leaf) 2003273881 KTree.leaf) 2004322440 (KTree.node KTree.leaf 2004322441 KTree.leaf)) 2004322457 (KTree.node (KTree.node (KTree.node KTree.leaf 2004322713 KTree.leaf) 2004326809 KTree.leaf) 2004387992 (KTree.node KTree.leaf 2004388248 KTree.leaf))) 2004388249 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 2004392345 KTree.leaf) 2004392361 KTree.leaf) 2005436808 (KTree.node KTree.leaf 2005436824 KTree.leaf)) 2005440920 (KTree.node (KTree.node KTree.leaf 2005440921 KTree.leaf) 2005441177 (KTree.node KTree.leaf 2022213768 KTree.leaf)))) 2022217864 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 2022218120 KTree.leaf) 2022218136 KTree.leaf) 2022218137 (KTree.node KTree.leaf 2022283672 KTree.leaf)) 2023266696 (KTree.node (KTree.node (KTree.node KTree.leaf 2272753544 KTree.leaf) 2272753800 KTree.leaf) 2272753801 (KTree.node KTree.leaf 2272757897 KTree.leaf))) 2272757913 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 2272819336 KTree.leaf) 2272819352 KTree.leaf) 2272823448 (KTree.node KTree.leaf 2272823449 KTree.leaf)) 2272823705 (KTree.node (KTree.node KTree.leaf 2273867912 KTree.leaf) 2273872008 (KTree.node KTree.leaf 2273872264 KTree.leaf))))) 2273872280 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 2273872281 KTree.leaf) 2273937816 KTree.leaf) 2289530744 (KTree.node KTree.leaf 2289530760 KTree.leaf)) 2289534856 (KTree.node (KTree.node (KTree.node KTree.leaf 2289534857 KTree.leaf) 2289535113 KTree.leaf) 2289596296 (KTree.node KTree.leaf 2289600392 KTree.leaf))) 2289600648 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 2289600664 KTree.leaf) 2289600665 KTree.leaf) 2290579320 (KTree.node KTree.leaf 2290583416 KTree.leaf)) 2290583672 (KTree.node (KTree.node KTree.leaf 2290583688 KTree.leaf) 2290583689 (KTree.node KTree.leaf 2290644855 KTree.leaf)))) 2290645128 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 2290648968 KTree.leaf) 2290649208 KTree.leaf) 2290649223 (KTree.node KTree.leaf 2290649225 KTree.leaf)) 2290649240 (KTree.node (KTree.node (KTree.node KTree.leaf 2290649480 KTree.leaf) 2290653320 KTree.leaf) 2290653593 (KTree.node KTree.leaf 2290714759 KTree.leaf))) 2290714760 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 2290714776 KTree.leaf) 2290715032 KTree.leaf) 2290719128 (KTree.node KTree.leaf 2291697783 KTree.leaf)) 2291697784 (KTree.node (KTree.node KTree.leaf 2291697800 KTree.leaf) 2291698056 (KTree.node KTree.leaf 2291702152 KTree.leaf)))))) 2291763335 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 2291763591 KTree.leaf) 2291763592 KTree.leaf) 2291767688 (KTree.node KTree.leaf 2291767704 KTree.leaf)) 2307360632 (KTree.node (KTree.node (KTree.node KTree.leaf 2307426167 KTree.leaf) 2307426168 KTree.leaf) 2307426184 (KTree.node KTree.leaf 2307426440 KTree.leaf))) 2307430536 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 2308474743 KTree.leaf) 2308474999 KTree.leaf) 2308475000 (KTree.node KTree.leaf 2308479096 KTree.leaf)) 2308479112 (KTree.node (KTree.node KTree.leaf 2308540535 KTree.leaf) 2308540551 (KTree.node KTree.leaf 2308544647 KTree.leaf)))) 2308544648 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 2308544904 KTree.leaf) 2558031752 KTree.leaf) 2559014776 (KTree.node KTree.leaf 2559080311 KTree.leaf)) 2559080312 (KTree.node (KTree.node (KTree.node KTree.leaf 2559080328 KTree.leaf) 2559080584 KTree.leaf) 2559084680 (KTree.node KTree.leaf 2575857271 KTree.leaf))) 2575857527 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 2575857528 KTree.leaf) 2575861624 KTree.leaf) 2575861640 (KTree.node KTree.leaf 2576906087 KTree.leaf)) 2576906103 (KTree.node (KTree.node KTree.leaf 2576910199 KTree.leaf) 2576910200 (KTree.node KTree.leaf 2576910456 KTree.leaf))))) 2576971639 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 2576975735 KTree.leaf) 2576975991 KTree.leaf) 2576976007 (KTree.node KTree.leaf 2576976008 KTree.leaf)) 2578024567 (KTree.node (KTree.node (KTree.node KTree.leaf 2593752951 KTree.leaf) 6282508168 KTree.leaf) 6298236792 (KTree.node KTree.leaf 6299285367 KTree.leaf))) 6299285368 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 6299285384 KTree.leaf) 6299285640 KTree.leaf) 6299289736 (KTree.node KTree.leaf 6299350920 KTree.leaf)) 6299351176 (KTree.node (KTree.node KTree.leaf 6299351177 KTree.leaf) 6299355273 (KTree.node KTree.leaf 6299355289 KTree.leaf)))) 6300399752 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 6300399768 KTree.leaf) 6300403864 KTree.leaf) 6300403865 (KTree.node KTree.leaf 6300404121 KTree.leaf)) 6317176968 (KTree.node (KTree.node KTree.leaf 6317181064 KTree.leaf) 6317181320 (KTree.node KTree.leaf 6317181336 KTree.leaf))) 6317181337 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 6317246873 KTree.leaf) 6318229912 KTree.leaf) 6567720567 (KTree.node KTree.leaf 6567720823 KTree.leaf)) 6567720824 (KTree.node (KTree.node KTree.leaf 6567724920 KTree.leaf) 6567724936 (KTree.node KTree.leaf 6567786360 KTree.leaf))))))) 6567786376 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 6567790472 KTree.leaf) 6567790473 KTree.leaf) 6567790729 (KTree.node KTree.leaf 6568834952 KTree.leaf)) 6568839048 (KTree.node (KTree.node (KTree.node KTree.leaf 6568839304 KTree.leaf) 6568839320 KTree.leaf) 6568839321 (KTree.node KTree.leaf 6568904857 KTree.leaf))) 6584498023 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 6584498039 KTree.leaf) 6584502135 KTree.leaf) 6584502136 (KTree.node KTree.leaf 6584502392 KTree.leaf)) 6584563576 (KTree.node (KTree.node KTree.leaf 6584567672 KTree.leaf) 6584567928 (KTree.node KTree.leaf 6584567944 KTree.leaf)))) 6584567945 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 6585546615 KTree.leaf) 6585550711 KTree.leaf) 6585550967 (KTree.node KTree.leaf 6585550983 KTree.leaf)) 6585550984 (KTree.node (KTree.node (KTree.node KTree.leaf 6585612151 KTree.leaf) 6585612424 KTree.leaf) 6585616264 (KTree.node KTree.leaf 6585616504 KTree.leaf))) 6585616519 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 6585616521 KTree.leaf) 6585616536 KTree.leaf) 6585616776 (KTree.node KTree.leaf 6585620616 KTree.leaf)) 6585620889 (KTree.node (KTree.node KTree.leaf 6585682056 KTree.leaf) 6585682057 (KTree.node KTree.leaf 6585682073 KTree.leaf))))) 6585682329 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 6585686425 KTree.leaf) 6586665095 KTree.leaf) 6586665096 (KTree.node KTree.leaf 6586665112 KTree.leaf)) 6586665368 (KTree.node (KTree.node (KTree.node KTree.leaf 6586669464 KTree.leaf) 6586730648 KTree.leaf) 6586730904 (KTree.node KTree.leaf 6586730905 KTree.leaf))) 6586735001 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 6586735017 KTree.leaf) 6602328183 KTree.leaf) 6602393719 (KTree.node KTree.leaf 6602393720 KTree.leaf)) 6602393736 (KTree.node (KTree.node KTree.leaf 6602393992 KTree.leaf) 6602398088 (KTree.node KTree.leaf 6603442311 KTree.leaf)))) 6603442567 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 6603442568 KTree.leaf) 6603446664 KTree.leaf) 6603446680 (KTree.node KTree.leaf 6603508104 KTree.leaf)) 6603508120 (KTree.node (KTree.node KTree.leaf 6603512216 KTree.leaf) 6603512217 (KTree.node KTree.leaf 6603512473 KTree.leaf))) 6853003128 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 6853986167 KTree.leaf) 6854051703 KTree.leaf) 6854051704 (KTree.node KTree.leaf 6854051720 KTree.leaf)) 6854051976 (KTree.node (KTree.node KTree.leaf 6854056072 KTree.leaf) 6870828919 (KTree.node KTree.leaf 6870829175 KTree.leaf)))))) 6870829176 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 6870833272 KTree.leaf) 6870833288 KTree.leaf) 6871877751 (KTree.node KTree.leaf 6871877767 KTree.leaf)) 6871881863 (KTree.node (KTree.node (KTree.node KTree.leaf 6871881864 KTree.leaf) 6871882120 KTree.leaf) 6871943304 (KTree.node KTree.leaf 6871947400 KTree.leaf))) 6871947656 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 6871947672 KTree.leaf) 6871947673 KTree.leaf) 6872996248 (KTree.node KTree.leaf 6888724872 KTree.leaf)) 10577479544 (KTree.node (KTree.node KTree.leaf 10593208183 KTree.leaf) 10594256759 (KTree.node KTree.leaf 10594256760 KTree.leaf)))) 10594256776 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 10594257032 KTree.leaf) 10594261128 KTree.leaf) 10594317943 (KTree.node KTree.leaf 10594318199 KTree.leaf)) 10594318200 (KTree.node (KTree.node (KTree.node KTree.leaf 10594322296 KTree.leaf) 10594322312 KTree.leaf) 10595366776 (KTree.node KTree.leaf 10595366792 KTree.leaf))) 10595370888 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 10595370889 KTree.leaf) 10595371145 KTree.leaf) 10612144008 (KTree.node KTree.leaf 10612148104 KTree.leaf)) 10612148360 (KTree.node (KTree.node KTree.leaf 10612148376 KTree.leaf) 10612148377 (KTree.node KTree.leaf 10612209544 KTree.leaf))))) 10613196953 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 10862692215 KTree.leaf) 10862692471 KTree.leaf) 10862692472 (KTree.node KTree.leaf 10862696568 KTree.leaf)) 10862696584 (KTree.node (KTree.node (KTree.node KTree.leaf 10862753639 KTree.leaf) 10862753655 KTree.leaf) 10862757751 (KTree.node KTree.leaf 10862757752 KTree.leaf))) 10862758008 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 10863802232 KTree.leaf) 10863806328 KTree.leaf) 10863806584 (KTree.node KTree.leaf 10863806600 KTree.leaf)) 10863806601 (KTree.node (KTree.node KTree.leaf 10863867768 KTree.leaf) 10879469687 (KTree.node KTree.leaf 10879469703 KTree.leaf)))) 10879473799 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 10879473800 KTree.leaf) 10879474056 KTree.leaf) 10879530871 (KTree.node KTree.leaf 10879534967 KTree.leaf)) 10879535223 (KTree.node (KTree.node KTree.leaf 10879535239 KTree.leaf) 10879535240 (KTree.node KTree.leaf 10880518280 KTree.leaf))) 10880522376 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 10880522632 KTree.leaf) 10880522648 KTree.leaf) 10880522649 (KTree.node KTree.leaf 10880579447 KTree.leaf)) 10880579720 (KTree.node (KTree.node KTree.leaf 10880583560 KTree.leaf) 10880583800 (KTree.node KTree.leaf 10880583815 KTree.leaf)))))))) 10880583817 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 10880583832 KTree.leaf) 10880584072 KTree.leaf) 10880587912 (KTree.node KTree.leaf 10880588185 KTree.leaf)) 10880644983 (KTree.node (KTree.node (KTree.node KTree.leaf 10880644984 KTree.leaf) 10880645000 KTree.leaf) 10880645256 (KTree.node KTree.leaf 10880649352 KTree.leaf))) 10881632392 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 10881632393 KTree.leaf) 10881632409 KTree.leaf) 10881632665 (KTree.node KTree.leaf 10881636761 KTree.leaf)) 10881693576 (KTree.node (KTree.node KTree.leaf 10881693832 KTree.leaf) 10881693833 (KTree.node KTree.leaf 10881697929 KTree.leaf)))) 10881697945 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 10897299864 KTree.leaf) 10897361031 KTree.leaf) 10897361032 (KTree.node KTree.leaf 10897361048 KTree.leaf)) 10897361304 (KTree.node (KTree.node (KTree.node KTree.leaf 10897365400 KTree.leaf) 10898409624 KTree.leaf) 10898409880 (KTree.node KTree.leaf 10898409881 KTree.leaf))) 10898413977 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 10898413993 KTree.leaf) 10898471048 KTree.leaf) 10898471064 (KTree.node KTree.leaf 10898475160 KTree.leaf)) 10898475161 (KTree.node (KTree.node KTree.leaf 10898475417 KTree.leaf) 11147970679 (KTree.node KTree.leaf 11148958088 KTree.leaf))))) 11149019255 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 11149019256 KTree.leaf) 11149019272 KTree.leaf) 11149019528 (KTree.node KTree.leaf 11149023624 KTree.leaf)) 11165796487 (KTree.node (KTree.node (KTree.node KTree.leaf 11165796743 KTree.leaf) 11165796744 KTree.leaf) 11165800840 (KTree.node KTree.leaf 11165800856 KTree.leaf))) 11166845320 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 11166845336 KTree.leaf) 11166849432 KTree.leaf) 11166849433 (KTree.node KTree.leaf 11166849689 KTree.leaf)) 11166906504 (KTree.node (KTree.node KTree.leaf 11166910600 KTree.leaf) 11166910856 (KTree.node KTree.leaf 11166910872 KTree.leaf)))) 11166910873 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 11167959449 KTree.leaf) 11183688088 KTree.leaf) 14872447095 (KTree.node KTree.leaf 14888180104 KTree.leaf)) 14889224311 (KTree.node (KTree.node KTree.leaf 14889224312 KTree.leaf) 14889224328 (KTree.node KTree.leaf 14889224584 KTree.leaf))) 14889228680 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 14889289591 KTree.leaf) 14889289847 KTree.leaf) 14889289848 (KTree.node KTree.leaf 14889293944 KTree.leaf)) 14889293960 (KTree.node (KTree.node KTree.leaf 14890334055 KTree.leaf) 14890334071 (KTree.node KTree.leaf 14890338167 KTree.leaf)))))) 14890338168 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 14890338424 KTree.leaf) 14907111288 KTree.leaf) 14907115384 (KTree.node KTree.leaf 14907115640 KTree.leaf)) 14907115656 (KTree.node (KTree.node (KTree.node KTree.leaf 14907115657 KTree.leaf) 14907180920 KTree.leaf) 14908159864 (KTree.node KTree.leaf 15157659783 KTree.leaf))) 15157660039 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 15157660040 KTree.leaf) 15157664136 KTree.leaf) 15157664152 (KTree.node KTree.leaf 15157725303 KTree.leaf)) 15157725319 (KTree.node (KTree.node KTree.leaf 15157729415 KTree.leaf) 15157729416 (KTree.node KTree.leaf 15157729672 KTree.leaf)))) 15158769527 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 15158773623 KTree.leaf) 15158773879 KTree.leaf) 15158773895 (KTree.node KTree.leaf 15158773896 KTree.leaf)) 15158839159 (KTree.node (KTree.node (KTree.node KTree.leaf 15174437256 KTree.leaf) 15174437272 KTree.leaf) 15174441368 (KTree.node KTree.leaf 15174441369 KTree.leaf))) 15174441625 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 15174502536 KTree.leaf) 15174506632 KTree.leaf) 15174506888 (KTree.node KTree.leaf 15174506904 KTree.leaf)) 15174506905 (KTree.node (KTree.node KTree.leaf 15175481480 KTree.leaf) 15175485576 (KTree.node KTree.leaf 15175485832 KTree.leaf))))) 15175485848 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 15175485849 KTree.leaf) 15175546743 KTree.leaf) 15175547016 (KTree.node KTree.leaf 15175550856 KTree.leaf)) 15175551096 (KTree.node (KTree.node (KTree.node KTree.leaf 15175551111 KTree.leaf) 15175551113 KTree.leaf) 15175551128 (KTree.node KTree.leaf 15175551368 KTree.leaf))) 15175555208 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 15175555481 KTree.leaf) 15175616375 KTree.leaf) 15175616376 (KTree.node KTree.leaf 15175616392 KTree.leaf)) 15175616648 (KTree.node (KTree.node KTree.leaf 15175620744 KTree.leaf) 15176595319 (KTree.node KTree.leaf 15176595320 KTree.leaf)))) 15176595336 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 15176595592 KTree.leaf) 15176599688 KTree.leaf) 15176660599 (KTree.node KTree.leaf 15176660855 KTree.leaf)) 15176660856 (KTree.node (KTree.node KTree.leaf 15176664952 KTree.leaf) 15176664968 (KTree.node KTree.leaf 15192263065 KTree.leaf))) 15192328328 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 15192328329 KTree.leaf) 15192328345 KTree.leaf) 15192328601 (KTree.node KTree.leaf 15192332697 KTree.leaf)) 15193372552 (KTree.node (KTree.node KTree.leaf 15193372808 KTree.leaf) 15193372809 (KTree.node KTree.leaf 15193376905 KTree.leaf))))))) 15193376921 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 15193438072 KTree.leaf) 15193438088 KTree.leaf) 15193442184 (KTree.node KTree.leaf 15193442185 KTree.leaf)) 15193442441 (KTree.node (KTree.node (KTree.node KTree.leaf 15442942360 KTree.leaf) 15443921304 KTree.leaf) 15443986567 (KTree.node KTree.leaf 15443986568 KTree.leaf))) 15443986584 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 15443986840 KTree.leaf) 15443990936 KTree.leaf) 15460763800 (KTree.node KTree.leaf 15460764056 KTree.leaf)) 15460764057 (KTree.node (KTree.node KTree.leaf 15460768153 KTree.leaf) 15460768169 (KTree.node KTree.leaf 15461808264 KTree.leaf)))) 15461808280 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 15461812376 KTree.leaf) 15461812377 KTree.leaf) 15461812633 (KTree.node KTree.leaf 15461873544 KTree.leaf)) 15461877640 (KTree.node (KTree.node (KTree.node KTree.leaf 15461877896 KTree.leaf) 15461877912 KTree.leaf) 15461877913 (KTree.node KTree.leaf 15462922120 KTree.leaf))) 15478655129 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 19167418776 KTree.leaf) 19183143320 KTree.leaf) 19184191623 (KTree.node KTree.leaf 19184191624 KTree.leaf)) 19184191640 (KTree.node (KTree.node KTree.leaf 19184191896 KTree.leaf) 19184195992 (KTree.node KTree.leaf 19184257159 KTree.leaf))))) 19184257415 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 19184257416 KTree.leaf) 19184261512 KTree.leaf) 19184261528 (KTree.node KTree.leaf 19185305719 KTree.leaf)) 19185305735 (KTree.node (KTree.node (KTree.node KTree.leaf 19185309831 KTree.leaf) 19185309832 KTree.leaf) 19185310088 (KTree.node KTree.leaf 19202078583 KTree.leaf))) 19202082679 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 19202082935 KTree.leaf) 19202082951 KTree.leaf) 19202082952 (KTree.node KTree.leaf 19202148471 KTree.leaf)) 19203131255 (KTree.node (KTree.node KTree.leaf 19452627096 KTree.leaf) 19452627352 (KTree.node KTree.leaf 19452627353 KTree.leaf)))) 19452631449 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 19452631465 KTree.leaf) 19452692872 KTree.leaf) 19452692888 (KTree.node KTree.leaf 19452696984 KTree.leaf)) 19452696985 (KTree.node (KTree.node KTree.leaf 19452697241 KTree.leaf) 19453741192 (KTree.node KTree.leaf 19453745288 KTree.leaf))) 19453745544 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 19453745560 KTree.leaf) 19453745561 KTree.leaf) 19453811080 (KTree.node KTree.leaf 19469400200 KTree.leaf)) 19469400216 (KTree.node (KTree.node KTree.leaf 19469404312 KTree.leaf) 19469404313 (KTree.node KTree.leaf 19469404569 KTree.leaf)))))) 19469465736 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 19469469832 KTree.leaf) 19469470088 KTree.leaf) 19469470104 (KTree.node KTree.leaf 19469470105 KTree.leaf)) 19470448520 (KTree.node (KTree.node (KTree.node KTree.leaf 19470452616 KTree.leaf) 19470452872 KTree.leaf) 19470452888 (KTree.node KTree.leaf 19470452889 KTree.leaf))) 19470514039 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 19470514312 KTree.leaf) 19470518152 KTree.leaf) 19470518392 (KTree.node KTree.leaf 19470518407 KTree.leaf)) 19470518409 (KTree.node (KTree.node KTree.leaf 19470518424 KTree.leaf) 19470518664 (KTree.node KTree.leaf 19470522504 KTree.leaf)))) 19470522777 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 19470583927 KTree.leaf) 19470583928 KTree.leaf) 19470583944 (KTree.node KTree.leaf 19470584200 KTree.leaf)) 19470588296 (KTree.node (KTree.node (KTree.node KTree.leaf 19471566711 KTree.leaf) 19471566712 KTree.leaf) 19471566728 (KTree.node KTree.leaf 19471566984 KTree.leaf))) 19471571080 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 19471632247 KTree.leaf) 19471632503 KTree.leaf) 19471632504 (KTree.node KTree.leaf 19471636600 KTree.leaf)) 19471636616 (KTree.node (KTree.node KTree.leaf 19487225736 KTree.leaf) 19487291255 (KTree.node KTree.leaf 19487291256 KTree.leaf))))) 19487291272 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 19487291528 KTree.leaf) 19487295624 KTree.leaf) 19488339575 (KTree.node KTree.leaf 19488339831 KTree.leaf)) 19488339832 (KTree.node (KTree.node (KTree.node KTree.leaf 19488343928 KTree.leaf) 19488343944 KTree.leaf) 19488405351 (KTree.node KTree.leaf 19488405367 KTree.leaf))) 19488409463 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 19488409464 KTree.leaf) 19488409720 KTree.leaf) 19737905561 (KTree.node KTree.leaf 19738888345 KTree.leaf)) 19738953864 (KTree.node (KTree.node KTree.leaf 19738953865 KTree.leaf) 19738953881 (KTree.node KTree.leaf 19738954137 KTree.leaf)))) 19738958233 (KTree.node (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 19755726728 KTree.leaf) 19755726984 KTree.leaf) 19755726985 (KTree.node KTree.leaf 19755731081 KTree.leaf)) 19755731097 (KTree.node (KTree.node KTree.leaf 19756775288 KTree.leaf) 19756775304 (KTree.node KTree.leaf 19756779400 KTree.leaf))) 19756779401 (KTree.node (KTree.node (KTree.node (KTree.node KTree.leaf 19756779657 KTree.leaf) 19756840824 KTree.leaf) 19756844920 (KTree.node KTree.leaf 19756845176 KTree.leaf)) 19756845192 (KTree.node (KTree.node KTree.leaf 19756845193 KTree.leaf) 19757893496 (KTree.node KTree.leaf 19773618040 KTree.leaf)))))))))

/-- The candidate keys. -/
def Pk5 : List ℕ := Tr5.toList

theorem Pk5_card : Pk5.length = 600 := by decide +kernel

/-- The candidate set of coordinate states, decoded from its keys. -/
def P5 : List ((ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) × ℕ) := Pk5.map decS

theorem Pk5_closed : ∀ k ∈ Pk5, ∀ r ∈ List.range 5,
    decS (encS (stepM 5 mulW5 (decS k) r)) = stepM 5 mulW5 (decS k) r ∧
      Tr5.lookup (encS (stepM 5 mulW5 (decS k) r)) = true := by decide +kernel

theorem Pk5_zero : decS (encS (((0, 0, 0, 0), (1, 0, 0, 0), 0))) = (((0, 0, 0, 0), (1, 0, 0, 0), 0)) ∧
    Tr5.lookup (encS (((0, 0, 0, 0), (1, 0, 0, 0), 0))) = true := by decide +kernel

theorem Pk5_vals : ∀ k ∈ Pk5, (decS k).2.1 = 0 ∨ cont4 (decS k).2.1 = true := by decide +kernel

theorem P5_closed : ∀ st ∈ P5, ∀ r ∈ List.range 5, stepM 5 mulW5 st r ∈ P5 := by
  intro st hst r hr
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hst
  obtain ⟨h1, h2⟩ := Pk5_closed k hk r hr
  exact List.mem_map.mpr ⟨_, Tr5.mem_of_lookup _ h2, h1⟩

theorem P5_zero : (((0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)), 0) ∈ P5 :=
  List.mem_map.mpr ⟨_, Tr5.mem_of_lookup _ Pk5_zero.2, Pk5_zero.1⟩

theorem P5_vals : ∀ st ∈ P5, st.2.1 = 0 ∨ cont4 st.2.1 = true := by
  intro st hst
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hst
  exact Pk5_vals k hk

theorem step2_five : Step2 5 := step2_five_of_closed P5 P5_zero P5_closed P5_vals

theorem dc_theorem_a_five {p a : ℕ} (hp : p.Prime) (w : List ℤ)
    (hdiv : Polynomial.toLaurent (Polynomial.cyclotomic (p ^ a * 5) ℤ) ∣ S w) :
    Polynomial.toLaurent (Polynomial.cyclotomic 5 ℤ) ∣ S w :=
  dc_of_step2 hp (by norm_num) step2_five w hdiv

/-- **The theorem of `statement.tex`, with no hypothesis.**  For `l ∈ {2, 3, 4, 5}`, any prime `p`, any
`a ≥ 1` and any integer word (any length), `Φ_{p^a l} ∣ S` implies `Φ_l ∣ S` in `ℤ[q, q⁻¹]`. -/
theorem dc_theorem_a_all {l : ℕ} (hl : l ∈ ({2, 3, 4, 5} : Finset ℕ))
    {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (w : List ℤ)
    (hdiv : Polynomial.toLaurent (Polynomial.cyclotomic (p ^ a * l) ℤ) ∣ S w) :
    Polynomial.toLaurent (Polynomial.cyclotomic l ℤ) ∣ S w := by
  have h2 : Step2 l := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact step2_two
    · exact step2_three
    · exact step2_four
    · exact step2_five
  exact dc_theorem_a hl h2 hp ha w hdiv

end

end DCTheoremA

#print axioms DCTheoremA.frob_ev
#print axioms DCTheoremA.step1
#print axioms DCTheoremA.dc_theorem_a
#print axioms DCTheoremA.step2_two
#print axioms DCTheoremA.dc_theorem_a_two
#print axioms DCTheoremA.step2_three
#print axioms DCTheoremA.dc_theorem_a_three
#print axioms DCTheoremA.step2_four
#print axioms DCTheoremA.dc_theorem_a_four
#print axioms DCTheoremA.step2_five
#print axioms DCTheoremA.dc_theorem_a_five
#print axioms DCTheoremA.dc_theorem_a_all
