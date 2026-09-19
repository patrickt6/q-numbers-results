-- statement_only: the statement compiles, the proofs are `sorry`. It is a finite check (4 <= k <= 24), not proved here.
import Mathlib

/-!
# length5-complete: the length-5 list is complete for `4 <= k <= 24` (verified, not proved)

Status: STATEMENT ONLY (`lean.state = "statement_only"`).  Every theorem below ends in
`sorry`; nothing here is proved.  The claim is a FINITE computation (moduli `4..24`, all
residue words in `(Z/k)^4`), recorded in the evidence folder as a Python check.  A Lean
proof would need a verified computable model of `Z[x]/Phi_k` and a proof that it agrees
with divisibility in `Z[q, q^-1]`; that was not attempted.  No `native_decide` (it would add
an axiom).

Source statement: `results/length5-complete/statement.tex`.

```
Phi_k | S_5  ==>  (c_2,c_3,c_4,c_5) mod k lies in the list      (checked for 4 <= k <= 24)
|V_5(k)| = 10k  (4 <= k <= 24, k != 5),     |V_5(5)| = 52
```

## Discrepancy inside the statement (recorded, not hidden)

Read literally, the first line (all `4 <= k <= 24`) is FALSE at `k = 5`, and the second line of
the same statement says why: `|V_5(5)| = 52`, whereas the list has only 50 residue words at
`k = 5`.  An exact recomputation with the evidence script `P4-length5-verify.py` (function
`solutions(k, 5)`) against the list, for every `k` from 2 to 24, gives: the list equals the
vanishing locus for every `k` in `2..24` except `k = 5`, where the locus is the list plus
exactly the two words `(2,2,2,2)` and `(3,3,3,3)` (the second is `-(2,2,2,2)` mod 5; the source's
remark on exceptional moduli gives `S_5(2,2,2,2) = Phi_5` and `Phi_5 | S_5(3,3,3,3)`).  So this file states:

* `length5_complete`: the list-inclusion for `4 <= k <= 24`, `k != 5` (the corrected reading);
* `length5_complete_five`: at `k = 5` the locus is the list together with those two words;
* `count_ne_five`, `count_five`: the two cardinalities.

The literal claim "list-inclusion at `k = 5` too" is NOT stated as a theorem because it is false.
This is a reshaping of the statement and is recorded in `status.json` too.

## Objects (same as in `length5`)

`LP = Z[q,q^-1]`, `qint c = [c]_q`, `S [c_2,...,c_5] = S_5`, `CycDvd k f` is
"`Phi_k | f` in `LP`", `InList k c2 c3 c4 c5` is "the residues lie in the list".
`V5 k` is the set of residue words `r in (Z/k)^4` such that `Phi_k | S_5` for every integer
lift (by `S_dvd_residue` this does not depend on the lift).  Cardinalities are `Set.ncard`.

## Not expressed

* Nothing dropped besides the `k = 5` correction above.
* The statement is about the exact locus for `k <= 24` only; nothing is claimed for larger `k`.
-/

open LaurentPolynomial
namespace Length5Complete
noncomputable section

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


/-- `(q⁻¹ - 1) [c]_{q⁻¹} = q^{-c} - 1`. -/
theorem qint_mul_inv (c : ℤ) : (T (-1) - 1) * invert (qint c) = T (-c) - 1 := by
  have h := congrArg (invert (R := ℤ)) (qint_mul c)
  simpa using h

/-- `[-c]_q = -q⁻¹ [c]_{q⁻¹}`. -/
theorem qint_neg (c : ℤ) : qint (-c) = -T (-1) * invert (qint c) := by
  apply mul_left_cancel₀ (T_one_sub_ne)
  rw [qint_mul]
  have h1 := qint_mul_inv c
  have h2 := T_one_mul_T_neg_one
  linear_combination (-1 : LP) * h1 + (invert (qint c)) * h2
  

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


/-! ### Cyclotomic divisibility and the second line of the statement -/

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

/-! ### Residue words: `V_j(k)` -/

/-- `ev` of the state of the recurrence, compared for two runs. -/
def EvEq (z : ℂˣ) (A B : LP × LP × ℤ) : Prop :=
  ev z A.1 = ev z B.1 ∧ ev z A.2.1 = ev z B.2.1 ∧ z ^ A.2.2 = z ^ B.2.2

theorem ev_qint_eq {k : ℕ} (z : ℂˣ) (hz : IsPrimitiveRoot (z : ℂ) k) (hk : 1 < k) (c c' : ℤ)
    (h : z ^ c = z ^ c') : ev z (qint c) = ev z (qint c') := by
  have hne : ev z (T 1 - 1) ≠ 0 := by
    rw [map_sub, ev_T, map_one, zpow_one]
    intro h0
    have h1 : (z : ℂ) = 1 := by linear_combination h0
    have := (hz.pow_eq_one_iff_dvd 1).mp (by simpa using h1)
    have := Nat.le_of_dvd one_pos this
    omega
  apply mul_left_cancel₀ hne
  rw [← map_mul, ← map_mul, qint_mul, qint_mul, map_sub, map_sub, ev_T, ev_T, h]

theorem step_evEq {k : ℕ} (z : ℂˣ) (hz : IsPrimitiveRoot (z : ℂ) k) (hk : 1 < k)
    {A B : LP × LP × ℤ} (h : EvEq z A B) {c c' : ℤ} (hc : z ^ c = z ^ c') :
    EvEq z (step A c) (step B c') := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h2, ?_, hc⟩
  show ev z (qint c * A.2.1 - T (A.2.2 - 1) * A.1) = ev z (qint c' * B.2.1 - T (B.2.2 - 1) * B.1)
  rw [map_sub, map_sub, map_mul, map_mul, map_mul, map_mul, ev_T, ev_T, ev_qint_eq z hz hk c c' hc,
    h1, h2, zpow_sub_one, zpow_sub_one, h3]


theorem fold_evEq {k : ℕ} (z : ℂˣ) (hz : IsPrimitiveRoot (z : ℂ) k) (hk : 1 < k) :
    ∀ (w w' : List ℤ) (A B : LP × LP × ℤ), EvEq z A B →
      w.map (Int.cast : ℤ → ZMod k) = w'.map (Int.cast : ℤ → ZMod k) →
      EvEq z (w.foldl step A) (w'.foldl step B) := by
  intro w
  induction w with
  | nil =>
    intro w' A B hAB hw
    cases w' with
    | nil => exact hAB
    | cons b w' => simp at hw
  | cons c w ih =>
    intro w' A B hAB hw
    cases w' with
    | nil => simp at hw
    | cons c' w' =>
      simp only [List.map_cons, List.cons.injEq] at hw
      have hc : z ^ c = z ^ c' := by
        have hd : (k : ℤ) ∣ c - c' := (ZMod.intCast_eq_intCast_iff_dvd_sub c' c k).mp hw.1.symm
        have := (hz.zpow_eq_one_iff_dvd (c - c')).mpr hd
        rw [zpow_sub₀ (hz.ne_zero (by omega))] at this
        apply Units.ext
        rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]
        exact div_eq_one_iff_eq (zpow_ne_zero _ (hz.ne_zero (by omega))) |>.mp this
      exact ih w' _ _ (step_evEq z hz hk hAB hc) hw.2

/-- The evaluation of `S_j` at a primitive `k`-th root depends only on the residues of the
word modulo `k` (`k > 1`). -/
theorem ev_S_residue {k : ℕ} (z : ℂˣ) (hz : IsPrimitiveRoot (z : ℂ) k) (hk : 1 < k)
    (w w' : List ℤ) (h : w.map (Int.cast : ℤ → ZMod k) = w'.map (Int.cast : ℤ → ZMod k)) :
    ev z (S w) = ev z (S w') :=
  (fold_evEq z hz hk w w' (0, 1, 0) (0, 1, 0) ⟨rfl, rfl, rfl⟩ h).2.1

/-- `Φ_k ∣ S_j` depends only on the residue word. -/
theorem S_dvd_residue {k : ℕ} (hk : 1 < k) (w w' : List ℤ)
    (h : w.map (Int.cast : ℤ → ZMod k) = w'.map (Int.cast : ℤ → ZMod k)) :
    Polynomial.toLaurent (Polynomial.cyclotomic k ℤ) ∣ S w ↔
    Polynomial.toLaurent (Polynomial.cyclotomic k ℤ) ∣ S w' := by
  have hk0 : 0 < k := by omega
  have hz : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / k)) k :=
    Complex.isPrimitiveRoot_exp k hk0.ne'
  let z : ℂˣ := Units.mk0 _ (hz.ne_zero hk0.ne')
  have hz' : IsPrimitiveRoot (z : ℂ) k := hz
  rw [cyc_dvd_iff hk0 z hz', cyc_dvd_iff hk0 z hz', ev_S_residue z hz' hk w w' h]

def Wlist : List (List ℤ) :=
  [[1, 2, 2, 1], [1, 3, 1, 2], [2, 1, 3, 1], [2, 2, 1, 3], [3, 1, 2, 2]]

def InList (k : ℕ) (c₂ c₃ c₄ c₅ : ℤ) : Prop :=
  (∃ (ε : ℤ) (t : ZMod k), (ε = 1 ∨ ε = -1) ∧
    (((c₂ : ZMod k) = 0 ∧ (c₃ : ZMod k) = t ∧ (c₄ : ZMod k) = ε ∧ (c₅ : ZMod k) = ε) ∨
     ((c₂ : ZMod k) = ε ∧ (c₃ : ZMod k) = ε ∧ (c₄ : ZMod k) = t ∧ (c₅ : ZMod k) = 0) ∨
     ((c₂ : ZMod k) = t ∧ (c₃ : ZMod k) = 0 ∧ (c₄ : ZMod k) = ε - t ∧ (c₅ : ZMod k) = ε) ∨
     ((c₂ : ZMod k) = ε ∧ (c₃ : ZMod k) = t ∧ (c₄ : ZMod k) = 0 ∧ (c₅ : ZMod k) = ε - t) ∨
     ((c₂ : ZMod k) = t ∧ (c₃ : ZMod k) = ε ∧ (c₄ : ZMod k) = ε ∧ (c₅ : ZMod k) = ε - t))) ∨
  (∃ w ∈ Wlist, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
    [c₂, c₃, c₄, c₅].map (Int.cast : ℤ → ZMod k) = (w.map (fun x => ε * x)).map (Int.cast : ℤ → ZMod k))

def CycDvd (k : ℕ) (f : LP) : Prop := Polynomial.toLaurent (Polynomial.cyclotomic k ℤ) ∣ f

/-- The vanishing locus `V_5(k)`: residue words `(c_2, c_3, c_4, c_5)` with `Phi_k | S_5`
for every integer lift (independent of the lift by `S_dvd_residue`). -/
def V5 (k : ℕ) : Set (List (ZMod k)) :=
  {r | r.length = 4 ∧ ∀ w : List ℤ, w.map (Int.cast : ℤ → ZMod k) = r → CycDvd k (S w)}

/-- Completeness of the list, `4 <= k <= 24`, `k != 5` (finite check; not proved). -/
theorem length5_complete {k : ℕ} (h4 : 4 ≤ k) (h24 : k ≤ 24) (h5 : k ≠ 5)
    (c₂ c₃ c₄ c₅ : ℤ) (h : CycDvd k (S [c₂, c₃, c₄, c₅])) : InList k c₂ c₃ c₄ c₅ := by
  sorry

/-- At `k = 5` the locus is the list plus exactly the words `±(2,2,2,2)` (finite check; not proved). -/
theorem length5_complete_five (c₂ c₃ c₄ c₅ : ℤ) (h : CycDvd 5 (S [c₂, c₃, c₄, c₅])) :
    InList 5 c₂ c₃ c₄ c₅ ∨
    [c₂, c₃, c₄, c₅].map (Int.cast : ℤ → ZMod 5) = [2, 2, 2, 2] ∨
    [c₂, c₃, c₄, c₅].map (Int.cast : ℤ → ZMod 5) = [3, 3, 3, 3] := by
  sorry

/-- `|V_5(k)| = 10 k` for `4 <= k <= 24`, `k != 5` (finite check; not proved). -/
theorem count_ne_five {k : ℕ} (h4 : 4 ≤ k) (h24 : k ≤ 24) (h5 : k ≠ 5) :
    (V5 k).ncard = 10 * k := by
  sorry

/-- `|V_5(5)| = 52` (finite check; not proved). -/
theorem count_five : (V5 5).ncard = 52 := by
  sorry

end
end Length5Complete
