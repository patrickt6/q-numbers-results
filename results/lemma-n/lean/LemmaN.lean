import Mathlib

/-!
# lemma-n: negation symmetry of the q-denominator recurrence, at every length

Source statement: `results/lemma-n/statement.tex`.

```
S_j(w; -c_2,...,-c_j) = (-1)^{j-1} w^{-(j-1)} S_j(w^{-1}; c_2,...,c_j)
V_j(k) = -V_j(k)  for all j, k
```

## What is formalised

`S_j` is the q-denominator of the write-up: the bottom-left entry of the product of the
matrices `[[ [c]_q , -q^(c-1) ],[ 1 , 0 ]]`, i.e. the recurrence

```
S_{i+1} = [c_{i+1}]_q S_i - q^(c_i - 1) S_{i-1},    (S_0, S_1) = (0, 1)
```

(the exponent carries the PREVIOUS quotient), with `[c]_q = (1 - q^c)/(1 - q)` for every
integer `c`, so `[-c]_q = -q^(-c) [c]_q`.  Everything lives in `ℤ[q, q⁻¹] = LaurentPolynomial ℤ`,
`q = T 1`.  Definitions in Lean:

* `qint c`   is `[c]_q`; the theorem `qint_mul` says `(q - 1) [c]_q = q^c - 1` for all `c : ℤ`.
* `S w`      is `S_j` for the word `w = [c_2, ..., c_j]` (a list of length `j - 1`).
  `c_1` never enters (it is multiplied by `S_0 = 0`), as in the write-up.
* `S_neg`    is the first line: an identity in `ℤ[q, q⁻¹]`,
  `S (-w) = (-q⁻¹)^(j-1) * invert (S w)`, where `invert` is the ring automorphism
  `q ↦ q⁻¹` and `(-q⁻¹)^(j-1) = (-1)^(j-1) q^(-(j-1))`.  Specialising `q` to a
  unit `ω` gives the displayed identity with `S_j(ω^{-1}; c)` on the right
  (`S_neg_ev`).  The proof is the write-up's two-step induction, run on the state
  `(S_{i-1}, S_i, c_i)`.
* `V k j`    is the set of residue words `r ∈ (ZMod k)^(j-1)` such that the cyclotomic
  polynomial `Φ_k` divides `S w` in `ℤ[q, q⁻¹]` for every integer lift `w` of `r`.
  `S_dvd_residue` proves that divisibility does not depend on the lift (the write-up's
  residue-only lemma), so `V` is well defined; `exists_lift` shows lifts exist.
  `V_neg` is the second line: `r ∈ V k j ↔ -r ∈ V k j`.
  The step "vanishing at `ω⁻¹` iff at `ω`" of the write-up (Galois conjugation) is
  `cyc_dvd_iff`: `Φ_k ∣ f ↔ f(ω) = 0` for any primitive `k`-th root `ω ∈ ℂ`, used for both
  `ω` and `ω⁻¹`.

## Hypothesis mapping

* modulus `k`: `1 < k` in `V_neg` and `S_dvd_residue` (the write-up defines `V_i(k)` for
  `k > 1`; `statement.tex` says "all `k`").  The integer-word form `S_neg_dvd_iff` holds for
  every `k ≥ 1`.
* word length `j - 1`, any `j ≥ 1`: arbitrary list length; no bound.
* integer partial quotients: `w : List ℤ`, no positivity (the write-up reads the recurrence
  for arbitrary integer quotients, so that the residue statements are uniform).

The complex primitive root `exp(2πi/k)` is used only inside proofs to convert
`Φ_k ∣ f` into a vanishing statement; it does not appear in any statement except
`S_neg_ev`, which holds for every unit `z ∈ ℂˣ`.
-/

open LaurentPolynomial
namespace LemmaN
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

/-- Smoke test of the convention (exponent carries the previous quotient): on the word
`(2, 2, 2)` the write-up states `S_4 = [4]_q`. -/
example : S [2, 2, 2] = qint 4 := by
  have h1 : (T 1 : LP) * T 1 = T 2 := by rw [← T_add]; rfl
  have h2 : (T 1 : LP) * T 2 = T 3 := by rw [← T_add]; rfl
  have h3 : (T 1 : LP) * T 3 = T 4 := by rw [← T_add]; rfl
  simp only [S, step, List.foldl_cons, List.foldl_nil, qint]
  norm_num [Finset.sum_range_succ, T_zero]
  linear_combination h1 + T 1 * h1 + h2

def Rel (u : LP) (A B : LP × LP × ℤ) : Prop :=
  A.2.1 = u * invert B.2.1 ∧ A.1 = -T 1 * u * invert B.1 ∧ A.2.2 = -B.2.2

theorem step_rel {u : LP} {A B : LP × LP × ℤ} (h : Rel u A B) (c : ℤ) :
    Rel (-T (-1) * u) (step A (-c)) (step B c) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hT := T_one_mul_T_neg_one
  refine ⟨?_, ?_, ?_⟩
  · show qint (-c) * A.2.1 - T (A.2.2 - 1) * A.1 =
      (-T (-1) * u) * invert (qint c * B.2.1 - T (B.2.2 - 1) * B.1)
    rw [qint_neg, h1, h2, h3, map_sub, map_mul, map_mul, invert_T]
    have e1 : T (-B.2.2 - 1) * T 1 = (T (-B.2.2) : LP) := by rw [← T_add]; congr 1; ring
    have e2 : T (-1) * T (-(B.2.2 - 1)) = (T (-B.2.2) : LP) := by rw [← T_add]; congr 1; ring
    linear_combination (u * invert B.1) * (e1 - e2)
  · show A.2.1 = (-T 1 * (-T (-1) * u)) * invert B.2.1
    rw [h1]
    linear_combination (-(u * invert B.2.1)) * hT
  · show -c = -c
    rfl

theorem fold_rel (w : List ℤ) : ∀ (A B : LP × LP × ℤ) (u : LP), Rel u A B →
    ((w.map (fun c => -c)).foldl step A).2.1 =
      (-T (-1)) ^ w.length * u * invert ((w.foldl step B).2.1) := by
  induction w with
  | nil =>
    intro A B u h
    simp [h.1]
  | cons c w ih =>
    intro A B u h
    simp only [List.map_cons, List.foldl_cons, List.length_cons]
    rw [ih _ _ _ (step_rel h c)]
    ring

/-- **Negation identity** (first line of the statement).  In `ℤ[q, q⁻¹]`,
`S_j(-c_2, ..., -c_j) = (-q⁻¹)^{j-1} S_j(c_2, ..., c_j)(q ↦ q⁻¹)`. -/
theorem S_neg (w : List ℤ) :
    S (w.map (fun c => -c)) = (-T (-1)) ^ w.length * invert (S w) := by
  have := fold_rel w (0, 1, 0) (0, 1, 0) 1 ⟨by simp, by simp, by simp⟩
  simpa [S] using this


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

theorem S_neg_dvd {k : ℕ} (hk : 0 < k) (w : List ℤ)
    (h : Polynomial.toLaurent (Polynomial.cyclotomic k ℤ) ∣ S w) :
    Polynomial.toLaurent (Polynomial.cyclotomic k ℤ) ∣ S (w.map (fun c => -c)) := by
  have hz : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / k)) k :=
    Complex.isPrimitiveRoot_exp k hk.ne'
  let z : ℂˣ := Units.mk0 _ (hz.ne_zero hk.ne')
  have hz' : IsPrimitiveRoot (z : ℂ) k := hz
  have hzi : IsPrimitiveRoot ((z⁻¹ : ℂˣ) : ℂ) k := by
    have := hz'.inv
    simpa using this
  have h0 : ev z⁻¹ (S w) = 0 := (cyc_dvd_iff hk z⁻¹ hzi (S w)).mp h
  rw [cyc_dvd_iff hk z hz', S_neg, map_mul, ev_invert, h0, mul_zero]

/-- Second line of the statement: divisibility of `S_j` by `Φ_k` is preserved by
`c ↦ -c` on the word, and the map is an involution. -/
theorem S_neg_dvd_iff {k : ℕ} (hk : 0 < k) (w : List ℤ) :
    Polynomial.toLaurent (Polynomial.cyclotomic k ℤ) ∣ S w ↔
    Polynomial.toLaurent (Polynomial.cyclotomic k ℤ) ∣ S (w.map (fun c => -c)) := by
  refine ⟨S_neg_dvd hk w, fun h => ?_⟩
  have := S_neg_dvd hk _ h
  simpa [List.map_map, Function.comp_def] using this


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

/-- The vanishing locus `V_j(k)`: residue words `(c_2, ..., c_j) ∈ (ℤ/k)^{j-1}` with
`Φ_k ∣ S_j`.  By `S_dvd_residue` this does not depend on the integer lift chosen. -/
def V (k j : ℕ) : Set (List (ZMod k)) :=
  {r | r.length + 1 = j ∧ ∀ w : List ℤ, w.map (Int.cast : ℤ → ZMod k) = r →
    Polynomial.toLaurent (Polynomial.cyclotomic k ℤ) ∣ S w}

/-- Every residue word has an integer lift. -/
theorem exists_lift {k : ℕ} [NeZero k] (r : List (ZMod k)) : ∃ w : List ℤ, w.map (Int.cast : ℤ → ZMod k) = r := by
  induction r with
  | nil => exact ⟨[], rfl⟩
  | cons a r ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨(a.val : ℤ) :: w, by simp [hw]⟩

/-- **Second line of the statement.**  `V_j(k) = -V_j(k)`: a residue word lies in `V_j(k)`
iff its negation does. -/
theorem V_neg {k : ℕ} (hk : 1 < k) (j : ℕ) (r : List (ZMod k)) :
    r ∈ V k j ↔ r.map (fun x => -x) ∈ V k j := by
  have hk0 : 0 < k := by omega
  have key : ∀ r : List (ZMod k), r ∈ V k j → r.map (fun x => -x) ∈ V k j := by
    rintro r ⟨hlen, hr⟩
    refine ⟨by simpa using hlen, fun w hw => ?_⟩
    haveI : NeZero k := ⟨hk0.ne'⟩
    obtain ⟨w0, hw0⟩ := exists_lift r
    have h0 := hr w0 hw0
    have h1 := S_neg_dvd hk0 w0 h0
    have hmap : (w0.map (fun c => -c)).map (Int.cast : ℤ → ZMod k) = w.map (Int.cast : ℤ → ZMod k) := by
      rw [hw, List.map_map, ← hw0, List.map_map]
      apply List.map_congr_left
      intro a _; simp
    exact (S_dvd_residue hk _ _ hmap).mp h1
  refine ⟨key r, fun h => ?_⟩
  have := key _ h
  simpa [List.map_map, Function.comp_def] using this


/-- The first line of the statement, evaluated at a unit `z` (for instance a primitive
`k`-th root of unity): `S_j(z; -c) = (-1)^{j-1} z^{-(j-1)} S_j(z⁻¹; c)`. -/
theorem S_neg_ev (z : ℂˣ) (w : List ℤ) :
    ev z (S (w.map (fun c => -c))) =
      (-((z⁻¹ : ℂˣ) : ℂ)) ^ w.length * ev z⁻¹ (S w) := by
  rw [S_neg, map_mul, map_pow, map_neg, ev_T, ev_invert]
  simp

/-- `V_j(k) = -V_j(k)` as an equality of sets of residue words. -/
theorem V_neg_set {k : ℕ} (hk : 1 < k) (j : ℕ) :
    (fun r : List (ZMod k) => r.map (fun x => -x)) '' V k j = V k j := by
  ext r
  constructor
  · rintro ⟨r', hr', rfl⟩
    exact (V_neg hk j r').mp hr'
  · intro hr
    refine ⟨r.map (fun x => -x), (V_neg hk j r).mp hr, ?_⟩
    simp [List.map_map, Function.comp_def]

end
end LemmaN

#print axioms LemmaN.S_neg
#print axioms LemmaN.S_neg_ev
#print axioms LemmaN.V_neg
#print axioms LemmaN.V_neg_set
