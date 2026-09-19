import Mathlib

/-!
# length5: every word of the length-5 list makes `Phi_k` divide `S_5`

Status: PROVED (compiles against Mathlib v4.29.1, no unfinished proofs, no new axiom; see
the `#print axioms` lines at the end).  This file proves the "list implies vanishing"
direction only.  The converse (no other word vanishes) is the separate result
`length5-complete`, which is a finite check for `4 <= k <= 24` and is NOT proved here.

Source statement: `results/length5/statement.tex`.

```
k >= 7:  Phi_k | S_5  <==  (c_2,c_3,c_4,c_5) mod k lies in one of
   (0,t,e,e), (e,e,t,0), (t,0,e-t,e), (e,t,0,e-t), (t,e,e,e-t), or W
   e = +-1, t in Z/k,   W = +-{(1,2,2,1),(1,3,1,2),(2,1,3,1),(2,2,1,3),(3,1,2,2)}
```

## What the objects are

* `LP = LaurentPolynomial Z = Z[q, q^-1]`, `q = T 1`.
* `qint c = [c]_q = (1 - q^c)/(1 - q)` for every integer `c` (Lean theorem `qint_mul`:
  `(q - 1) [c]_q = q^c - 1`; for negative `c`, `[-c]_q = -q^(-c) [c]_q`).
* `S w` is `S_j` for the word `w = [c_2, ..., c_j]` from the recurrence
  `S_{i+1} = [c_{i+1}]_q S_i - q^(c_i - 1) S_{i-1}`, `(S_0, S_1) = (0, 1)`
  (the exponent carries the PREVIOUS quotient).  `S5 c1 c2 c3 c4 c5` is `S_5` of the
  fraction `[c_1,...,c_5]`; `S5_indep` proves it does not depend on `c_1`.
* `Phi_k` divides `S` means divisibility in `LP` of `toLaurent (cyclotomic k Z)` into `S`.

## Hypothesis mapping to statement.tex

* "`k >= 7`": theorem `length5_vanishing` has hypothesis `7 <= k`.  It is not used by the
  proof: `length5_vanishing_all` proves the same conclusion for every `k > 1`.  (For
  `k = 1` the statement is also meaningful but the residue lemma used needs `k > 1`;
  not claimed.)  This is a strengthening, recorded here on purpose.
* "`(c_2,c_3,c_4,c_5) mod k`": the integers `c2 c3 c4 c5 : Z` enter through their images in
  `ZMod k`; predicate `InList k c2 c3 c4 c5`.  `c_1` is an arbitrary integer.
* "`e = +-1`, `t in Z/k`": `eps : Z` with `eps = 1 or eps = -1`, and `t : ZMod k`.
  One governing sign `eps` is used in a whole shape, as in the source.
* the five shapes: the five disjuncts of `InList` (with `e - t` computed in `ZMod k`).
* `W`: the list `Wlist` of five words, times `eps = +-1` (this gives the ten words),
  compared residue-wise.
* Conclusion `Phi_k | S_5`: `toLaurent (cyclotomic k Z) ∣ S5 c1 c2 c3 c4 c5`.

## Proof

Strong form: for INTEGER `t` and `eps = +-1` each of the five shapes gives `S = 0` in
`Z[q, q^-1]` (theorems `shape1_pos` ... `shape5_neg`), and each of the ten words gives
`S = 0` (theorems `W1` ... `W5n`).  These are identities of Laurent polynomials, so they
hold at every `k`; this is the source's remark that the ten words are "not root of unity
coincidences" and the five shapes are "identities of Laurent polynomials".  They are
proved by mapping into the fraction field of `LP`, where `[c]_q = (g^c - 1)/(g - 1)`
(`g = q`), and closing with `field_simp; ring`.  The residue step (`S_dvd_residue`) says
divisibility by `Phi_k` depends only on the residues of the word modulo `k`; it is proved
through evaluation at a primitive `k`-th root of unity in `C` (`cyc_dvd_iff`, via the
minimal polynomial of a primitive root over `Z`).

## Not expressed

* Nothing of the statement is dropped.  The converse is not part of this id.
* "Free parameter `t`" is quantified over `ZMod k`, which is exactly "modulo `k`".
* Note for review: in the shapes with `e - t` the difference is taken in `ZMod k`, as the
  residues `(c_2,...,c_5) mod k` in the source are.
-/

open LaurentPolynomial
namespace Length5
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

theorem S5_eq (a b c d : ℤ) :
    S [a, b, c, d] = qint d * (qint c * (qint b * qint a - T (a - 1)) - T (b - 1) * qint a)
      - T (c - 1) * (qint b * qint a - T (a - 1)) := by
  simp [S, step]

abbrev K := FractionRing LP
def φ : LP →+* K := algebraMap LP K
theorem φ_inj : Function.Injective φ := IsFractionRing.injective LP K

def g : K := φ (T 1)
theorem g_ne : g ≠ 0 := by
  have : IsUnit (φ (T 1)) := (isUnit_T (R := ℤ) 1).map φ
  exact this.ne_zero
theorem g_sub_ne : g - 1 ≠ 0 := by
  intro h
  apply T_one_sub_ne
  apply φ_inj
  simpa [g, sub_eq_zero] using h

theorem φ_T (n : ℤ) : φ (T n) = g ^ n := by
  have hT : ∀ m : ℕ, φ (T (m : ℤ)) = g ^ m := by
    intro m
    have : (T (m : ℤ) : LP) = T 1 ^ m := by rw [T_pow]; simp
    rw [this, map_pow]; rfl
  rcases n with m | m
  · simpa using hT m
  · have h1 : φ (T (m + 1 : ℕ)) * φ (T (-((m + 1 : ℕ) : ℤ))) = 1 := by
      rw [← map_mul, ← T_add]; simp
    rw [hT] at h1
    have h2 : g ^ (m + 1) ≠ 0 := pow_ne_zero _ g_ne
    rw [Int.negSucc_eq]
    have : φ (T (-((m : ℤ) + 1))) = (g ^ (m + 1))⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      simpa using h1
    rw [this, show (-((m:ℤ) + 1)) = -((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]

theorem φ_qint (c : ℤ) : φ (qint c) = (g ^ c - 1) / (g - 1) := by
  rw [eq_div_iff g_sub_ne]
  have := congrArg φ (qint_mul c)
  rw [map_mul, map_sub, map_sub, map_one, φ_T c] at this
  rw [mul_comm]; exact this

theorem φ_S5 (a b c d : ℤ) :
    φ (S [a, b, c, d]) = ((g^d-1)/(g-1)) * (((g^c-1)/(g-1)) * (((g^b-1)/(g-1)) * ((g^a-1)/(g-1)) - g^(a-1)) - g^(b-1) * ((g^a-1)/(g-1))) - g^(c-1) * (((g^b-1)/(g-1)) * ((g^a-1)/(g-1)) - g^(a-1)) := by
  rw [S5_eq]; simp only [map_sub, map_mul, φ_qint, φ_T]

theorem S5_zero_of {a b c d : ℤ}
    (h : ((g^d-1)/(g-1)) * (((g^c-1)/(g-1)) * (((g^b-1)/(g-1)) * ((g^a-1)/(g-1)) - g^(a-1)) - g^(b-1) * ((g^a-1)/(g-1))) - g^(c-1) * (((g^b-1)/(g-1)) * ((g^a-1)/(g-1)) - g^(a-1)) = 0) :
    S [a, b, c, d] = 0 := by
  apply φ_inj
  rw [φ_S5, h, map_zero]

macro "shape_tac" : tactic => `(tactic| (
  apply S5_zero_of
  have hg := g_ne
  have hg1 := g_sub_ne
  norm_num [zpow_sub₀ hg, zpow_add₀ hg]
  all_goals (try simp)
  all_goals (field_simp; try ring_nf)
  all_goals (try simp)))

theorem shape1_pos (t : ℤ) : S [0, t, 1, 1] = 0 := by shape_tac
theorem shape1_neg (t : ℤ) : S [0, t, -1, -1] = 0 := by shape_tac
theorem shape2_pos (t : ℤ) : S [1, 1, t, 0] = 0 := by shape_tac
theorem shape2_neg (t : ℤ) : S [-1, -1, t, 0] = 0 := by shape_tac
theorem shape3_pos (t : ℤ) : S [t, 0, 1 - t, 1] = 0 := by shape_tac
theorem shape3_neg (t : ℤ) : S [t, 0, -1 - t, -1] = 0 := by shape_tac
theorem shape4_pos (t : ℤ) : S [1, t, 0, 1 - t] = 0 := by shape_tac
theorem shape4_neg (t : ℤ) : S [-1, t, 0, -1 - t] = 0 := by shape_tac
theorem shape5_pos (t : ℤ) : S [t, 1, 1, 1 - t] = 0 := by shape_tac
theorem shape5_neg (t : ℤ) : S [t, -1, -1, -1 - t] = 0 := by shape_tac

theorem W1 : S [1, 2, 2, 1] = 0 := by shape_tac
theorem W2 : S [1, 3, 1, 2] = 0 := by shape_tac
theorem W3 : S [2, 1, 3, 1] = 0 := by shape_tac
theorem W4 : S [2, 2, 1, 3] = 0 := by shape_tac
theorem W5 : S [3, 1, 2, 2] = 0 := by shape_tac
theorem W1n : S [-1, -2, -2, -1] = 0 := by shape_tac
theorem W2n : S [-1, -3, -1, -2] = 0 := by shape_tac
theorem W3n : S [-2, -1, -3, -1] = 0 := by shape_tac
theorem W4n : S [-2, -2, -1, -3] = 0 := by shape_tac
theorem W5n : S [-3, -1, -2, -2] = 0 := by shape_tac

/-! ### The statement -/

/-- `S_5` of the fraction `[c_1, c_2, c_3, c_4, c_5]`, run from the state `(S_0, S_1, c_1)`. -/
def S5 (c₁ c₂ c₃ c₄ c₅ : ℤ) : LP := ([c₂, c₃, c₄, c₅].foldl step (0, 1, c₁)).2.1

/-- `S_5` does not involve `c_1` (it is multiplied by `S_0 = 0`). -/
theorem S5_indep (c₁ c₂ c₃ c₄ c₅ : ℤ) : S5 c₁ c₂ c₃ c₄ c₅ = S [c₂, c₃, c₄, c₅] := by
  simp [S5, S, step]

/-- The five base words of `W` (up to sign). -/
def Wlist : List (List ℤ) :=
  [[1, 2, 2, 1], [1, 3, 1, 2], [2, 1, 3, 1], [2, 2, 1, 3], [3, 1, 2, 2]]

/-- The residues `(c_2, c_3, c_4, c_5) mod k` lie in the length-5 list of `statement.tex`. -/
def InList (k : ℕ) (c₂ c₃ c₄ c₅ : ℤ) : Prop :=
  (∃ (ε : ℤ) (t : ZMod k), (ε = 1 ∨ ε = -1) ∧
    (((c₂ : ZMod k) = 0 ∧ (c₃ : ZMod k) = t ∧ (c₄ : ZMod k) = ε ∧ (c₅ : ZMod k) = ε) ∨
     ((c₂ : ZMod k) = ε ∧ (c₃ : ZMod k) = ε ∧ (c₄ : ZMod k) = t ∧ (c₅ : ZMod k) = 0) ∨
     ((c₂ : ZMod k) = t ∧ (c₃ : ZMod k) = 0 ∧ (c₄ : ZMod k) = ε - t ∧ (c₅ : ZMod k) = ε) ∨
     ((c₂ : ZMod k) = ε ∧ (c₃ : ZMod k) = t ∧ (c₄ : ZMod k) = 0 ∧ (c₅ : ZMod k) = ε - t) ∨
     ((c₂ : ZMod k) = t ∧ (c₃ : ZMod k) = ε ∧ (c₄ : ZMod k) = ε ∧ (c₅ : ZMod k) = ε - t))) ∨
  (∃ w ∈ Wlist, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
    [c₂, c₃, c₄, c₅].map (Int.cast : ℤ → ZMod k) = (w.map (fun x => ε * x)).map (Int.cast : ℤ → ZMod k))

/-- A local abbreviation for "`Phi_k` divides `f`" in `Z[q, q^-1]`. -/
def CycDvd (k : ℕ) (f : LP) : Prop := Polynomial.toLaurent (Polynomial.cyclotomic k ℤ) ∣ f

theorem zero_cycDvd (k : ℕ) : CycDvd k 0 := dvd_zero _

/-- Reduction of the residue statement to integer words. -/
theorem cycDvd_of_residue {k : ℕ} (hk : 1 < k) {w w' : List ℤ}
    (h : w.map (Int.cast : ℤ → ZMod k) = w'.map (Int.cast : ℤ → ZMod k)) (h0 : S w' = 0) :
    CycDvd k (S w) := by
  unfold CycDvd
  rw [S_dvd_residue hk w w' h, h0]
  exact dvd_zero _

/-- Every listed word gives `Phi_k | S_5`, for every modulus `k > 1`
(the source states it for `k >= 7`; the proof does not need that). -/
theorem length5_vanishing_all {k : ℕ} (hk : 1 < k) (c₁ c₂ c₃ c₄ c₅ : ℤ)
    (h : InList k c₂ c₃ c₄ c₅) : CycDvd k (S5 c₁ c₂ c₃ c₄ c₅) := by
  haveI : NeZero k := ⟨by omega⟩
  rw [S5_indep]
  rcases h with ⟨ε, t, hε, h⟩ | ⟨w, hw, ε, hε, h⟩
  · obtain ⟨t', ht⟩ : ∃ t' : ℤ, (t' : ZMod k) = t := ⟨(t.val : ℤ), by simp⟩
    rcases hε with rfl | rfl <;>
    rcases h with ⟨h2, h3, h4, h5⟩ | ⟨h2, h3, h4, h5⟩ | ⟨h2, h3, h4, h5⟩ | ⟨h2, h3, h4, h5⟩ | ⟨h2, h3, h4, h5⟩
    · exact cycDvd_of_residue hk (w' := [0, t', 1, 1]) (by simp [h2, h3, h4, h5, ht]) (shape1_pos t')
    · exact cycDvd_of_residue hk (w' := [1, 1, t', 0]) (by simp [h2, h3, h4, h5, ht]) (shape2_pos t')
    · exact cycDvd_of_residue hk (w' := [t', 0, 1 - t', 1]) (by simp [h2, h3, h4, h5, ht]) (shape3_pos t')
    · exact cycDvd_of_residue hk (w' := [1, t', 0, 1 - t']) (by simp [h2, h3, h4, h5, ht]) (shape4_pos t')
    · exact cycDvd_of_residue hk (w' := [t', 1, 1, 1 - t']) (by simp [h2, h3, h4, h5, ht]) (shape5_pos t')
    · exact cycDvd_of_residue hk (w' := [0, t', -1, -1]) (by simp [h2, h3, h4, h5, ht]) (shape1_neg t')
    · exact cycDvd_of_residue hk (w' := [-1, -1, t', 0]) (by simp [h2, h3, h4, h5, ht]) (shape2_neg t')
    · exact cycDvd_of_residue hk (w' := [t', 0, -1 - t', -1]) (by simp [h2, h3, h4, h5, ht]) (shape3_neg t')
    · exact cycDvd_of_residue hk (w' := [-1, t', 0, -1 - t']) (by simp [h2, h3, h4, h5, ht]) (shape4_neg t')
    · exact cycDvd_of_residue hk (w' := [t', -1, -1, -1 - t']) (by simp [h2, h3, h4, h5, ht]) (shape5_neg t')
  · simp only [Wlist, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hε with rfl | rfl <;>
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact cycDvd_of_residue hk (w' := [1, 2, 2, 1]) (by simpa using h) W1
    · exact cycDvd_of_residue hk (w' := [1, 3, 1, 2]) (by simpa using h) W2
    · exact cycDvd_of_residue hk (w' := [2, 1, 3, 1]) (by simpa using h) W3
    · exact cycDvd_of_residue hk (w' := [2, 2, 1, 3]) (by simpa using h) W4
    · exact cycDvd_of_residue hk (w' := [3, 1, 2, 2]) (by simpa using h) W5
    · exact cycDvd_of_residue hk (w' := [-1, -2, -2, -1]) (by simpa using h) W1n
    · exact cycDvd_of_residue hk (w' := [-1, -3, -1, -2]) (by simpa using h) W2n
    · exact cycDvd_of_residue hk (w' := [-2, -1, -3, -1]) (by simpa using h) W3n
    · exact cycDvd_of_residue hk (w' := [-2, -2, -1, -3]) (by simpa using h) W4n
    · exact cycDvd_of_residue hk (w' := [-3, -1, -2, -2]) (by simpa using h) W5n

/-- **Statement of `results/length5/statement.tex`** (for `k >= 7`). -/
theorem length5_vanishing {k : ℕ} (hk : 7 ≤ k) (c₁ c₂ c₃ c₄ c₅ : ℤ)
    (h : InList k c₂ c₃ c₄ c₅) : CycDvd k (S5 c₁ c₂ c₃ c₄ c₅) :=
  length5_vanishing_all (by omega) c₁ c₂ c₃ c₄ c₅ h

/-! ### Sanity checks that `S_5` is not trivially zero -/

/-- The word `(1,1,1,1)` is not in the list and `S_5 = -1`. -/
example : S [1, 1, 1, 1] = -1 := by
  simp [S, step, qint]

end
end Length5

#print axioms Length5.length5_vanishing
#print axioms Length5.length5_vanishing_all
