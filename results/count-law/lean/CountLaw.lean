-- statement_only: the statement compiles; the cited theorem of Laurent (1984) is `sorry` and Theorem A is proved only relative to it.
import Mathlib

/-!
# count-law (Theorem A): the vanishing locus is the torsion of a fixed hypersurface in a torus

Status: STATEMENT ONLY (`lean.state = "statement_only"`).  The one `sorry` is the general
theorem of Laurent (Invent. Math. 78 (1984)) on torsion points of subvarieties of the
torus, which the write-up itself cites and does not prove.  Everything else in the
statement is stated here relative to it; parts that are proved without it are proved
below (see "Proved in this file").

Source statement: `results/count-law/statement.tex`.  Source argument:
Lemma 1, Corollary 1, Step 2, Step 3 and Theorem A of the write-up (section 4 of its
count-law note).

```
U_0 = 0, U_1 = 1, U_{j+1} = t (x_{j+1} - 1) U_j - t (t-1)^2 x_j U_{j-1}
S_i(q) = U_i(q, q^{c_2},...,q^{c_i}) / (q(q-1))^{i-1},     X_i = {U_i = 0} in G_m^i
V_i(k) = {c in (Z/k)^{i-1} : (w, w^{c_2},...,w^{c_i}) in X_i},   w a primitive k-th root of unity
{torsion points of X_i} = union_nu y_nu H_nu   (finite union of torsion cosets, independent of k)
```

## Proved in this file (no `sorry`, axioms propext, Classical.choice, Quot.sound)

* `lemma1`: Lemma 1 of the write-up, `(q(q-1))^(i-1) S_i = U_i(q, q^{c_2},...,q^{c_i})` in
  `Z[q, q^-1]`, for every word of integers.
* `pt_mem_Xvar_iff`, `Vlocus_iff`: the point `(w, w^{c_2},...,w^{c_i})` lies on `X_i` exactly when
  `Phi_k | S_i`; hence `V_i(k)` of the statement (`Vlocus`) is the set of residue words all of
  whose lifts have `Phi_k | S_i` (Corollary 1 plus `Phi_k | f <-> f(w) = 0`).
* `pt_pow_eq_one`: the points occurring are `k`-torsion (Step 2 of the write-up).
* `count_law_torsion` is proved FROM `laurent_torsion`; the only `sorry` is `laurent_torsion`.

## Formalisation choices (all recorded)

* Coordinates.  `Upoly j : MvPolynomial N Z` uses `X 0 = t` and `X m = x_{m+1}` for `m >= 1`
  (so `x_1` is `X 0`, which is harmless because `x_1` is only ever multiplied by `U_0 = 0`).
  The torus `G_m^i` is `Fin i -> Cˣ` with coordinate `0` for `t` and coordinate `m` for
  `x_{m+1}`.  Points are evaluated with the value `1` outside the first `i` coordinates
  (`ptval`); this never matters because `U_i` involves only `X 0, ..., X (i-1)` (checked by
  hand from the recursion; NOT proved in Lean).
* Word length.  The Lean statements take `n = i - 1` (the number of quotients `c_2..c_i`),
  so `i = n + 1`.  A word is `c : Fin n -> Z` with `c j = c_{j+2}`.
* Field.  The torus is over `C`, not over `Q` or a number field.  `U_i` has integer
  coefficients, torsion points are algebraic, so this changes nothing for the torsion
  statement; it is a choice of ambient field, recorded.
* "Torsion points of `X_i` = union of `y_nu H_nu`": read as in Laurent's theorem, that is
  the torsion points of `X_i` are exactly the torsion points of finitely many cosets
  `y_nu H_nu`, each coset having `y_nu` a torsion point, `H_nu` a subtorus, and lying
  inside `X_i`.  (The cosets themselves contain non-torsion points, so the literal
  set equality in `statement.tex` is read this way.)
* Subtorus.  `subtorus L = {u | forall a in L, prod_j u_j^{a_j} = 1}` for a saturated
  subgroup `L` of `Z^(n+1)` (saturated: `m a in L, m != 0 => a in L`).
* `k` does not occur in the torsion decomposition at all: it is one finite list
  for all `k`, as the statement says.

## What is NOT expressed

* The step from the decomposition to "V_i(k) is a finite union of congruence conditions
  with `k`-independent coefficients" (Step 3, the displayed formula for Theorem A,
  `beta_s`, and Theorems B and C: counts, quasi-polynomials, degree) is NOT stated here.
  `statement.tex` itself contains only the four displayed lines above, and the last of them
  is the torsion decomposition; those four lines are what is formalised.
* Nothing is claimed about which cosets occur (no explicit list).

## Mathlib check (rev 5e932f97): what it lacks

Searched Mathlib (`Mathlib/`) for Manin-Mumford, Mordell-Lang, "Laurent's theorem",
torsion cosets, subtori, Zariski closure of torsion points, multivariable Laurent
polynomials.  Found nothing on torsion points of subvarieties of tori.  What exists:
`IsOfFinOrder`, `CommGroup.torsion`, `rootsOfUnity`, `IsPrimitiveRoot` and its cyclotomic
theory (used here), group objects in schemes and commutativity of proper group schemes
(`AlgebraicGeometry/Group`), torsion of the unit group of a number field (finite).  There is
no `G_m^n` as an algebraic group, no subtorus, no Kronecker or Lang-type statement.  So the
cited theorem would have to be proved from scratch (its known proofs use heights or
Galois/lattice arguments of substantial length).
-/

open LaurentPolynomial
namespace CountLaw
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

/-! ### The universal polynomial -/

open MvPolynomial in
/-- `U_j` of the write-up, in `Z[X 0, X 1, ...]` with `t = X 0`, `x_{m+1} = X m`. -/
def Upoly : ℕ → MvPolynomial ℕ ℤ
  | 0 => 0
  | 1 => 1
  | (j + 2) => X 0 * (X (j + 1) - 1) * Upoly (j + 1) - X 0 * (X 0 - 1) ^ 2 * X j * Upoly j

/-- The torus `G_m^(n+1)`: points `(t, x_2, ..., x_{n+1})` with nonzero complex coordinates. -/
abbrev Torus (n : ℕ) := Fin n → ℂˣ

/-- A point of the torus as an `ℕ`-indexed valuation (value `1` outside the first `n`). -/
def ptval {n : ℕ} (y : Torus n) : ℕ → ℂ := fun m => if h : m < n then (y ⟨m, h⟩ : ℂ) else 1

/-- `X_i = {U_i = 0}` in `G_m^i`, here for `i = n + 1`. -/
def Xvar (n : ℕ) : Set (Torus (n + 1)) :=
  {y | MvPolynomial.aeval (ptval y) (Upoly (n + 1)) = 0}

/-- The point `(w, w^{c_2}, ..., w^{c_i})` of the torus for a word `c = (c_2, ..., c_i)`. -/
def pt {n : ℕ} (w : ℂˣ) (c : Fin n → ℤ) : Torus (n + 1) := Fin.cons w (fun j => w ^ c j)

/-- `V_i(k)`: residue words `r in (Z/k)^(i-1)` whose lifts all give points of `X_i`, at the
primitive `k`-th root `w`. -/
def Vlocus (n k : ℕ) (w : ℂˣ) : Set (Fin n → ZMod k) :=
  {r | ∀ c : Fin n → ℤ, (fun j => (c j : ZMod k)) = r → pt w c ∈ Xvar n}

/-! ### Torsion cosets in the torus -/

/-- The character `a` evaluated at `u`: `prod_j u_j^(a_j)`. -/
def charEval {n : ℕ} (a : Fin n → ℤ) (u : Torus n) : ℂˣ := ∏ j, u j ^ a j

/-- A saturated subgroup of the character lattice: `m a ∈ L`, `m ≠ 0` implies `a ∈ L`. -/
def Saturated {n : ℕ} (L : AddSubgroup (Fin n → ℤ)) : Prop :=
  ∀ (m : ℤ) (a : Fin n → ℤ), m ≠ 0 → m • a ∈ L → a ∈ L

/-- The subtorus cut out by a subgroup of characters. -/
def subtorus {n : ℕ} (L : AddSubgroup (Fin n → ℤ)) : Set (Torus n) :=
  {u | ∀ a ∈ L, charEval a u = 1}

/-- The translate `y H`. -/
def coset {n : ℕ} (y : Torus n) (L : AddSubgroup (Fin n → ℤ)) : Set (Torus n) :=
  {u | ∃ h ∈ subtorus L, u = y * h}

/-- **Theorem of Laurent (1984), general form, cited and not proved here.**  For any
polynomial `F` (in variables indexed by `ℕ`, evaluated with value `1` outside the first `n`
coordinates, which is the same as an arbitrary polynomial in `n` variables), the torsion
points of `{F = 0}` in the torus are the torsion points of finitely many torsion cosets
`y_nu H_nu`, each contained in `{F = 0}`. -/
theorem laurent_torsion (n : ℕ) (F : MvPolynomial ℕ ℂ) :
    ∃ (m : ℕ) (L : Fin m → AddSubgroup (Fin n → ℤ)) (y : Fin m → Torus n),
      (∀ ν, Saturated (L ν) ∧ IsOfFinOrder (y ν) ∧
        ∀ u ∈ coset (y ν) (L ν), MvPolynomial.aeval (ptval u) F = 0) ∧
      {u : Torus n | IsOfFinOrder u ∧ MvPolynomial.aeval (ptval u) F = 0} =
        ⋃ ν, {u | IsOfFinOrder u ∧ u ∈ coset (y ν) (L ν)} := by
  sorry

/-- **Theorem A (count-law), last line of `statement.tex`**: the torsion points of `X_i` are a
finite union of torsion cosets, one finite list for all `k`.  Proved from `laurent_torsion`. -/
theorem count_law_torsion (n : ℕ) :
    ∃ (m : ℕ) (L : Fin m → AddSubgroup (Fin (n + 1) → ℤ)) (y : Fin m → Torus (n + 1)),
      (∀ ν, Saturated (L ν) ∧ IsOfFinOrder (y ν) ∧ coset (y ν) (L ν) ⊆ Xvar n) ∧
      {u : Torus (n + 1) | IsOfFinOrder u ∧ u ∈ Xvar n} =
        ⋃ ν, {u | IsOfFinOrder u ∧ u ∈ coset (y ν) (L ν)} := by
  obtain ⟨m, L, y, h1, h2⟩ := laurent_torsion (n + 1) ((Upoly (n + 1)).map (Int.castRingHom ℂ))
  refine ⟨m, L, y, fun ν => ⟨(h1 ν).1, (h1 ν).2.1, fun u hu => ?_⟩, ?_⟩
  · have := (h1 ν).2.2 u hu
    simpa [Xvar, MvPolynomial.aeval_def, MvPolynomial.eval₂_map] using this
  · simpa [Xvar, MvPolynomial.aeval_def, MvPolynomial.eval₂_map] using h2

/-- The torsion points of `G_m^(n+1)` that occur in `V_i(k)` are of order dividing `k`:
`(w, w^{c_2}, ..., w^{c_i})` is `k`-torsion.  (This is the link between the locus and the
torsion set in Step 2 of the write-up; proved.) -/
theorem pt_pow_eq_one {n k : ℕ} {w : ℂˣ} (hw : IsPrimitiveRoot (w : ℂ) k) (c : Fin n → ℤ) :
    pt w c ^ k = 1 := by
  have hwk : w ^ k = 1 := by
    apply Units.ext
    simpa using hw.pow_eq_one
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa [pt] using hwk
  · show (w ^ c j) ^ k = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hwk, one_zpow]

/-! ### Lemma 1 of the write-up, proved -/

/-- `U_j` evaluated at a point `p` of any commutative ring (same recursion as `Upoly`). -/
def Uev {R : Type*} [CommRing R] (p : ℕ → R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | (j + 2) => p 0 * (p (j + 1) - 1) * Uev p (j + 1) - p 0 * (p 0 - 1) ^ 2 * p j * Uev p j

theorem aeval_Upoly {R : Type*} [CommRing R] (p : ℕ → R) (j : ℕ) :
    MvPolynomial.aeval p (Upoly j) = Uev p j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => simp [Upoly, Uev]
    | 1, _ => simp [Upoly, Uev]
    | (j + 2), ih =>
      simp only [Upoly, Uev, map_sub, map_mul, map_pow, map_one, MvPolynomial.aeval_X]
      rw [ih (j + 1) (by omega), ih j (by omega)]

theorem Uev_congr {R : Type*} [CommRing R] (p p' : ℕ → R) :
    ∀ j, (∀ m < j, p m = p' m) → Uev p j = Uev p' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    match j, ih, h with
    | 0, _, _ => simp [Uev]
    | 1, _, _ => simp [Uev]
    | (j + 2), ih, h =>
      simp only [Uev]
      rw [ih (j + 1) (by omega) (fun m hm => h m (by omega)), ih j (by omega) (fun m hm => h m (by omega)),
        h 0 (by omega), h (j + 1) (by omega), h j (by omega)]

theorem Uev_map {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R') (p : ℕ → R) (j : ℕ) :
    f (Uev p j) = Uev (fun m => f (p m)) j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => simp [Uev]
    | 1, _ => simp [Uev]
    | (j + 2), ih =>
      simp only [Uev, map_sub, map_mul, map_pow, map_one]
      rw [ih (j + 1) (by omega), ih j (by omega)]

/-- The point `(q, q^{c_1}, q^{c_2}, ...)` in `LP`, for the word `c = [c_2, c_3, ...]`. -/
def ptLP (c : List ℤ) : ℕ → LP := fun m => if m = 0 then T 1 else T (c.getD (m - 1) 0)

theorem getD_lt (l l' : List ℤ) (n : ℕ) (h : n < l.length) : (l ++ l').getD n 0 = l.getD n 0 :=
  List.getD_append l l' 0 n h

theorem lemma1_aux (n : ℕ) : ∀ c : List ℤ, c.length = n →
    (T 1 * (T 1 - 1)) ^ n * S c = Uev (ptLP c) (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c hn
  rcases c.eq_nil_or_concat with rfl | ⟨c0, a, rfl⟩
  · simp only [List.length_nil] at hn
    subst hn
    simp [S, Uev]
  · rw [List.concat_eq_append] at hn ⊢
    rcases c0.eq_nil_or_concat with rfl | ⟨c1, b, rfl⟩
    · -- word `[a]`
      simp only [List.nil_append, List.length_singleton] at hn ⊢
      subst hn
      have hq := qint_mul a
      simp only [pow_one, Uev, ptLP, S, step, List.foldl_cons, List.foldl_nil]
      simp
      linear_combination (T 1 : LP) * hq
    · -- word `c1 ++ [b] ++ [a]`
      rw [List.concat_eq_append] at hn ⊢
      have hlen : (c1 ++ [b] ++ [a]).length = c1.length + 2 := by simp
      rw [hlen] at hn
      subst hn
      have ih1 := ih (c1.length + 1) (by omega) (c1 ++ [b]) (by simp)
      have ih0 := ih c1.length (by omega) c1 rfl
      set p := ptLP (c1 ++ [b] ++ [a]) with hp
      have e1 : Uev (ptLP (c1 ++ [b])) (c1.length + 1 + 1) = Uev p (c1.length + 2) := by
        apply Uev_congr
        intro m hm
        simp only [hp, ptLP]
        split_ifs with h
        · rfl
        · rw [getD_lt (c1 ++ [b]) [a] (m - 1) (by simp; omega)]
      have e0 : Uev (ptLP c1) (c1.length + 1) = Uev p (c1.length + 1) := by
        apply Uev_congr
        intro m hm
        simp only [hp, ptLP]
        split_ifs with h
        · rfl
        · rw [getD_lt (c1 ++ [b]) [a] (m - 1) (by simp; omega), getD_lt c1 [b] (m - 1) (by omega)]
      rw [e1] at ih1
      rw [e0] at ih0
      have hb : p (c1.length + 1) = T b := by
        simp [hp, ptLP, List.getD_append_right]
      have ha : p (c1.length + 2) = T a := by
        simp [hp, ptLP, List.getD_append_right]
      have hS : S (c1 ++ [b] ++ [a]) =
          qint a * S (c1 ++ [b]) - T (b - 1) * S c1 := by
        simp [S, step, List.foldl_append]
      have h0 : p 0 = T 1 := by simp [hp, ptLP]
      have hTT : (T 1 : LP) * T (b - 1) = T b := by rw [← T_add]; congr 1; ring
      have hq := qint_mul a
      have hU : Uev p (c1.length + 2 + 1) = p 0 * (p (c1.length + 2) - 1) * Uev p (c1.length + 2)
          - p 0 * (p 0 - 1) ^ 2 * p (c1.length + 1) * Uev p (c1.length + 1) := rfl
      rw [hU, hb, ha, h0, ← ih1, ← ih0, hS]
      linear_combination ((T 1 * (T 1 - 1)) ^ (c1.length + 1) * S (c1 ++ [b]) * T 1) * hq
        - ((T 1 * (T 1 - 1)) ^ c1.length * S c1 * T 1 * (T 1 - 1) ^ 2) * hTT

/-- **Lemma 1** of the write-up: `(q(q-1))^{i-1} S_i = U_i(q, q^{c_2}, ..., q^{c_i})` as an
identity in `Z[q, q^-1]`, for every word of integers (not only nonnegative ones). -/
theorem lemma1 (c : List ℤ) :
    (T 1 * (T 1 - 1)) ^ c.length * S c = Uev (ptLP c) (c.length + 1) :=
  lemma1_aux c.length c rfl

/-! ### The locus `V_i(k)` of the statement equals the divisibility locus -/

/-- A local abbreviation for "`Phi_k` divides `f`" in `Z[q, q^-1]`. -/
def CycDvd (k : ℕ) (f : LP) : Prop := Polynomial.toLaurent (Polynomial.cyclotomic k ℤ) ∣ f

theorem ptval_pt {n : ℕ} (w : ℂˣ) (c : Fin n → ℤ) (m : ℕ) (hm : m < n + 1) :
    ptval (pt w c) m = ev w (ptLP (List.ofFn c) m) := by
  rcases m with _ | j
  · simp [ptval, pt, ptLP, ev_T]
  · have hj : j < n := by omega
    have e : (⟨j + 1, hm⟩ : Fin (n + 1)) = Fin.succ ⟨j, hj⟩ := rfl
    simp only [ptval, hm, dite_true, ptLP, Nat.succ_ne_zero, if_false, ev_T, Nat.add_sub_cancel, e, pt,
      Fin.cons_succ, Units.val_zpow_eq_zpow_val, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hj]

/-- For a primitive `k`-th root `w` (`k > 1`), `pt w c` lies on `X_i` exactly when
`Phi_k` divides `S_i(c_2, ..., c_i)`.  This is Corollary 1 of the write-up together with
`Phi_k | f <-> f(w) = 0`. -/
theorem pt_mem_Xvar_iff {n k : ℕ} (hk : 1 < k) (w : ℂˣ) (hw : IsPrimitiveRoot (w : ℂ) k)
    (c : Fin n → ℤ) : pt w c ∈ Xvar n ↔ CycDvd k (S (List.ofFn c)) := by
  have hne : ev w (T 1 * (T 1 - 1)) ≠ 0 := by
    rw [map_mul, map_sub, ev_T, map_one, zpow_one]
    refine mul_ne_zero (by simp) ?_
    intro h0
    have h1 : (w : ℂ) = 1 := by simpa [sub_eq_zero] using h0
    have := (hw.pow_eq_one_iff_dvd 1).mp (by simpa using h1)
    have := Nat.le_of_dvd one_pos this
    omega
  have hl := congrArg (ev w) (lemma1 (List.ofFn c))
  rw [map_mul, map_pow, List.length_ofFn, Uev_map] at hl
  have hU : Uev (fun m => ev w (ptLP (List.ofFn c) m)) (n + 1) = Uev (ptval (pt w c)) (n + 1) := by
    apply Uev_congr
    intro m hm
    exact (ptval_pt w c m hm).symm
  rw [hU] at hl
  unfold CycDvd
  rw [cyc_dvd_iff (by omega) w hw, Xvar, Set.mem_setOf_eq, aeval_Upoly, ← hl]
  rw [mul_eq_zero, or_iff_right (pow_ne_zero _ hne)]

/-- `V_i(k)` of the statement is the set of residue words all of whose integer lifts have
`Phi_k | S_i`, for every primitive `k`-th root `w`. -/
theorem Vlocus_iff {n k : ℕ} (hk : 1 < k) (w : ℂˣ) (hw : IsPrimitiveRoot (w : ℂ) k)
    (r : Fin n → ZMod k) :
    r ∈ Vlocus n k w ↔ ∀ c : Fin n → ℤ, (fun j => (c j : ZMod k)) = r → CycDvd k (S (List.ofFn c)) := by
  unfold Vlocus
  simp only [Set.mem_setOf_eq]
  exact forall_congr' fun c => imp_congr_right fun _ => pt_mem_Xvar_iff hk w hw c

end
end CountLaw

#print axioms CountLaw.lemma1
#print axioms CountLaw.Vlocus_iff
#print axioms CountLaw.count_law_torsion
#print axioms CountLaw.pt_pow_eq_one
