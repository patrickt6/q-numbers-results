/-
  Degree-equality theorem (arithmetic core), integer level only.

  Setting: digits c : Nat -> Int with c i >= 2 for i >= 2 (c 1 = 1 plays no
  role in the arithmetic: the sequence starts s 0 = 0, s 1 = 1 directly).
  Continuant sequence: s 0 = 0, s 1 = 1, s j = c j * s (j-1) - s (j-2) for j >= 2.
  T k = sum_{j=2}^{k} (c j - 1).

  Main theorem (necessity): if k >= 3 and T k = s k - 1 (tightness), then
  c j = 2 for all 2 <= j <= k, and s j = j for all j <= k.
  Sufficiency: if c j = 2 for 2 <= j <= k then s j = j for all j <= k.
  The k = 2 case is trivial: T 2 = s 2 - 1 holds identically (tight_at_two).

  Plain Lean 4 core, no Mathlib.
-/

namespace DegreeEq

/-- Digit hypothesis: every digit from index 2 onward is at least 2. -/
def DigitsOK (c : Nat → Int) : Prop := ∀ i, 2 ≤ i → c i ≥ 2

/-- The continuant sequence associated to the digits `c`. -/
def s (c : Nat → Int) : Nat → Int
  | 0 => 0
  | 1 => 1
  | (n + 2) => c (n + 2) * s c (n + 1) - s c n

/-- Partial sum `sum_{j=2}^{k} (c j - 1)` (0 for k = 0, 1: empty range). -/
def T (c : Nat → Int) : Nat → Int
  | 0 => 0
  | 1 => 0
  | (n + 2) => T c (n + 1) + (c (n + 2) - 1)

variable {c : Nat → Int}

/-- Two integer factors, each at least 1, with product 1 are both 1. -/
theorem eq_one_of_mul_eq_one_of_ge_one {a b : Int}
    (ha : a ≥ 1) (hb : b ≥ 1) (hab : a * b = 1) : a = 1 ∧ b = 1 := by
  by_cases h : a ≥ 2
  · exfalso
    have hge : 2 * b ≤ a * b := Int.mul_le_mul_of_nonneg_right h (by omega)
    omega
  · have ha1 : a = 1 := by omega
    subst ha1
    simp at hab
    omega

/-- `a >= 1`, `b >= 1`, and `a * b = b` force `a = 1`. -/
theorem eq_one_of_mul_self_of_ge_one {a b : Int}
    (ha : a ≥ 1) (hb : b ≥ 1) (hab : a * b = b) : a = 1 := by
  by_cases h : a ≥ 2
  · exfalso
    have hge : 2 * b ≤ a * b := Int.mul_le_mul_of_nonneg_right h (by omega)
    omega
  · omega

/- ------------------------------------------------------------------ -/
/-  Growth lemmas                                                     -/
/- ------------------------------------------------------------------ -/

/-- Combined growth lemma: `s (n+1) >= n + 1` (linear growth), strict
    increase `s (n+2) >= s (n+1) + 1`, and the termwise inequality
    `s (n+2) - s (n+1) >= c (n+2) - 1`. -/
theorem s_aux (hc : DigitsOK c) :
    ∀ n : Nat,
      s c (n + 1) ≥ (n : Int) + 1 ∧
      s c (n + 2) ≥ s c (n + 1) + 1 ∧
      s c (n + 2) - s c (n + 1) ≥ c (n + 2) - 1 := by
  intro n
  induction n with
  | zero =>
      have h2 : c 2 ≥ 2 := hc 2 (by omega)
      have e1 : s c 1 = 1 := rfl
      have e0 : s c 0 = 0 := rfl
      have e2 : s c 2 = c 2 * s c 1 - s c 0 := rfl
      have e2' : s c 2 = c 2 := by rw [e2, e1, e0]; omega
      show s c 1 ≥ (0 : Int) + 1 ∧ s c 2 ≥ s c 1 + 1 ∧ s c 2 - s c 1 ≥ c 2 - 1
      rw [e1, e2']
      omega
  | succ n IH =>
      obtain ⟨h1, h2, h3⟩ := IH
      have hcnp3 : c (n + 3) ≥ 2 := hc (n + 3) (by omega)
      have hs3 : s c (n + 3) = c (n + 3) * s c (n + 2) - s c (n + 1) := rfl
      -- algebraic identity: (a-1)*(b-1) = a*b - a - b + 1
      have identity : (c (n + 3) - 1) * (s c (n + 2) - 1)
          = c (n + 3) * s c (n + 2) - c (n + 3) - s c (n + 2) + 1 := by
        rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
        omega
      have hx0 : (0 : Int) ≤ s c (n + 2) - 1 := by omega
      have ha1 : (1 : Int) ≤ c (n + 3) - 1 := by omega
      have hmul : 1 * (s c (n + 2) - 1) ≤ (c (n + 3) - 1) * (s c (n + 2) - 1) :=
        Int.mul_le_mul_of_nonneg_right ha1 hx0
      have key : c (n + 3) * s c (n + 2) - c (n + 3) - s c (n + 2) + 1 ≥ s c (n + 1) := by
        rw [← identity]
        omega
      have step : s c (n + 3) - s c (n + 2) ≥ c (n + 3) - 1 := by
        rw [hs3]; omega
      refine ⟨?_, ?_, ?_⟩
      · show s c (n + 2) ≥ (↑(n + 1) : Int) + 1
        have hcast : (↑(n + 1) : Int) = (n : Int) + 1 := by omega
        rw [hcast]; omega
      · show s c (n + 3) ≥ s c (n + 2) + 1
        omega
      · show s c (n + 3) - s c (n + 2) ≥ c (n + 3) - 1
        exact step

/-- `s` is strictly increasing from index 1. -/
theorem s_strict_mono (hc : DigitsOK c) (n : Nat) :
    s c (n + 2) > s c (n + 1) := by
  have := (s_aux hc n).2.1
  omega

/-- Termwise lower bound: `s (n+2) - s (n+1) >= c (n+2) - 1`. -/
theorem s_step_ge (hc : DigitsOK c) (n : Nat) :
    s c (n + 2) - s c (n + 1) ≥ c (n + 2) - 1 :=
  (s_aux hc n).2.2

/- ------------------------------------------------------------------ -/
/-  Tightness propagates down                                         -/
/- ------------------------------------------------------------------ -/

/-- Telescoping bound: `T n <= s n - 1` for `n >= 1`. -/
theorem T_le (hc : DigitsOK c) : ∀ n, 1 ≤ n → T c n ≤ s c n - 1 := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by omega)
  | succ n IH =>
      intro _
      cases n with
      | zero =>
          have e : T c 1 = 0 := rfl
          have e' : s c 1 = 1 := rfl
          show T c 1 ≤ s c 1 - 1
          omega
      | succ m =>
          have hIH := IH (by omega)
          have hterm := s_step_ge hc m
          have hT : T c (m + 2) = T c (m + 1) + (c (m + 2) - 1) := rfl
          show T c (m + 2) ≤ s c (m + 2) - 1
          omega

/-- One downward step: tightness at `m + 1` gives tightness at `m` (m >= 1). -/
theorem tight_down (hc : DigitsOK c) {m : Nat} (hm : 1 ≤ m)
    (h : T c (m + 1) = s c (m + 1) - 1) : T c m = s c m - 1 := by
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  have hterm := s_step_ge hc p
  have hT : T c (p + 2) = T c (p + 1) + (c (p + 2) - 1) := rfl
  have hle := T_le hc (p + 1) (by omega)
  have h' : T c (p + 2) = s c (p + 2) - 1 := h
  omega

/-- Tightness at `k` gives tightness at every level `1 <= n <= k`. -/
theorem tight_all (hc : DigitsOK c) {k : Nat} (htight : T c k = s c k - 1) :
    ∀ n, 1 ≤ n → n ≤ k → T c n = s c n - 1 := by
  have aux : ∀ d n, 1 ≤ n → T c (n + d) = s c (n + d) - 1 → T c n = s c n - 1 := by
    intro d
    induction d with
    | zero => intro n _ h; exact h
    | succ d IH =>
        intro n hn h
        have h' : T c (n + d + 1) = s c (n + d + 1) - 1 := h
        exact IH n hn (tight_down hc (by omega) h')
  intro n h1 h2
  obtain ⟨d, rfl⟩ : ∃ d, k = n + d := ⟨k - n, by omega⟩
  exact aux d n h1 htight

/-- Every term tight: `s (m+1) - s m = c (m+1) - 1` for `1 <= m`, `m + 1 <= k`. -/
theorem termwise_tight (hc : DigitsOK c) {k : Nat} (htight : T c k = s c k - 1) :
    ∀ m, 1 ≤ m → m + 1 ≤ k → s c (m + 1) - s c m = c (m + 1) - 1 := by
  intro m hm hmk
  have t1 := tight_all hc htight m hm (by omega)
  have t2 := tight_all hc htight (m + 1) (by omega) hmk
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  have hT : T c (p + 2) = T c (p + 1) + (c (p + 2) - 1) := rfl
  have t2' : T c (p + 2) = s c (p + 2) - 1 := t2
  show s c (p + 2) - s c (p + 1) = c (p + 2) - 1
  omega

/-- The rewritten recurrence under tightness:
    `(c (p+2) - 1) * (s (p+1) - 1) = s p` for `1 <= p`, `p + 2 <= k`. -/
theorem product_form (hc : DigitsOK c) {k : Nat} (htight : T c k = s c k - 1) :
    ∀ p, 1 ≤ p → p + 2 ≤ k →
      (c (p + 2) - 1) * (s c (p + 1) - 1) = s c p := by
  intro p hp hpk
  have ht : s c (p + 2) - s c (p + 1) = c (p + 2) - 1 :=
    termwise_tight hc htight (p + 1) (by omega) hpk
  have hrec : s c (p + 2) = c (p + 2) * s c (p + 1) - s c p := rfl
  have identity : (c (p + 2) - 1) * (s c (p + 1) - 1)
      = c (p + 2) * s c (p + 1) - c (p + 2) - s c (p + 1) + 1 := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
    omega
  omega

/- ------------------------------------------------------------------ -/
/-  The forward induction (necessity)                                 -/
/- ------------------------------------------------------------------ -/

/-- Forward induction core: under tightness at `k` with `n + 3 <= k`,
    `s i = i` for all `i <= n + 3` and `c i = 2` for all `2 <= i <= n + 3`. -/
theorem forward (hc : DigitsOK c) {k : Nat} (htight : T c k = s c k - 1) :
    ∀ n, n + 3 ≤ k →
      (∀ i, i ≤ n + 3 → s c i = (i : Int)) ∧
      (∀ i, 2 ≤ i → i ≤ n + 3 → c i = 2) := by
  intro n
  induction n with
  | zero =>
      intro hk
      -- base: j = 3.  product_form at p = 1: (c 3 - 1)(s 2 - 1) = s 1 = 1.
      have hpf := product_form hc htight 1 (by omega) hk
      have e1 : s c 1 = 1 := rfl
      rw [e1] at hpf
      have hc3 : c 3 ≥ 2 := hc 3 (by omega)
      have hs2ge : s c 2 ≥ s c 1 + 1 := (s_aux hc 0).2.1
      rw [e1] at hs2ge
      have h13 := eq_one_of_mul_eq_one_of_ge_one
        (by omega : c 3 - 1 ≥ 1) (by omega : s c 2 - 1 ≥ 1) hpf
      have hc3' : c 3 = 2 := by omega
      have hs2 : s c 2 = 2 := by omega
      have e2 : s c 2 = c 2 * s c 1 - s c 0 := rfl
      have e0 : s c 0 = 0 := rfl
      have hc2 : c 2 = 2 := by rw [e2, e1, e0] at hs2; omega
      have e3 : s c 3 = c 3 * s c 2 - s c 1 := rfl
      have hs3 : s c 3 = 3 := by rw [e3, hc3', hs2, e1]; omega
      constructor
      · intro i hi
        match i, hi with
        | 0, _ => exact e0
        | 1, _ => exact e1
        | 2, _ => rw [hs2]; rfl
        | 3, _ => rw [hs3]; rfl
      · intro i h2i hi
        match i, h2i, hi with
        | 2, _, _ => exact hc2
        | 3, _, _ => exact hc3'
  | succ n IH =>
      intro hk
      obtain ⟨hs, hcs⟩ := IH (by omega)
      -- product_form at p = n + 2: (c (n+4) - 1)(s (n+3) - 1) = s (n+2).
      have hpf : (c (n + 4) - 1) * (s c (n + 3) - 1) = s c (n + 2) :=
        product_form hc htight (n + 2) (by omega) (by omega)
      have hsn3 : s c (n + 3) = (n : Int) + 3 := by
        have := hs (n + 3) (by omega)
        omega
      have hsn2 : s c (n + 2) = (n : Int) + 2 := by
        have := hs (n + 2) (by omega)
        omega
      rw [hsn3, hsn2] at hpf
      -- (c (n+4) - 1) * (n + 2) = n + 2 with n + 2 >= 1 forces c (n+4) = 2
      have hfact : (c (n + 4) - 1) * ((n : Int) + 2) = (n : Int) + 2 := by
        have heq : (n : Int) + 3 - 1 = (n : Int) + 2 := by omega
        rw [heq] at hpf
        exact hpf
      have hcge : c (n + 4) ≥ 2 := hc (n + 4) (by omega)
      have hc4 : c (n + 4) = 2 := by
        have := eq_one_of_mul_self_of_ge_one
          (by omega : c (n + 4) - 1 ≥ 1) (by omega : (n : Int) + 2 ≥ 1) hfact
        omega
      have e4 : s c (n + 4) = c (n + 4) * s c (n + 3) - s c (n + 2) := rfl
      have hs4 : s c (n + 4) = (n : Int) + 4 := by
        rw [e4, hc4, hsn3, hsn2]; omega
      constructor
      · intro i hi
        by_cases hi' : i ≤ n + 3
        · exact hs i hi'
        · have hi4 : i = n + 4 := by omega
          subst hi4
          rw [hs4]
          omega
      · intro i h2i hi
        by_cases hi' : i ≤ n + 3
        · exact hcs i h2i hi'
        · have hi4 : i = n + 4 := by omega
          subst hi4
          exact hc4

/- ------------------------------------------------------------------ -/
/-  MAIN THEOREMS                                                     -/
/- ------------------------------------------------------------------ -/

/-- k = 2 case: the tightness identity holds automatically for ANY digit
    c 2 (nothing to force). -/
theorem tight_at_two : T c 2 = s c 2 - 1 := by
  have eT : T c 2 = T c 1 + (c 2 - 1) := rfl
  have eT1 : T c 1 = 0 := rfl
  have e2 : s c 2 = c 2 * s c 1 - s c 0 := rfl
  have e1 : s c 1 = 1 := rfl
  have e0 : s c 0 = 0 := rfl
  rw [eT, eT1, e2, e1, e0]
  omega

/-- MAIN THEOREM (necessity): digits with c i >= 2 for i >= 2, k >= 3, and
    the tightness hypothesis sum_{j=2}^{k} (c j - 1) = s k - 1 force
    c j = 2 for all 2 <= j <= k, and consequently s j = j for all j <= k. -/
theorem necessity (hc : DigitsOK c) {k : Nat} (hk : 3 ≤ k)
    (htight : T c k = s c k - 1) :
    (∀ j, 2 ≤ j → j ≤ k → c j = 2) ∧ (∀ j, j ≤ k → s c j = (j : Int)) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
  obtain ⟨hs, hcs⟩ := forward hc htight n (by omega)
  exact ⟨hcs, hs⟩

/-- Sufficiency at the sequence level: if c j = 2 for all 2 <= j <= k,
    then s j = j for all j <= k (so s k = k). -/
theorem sufficiency {k : Nat} (hc2 : ∀ j, 2 ≤ j → j ≤ k → c j = 2) :
    ∀ j, j ≤ k → s c j = (j : Int) := by
  have aux : ∀ n, n + 1 ≤ k → s c n = (n : Int) ∧ s c (n + 1) = (n : Int) + 1 := by
    intro n
    induction n with
    | zero =>
        intro _
        have e0 : s c 0 = 0 := rfl
        have e1 : s c 1 = 1 := rfl
        constructor
        · show s c 0 = ((0 : Nat) : Int)
          omega
        · show s c 1 = ((0 : Nat) : Int) + 1
          omega
    | succ n IH =>
        intro h
        obtain ⟨h1, h2⟩ := IH (by omega)
        have hcn : c (n + 2) = 2 := hc2 (n + 2) (by omega) h
        have hrec : s c (n + 2) = c (n + 2) * s c (n + 1) - s c n := rfl
        have hs2 : s c (n + 2) = (n : Int) + 2 := by
          rw [hrec, hcn, h1, h2]; omega
        constructor
        · omega
        · show s c (n + 2) = (↑(n + 1) : Int) + 1
          omega
  intro j hj
  cases j with
  | zero => rfl
  | succ m =>
      have := (aux m hj).2
      omega

/-- Combined statement: under the digit hypothesis and k >= 3, tightness
    holds if and only if every digit from 2 to k equals 2. -/
theorem tight_iff_all_two (hc : DigitsOK c) {k : Nat} (hk : 3 ≤ k) :
    T c k = s c k - 1 ↔ (∀ j, 2 ≤ j → j ≤ k → c j = 2) := by
  constructor
  · intro htight
    exact (necessity hc hk htight).1
  · intro h2
    have hs := sufficiency h2
    -- with all digits 2, T n = n - 1 for 1 <= n <= k by telescoping
    have hT : ∀ n, 1 ≤ n → n ≤ k → T c n = (n : Int) - 1 := by
      intro n
      induction n with
      | zero => intro h _; exact absurd h (by omega)
      | succ n IH =>
          intro _ h
          cases n with
          | zero =>
              have e : T c 1 = 0 := rfl
              show T c 1 = ((1 : Nat) : Int) - 1
              omega
          | succ m =>
              have hIH := IH (by omega) (by omega)
              have eT : T c (m + 2) = T c (m + 1) + (c (m + 2) - 1) := rfl
              have hcm : c (m + 2) = 2 := h2 (m + 2) (by omega) h
              show T c (m + 2) = (↑(m + 2) : Int) - 1
              rw [eT, hcm]
              omega
    have hTk := hT k (by omega) (by omega)
    have hsk := hs k (by omega)
    omega

/- ------------------------------------------------------------------ -/
/-  #eval sanity checks                                               -/
/- ------------------------------------------------------------------ -/

/-- Digits from a list (position i holds c i; index 0 unused). -/
def digitsOf (l : List Int) : Nat → Int := fun i => l.getD i 0

-- all-2 digits: s should be 0,1,2,3,4,5,6 (the tight case), T 6 = 5 = s 6 - 1
#eval (List.range 7).map (s (digitsOf [0, 1, 2, 2, 2, 2, 2]))
#eval (T (digitsOf [0, 1, 2, 2, 2, 2, 2]) 6, s (digitsOf [0, 1, 2, 2, 2, 2, 2]) 6)
-- non-tight example c = [_,1,2,2,3,2,2]: s grows faster, T 6 < s 6 - 1
#eval (List.range 7).map (s (digitsOf [0, 1, 2, 2, 3, 2, 2]))
#eval (T (digitsOf [0, 1, 2, 2, 3, 2, 2]) 6, s (digitsOf [0, 1, 2, 2, 3, 2, 2]) 6)

end DegreeEq
