-- statement_only: the statement compiles, the proof is `sorry`. The result is already published (see header), so only the statement is formalised.
import Mathlib

/-!
# k6-level-six: `Phi_6 | S_i` implies `[6]_q | S_i`, hence `6 | S_i(1)`

Status: STATEMENT ONLY (`lean.state = "statement_only"`); the theorem is proved in the
literature, and no proof is attempted here.

PUBLISHED SOURCE (as recorded in `results.json` for this id): this claim is
Byakuno-Ren-Yanagawa, arXiv:2603.08439, Proposition 5.3.  It was found independently and
was found afterwards to be already published; the only new part of the write-up is the
`A_i` profile, which is not part of this statement.

Source statement: `results/k6-level-six/statement.tex`.  Source argument (evidence folder):
a telescoping identity reducing `Phi_6`-divisibility to the vanishing of one Eisenstein
integer built from suffix partial sums of the digits, plus two congruences (at the inert
prime 2 and the ramified prime above 3 in `Z[zeta_6]`).

```
i >= 1,  c_1,...,c_i in Z:   Phi_6 | S_i  ==>  [6]_q | S_i,   hence 6 | S_i(1)
```

## Objects and hypothesis mapping

* `S w` is `S_i` for the word `w = [c_2, ..., c_i]` of length `i - 1` from the recursion
  `S_{j+1} = [c_{j+1}]_q S_j - q^(c_j - 1) S_{j-1}`, `(S_0, S_1) = (0, 1)`; `c_1` never enters
  (the write-up's remark on `c_1`).  So "all `i >= 1` and all integers `c_1..c_i`" is
  "every list of integers `w`".
* `[6]_q = qint 6 = 1 + q + ... + q^5 = Phi_2 Phi_3 Phi_6`; divisibility in `Z[q, q^-1]`.
* "`Phi_6 | S_i`": `Polynomial.toLaurent (cyclotomic 6 Z) ∣ S w`.
* "hence `6 | S_i(1)`": `6 ∣ ev1 (S w)` where `ev1` evaluates a Laurent polynomial at `q = 1`.
  Both conclusions are stated as one conjunction.

## Not expressed

* Nothing dropped.  The statement holds for all integer digits (negative ones included), as
  in the source; `[n]_q` for negative `n` is the rational-expression extension.
-/

open LaurentPolynomial
namespace K6LevelSix
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




/-- Evaluation at `q = 1`. -/
def ev1 : LP →+* ℤ := LaurentPolynomial.eval₂ (RingHom.id ℤ) (1 : ℤˣ)

/-- **Level six** (Byakuno-Ren-Yanagawa, arXiv:2603.08439, Proposition 5.3). -/
theorem level_six (w : List ℤ)
    (h : Polynomial.toLaurent (Polynomial.cyclotomic 6 ℤ) ∣ S w) :
    qint 6 ∣ S w ∧ (6 : ℤ) ∣ ev1 (S w) := by
  sorry

end
end K6LevelSix
