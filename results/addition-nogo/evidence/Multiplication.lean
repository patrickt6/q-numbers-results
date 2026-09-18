/-
  GosperCF.Multiplication
  =======================

  The q-deformed multiplication results on the integer slice:

  * the **integer multiplication law** `[m·n]_q = [m]_{q^n}·[n]_q`
    (the special case underlying the closed form), and
  * the **integer-slice multiplication-deficit closed form**
        `Dx_{m,n}(q) = [m·n]_q − [m]_q·[n]_q = [n]_q·([m]_{q^n} − [m]_q)`
    (= `[m]_q·([n]_{q^m} − [n]_q)` by the `m ↔ n` symmetry).

  Both are proved here **from scratch and unconditionally** over an arbitrary
  commutative ring `R`, reusing only the q-integer `[n]_q = ∑_{i<n} q^i` and its
  recurrences from `GosperCF.QInteger`.  No `q ≠ 1` / field hypothesis is needed:
  the law is a genuine polynomial identity in `q` (at `q = 1` both sides are `m·n`).

  The engine reads off the deficit `Dx_{m,n} = [m·n]_q − [m]_q·[n]_q` with
  `[m·n]_q = q_real_rational(m·n)` and `[m]_q·[n]_q = q_gosper(m,n,'mul')`; the
  closed form above is exactly that gap, so `qint_mul` is the mathematical content
  behind the engine's verified anchors `(2,2) ↦ q(q-1)(q+1)` and
  `(2,3) ↦ q(q-1)(q+1)(q²+q+1)`, recorded here as `mulDeficit_two_two` /
  `mulDeficit_two_three`.

  Scope / what is NOT formalized here (honest, matching the source notes):

  * The `q → q^n` twist does **not** extend to a rational factor
    (`[x·n]_q ≠ [x]_{q^n}·[n]_q` for rational `x`), so the rational-factor and
    rational-product cases stay **open**.
  * `[x·y]_q` is **not bihomographic** in `[x]_q,[y]_q` (rank-8 kernel over `ℚ(q)`)
    and the square deficit `[x²]_q − [x]_q²` does **not** carry the q-reversal
    `[x]_{1/q}`.  Both are exact-rank / engine statements over `ℚ(q)`, left **open**
    in Lean (the same status as the addition not-bihomographic row), not formalized
    in this module.
-/
import GosperCF.QInteger
import Mathlib.Tactic

namespace GosperCF

variable {R : Type*} [CommRing R]

/-! ## §1  The geometric-sum additivity of `[·]_q`.

The single fact the multiplication law iterates: the q-integer of a sum splits as

    [a + b]_q = [a]_q + q^a · [b]_q.

This is `∑_{i<a+b} q^i = ∑_{i<a} q^i + q^a ∑_{i<b} q^i`, proved from scratch by
induction on `b` using only the right recurrence `[n+1]_q = [n]_q + q^n`. -/

/-- **Additivity of the q-integer.**  `[a + b]_q = [a]_q + q^a · [b]_q`. -/
theorem qint_add (a b : ℕ) (q : R) :
    qint (a + b) q = qint a q + q ^ a * qint b q := by
  induction b with
  | zero => simp
  | succ c ih =>
      have h : a + (c + 1) = (a + c) + 1 := by ring
      rw [h, qint_succ_right (a + c), ih, qint_succ_right c, pow_add]
      ring

/-! ## §2  The integer multiplication law `[m·n]_q = [m]_{q^n} · [n]_q`.

Proved by induction on `m`.  The step uses `(k+1)·n = k·n + n`, then `qint_add`
splits `[k·n + n]_q`, the induction hypothesis rewrites `[k·n]_q`, and the
`q → q^n` twisted factor reassembles via the right recurrence
`[k+1]_{q^n} = [k]_{q^n} + (q^n)^k` together with `q^{k·n} = (q^n)^k`. -/

/-- **The integer multiplication law** `[m·n]_q = [m]_{q^n} · [n]_q`.

    The `q → q^n` twist on one factor turns the q-integer of a product into a
    product of q-integers.  Unconditional polynomial identity in `q`; reproduced
    by the engine on every integer pair (the law being the
    `Dx + [m]_q[n]_q = [n]_q[m]_{q^n} = [m·n]_q` rearrangement of the deficit
    closed form). -/
theorem qint_mul (m n : ℕ) (q : R) :
    qint (m * n) q = qint m (q ^ n) * qint n q := by
  induction m with
  | zero => simp
  | succ k ih =>
      have e1 : (k + 1) * n = k * n + n := by ring
      have hpow : q ^ (k * n) = (q ^ n) ^ k := by rw [Nat.mul_comm k n, pow_mul]
      rw [e1, qint_add, ih, qint_succ_right k (q ^ n), hpow]
      ring

/-! ## §3  The multiplication-deficit closed form (integer slice). -/

/-- The q-multiplication deficit `Dx_{m,n}(q) = [m·n]_q − [m]_q · [n]_q`, the gap
    between the single q-real of the product and the engine's bihomographic
    product `[m]_q · [n]_q`. -/
def mulDeficit (m n : ℕ) (q : R) : R := qint (m * n) q - qint m q * qint n q

/-- **Integer-slice deficit closed form.**
    `Dx_{m,n}(q) = [n]_q · ([m]_{q^n} − [m]_q)`.  Immediate from the
    multiplication law `[m·n]_q = [m]_{q^n}·[n]_q`. -/
theorem mulDeficit_closed_form (m n : ℕ) (q : R) :
    mulDeficit m n q = qint n q * (qint m (q ^ n) - qint m q) := by
  unfold mulDeficit
  rw [qint_mul]
  ring

/-- The deficit is symmetric in its two factors: `Dx_{m,n} = Dx_{n,m}`. -/
theorem mulDeficit_comm (m n : ℕ) (q : R) :
    mulDeficit m n q = mulDeficit n m q := by
  unfold mulDeficit
  rw [Nat.mul_comm m n, mul_comm (qint m q) (qint n q)]

/-- **Deficit closed form, `m ↔ n` swapped factor.**
    `Dx_{m,n}(q) = [m]_q · ([n]_{q^m} − [n]_q)`. -/
theorem mulDeficit_closed_form_symm (m n : ℕ) (q : R) :
    mulDeficit m n q = qint m q * (qint n (q ^ m) - qint n q) := by
  rw [mulDeficit_comm]
  exact mulDeficit_closed_form n m q

/-- **The two closed forms agree** (the `m ↔ n` symmetry of the deficit, stated on
    the twisted forms directly): `[n]_q·([m]_{q^n} − [m]_q) = [m]_q·([n]_{q^m} − [n]_q)`. -/
theorem twist_deficit_symm (m n : ℕ) (q : R) :
    qint n q * (qint m (q ^ n) - qint m q) = qint m q * (qint n (q ^ m) - qint n q) := by
  rw [← mulDeficit_closed_form, ← mulDeficit_closed_form_symm]

/-! ## §4  Engine cross-checks (the literal anchors). -/

/-- Engine anchor `(2,2)`: `Dx_{2,2} = q(q-1)(q+1) = q³ − q`
    (the square deficit `[2²]_q − [2]_q² = q³ − q`). -/
theorem mulDeficit_two_two (q : R) : mulDeficit 2 2 q = q ^ 3 - q := by
  simp only [mulDeficit, show (2 * 2 : ℕ) = 4 from rfl, qint, Finset.sum_range_succ,
    Finset.sum_range_zero]
  ring

/-- Engine anchor `(2,3)`: `Dx_{2,3} = q(q-1)(q+1)(q²+q+1) = q⁵ + q⁴ − q² − q`. -/
theorem mulDeficit_two_three (q : R) : mulDeficit 2 3 q = q ^ 5 + q ^ 4 - q ^ 2 - q := by
  simp only [mulDeficit, show (2 * 3 : ℕ) = 6 from rfl, qint, Finset.sum_range_succ,
    Finset.sum_range_zero]
  ring

/-! ## §5  False variants (statement-correctness gate).

Each headline statement ships at least one deliberately FALSE variant, confirmed
refutable, so the formalization is shown to capture the real content. -/

/-- **False variant 1 - naive multiplicativity.**  `[m·n]_q = [m]_q · [n]_q`
    (i.e. the deficit vanishes) is refutable: at `m = n = 2`, `q = 2`,
    `[4]_q = 15` but `[2]_q · [2]_q = 9`. -/
theorem qint_mul_false_variant_naive :
    ¬ (∀ (m n : ℕ) (q : ℚ), qint (m * n) q = qint m q * qint n q) := by
  intro h
  have := h 2 2 2
  norm_num [show (2 * 2 : ℕ) = 4 from rfl, qint, Finset.sum_range_succ] at this

/-- **False variant 2 - twist on the wrong factor.**  Replacing the `q → q^n`
    twist by `q → q^m` (`[m·n]_q = [m]_{q^m} · [n]_q`) is refutable: at
    `m = 2`, `n = 3`, `q = 2` the true value is `[6]_q = 63 = [2]_{q³}·[3]_q
    = 9·7`, while `[2]_{q²}·[3]_q = 5·7 = 35`.  This confirms the twist exponent
    really is the OTHER factor `n`, not `m`. -/
theorem qint_mul_false_variant_wrongtwist :
    ¬ (∀ (m n : ℕ) (q : ℚ), qint (m * n) q = qint m (q ^ m) * qint n q) := by
  intro h
  have := h 2 3 2
  norm_num [show (2 * 3 : ℕ) = 6 from rfl, qint, Finset.sum_range_succ] at this

/-- **False variant 3 - sign-flipped deficit closed form.**  Reversing the
    subtraction to `[n]_q · ([m]_q − [m]_{q^n})` is refutable: at `m = n = 2`,
    `q = 2` the true deficit is `q³ − q = 6` while the flipped form gives `−6`. -/
theorem mulDeficit_closed_form_false_variant :
    ¬ (∀ (m n : ℕ) (q : ℚ), mulDeficit m n q = qint n q * (qint m q - qint m (q ^ n))) := by
  intro h
  have := h 2 2 2
  norm_num [mulDeficit, show (2 * 2 : ℕ) = 4 from rfl, qint, Finset.sum_range_succ] at this

end GosperCF
