/-
  GosperCF.JumpGap
  ================

  The rational two-version (jump) gap of the MGO q-deformed reals
  (`<path>`, provenance record [id removed], topic `q-jump-gap`; interpreted in
  `gap_meaning.md`, provenance record [id removed]):

      [r/s]_q^+ - [r/s]_q^-  =  (1 - q) q^E / ( S_+(q) S_-(q) ).

  The MGO map `x ↦ [x]_q` is discontinuous at every rational; `r/s` carries two
  q-deformations.  With `M_q = [[R, R'], [S, S']]` the q-continuant matrix of the
  (even-length) continued fraction of `r/s`, Jouteur (arXiv:2503.02122, Def 1.2 +
  Prop 4.8) identifies the two one-sided limits as the two **Möbius images** of
  `M_q` on the two q-deformations of the point at infinity:

  * right version  `[r/s]_q^+ = M_q . (1, 0)   = R / S`               (limit from above, the MGO `q_rational`),
  * left version   `[r/s]_q^- = M_q . (1, 1-q) = (R + (1-q)R')/(S + (1-q)S')`  (limit from below, Bapat-Becker-Licata; `1/(1-q)` is the left q-deformation of ∞).

  What is formalized here, honestly:

  * `gap_telescope` - the **pure field-algebra core**: the difference of the two
    Möbius images telescopes through the determinant of the continuant,
        right - left = (1 - q)·(R S' - R' S) / ( S · (S + (1-q)S') ).
    `R S' - R' S = det M_q` is the q-Wronskian of the two versions.  This is fully
    proved from scratch; no MGO input is assumed beyond the two denominators being
    nonzero.

  * `gap_closed_form` - substitutes the single **MGO continuant input**, supplied
    as a labelled hypothesis `hdet : R S' - R' S = q^n`: the q-Wronskian is a
    single monomial (the q-analogue of the continuant unimodularity `det = +1`, the
    even-length CF convention forcing the `+` sign).  With `S_+ = S` and
    `S_- = S + (1-q)S'` (the **raw** continuant denominators) this gives
        [r/s]_q^+ - [r/s]_q^- = (1 - q) q^n / (S_+ S_-),
    where the exponent `n` here is the **determinant exponent**, which for the real
    continuant is `D = a_0 - a_1 + a_2 - ... ` (the **alternating** CF sum), NOT the
    headline `E = (sum of digits) - 1`.  The two differ: `E = D + 2 P_odd - 1`.  The
    `E = sum - 1` form is the *same gap* rewritten over the **normalised** polynomial
    denominators `S_+, S_-` (each `= s` at `q = 1`); the extra powers of `q` move from
    the cleared denominators into the numerator.  See `gap_meaning.md` and the proof
    in `GosperCF.JumpGapDet`.

  Now formalized in `GosperCF.JumpGapDet` (2026-06-02): the derivation of the
  q-Wronskian monomial `det M_q = q^D` with `D` the **alternating** CF sum, from the
  per-block MGO continuant matrices and the even-length CF parity (that is what
  `hdet` abstracts).  This discharges `hdet` for the real continuant.  Note the
  exponent is `q^D` (alternating sum), NOT `q^E` with `E = sum - 1`: an earlier
  draft (and the lab-report PDF) mislabelled the determinant as `q^E`; the
  determinant is `q^D` and `E = sum - 1` is the numerator exponent only after the
  denominators are normalised (`gap_meaning.md`, verified symbolically on 173
  rationals).  Still open: the reading of `E`, `S_+`, `S_-` off the CF digits as
  Lean objects, and lifting the strict order onto the q-reals.

  Author: (removed)
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

namespace GosperCF

variable {K : Type*} [Field K]

/-- The image of the point `(a, b)` of the q-deformed projective line at infinity
    under the q-continuant matrix `M_q = [[R, R'], [S, S']]`, read as the q-real
    `(R·a + R'·b) / (S·a + S'·b)`.  The two one-sided limits at `r/s` are the
    images at `(1, 0)` and `(1, 1-q)` (Jouteur Def 1.2). -/
def mobius (R R' S S' a b : K) : K := (R * a + R' * b) / (S * a + S' * b)

/-- **Right version** `[r/s]_q^+ = M_q . (1, 0) = R / S` (limit from above, the
    standard MGO `q_rational`). -/
def rightVer (R S : K) : K := R / S

/-- **Left version** `[r/s]_q^- = M_q . (1, 1-q) = (R + (1-q)R')/(S + (1-q)S')`
    (limit from below, Bapat-Becker-Licata). -/
def leftVer (q R R' S S' : K) : K := (R + (1 - q) * R') / (S + (1 - q) * S')

/-- **Right q-denominator** `S_+ = S` (the bottom-left continuant entry), the
    qreals q-denominator of `[r/s]_q`. -/
def qDenomRight (S : K) : K := S

/-- **Left q-denominator** `S_- = S + (1-q)S'`, the denominator of the left
    Möbius image. -/
def qDenomLeft (q S S' : K) : K := S + (1 - q) * S'

/-- The right version really is the `(1, 0)` Möbius image of the continuant. -/
theorem rightVer_eq_mobius (R R' S S' : K) :
    rightVer R S = mobius R R' S S' 1 0 := by
  simp only [rightVer, mobius, mul_one, mul_zero, add_zero]

/-- The left version really is the `(1, 1-q)` Möbius image of the continuant. -/
theorem leftVer_eq_mobius (q R R' S S' : K) :
    leftVer q R R' S S' = mobius R R' S S' 1 (1 - q) := by
  unfold leftVer mobius
  rw [mul_one, mul_one, mul_comm R' (1 - q), mul_comm S' (1 - q)]

/-- **Telescoping core of the jump gap.**  The difference of the two one-sided
    Möbius images of the continuant collapses, through the determinant
    `R S' - R' S` (the q-Wronskian), to

        right - left = (1 - q)·(R S' - R' S) / ( S · (S + (1-q)S') ).

    Pure field algebra: the only hypotheses are that the two q-denominators are
    nonzero.  No MGO continuant structure is assumed. -/
theorem gap_telescope (q R R' S S' : K)
    (hS : S ≠ 0) (hSm : S + (1 - q) * S' ≠ 0) :
    rightVer R S - leftVer q R R' S S'
      = (1 - q) * (R * S' - R' * S) / (S * (S + (1 - q) * S')) := by
  unfold rightVer leftVer
  field_simp
  ring

/-- **Rational jump-gap closed form** (provenance record [id removed]).

    With the single MGO continuant input that the q-Wronskian is a monomial
    (`hdet : R S' - R' S = q^E`, the q-analogue of continuant unimodularity, the
    even-length CF convention fixing the `+` sign), the difference of the two
    one-sided Möbius images is

        [r/s]_q^+ - [r/s]_q^-  =  (1 - q) q^E / (S_+ S_-),

    with `S_+ = S` and `S_- = S + (1-q)S'` the **raw** continuant denominators.
    Here the exponent variable `E` is the **determinant exponent**: for the real
    continuant `R S' - R' S = q^D` with `D` the **alternating** CF sum (proved in
    `GosperCF.JumpGapDet.det_continuant`), so `hdet` is discharged with `E := D`.
    Caution: this `E` is NOT the headline numerator exponent `sum - 1`; that form is
    the same gap over the *normalised* polynomial denominators (see the module
    docstring and `gap_meaning.md`).  The two-line derivation on top of `hdet` is
    fully proved. -/
theorem gap_closed_form (q R R' S S' : K) (E : ℕ)
    (hS : qDenomRight S ≠ 0) (hSm : qDenomLeft q S S' ≠ 0)
    (hdet : R * S' - R' * S = q ^ E) :
    rightVer R S - leftVer q R R' S S'
      = (1 - q) * q ^ E / (qDenomRight S * qDenomLeft q S S') := by
  simp only [qDenomRight, qDenomLeft] at hS hSm ⊢
  rw [gap_telescope q R R' S S' hS hSm, hdet]

/-- **False variant of the gap closed form** (buildout 37 statement-correctness
    gate): flipping the q-deformation prefactor `(1 - q)` to `(1 + q)` is
    refutable.  Take the integer continuant `2/1` shape `R = 0, R' = -q, S = 1,
    S' = 0` at `q = 2` (so `det = q = q^1`, `E = 1`, both denominators `1`): the
    true gap is `-2` but the flipped form claims `+6`.  This confirms the `(1 - q)`
    prefactor - the vanishing of the gap at `q = 1` (classical continuity) - is
    carrying real content. -/
theorem gap_closed_form_false_variant :
    ¬ (∀ (q R R' S S' : ℚ) (E : ℕ),
        S ≠ 0 → S + (1 - q) * S' ≠ 0 → R * S' - R' * S = q ^ E →
        rightVer R S - leftVer q R R' S S'
          = (1 + q) * q ^ E / (S * (S + (1 - q) * S'))) := by
  intro h
  have := h 2 0 (-2) 1 0 1 (by norm_num) (by norm_num) (by norm_num)
  norm_num [rightVer, leftVer] at this

end GosperCF
