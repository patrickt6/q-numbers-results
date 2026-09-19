/-
  AdditionNogo: [x+y]_q is not a bihomographic function of [x]_q and [y]_q

  Statement (results/addition-nogo/statement.tex):
      there is no (a,...,h) in Q(q)^8 other than 0 with
        (a XY + b X + c Y + d) - T (e XY + f X + g Y + h) = 0   for all x, y > 1,
      where X = [x]_q, Y = [y]_q, T = [x+y]_q;
      equivalently rank_{Q(q)} [XY, X, Y, 1, -TXY, -TX, -TY, -T] = 8.

  MAP OF THE LEAN STATEMENT TO THE ABOVE
      v : Fin 8 -> Q(q)             (a,b,c,d,e,f,g,h) = (v 0, ..., v 7)
      `Rel q v x y t`               the displayed relation, with X = qcf q x,
                                    Y = qcf q y, T = qcf q t
      `qcf`                         the Morier-Genoud--Ovsienko q-continued fraction of
                                    an even-length regular continued fraction
                                    [a1,...,a_2n]:
                                      [a1]_q + q^a1 / ([a2]_(1/q) + q^(-a2) / ([a3]_q + ...))
      hypothesis of `nogo_ratfunc`  for every even-length list x, y, t of partial
                                    quotients >= 1 (`Valid`), with cfVal x > 1,
                                    cfVal y > 1 (so x, y > 1) and cfVal t = cfVal x + cfVal y
                                    (so T = [x+y]_q), the relation holds
      conclusion `v = 0`            no nonzero coefficient vector exists
      `rank_eq_eight`               the 8 x 8 relation matrix at the samples has rank 8
                                    over Q(q); the full stack has only 8 columns, so
                                    its rank is 8

  WHAT IS PROVED, in full, with no unfinished proofs: the statement above over the field
  Q(q) = RatFunc Q with q the indeterminate (`nogo_ratfunc`, `rank_eq_eight`), and over
  any field K of characteristic zero in which q is transcendental over Q (`nogo`).

  PROOF SHAPE.  The 8 columns are cleared of denominators, so the relation matrix at
  eight sample pairs is a matrix over Laurent polynomials Q[q, q^-1], computed by a
  division-free recursion (`qcol`).  Its determinant is shown nonzero by specialising
  q = 2 (a ring homomorphism, `phi2`) and exhibiting an exact rational inverse `N1` with
  `N1 * N0 = 1` (checked by kernel evaluation).  Nonvanishing of the determinant over the
  Laurent ring transfers to Q(q) by injectivity of Q[q, q^-1] -> Q(q)
  (`iota_injective_ratfunc`); a square matrix with nonzero determinant over a field has
  trivial kernel.  The sample rows are enough because any coefficient vector valid for
  all x, y > 1 is valid at the samples.

  READING CHOICES AND DIFFERENCES FROM THE SOURCE SCRIPTS (recorded, not silent)
    * The source scripts use their own catalogue of rational pairs and specialise q at
      several rational values.  Here the eight pairs `S` are a different, smaller set
      chosen for exact arithmetic at q = 2.  Several sample sums x + y happen to be integers; that is allowed, since x + y is any number in the domain.
    * The samples are pairs of non-integer rationals.  For INTEGER x, y the addition
      relation does hold ([x+y]_q = X + Y + (q-1) X Y), so integer samples would not
      work; the theorem is about all x, y > 1 and non-integer pairs are among them.
    * The definition `qcf` was checked outside Lean against a reference q-rational tool
      at 4/15, 7/2 and 35/12, and the control target T = X + Y gives rank 7 at q = 2 on
      the same samples (a genuine bihomographic law exists), so the test detects a
      real relation.  These checks are not part of the Lean proof.
    * `nogo_ratfunc` quantifies over lists, not over real numbers: [x]_q is defined
      for rational x through the even-length regular continued fraction, which is unique
      for each rational > 1.  Real (irrational) x, y are not covered by the Lean
      statement; the source statement's scripts also test rational pairs only.
-/
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

open Polynomial LaurentPolynomial

namespace AdditionNogo

/-- `[k]_w = 1 + w + ... + w^(k-1)`. -/
def qn {R : Type*} [CommRing R] (w : R) (k : ℕ) : R := ∑ i ∈ Finset.range k, w ^ i

/-- Weight at a position: `q` at odd positions (flag true), `q⁻¹` at even ones. -/
def wt {R : Type*} [CommRing R] (q qi : R) (s : Bool) : R := if s then q else qi

/-- Division-free numerator/denominator pair of the MGO q-continued fraction. -/
def qcol {R : Type*} [CommRing R] (q qi : R) : Bool → List ℕ → R × R
  | _, [] => (0, 1)
  | s, [a] => (qn (wt q qi s) a, 1)
  | s, a :: b :: t =>
      (qn (wt q qi s) a * (qcol q qi (!s) (b :: t)).1 + wt q qi s ^ a * (qcol q qi (!s) (b :: t)).2,
       (qcol q qi (!s) (b :: t)).1)

/-- Nonvanishing of every tail numerator that the field recursion divides by. -/
def Good {R : Type*} [CommRing R] (q qi : R) : Bool → List ℕ → Prop
  | _, [] => True
  | _, [_] => True
  | s, _ :: b :: t => (qcol q qi (!s) (b :: t)).1 ≠ 0 ∧ Good q qi (!s) (b :: t)

/-- The nested MGO formula in a field. -/
def qcfAux {K : Type*} [Field K] (q : K) : Bool → List ℕ → K
  | _, [] => 0
  | s, [a] => qn (wt q q⁻¹ s) a
  | s, a :: b :: t => qn (wt q q⁻¹ s) a + wt q q⁻¹ s ^ a / qcfAux q (!s) (b :: t)

def qcf {K : Type*} [Field K] (q : K) (l : List ℕ) : K := qcfAux q true l

theorem map_qn {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (w : R) (k : ℕ) :
    f (qn w k) = qn (f w) k := by simp [qn, map_sum, map_pow]

theorem map_wt {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (q qi : R) (s : Bool) :
    f (wt q qi s) = wt (f q) (f qi) s := by cases s <;> simp [wt]

theorem map_qcol {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (q qi : R) :
    ∀ (l : List ℕ) (s : Bool),
      qcol (f q) (f qi) s l = (f (qcol q qi s l).1, f (qcol q qi s l).2) := by
  intro l
  induction l with
  | nil => intro s; simp [qcol]
  | cons a t ih =>
    intro s
    cases t with
    | nil => simp [qcol, map_qn, map_wt]
    | cons b t' =>
      have := ih (!s)
      simp only [qcol, this, map_add, map_mul, map_qn, map_wt, map_pow]

theorem Good_of_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (q qi : R) :
    ∀ (l : List ℕ) (s : Bool), Good (f q) (f qi) s l → Good q qi s l := by
  intro l
  induction l with
  | nil => intro s _; trivial
  | cons a t ih =>
    intro s h
    cases t with
    | nil => trivial
    | cons b t' =>
      simp only [Good, map_qcol] at h
      refine ⟨fun h0 => h.1 (by rw [h0, map_zero]), ih _ ?_⟩
      simpa [Good] using h.2 -- placeholder

theorem Good_map_inj {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (q qi : R) :
    ∀ (l : List ℕ) (s : Bool), Good q qi s l → Good (f q) (f qi) s l := by
  intro l
  induction l with
  | nil => intro s _; trivial
  | cons a t ih =>
    intro s h
    cases t with
    | nil => trivial
    | cons b t' =>
      simp only [Good, map_qcol] at h ⊢
      refine ⟨fun h0 => h.1 (hf (by rw [h0, map_zero])), ih _ h.2⟩

theorem qcol_snd_ne_zero {K : Type*} [Field K] (q qi : K) :
    ∀ (l : List ℕ) (s : Bool), l ≠ [] → Good q qi s l → (qcol q qi s l).2 ≠ 0 := by
  intro l s hl hg
  cases l with
  | nil => exact absurd rfl hl
  | cons a t =>
    cases t with
    | nil => simp [qcol]
    | cons b t' => simpa [qcol, Good] using hg.1

/-- Field recursion equals the division-free ratio. -/
theorem qcfAux_eq {K : Type*} [Field K] {q : K} :
    ∀ (l : List ℕ) (s : Bool), l ≠ [] → Good q q⁻¹ s l →
      qcfAux q s l = (qcol q q⁻¹ s l).1 / (qcol q q⁻¹ s l).2 := by
  intro l
  induction l with
  | nil => intro s h; exact absurd rfl h
  | cons a t ih =>
    intro s _ hg
    cases t with
    | nil => simp [qcfAux, qcol]
    | cons b t' =>
      have hg' := hg
      simp only [Good] at hg'
      have e := ih (!s) (by simp) hg'.2
      have hP := hg'.1
      have hQ := qcol_snd_ne_zero q q⁻¹ (b :: t') (!s) (by simp) hg'.2
      simp only [qcfAux, qcol]
      rw [e]
      generalize (qcol q q⁻¹ (!s) (b :: t')).1 = P at *
      generalize (qcol q q⁻¹ (!s) (b :: t')).2 = Q at *
      generalize qn (wt q q⁻¹ s) a = A
      generalize wt q q⁻¹ s ^ a = W
      field_simp

/-- Regular continued-fraction value `a1 + 1/(a2 + 1/(...))`. -/
def cfVal : List ℕ → ℚ
  | [] => 0
  | [a] => a
  | a :: b :: t => a + 1 / cfVal (b :: t)

/-- Even length, all partial quotients at least 1. -/
def Valid (l : List ℕ) : Prop := Even l.length ∧ ∀ a ∈ l, 1 ≤ a

/-- `Q[q, q⁻¹]`. -/
abbrev L := LaurentPolynomial ℚ

/-- Evaluation `q ↦ q` into a field. -/
noncomputable def iota {K : Type*} [Field K] [CharZero K] (q : K) (hq : q ≠ 0) : L →+* K :=
  LaurentPolynomial.eval₂ (algebraMap ℚ K) (Units.mk0 q hq)

/-- Evaluation at `q = 2`. -/
noncomputable def phi2 : L →+* ℚ :=
  LaurentPolynomial.eval₂ (RingHom.id ℚ) (Units.mk0 (2 : ℚ) (by norm_num))

theorem iota_T1 {K : Type*} [Field K] [CharZero K] (q : K) (hq : q ≠ 0) : iota q hq (T 1) = q := by
  simp [iota, LaurentPolynomial.eval₂_T]

theorem iota_Tm1 {K : Type*} [Field K] [CharZero K] (q : K) (hq : q ≠ 0) : iota q hq (T (-1)) = q⁻¹ := by
  simp [iota, LaurentPolynomial.eval₂_T]

theorem phi2_T1 : phi2 (T 1) = 2 := by
  simp [phi2, LaurentPolynomial.eval₂_T]

theorem phi2_Tm1 : phi2 (T (-1)) = 1 / 2 := by
  simp [phi2, LaurentPolynomial.eval₂_T]

/-- The eight relation columns `XY, X, Y, 1, -TXY, -TX, -TY, -T`, scaled to be
division-free (multiplied by `Qx Qy Qt`). -/
def rowOf {R : Type*} [CommRing R] (Px Qx Py Qy Pt Qt : R) : Fin 8 → R :=
  ![Px * Py * Qt, Px * Qy * Qt, Qx * Py * Qt, Qx * Qy * Qt,
    -(Pt * Px * Py), -(Pt * Px * Qy), -(Pt * Qx * Py), -(Pt * Qx * Qy)]

def sampleRow {R : Type*} [CommRing R] (q qi : R) (x y t : List ℕ) : Fin 8 → R :=
  rowOf (qcol q qi true x).1 (qcol q qi true x).2 (qcol q qi true y).1 (qcol q qi true y).2
    (qcol q qi true t).1 (qcol q qi true t).2

def relMat {R : Type*} [CommRing R] (q qi : R) (S : Fin 8 → List ℕ × List ℕ × List ℕ) :
    Matrix (Fin 8) (Fin 8) R :=
  Matrix.of fun k => sampleRow q qi (S k).1 (S k).2.1 (S k).2.2

theorem map_relMat {R T' : Type*} [CommRing R] [CommRing T'] (f : R →+* T') (q qi : R)
    (S : Fin 8 → List ℕ × List ℕ × List ℕ) :
    (relMat q qi S).map f = relMat (f q) (f qi) S := by
  ext k j
  simp only [relMat, sampleRow, rowOf, Matrix.map_apply, Matrix.of_apply, map_qcol]
  fin_cases j <;> simp

/-- The bihomographic relation at one sample, in the field. -/
def Rel {K : Type*} [Field K] (q : K) (v : Fin 8 → K) (x y t : List ℕ) : Prop :=
  (v 0 * (qcf q x * qcf q y) + v 1 * qcf q x + v 2 * qcf q y + v 3)
    - qcf q t * (v 4 * (qcf q x * qcf q y) + v 5 * qcf q x + v 6 * qcf q y + v 7) = 0

theorem row_of_rel {K : Type*} [Field K] (q : K) (v : Fin 8 → K)
    (x y t : List ℕ) (hx : x ≠ []) (hy : y ≠ []) (ht : t ≠ [])
    (gx : Good q q⁻¹ true x) (gy : Good q q⁻¹ true y) (gt : Good q q⁻¹ true t)
    (h : Rel q v x y t) :
    (sampleRow q q⁻¹ x y t) ⬝ᵥ v = 0 := by
  have ex := qcfAux_eq (q := q) x true hx gx
  have ey := qcfAux_eq (q := q) y true hy gy
  have et := qcfAux_eq (q := q) t true ht gt
  have qx := qcol_snd_ne_zero q q⁻¹ x true hx gx
  have qy := qcol_snd_ne_zero q q⁻¹ y true hy gy
  have qt := qcol_snd_ne_zero q q⁻¹ t true ht gt
  have hPx : (qcol q q⁻¹ true x).1 = qcf q x * (qcol q q⁻¹ true x).2 := by
    unfold qcf; rw [ex, div_mul_cancel₀ _ qx]
  have hPy : (qcol q q⁻¹ true y).1 = qcf q y * (qcol q q⁻¹ true y).2 := by
    unfold qcf; rw [ey, div_mul_cancel₀ _ qy]
  have hPt : (qcol q q⁻¹ true t).1 = qcf q t * (qcol q q⁻¹ true t).2 := by
    unfold qcf; rw [et, div_mul_cancel₀ _ qt]
  simp only [sampleRow, rowOf, dotProduct, Fin.sum_univ_eight]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
  rw [hPx, hPy, hPt]
  unfold Rel at h
  linear_combination ((qcol q q⁻¹ true x).2 * (qcol q q⁻¹ true y).2 * (qcol q q⁻¹ true t).2) * h

/-- Eight sample points with nonzero relation determinant force the coefficient vector to
vanish. -/
theorem samples_trivial {K : Type*} [Field K] [CharZero K] (q : K) (hq : q ≠ 0)
    (hinj : Function.Injective (iota q hq))
    (S : Fin 8 → List ℕ × List ℕ × List ℕ)
    (hdet : (relMat (T 1 : L) (T (-1)) S).det ≠ 0)
    (hg : ∀ k, (S k).1 ≠ [] ∧ (S k).2.1 ≠ [] ∧ (S k).2.2 ≠ [] ∧
      Good (T 1 : L) (T (-1)) true (S k).1 ∧ Good (T 1 : L) (T (-1)) true (S k).2.1 ∧
      Good (T 1 : L) (T (-1)) true (S k).2.2)
    (v : Fin 8 → K) (hrel : ∀ k, Rel q v (S k).1 (S k).2.1 (S k).2.2) : v = 0 := by
  have hdetK : ((relMat (T 1 : L) (T (-1)) S).map (iota q hq)).det ≠ 0 := by
    have e : ((relMat (T 1 : L) (T (-1)) S).map (iota q hq)).det
        = iota q hq (relMat (T 1 : L) (T (-1)) S).det := (RingHom.map_det (iota q hq) _).symm
    rw [e]
    intro h0
    exact hdet (hinj (by rw [h0, map_zero]))
  rw [map_relMat, iota_T1, iota_Tm1] at hdetK
  apply Matrix.eq_zero_of_mulVec_eq_zero hdetK
  ext k
  have hk := hg k
  have gx := Good_map_inj (iota q hq) hinj _ _ _ _ hk.2.2.2.1
  have gy := Good_map_inj (iota q hq) hinj _ _ _ _ hk.2.2.2.2.1
  have gt := Good_map_inj (iota q hq) hinj _ _ _ _ hk.2.2.2.2.2
  rw [iota_T1, iota_Tm1] at gx gy gt
  have := row_of_rel q v _ _ _ hk.1 hk.2.1 hk.2.2.1 gx gy gt (hrel k)
  simpa [relMat, Matrix.mulVec] using this

theorem hdet_of_numeric (S : Fin 8 → List ℕ × List ℕ × List ℕ)
    (h : (relMat (2 : ℚ) (1 / 2) S).det ≠ 0) : (relMat (T 1 : L) (T (-1)) S).det ≠ 0 := by
  intro h0
  apply h
  have e : phi2 (relMat (T 1 : L) (T (-1)) S).det =
      ((relMat (T 1 : L) (T (-1)) S).map phi2).det := RingHom.map_det phi2 _
  rw [map_relMat, phi2_T1, phi2_Tm1, h0, map_zero] at e
  exact e.symm

theorem good_of_numeric (l : List ℕ) (h : Good (2 : ℚ) (1 / 2) true l) :
    Good (T 1 : L) (T (-1)) true l :=
  Good_of_map phi2 (T 1) (T (-1)) l true (by rw [phi2_T1, phi2_Tm1]; exact h)

/-- `iota` is injective for `Q(q)`: no nonzero Laurent polynomial vanishes at the
indeterminate. -/
theorem iota_injective_ratfunc :
    Function.Injective (iota (RatFunc.X : RatFunc ℚ) RatFunc.X_ne_zero) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  obtain ⟨n, f', hf'⟩ := LaurentPolynomial.exists_T_pow f
  have h1 : iota (RatFunc.X : RatFunc ℚ) RatFunc.X_ne_zero (toLaurent f') = 0 := by
    rw [hf', map_mul, hf, zero_mul]
  have h2 : algebraMap ℚ[X] (RatFunc ℚ) f' = 0 := by
    have e : iota (RatFunc.X : RatFunc ℚ) RatFunc.X_ne_zero (toLaurent f') =
        Polynomial.eval₂ (algebraMap ℚ (RatFunc ℚ)) RatFunc.X f' := by
      simp [iota]
    rw [e] at h1
    have e2 : Polynomial.eval₂ (algebraMap ℚ (RatFunc ℚ)) RatFunc.X f' =
        algebraMap ℚ[X] (RatFunc ℚ) f' := by
      rw [← Polynomial.aeval_def, ← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply,
        Polynomial.aeval_X_left_apply]
    rwa [e2] at h1
  have h3 : f' = 0 := (RatFunc.algebraMap_injective ℚ) (by rw [h2, map_zero])
  have h4 : f * T n = 0 := by rw [← hf', h3, map_zero]
  have : IsUnit (T n : L) := isUnit_T n
  exact (this.mul_left_eq_zero).mp h4

end AdditionNogo

namespace AdditionNogo

/-- Eight sample points `(x, y, T)` with `T` the value of x + y, each given as an
even-length regular continued fraction. -/
def S : Fin 8 → List ℕ × List ℕ × List ℕ :=
  ![([1, 2], [1, 2], [2, 1]),
    ([1, 2], [2, 2], [3, 1]),
    ([1, 4], [1, 4], [2, 2]),
    ([1, 2], [3, 2], [4, 1]),
    ([1, 3], [1, 1, 1, 1], [2, 1]),
    ([2, 2], [2, 2], [4, 1]),
    ([1, 4], [1, 1, 2, 1], [2, 1]),
    ([1, 4], [2, 4], [3, 2])]

theorem S_valid (k : Fin 8) :
    Valid (S k).1 ∧ Valid (S k).2.1 ∧ Valid (S k).2.2 ∧ 1 < cfVal (S k).1 ∧
      1 < cfVal (S k).2.1 ∧ cfVal (S k).2.2 = cfVal (S k).1 + cfVal (S k).2.1 := by
  fin_cases k <;> simp [S, Valid, cfVal] <;> norm_num

/-- The relation matrix at `q = 2` (exact rationals). -/
def N0 : Matrix (Fin 8) (Fin 8) ℚ :=
  !![((49 : ℚ) / 4), ((21 : ℚ) / 4), ((21 : ℚ) / 4), ((9 : ℚ) / 4), ((-343 : ℚ) / 4), ((-147 : ℚ) / 4), ((-147 : ℚ) / 4), ((-63 : ℚ) / 4);
    ((119 : ℚ) / 4), ((21 : ℚ) / 4), ((51 : ℚ) / 4), ((9 : ℚ) / 4), ((-1785 : ℚ) / 4), ((-315 : ℚ) / 4), ((-765 : ℚ) / 4), ((-135 : ℚ) / 4);
    ((2883 : ℚ) / 128), ((1395 : ℚ) / 128), ((1395 : ℚ) / 128), ((675 : ℚ) / 128), ((-16337 : ℚ) / 128), ((-7905 : ℚ) / 128), ((-7905 : ℚ) / 128), ((-3825 : ℚ) / 128);
    ((259 : ℚ) / 4), ((21 : ℚ) / 4), ((111 : ℚ) / 4), ((9 : ℚ) / 4), ((-8029 : ℚ) / 4), ((-651 : ℚ) / 4), ((-3441 : ℚ) / 4), ((-279 : ℚ) / 4);
    ((285 : ℚ) / 8), ((105 : ℚ) / 8), ((133 : ℚ) / 8), ((49 : ℚ) / 8), ((-1995 : ℚ) / 8), ((-735 : ℚ) / 8), ((-931 : ℚ) / 8), ((-343 : ℚ) / 8);
    ((289 : ℚ) / 4), ((51 : ℚ) / 4), ((51 : ℚ) / 4), ((9 : ℚ) / 4), ((-8959 : ℚ) / 4), ((-1581 : ℚ) / 4), ((-1581 : ℚ) / 4), ((-279 : ℚ) / 4);
    ((1333 : ℚ) / 16), ((465 : ℚ) / 16), ((645 : ℚ) / 16), ((225 : ℚ) / 16), ((-9331 : ℚ) / 16), ((-3255 : ℚ) / 16), ((-4515 : ℚ) / 16), ((-1575 : ℚ) / 16);
    ((7161 : ℚ) / 128), ((1395 : ℚ) / 128), ((3465 : ℚ) / 128), ((675 : ℚ) / 128), ((-88319 : ℚ) / 128), ((-17205 : ℚ) / 128), ((-42735 : ℚ) / 128), ((-8325 : ℚ) / 128)]

/-- An exact inverse of `N0`. -/
def N1 : Matrix (Fin 8) (Fin 8) ℚ :=
  !![((96565 : ℚ) / 5856), ((8365 : ℚ) / 1952), ((-28 : ℚ) / 61), ((-7 : ℚ) / 96), ((-48555 : ℚ) / 1952), ((-49 : ℚ) / 488), ((8449 : ℚ) / 976), ((-154 : ℚ) / 61);
    ((-3578237 : ℚ) / 43920), ((-548633 : ℚ) / 29280), ((332 : ℚ) / 915), ((119 : ℚ) / 288), ((30153 : ℚ) / 244), ((2899 : ℚ) / 7320), ((-7687 : ℚ) / 183), ((9634 : ℚ) / 915);
    ((-2253607 : ℚ) / 87840), ((-211579 : ℚ) / 29280), ((-44 : ℚ) / 915), ((217 : ℚ) / 1440), ((76479 : ℚ) / 1952), ((3673 : ℚ) / 21960), ((-117157 : ℚ) / 8784), ((3662 : ℚ) / 915);
    ((26174881 : ℚ) / 131760), ((3916339 : ℚ) / 87840), ((-1372 : ℚ) / 915), ((-3689 : ℚ) / 4320), ((-146083 : ℚ) / 488), ((-12691 : ℚ) / 13176), ((672077 : ℚ) / 6588), ((-70462 : ℚ) / 2745);
    ((17455 : ℚ) / 5856), ((1195 : ℚ) / 1952), ((-4 : ℚ) / 61), ((-1 : ℚ) / 96), ((-8505 : ℚ) / 1952), ((-7 : ℚ) / 488), ((1451 : ℚ) / 976), ((-22 : ℚ) / 61);
    ((-761693 : ℚ) / 43920), ((-101087 : ℚ) / 29280), ((68 : ℚ) / 183), ((17 : ℚ) / 288), ((12369 : ℚ) / 488), ((1663 : ℚ) / 21960), ((-18973 : ℚ) / 2196), ((374 : ℚ) / 183);
    ((-611413 : ℚ) / 87840), ((-41581 : ℚ) / 29280), ((28 : ℚ) / 183), ((31 : ℚ) / 1440), ((19845 : ℚ) / 1952), ((49 : ℚ) / 1464), ((-10157 : ℚ) / 2928), ((154 : ℚ) / 183);
    ((99169 : ℚ) / 2160), ((13081 : ℚ) / 1440), ((-4 : ℚ) / 3), ((-527 : ℚ) / 4320), (-67 : ℚ), ((-221 : ℚ) / 1080), ((1243 : ℚ) / 54), ((-50 : ℚ) / 9)]

set_option maxHeartbeats 4000000 in
theorem S_numeric : relMat (2 : ℚ) (1 / 2) S = N0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [N0, relMat, sampleRow, rowOf, qcol, qn, wt, S, Finset.sum_range_succ]

theorem N1_mul : N1 * N0 = 1 := by decide +kernel

theorem det_N0 : N0.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse N1_mul

theorem S_good (k : Fin 8) :
    (S k).1 ≠ [] ∧ (S k).2.1 ≠ [] ∧ (S k).2.2 ≠ [] ∧
      Good (T 1 : L) (T (-1)) true (S k).1 ∧ Good (T 1 : L) (T (-1)) true (S k).2.1 ∧
      Good (T 1 : L) (T (-1)) true (S k).2.2 := by
  have hnum : Good (2 : ℚ) (1 / 2) true (S k).1 ∧ Good (2 : ℚ) (1 / 2) true (S k).2.1 ∧
      Good (2 : ℚ) (1 / 2) true (S k).2.2 := by
    fin_cases k <;> simp [S, Good, qcol, qn, wt, Finset.sum_range_succ] <;> norm_num
  have hne : (S k).1 ≠ [] ∧ (S k).2.1 ≠ [] ∧ (S k).2.2 ≠ [] := by
    fin_cases k <;> simp [S]
  exact ⟨hne.1, hne.2.1, hne.2.2, good_of_numeric _ hnum.1, good_of_numeric _ hnum.2.1,
    good_of_numeric _ hnum.2.2⟩

theorem S_det : (relMat (T 1 : L) (T (-1)) S).det ≠ 0 :=
  hdet_of_numeric S (by rw [S_numeric]; exact det_N0)

/-- **Trivial kernel** for any field `K` in which `q` is nonzero and generic
(`iota` injective): a coefficient vector `v = (a, b, c, d, e, f, g, h)` satisfying the
bihomographic relation at every pair `x, y > 1` is zero. -/
theorem nogo {K : Type*} [Field K] [CharZero K] (q : K) (hq : q ≠ 0)
    (hinj : Function.Injective (iota q hq)) (v : Fin 8 → K)
    (h : ∀ x y t : List ℕ, Valid x → Valid y → Valid t → 1 < cfVal x → 1 < cfVal y →
      cfVal t = cfVal x + cfVal y → Rel q v x y t) : v = 0 :=
  samples_trivial q hq hinj S S_det S_good v
    (fun k => h _ _ _ (S_valid k).1 (S_valid k).2.1 (S_valid k).2.2.1 (S_valid k).2.2.2.1
      (S_valid k).2.2.2.2.1 (S_valid k).2.2.2.2.2)

/-- The same over `Q(q)`, `q` the indeterminate. -/
theorem nogo_ratfunc (v : Fin 8 → RatFunc ℚ)
    (h : ∀ x y t : List ℕ, Valid x → Valid y → Valid t → 1 < cfVal x → 1 < cfVal y →
      cfVal t = cfVal x + cfVal y → Rel (RatFunc.X : RatFunc ℚ) v x y t) : v = 0 :=
  nogo RatFunc.X RatFunc.X_ne_zero iota_injective_ratfunc v h

/-- The unscaled `8 x 8` relation matrix `[XY, X, Y, 1, -TXY, -TX, -TY, -T]` at the eight
samples, over `Q(q)`. -/
noncomputable def relMatK (q : RatFunc ℚ) : Matrix (Fin 8) (Fin 8) (RatFunc ℚ) :=
  Matrix.of fun k => ![qcf q (S k).1 * qcf q (S k).2.1, qcf q (S k).1, qcf q (S k).2.1, 1,
    -(qcf q (S k).2.2 * (qcf q (S k).1 * qcf q (S k).2.1)), -(qcf q (S k).2.2 * qcf q (S k).1),
    -(qcf q (S k).2.2 * qcf q (S k).2.1), -qcf q (S k).2.2]

/-- **Rank 8.**  The relation matrix at the eight samples has full rank over `Q(q)`; since
the full stack over all `x, y > 1` has only eight columns, its rank is `8` too. -/
theorem rank_eq_eight : (relMatK (RatFunc.X : RatFunc ℚ)).rank = 8 := by
  have hdet : (relMatK (RatFunc.X : RatFunc ℚ)).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hv
    refine samples_trivial RatFunc.X RatFunc.X_ne_zero iota_injective_ratfunc S S_det S_good v ?_
    intro k
    have := congrFun hMv k
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_eight, relMatK, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons,
      Pi.zero_apply] at this
    unfold Rel
    linear_combination this
  have hu : IsUnit (relMatK (RatFunc.X : RatFunc ℚ)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  rw [Matrix.rank_of_isUnit _ hu]
  simp

#print axioms nogo
#print axioms nogo_ratfunc
#print axioms rank_eq_eight

end AdditionNogo
