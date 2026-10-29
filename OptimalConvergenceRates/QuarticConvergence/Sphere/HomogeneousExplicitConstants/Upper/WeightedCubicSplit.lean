import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.WeightedQuadraticSplit

/-! Actual mixed cubic estimates from weighted diagonal domination.
No mixed norm bound or polynomial completion is assumed. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace WeightedCubicSplit

set_option backward.isDefEq.respectTransparency.types false

open scoped InnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Tri (E : Type*) [AddCommMonoid E] [Module ℝ E] :=
  E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ

def diagonalCubic (T : Tri E) (x : E) : ℝ := T x x x

theorem hll_polarization (T : Tri E)
    (h12 : ∀ x y z, T x y z = T y x z)
    (h23 : ∀ x y z, T x y z = T x z y) (v u : E) :
    diagonalCubic T (v + u) + diagonalCubic T (v - u) - 2 * diagonalCubic T v =
      6 * T v u u := by
  have h1 : T u v v = T v v u := by rw [h12 u v v, h23 v u v]
  have h2 : T u v u = T v u u := h12 u v u
  have h3 : T u u v = T v u u := by rw [h23 u u v, h2]
  simp only [diagonalCubic, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  rw [h1, h2, h3, h23 v u v]
  ring

theorem hhl_polarization (T : Tri E)
    (h12 : ∀ x y z, T x y z = T y x z)
    (h23 : ∀ x y z, T x y z = T x z y) (v u : E) :
    diagonalCubic T (v + u) - diagonalCubic T (v - u) - 2 * diagonalCubic T u =
      6 * T v v u := by
  have h1 : T u v v = T v v u := by rw [h12 u v v, h23 v u v]
  have h2 : T u v u = T v u u := h12 u v u
  have h3 : T u u v = T v u u := by rw [h23 u u v, h2]
  simp only [diagonalCubic, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  rw [h1, h2, h3, h23 v u v]
  ring

theorem cubic_split_identity (T : Tri E)
    (h12 : ∀ x y z, T x y z = T y x z)
    (h23 : ∀ x y z, T x y z = T x z y) (v u : E) :
    diagonalCubic T (v + u) = diagonalCubic T v + 3 * T v v u +
      3 * T v u u + diagonalCubic T u := by
  have h1 : T u v v = T v v u := by rw [h12 u v v, h23 v u v]
  have h2 : T u v u = T v u u := h12 u v u
  have h3 : T u u v = T v u u := by rw [h23 u u v, h2]
  simp only [diagonalCubic, map_add, LinearMap.add_apply]
  rw [h1, h2, h3, h23 v u v]
  ring

/-- Two mixed bounds follow directly from the ORIGINAL cubic domination.
The hypotheses do not include orthogonality of the L-images. -/
theorem mixed_bounds_unit (T : Tri E) (L : E →ₗ[ℝ] E)
    (h12 : ∀ x y z, T x y z = T y x z)
    (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2 * ‖L x‖ * ‖x‖ ^ 2)
    {v u : E} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1)
    (horth : ⟪v, u⟫_ℝ = 0) (horder : ‖L u‖ ≤ ‖L v‖) :
    |T v u u| ≤ 4 * ‖L v‖ ∧ |T v v u| ≤ 4 * ‖L v‖ := by
  have hp : ‖v + u‖ ^ 2 = 2 := by
    rw [norm_add_sq_real, hv, hu, horth]
    norm_num
  have hm : ‖v - u‖ ^ 2 = 2 := by
    rw [norm_sub_sq_real, hv, hu, horth]
    norm_num
  have hLp : ‖L (v + u)‖ ≤ 2 * ‖L v‖ := by
    rw [map_add]
    calc
      ‖L v + L u‖ ≤ ‖L v‖ + ‖L u‖ := norm_add_le _ _
      _ ≤ 2 * ‖L v‖ := by linarith
  have hLm : ‖L (v - u)‖ ≤ 2 * ‖L v‖ := by
    rw [map_sub]
    calc
      ‖L v - L u‖ ≤ ‖L v‖ + ‖L u‖ := norm_sub_le _ _
      _ ≤ 2 * ‖L v‖ := by linarith
  have hBp : |diagonalCubic T (v + u)| ≤ 8 * ‖L v‖ := by
    have h := hdom (v + u)
    rw [hp] at h
    linarith
  have hBm : |diagonalCubic T (v - u)| ≤ 8 * ‖L v‖ := by
    have h := hdom (v - u)
    rw [hm] at h
    linarith
  have hBv : |diagonalCubic T v| ≤ 2 * ‖L v‖ := by simpa only [hv, one_pow, mul_one] using hdom v
  have hBu : |diagonalCubic T u| ≤ 2 * ‖L v‖ := by
    have h := hdom u
    rw [hu, one_pow, mul_one] at h
    linarith
  have hp0 := abs_le.mp hBp
  have hm0 := abs_le.mp hBm
  have hv0 := abs_le.mp hBv
  have hu0 := abs_le.mp hBu
  have hll := hll_polarization T h12 h23 v u
  have hhl := hhl_polarization T h12 h23 v u
  have hn := norm_nonneg (L v)
  constructor
  · exact abs_le.mpr ⟨by linarith [hp0.1, hm0.1, hv0.2], by linarith [hp0.2, hm0.2, hv0.1]⟩
  · exact abs_le.mpr ⟨by linarith [hp0.1, hm0.2, hu0.2], by linarith [hp0.2, hm0.1, hu0.1]⟩

theorem mixed_bounds (T : Tri E) (L : E →ₗ[ℝ] E)
    (h12 : ∀ x y z, T x y z = T y x z)
    (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2 * ‖L x‖ * ‖x‖ ^ 2)
    {v u : E} (horth : ⟪v, u⟫_ℝ = 0)
    (horder : ‖L u‖ * ‖v‖ ≤ ‖L v‖ * ‖u‖) :
    |T v u u| ≤ 4 * ‖L v‖ * ‖u‖^2 ∧
      |T v v u| ≤ 4 * ‖L v‖ * ‖v‖ * ‖u‖ := by
  by_cases hv0 : v = 0
  · simp [hv0]
  by_cases hu0 : u = 0
  · simp [hu0]
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hup : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  let v' : E := ‖v‖⁻¹ • v
  let u' : E := ‖u‖⁻¹ • u
  have hv' : ‖v'‖ = 1 := norm_smul_inv_norm hv0
  have hu' : ‖u'‖ = 1 := norm_smul_inv_norm hu0
  have horth' : ⟪v', u'⟫_ℝ = 0 := by
    simp only [v', u', inner_smul_left, inner_smul_right, horth, mul_zero,
      map_inv₀, RCLike.conj_to_real]
  have hnormL (x : E) : ‖L (‖x‖⁻¹ • x)‖ = ‖L x‖ / ‖x‖ := by
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
    ring
  have horder' : ‖L u'‖ ≤ ‖L v'‖ := by
    change ‖L (‖u‖⁻¹ • u)‖ ≤ ‖L (‖v‖⁻¹ • v)‖
    rw [hnormL, hnormL]
    exact (div_le_div_iff₀ hup hvp).2 horder
  obtain ⟨hll,hhl⟩ := mixed_bounds_unit T L h12 h23 hdom hv' hu' horth' horder'
  have hs1 : |T v u u| = (‖v‖ * ‖u‖^2) * |T v' u' u'| := by
    simp only [v', u', map_smul, LinearMap.smul_apply, smul_eq_mul, abs_mul,
      abs_inv, abs_of_nonneg (norm_nonneg _)]
    field_simp
  have hs2 : |T v v u| = (‖v‖^2 * ‖u‖) * |T v' v' u'| := by
    simp only [v', u', map_smul, LinearMap.smul_apply, smul_eq_mul, abs_mul,
      abs_inv, abs_of_nonneg (norm_nonneg _)]
    field_simp
  constructor
  · calc
      |T v u u| = (‖v‖ * ‖u‖^2) * |T v' u' u'| := hs1
      _ ≤ (‖v‖ * ‖u‖^2) * (4 * ‖L v'‖) := mul_le_mul_of_nonneg_left hll (by positivity)
      _ = 4 * ‖L v‖ * ‖u‖^2 := by
        change (‖v‖ * ‖u‖^2) * (4 * ‖L (‖v‖⁻¹ • v)‖) = _
        rw [hnormL]
        field_simp
  · calc
      |T v v u| = (‖v‖^2 * ‖u‖) * |T v' v' u'| := hs2
      _ ≤ (‖v‖^2 * ‖u‖) * (4 * ‖L v'‖) := mul_le_mul_of_nonneg_left hhl (by positivity)
      _ = 4 * ‖L v‖ * ‖v‖ * ‖u‖ := by
        change (‖v‖^2 * ‖u‖) * (4 * ‖L (‖v‖⁻¹ • v)‖) = _
        rw [hnormL]
        field_simp

section Finite

open WeightedQuadraticSplit MvPolynomial

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The actual trilinear form of a finite coefficient tensor. -/
def tensorForm (t : ι → ι → ι → ℝ) : Tri (Point ι) :=
  ∑ i, (EuclideanSpace.proj i).toLinearMap.smulRight
    (matrixForm (fun j k ↦ t i j k))

theorem tensorForm_apply (t : ι → ι → ι → ℝ) (x y z : Point ι) :
    tensorForm t x y z = ∑ i, ∑ j, ∑ k, t i j k * x i * y j * z k := by
  simp [tensorForm, matrixForm, Matrix.toBilin'_apply, Finset.mul_sum, mul_assoc, mul_comm,
    mul_left_comm]

theorem tensorForm_symm12 (t : ι → ι → ι → ℝ)
    (ht : ∀ i j k, t i j k = t j i k) (x y z : Point ι) :
    tensorForm t x y z = tensorForm t y x z := by
  rw [tensorForm_apply, tensorForm_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [ht i j k]
  ring

theorem tensorForm_symm23 (t : ι → ι → ι → ℝ)
    (ht : ∀ i j k, t i j k = t i k j) (x y z : Point ι) :
    tensorForm t x y z = tensorForm t x z y := by
  rw [tensorForm_apply, tensorForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  rw [ht i j k]
  ring

def cubicPolynomial (t : ι → ι → ι → ℝ) : MvPolynomial ι ℝ :=
  ∑ i, ∑ j, ∑ k, C (t i j k) * X i * X j * X k

omit [DecidableEq ι] in
theorem cubicPolynomial_homogeneous (t : ι → ι → ι → ℝ) :
    (cubicPolynomial t).IsHomogeneous 3 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  apply MvPolynomial.IsHomogeneous.sum
  intro k _
  exact (((MvPolynomial.isHomogeneous_X ℝ i).C_mul _).mul
    (MvPolynomial.isHomogeneous_X ℝ j)).mul (MvPolynomial.isHomogeneous_X ℝ k)

theorem cubicPolynomial_eval (t : ι → ι → ι → ℝ) (x : Point ι) :
    eval (fun i ↦ x i) (cubicPolynomial t) = diagonalCubic (tensorForm t) x := by
  simp [cubicPolynomial, diagonalCubic, tensorForm_apply]

theorem tensorForm_hll (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ)
    (x : Point ι) (y : Point κ) :
    tensorForm t (high x) (low y) (low y) =
      ∑ i, ∑ j, ∑ k, t (Sum.inl i) (Sum.inr j) (Sum.inr k) * x i * y j * y k := by
  simp [tensorForm_apply, high, low, Fintype.sum_sum_type]

theorem tensorForm_hhl (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ)
    (x : Point ι) (y : Point κ) :
    tensorForm t (high x) (high x) (low y) =
      ∑ i, ∑ j, ∑ k, t (Sum.inl i) (Sum.inl j) (Sum.inr k) * x i * x j * y k := by
  simp [tensorForm_apply, high, low, Fintype.sum_sum_type]

/-- The two actual mixed tensor expressions obey the desired estimates
from domination of the actual cubic polynomial. Constants4 imply the
previous conservative constants13. -/
theorem spectral_mixed_bounds
    (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ)
    (a : ι → ℝ) (b : κ → ℝ) {tau : ℝ} (htau : 0 ≤ tau)
    (ha : ∀ i, tau ≤ a i) (hb0 : ∀ j, 0 ≤ b j) (hb : ∀ j, b j ≤ tau)
    (ht12 : ∀ i j k, t i j k = t j i k) (ht23 : ∀ i j k, t i j k = t i k j)
    (hdom : ∀ z : Point (ι ⊕ κ), |eval (fun i ↦ z i) (cubicPolynomial t)| ≤
      2 * ‖diagonal (Sum.elim a b) z‖ * ‖z‖^2) (x : Point ι) (y : Point κ) :
    |tensorForm t (high x) (low y) (low y)| ≤ 4 * ‖diagonal a x‖ * ‖y‖^2 ∧
    |tensorForm t (high x) (high x) (low y)| ≤ 4 * ‖diagonal a x‖ * ‖x‖ * ‖y‖ := by
  have horder : ‖diagonal (Sum.elim a b) (low y)‖ * ‖high (κ:=κ) x‖ ≤
      ‖diagonal (Sum.elim a b) (high x)‖ * ‖low (ι:=ι) y‖ := by
    simp only [diagonal_low, diagonal_high, norm_low, norm_high]
    calc
      ‖diagonal b y‖ * ‖x‖ ≤ (tau * ‖y‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (diagonal_norm_le htau hb0 hb y) (norm_nonneg _)
      _ = (tau * ‖x‖) * ‖y‖ := by ring
      _ ≤ ‖diagonal a x‖ * ‖y‖ :=
        mul_le_mul_of_nonneg_right (le_diagonal_norm htau ha x) (norm_nonneg _)
  have hd : ∀ z : Point (ι ⊕ κ), |diagonalCubic (tensorForm t) z| ≤
      2 * ‖diagonal (Sum.elim a b) z‖ * ‖z‖^2 := by
    intro z
    rw [← cubicPolynomial_eval]
    exact hdom z
  have hc := mixed_bounds (tensorForm t) (diagonal (Sum.elim a b))
    (tensorForm_symm12 t ht12) (tensorForm_symm23 t ht23) hd (high_low_inner x y) horder
  simpa only [diagonal_high, norm_high, norm_low] using hc

/-- The actual inverse-weighted quadratic coefficient tensor. -/
def hllCoefficients (a : ι → ℝ)
    (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ) (i : ι) (j k : κ) : ℝ :=
  t (Sum.inl i) (Sum.inr j) (Sum.inr k) / a i

def hllVector (a : ι → ℝ)
    (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ) (y : Point κ) : Point ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm
    (fun i ↦ ∑ j, ∑ k, hllCoefficients a t i j k * y j * y k)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem weighted_hllCoefficients (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)
    (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ) (i : ι) (j k : κ) :
    a i * hllCoefficients a t i j k = t (Sum.inl i) (Sum.inr j) (Sum.inr k) := by
  simp only [hllCoefficients]
  field_simp [ha i]

theorem hllVector_pair (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)
    (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ) (x : Point ι) (y : Point κ) :
    ⟪diagonal a x, hllVector a t y⟫_ℝ = tensorForm t (high x) (low y) (low y) := by
  rw [tensorForm_hll]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, diagonal_apply]
  change (∑ i, (∑ j, ∑ k, hllCoefficients a t i j k * y j * y k) * (a i * x i)) = _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  calc
    hllCoefficients a t i j k * y j * y k * (a i * x i) =
        (a i * hllCoefficients a t i j k) * x i * y j * y k := by ring
    _ = _ := by rw [weighted_hllCoefficients a ha t i j k]

/-- The explicit quadratic vector is bounded by4 times the low squared
radius, deduced from the original actual cubic domination. -/
theorem hllVector_norm_le
    (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ)
    (a : ι → ℝ) (b : κ → ℝ) {tau : ℝ} (htau : 0 < tau)
    (ha : ∀ i, tau ≤ a i) (hb0 : ∀ j, 0 ≤ b j) (hb : ∀ j, b j ≤ tau)
    (ht12 : ∀ i j k, t i j k = t j i k) (ht23 : ∀ i j k, t i j k = t i k j)
    (hdom : ∀ z : Point (ι ⊕ κ), |eval (fun i ↦ z i) (cubicPolynomial t)| ≤
      2 * ‖diagonal (Sum.elim a b) z‖ * ‖z‖^2) (y : Point κ) :
    ‖hllVector a t y‖ ≤ 4 * ‖y‖^2 := by
  let c : Point ι := hllVector a t y
  let v : Point ι := diagonal (fun i ↦ (a i)⁻¹) c
  have ha0 : ∀ i, a i ≠ 0 := fun i ↦ (htau.trans_le (ha i)).ne'
  have hLv : diagonal a v = c := by
    ext i
    simp only [v, diagonal_apply]
    field_simp [ha0 i]
  have hpair : ‖c‖^2 = tensorForm t (high v) (low y) (low y) := by
    rw [← hllVector_pair a ha0 t v y, hLv]
    exact (real_inner_self_eq_norm_sq c).symm
  have hc := (spectral_mixed_bounds t a b htau.le ha hb0 hb ht12 ht23 hdom v y).1
  rw [hLv] at hc
  by_cases hc0 : c = 0
  · change ‖c‖ ≤ _
    simp only [hc0, norm_zero]
    positivity
  have hcp : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  have hs : ‖c‖ * ‖c‖ ≤ ‖c‖ * (4 * ‖y‖^2) := by
    nlinarith [le_abs_self (tensorForm t (high v) (low y) (low y))]
  exact (mul_le_mul_iff_right₀ hcp).mp hs

def hllCompletionPolynomial (a : ι → ℝ)
    (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ) (i : ι) : MvPolynomial (ι ⊕ κ) ℝ :=
  ∑ j, ∑ k, C (hllCoefficients a t i j k) * X (Sum.inr j) * X (Sum.inr k)

def hllPolynomial (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ) :
    MvPolynomial (ι ⊕ κ) ℝ :=
  ∑ i, ∑ j, ∑ k, C (t (Sum.inl i) (Sum.inr j) (Sum.inr k)) *
    X (Sum.inl i) * X (Sum.inr j) * X (Sum.inr k)

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem hllCompletionPolynomial_homogeneous (a : ι → ℝ)
    (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ) (i : ι) :
    (hllCompletionPolynomial a t i).IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  apply MvPolynomial.IsHomogeneous.sum
  intro k _
  exact ((MvPolynomial.isHomogeneous_X ℝ (Sum.inr j)).C_mul _).mul
    (MvPolynomial.isHomogeneous_X ℝ (Sum.inr k))

omit [DecidableEq ι] [DecidableEq κ] in
theorem hllPolynomial_homogeneous
    (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ) :
    (hllPolynomial t).IsHomogeneous 3 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  apply MvPolynomial.IsHomogeneous.sum
  intro k _
  exact (((MvPolynomial.isHomogeneous_X ℝ (Sum.inl i)).C_mul _).mul
    (MvPolynomial.isHomogeneous_X ℝ (Sum.inr j))).mul
    (MvPolynomial.isHomogeneous_X ℝ (Sum.inr k))

omit [DecidableEq ι] [DecidableEq κ] in
/-- An exact identity of actual cubic polynomials, with a genuinely
quadratic vector on the right of the weighted linear factor. -/
theorem hll_polynomial_identity (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)
    (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ) :
    (∑ i, C (a i) * X (Sum.inl i) * hllCompletionPolynomial a t i) = hllPolynomial t := by
  classical
  simp only [hllCompletionPolynomial, hllPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  calc
    C (a i) * X (Sum.inl i) *
        (C (hllCoefficients a t i j k) * X (Sum.inr j) * X (Sum.inr k)) =
        C (a i * hllCoefficients a t i j k) * X (Sum.inl i) * X (Sum.inr j) * X (Sum.inr k) := by
      rw [map_mul]
      ring
    _ = _ := by rw [weighted_hllCoefficients a ha t i j k]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem hllCompletionPolynomial_eval (a : ι → ℝ)
    (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ) (x : Point ι) (y : Point κ) (i : ι) :
    eval (Sum.elim (fun k ↦ x k) (fun j ↦ y j)) (hllCompletionPolynomial a t i) =
      hllVector a t y i := by
  simp [hllCompletionPolynomial, hllVector]

theorem hllPolynomial_eval (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ)
    (x : Point ι) (y : Point κ) :
    eval (Sum.elim (fun k ↦ x k) (fun j ↦ y j)) (hllPolynomial t) =
      tensorForm t (high x) (low y) (low y) := by
  simp [hllPolynomial, tensorForm_hll]

theorem hllCompletionPolynomial_norm_le
    (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ)
    (a : ι → ℝ) (b : κ → ℝ) {tau : ℝ} (htau : 0 < tau)
    (ha : ∀ i, tau ≤ a i) (hb0 : ∀ j, 0 ≤ b j) (hb : ∀ j, b j ≤ tau)
    (ht12 : ∀ i j k, t i j k = t j i k) (ht23 : ∀ i j k, t i j k = t i k j)
    (hdom : ∀ z : Point (ι ⊕ κ), |eval (fun i ↦ z i) (cubicPolynomial t)| ≤
      2 * ‖diagonal (Sum.elim a b) z‖ * ‖z‖^2) (x : Point ι) (y : Point κ) :
    ‖(WithLp.equiv 2 (ι → ℝ)).symm (fun i ↦
      eval (Sum.elim (fun k ↦ x k) (fun j ↦ y j)) (hllCompletionPolynomial a t i))‖ ≤
      4 * ‖y‖^2 := by
  have hv : (WithLp.equiv 2 (ι → ℝ)).symm (fun i ↦
      eval (Sum.elim (fun k ↦ x k) (fun j ↦ y j)) (hllCompletionPolynomial a t i)) =
      hllVector a t y := by
    ext i
    exact hllCompletionPolynomial_eval a t x y i
  rw [hv]
  exact hllVector_norm_le t a b htau ha hb0 hb ht12 ht23 hdom y

/-- The actual symmetric quadratic coefficient matrix of the HHL part,
linear in the original low parameter. -/
def hhlFamily (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ) (k : κ) : Matrix ι ι ℝ :=
  fun i j ↦ t (Sum.inl i) (Sum.inl j) (Sum.inr k)

def hhlMatrix (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ) (y : Point κ) : Matrix ι ι ℝ :=
  ∑ k, y k • hhlFamily t k

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem hhlFamily_symmetric (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ)
    (ht12 : ∀ i j k, t i j k = t j i k) (k : κ) (i j : ι) :
    hhlFamily t k i j = hhlFamily t k j i :=
  ht12 (Sum.inl i) (Sum.inl j) (Sum.inr k)

theorem hhlMatrix_eval (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ)
    (x : Point ι) (y : Point κ) :
    matrixForm (hhlMatrix t y) x x = tensorForm t (high x) (high x) (low y) := by
  rw [matrixForm_apply, tensorForm_hhl]
  simp only [hhlMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp only [hhlFamily]
  ring

/-- The matrix-family domination needed by the genuine linear quadratic
division construction is derived, rather than added as an assumption. -/
theorem hhlMatrix_dom
    (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ)
    (a : ι → ℝ) (b : κ → ℝ) {tau : ℝ} (htau : 0 ≤ tau)
    (ha : ∀ i, tau ≤ a i) (hb0 : ∀ j, 0 ≤ b j) (hb : ∀ j, b j ≤ tau)
    (ht12 : ∀ i j k, t i j k = t j i k) (ht23 : ∀ i j k, t i j k = t i k j)
    (hdom : ∀ z : Point (ι ⊕ κ), |eval (fun i ↦ z i) (cubicPolynomial t)| ≤
      2 * ‖diagonal (Sum.elim a b) z‖ * ‖z‖^2) (x : Point ι) (y : Point κ) :
    |matrixForm (hhlMatrix t y) x x| ≤ (4 * ‖y‖) * ‖diagonal a x‖ * ‖x‖ := by
  rw [hhlMatrix_eval]
  have hc := (spectral_mixed_bounds t a b htau ha hb0 hb ht12 ht23 hdom x y).2
  convert hc using 1
  ring

section Nested

variable {μ : Type*} [Fintype μ] [DecidableEq μ]

/-- The HHL completion at an inner ordered split is an ACTUAL quadratic
polynomial in the original low parameter and the inner low variables. -/
def hhlCrossPolynomial (a : ι → ℝ)
    (t : ((ι ⊕ κ) ⊕ μ) → ((ι ⊕ κ) ⊕ μ) → ((ι ⊕ κ) ⊕ μ) → ℝ) (i : ι) :
    MvPolynomial (μ ⊕ (ι ⊕ κ)) ℝ :=
  parameterCompletionPolynomial a (hhlFamily t) i

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] in
theorem hhlCrossPolynomial_homogeneous (a : ι → ℝ)
    (t : ((ι ⊕ κ) ⊕ μ) → ((ι ⊕ κ) ⊕ μ) → ((ι ⊕ κ) ⊕ μ) → ℝ) (i : ι) :
    (hhlCrossPolynomial a t i).IsHomogeneous 2 :=
  parameterCompletionPolynomial_homogeneous a (hhlFamily t) i

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] in
theorem hhl_cross_polynomial_identity (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)
    (t : ((ι ⊕ κ) ⊕ μ) → ((ι ⊕ κ) ⊕ μ) → ((ι ⊕ κ) ⊕ μ) → ℝ) :
    (∑ i, C (a i) * X (Sum.inr (Sum.inl i)) * hhlCrossPolynomial a t i) =
      mixedCubicPolynomial (hhlFamily t) :=
  cubic_polynomial_identity a ha (hhlFamily t)

/-- This bound starts only from domination of the ORIGINAL cubic, with
actual outer and inner spectral gaps. No mixed-family bound or completion
is supplied by a hypothesis. -/
theorem hhlCrossPolynomial_norm_le
    (t : ((ι ⊕ κ) ⊕ μ) → ((ι ⊕ κ) ⊕ μ) → ((ι ⊕ κ) ⊕ μ) → ℝ)
    (a : ι → ℝ) (b : κ → ℝ) (c : μ → ℝ) {tau sigma : ℝ}
    (htau : 0 ≤ tau) (hOuter : ∀ i, tau ≤ Sum.elim a b i)
    (hc0 : ∀ k, 0 ≤ c k) (hc : ∀ k, c k ≤ tau)
    (hsigma : 0 < sigma) (ha : ∀ i, sigma ≤ a i)
    (hb0 : ∀ j, 0 ≤ b j) (hb : ∀ j, b j ≤ sigma)
    (ht12 : ∀ i j k, t i j k = t j i k) (ht23 : ∀ i j k, t i j k = t i k j)
    (hdom : ∀ w : Point ((ι ⊕ κ) ⊕ μ), |eval (fun i ↦ w i) (cubicPolynomial t)| ≤
      2 * ‖diagonal (Sum.elim (Sum.elim a b) c) w‖ * ‖w‖^2)
    (z : Point μ) (x : Point ι) (y : Point κ) :
    ‖(WithLp.equiv 2 (ι → ℝ)).symm (fun i ↦
      eval (Sum.elim (fun k ↦ z k) (Sum.elim (fun k ↦ x k) (fun j ↦ y j)))
        (hhlCrossPolynomial a t i))‖ ≤ 8 * ‖z‖ * ‖y‖ := by
  have hd : ∀ (z : Point μ) (w : Point (ι ⊕ κ)),
      |matrixForm (matrixFamily (hhlFamily t) (fun k ↦ z k)) w w| ≤
      (4 * ‖z‖) * ‖diagonal (Sum.elim a b) w‖ * ‖w‖ := by
    intro z w
    exact hhlMatrix_dom t (Sum.elim a b) c htau hOuter hc0 hc ht12 ht23 hdom w z
  have hbound := parameterCompletionPolynomial_norm_le (hhlFamily t) a b
    (by norm_num : (0:ℝ) ≤ 4) hsigma ha hb0 hb
    (hhlFamily_symmetric t ht12) hd z x y
  convert hbound using 1 <;> first | rfl | ring

end Nested

end Finite

end WeightedCubicSplit
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
