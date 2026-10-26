import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Basic.Real.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
/-! Actual weighted quadratic division at one ordered spectral split.
The balanced recursive tree and full cubic construction are separate. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.WeightedQuadraticSplit

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem cross_bound_unit
    (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (L : E →ₗ[ℝ] E) {D : ℝ} (hD : 0 ≤ D)
    (hS : ∀ x y, S x y = S y x)
    (hdom : ∀ x, |S x x| ≤ D * ‖L x‖ * ‖x‖)
    {v u : E} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1)
    (horth : ⟪v, u⟫_ℝ = 0) (hLorth : ⟪L v, L u⟫_ℝ = 0)
    (horder : ‖L u‖ ≤ ‖L v‖) : |S v u| ≤ D * ‖L v‖ := by
  have hsq : ‖L u‖ ^ 2 ≤ ‖L v‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 horder
  have hp : ‖v + u‖ ^ 2 = 2 := by
    rw [norm_add_sq_real, hv, hu, horth]
    norm_num
  have hm : ‖v - u‖ ^ 2 = 2 := by
    rw [norm_sub_sq_real, hv, hu, horth]
    norm_num
  have hLp : ‖L (v + u)‖ ^ 2 ≤ 2 * ‖L v‖ ^ 2 := by
    rw [map_add, norm_add_sq_real, hLorth]
    nlinarith
  have hLm : ‖L (v - u)‖ ^ 2 ≤ 2 * ‖L v‖ ^ 2 := by
    rw [map_sub, norm_sub_sq_real, hLorth]
    nlinarith
  have hbound (w : E) (hw : ‖w‖ ^ 2 = 2)
      (hLw : ‖L w‖ ^ 2 ≤ 2 * ‖L v‖ ^ 2) : |S w w| ≤ 2 * D * ‖L v‖ := by
    have hs := (sq_le_sq₀ (abs_nonneg (S w w))
      (mul_nonneg (mul_nonneg hD (norm_nonneg _)) (norm_nonneg _))).2 (hdom w)
    have hmul := mul_le_mul_of_nonneg_left hLw (sq_nonneg D)
    apply abs_le_of_sq_le_sq _ (by positivity)
    simp only [sq_abs, mul_pow] at hs
    rw [hw] at hs
    nlinarith
  have hb1 := abs_le.mp (hbound (v + u) hp hLp)
  have hb2 := abs_le.mp (hbound (v - u) hm hLm)
  have hid : S (v + u) (v + u) - S (v - u) (v - u) = 4 * S v u := by
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    rw [hS u v]
    ring
  exact abs_le.mpr ⟨by linarith [hb1.1, hb2.2], by linarith [hb1.2, hb2.1]⟩

theorem cross_bound
    (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (L : E →ₗ[ℝ] E) {D : ℝ} (hD : 0 ≤ D)
    (hS : ∀ x y, S x y = S y x)
    (hdom : ∀ x, |S x x| ≤ D * ‖L x‖ * ‖x‖)
    {v u : E} (horth : ⟪v, u⟫_ℝ = 0) (hLorth : ⟪L v, L u⟫_ℝ = 0)
    (horder : ‖L u‖ * ‖v‖ ≤ ‖L v‖ * ‖u‖) :
    |S v u| ≤ D * ‖L v‖ * ‖u‖ := by
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
  have hLorth' : ⟪L v', L u'⟫_ℝ = 0 := by
    simp only [v', u', map_smul, inner_smul_left, inner_smul_right, hLorth,
      mul_zero, map_inv₀, RCLike.conj_to_real]
  have hnormL (x : E) : ‖L (‖x‖⁻¹ • x)‖ = ‖L x‖ / ‖x‖ := by
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
    ring
  have horder' : ‖L u'‖ ≤ ‖L v'‖ := by
    change ‖L (‖u‖⁻¹ • u)‖ ≤ ‖L (‖v‖⁻¹ • v)‖
    rw [hnormL, hnormL]
    exact (div_le_div_iff₀ hup hvp).2 horder
  have hunit := cross_bound_unit S L hD hS hdom hv' hu' horth' hLorth' horder'
  have habs : |S v u| = (‖v‖ * ‖u‖) * |S v' u'| := by
    simp only [v', u', map_smul, LinearMap.smul_apply, smul_eq_mul, abs_mul,
      abs_inv, abs_of_nonneg (norm_nonneg _)]
    field_simp
  calc
    |S v u| = (‖v‖ * ‖u‖) * |S v' u'| := habs
    _ ≤ (‖v‖ * ‖u‖) * (D * ‖L v'‖) :=
      mul_le_mul_of_nonneg_left hunit (by positivity)
    _ = D * ‖L v‖ * ‖u‖ := by
      change (‖v‖ * ‖u‖) * (D * ‖L (‖v‖⁻¹ • v)‖) = _
      rw [hnormL]
      field_simp

/-- The full quadratic block on the kernel is actually zero, as required
when a semidefinite spectrum has a terminal kernel leaf. -/
theorem kernel_vanishing (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (L : E →ₗ[ℝ] E) {D : ℝ}
    (hS : ∀ x y, S x y = S y x)
    (hdom : ∀ x, |S x x| ≤ D * ‖L x‖ * ‖x‖)
    {v u : E} (hv : L v = 0) (hu : L u = 0) : S v u = 0 := by
  have hzero (x : E) (hx : L x = 0) : S x x = 0 := by
    apply abs_eq_zero.mp
    apply le_antisymm _ (abs_nonneg _)
    simpa only [hx, norm_zero, mul_zero, zero_mul] using hdom x
  have hp := hzero (v + u) (by simp only [map_add, hv, hu, add_zero])
  have hm := hzero (v - u) (by simp only [map_sub, hv, hu, sub_zero])
  have hid : S (v + u) (v + u) - S (v - u) (v - u) = 4 * S v u := by
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    rw [hS u v]
    ring
  linarith


section Finite

open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

abbrev Point (ι : Type*) := EuclideanSpace ℝ ι

def high (x : Point ι) : Point (ι ⊕ κ) :=
  (WithLp.equiv 2 ((ι ⊕ κ) → ℝ)).symm (Sum.elim (fun i => x i) (fun _ => 0))

def low (y : Point κ) : Point (ι ⊕ κ) :=
  (WithLp.equiv 2 ((ι ⊕ κ) → ℝ)).symm (Sum.elim (fun _ => 0) (fun j => y j))

def diagonal (a : ι → ℝ) : Point ι →ₗ[ℝ] Point ι :=
  Matrix.toEuclideanLin (Matrix.diagonal a)

@[simp] theorem diagonal_apply (a : ι → ℝ) (x : Point ι) (i : ι) :
    diagonal a x i = a i * x i := by
  simp [diagonal, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]

omit [DecidableEq ι] in
theorem norm_sq (x : Point ι) : ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  exact EuclideanSpace.real_norm_sq_eq x

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem norm_high (x : Point ι) : ‖high (κ:=κ) x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [norm_sq, high, Fintype.sum_sum_type]

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem norm_low (y : Point κ) : ‖low (ι:=ι) y‖ = ‖y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [norm_sq, low, Fintype.sum_sum_type]

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem high_low_inner (x : Point ι) (y : Point κ) :
    ⟪high (κ:=κ) x, low (ι:=ι) y⟫_ℝ = 0 := by
  simp [PiLp.inner_apply, high, low, Fintype.sum_sum_type]

@[simp] theorem diagonal_high (a : ι → ℝ) (b : κ → ℝ) (x : Point ι) :
    diagonal (Sum.elim a b) (high x) = high (κ:=κ) (diagonal a x) := by
  ext i
  cases i <;> simp [high, diagonal_apply]

@[simp] theorem diagonal_low (a : ι → ℝ) (b : κ → ℝ) (y : Point κ) :
    diagonal (Sum.elim a b) (low y) = low (ι:=ι) (diagonal b y) := by
  ext i
  cases i <;> simp [low, diagonal_apply]

theorem diagonal_norm_le {b : κ → ℝ} {tau : ℝ} (htau : 0 ≤ tau)
    (hb0 : ∀ j, 0 ≤ b j) (hb : ∀ j, b j ≤ tau) (y : Point κ) :
    ‖diagonal b y‖ ≤ tau * ‖y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, norm_sq, norm_sq]
  calc
    ∑ j, (diagonal b y j)^2 ≤ ∑ j, tau^2 * (y j)^2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [diagonal_apply, mul_pow]
      exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (hb0 j) htau).2 (hb j)) (sq_nonneg _)
    _ = tau^2 * ∑ j, (y j)^2 := (Finset.mul_sum _ _ _).symm

theorem le_diagonal_norm {a : ι → ℝ} {tau : ℝ} (htau : 0 ≤ tau)
    (ha : ∀ i, tau ≤ a i) (x : Point ι) :
    tau * ‖x‖ ≤ ‖diagonal a x‖ := by
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  rw [mul_pow, norm_sq, norm_sq]
  calc
    tau^2 * ∑ i, (x i)^2 = ∑ i, tau^2 * (x i)^2 := Finset.mul_sum _ _ _
    _ ≤ ∑ i, (diagonal a x i)^2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [diagonal_apply, mul_pow]
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ htau (htau.trans (ha i))).2 (ha i)) (sq_nonneg _)

def matrixForm (S : Matrix ι ι ℝ) : Point ι →ₗ[ℝ] Point ι →ₗ[ℝ] ℝ :=
  S.toBilin'.compl₁₂ (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toLinearMap
    (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toLinearMap

theorem matrixForm_apply (S : Matrix ι ι ℝ) (x y : Point ι) :
    matrixForm S x y = ∑ i, ∑ j, x i * S i j * y j := by
  simp [matrixForm, Matrix.toBilin'_apply]

theorem matrixForm_symmetric (S : Matrix ι ι ℝ) (hS : ∀ i j, S i j = S j i)
    (x y : Point ι) : matrixForm S x y = matrixForm S y x := by
  rw [matrixForm_apply, matrixForm_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hS i j]
  ring

theorem diagonal_single (a : ι → ℝ) (i : ι) :
    diagonal a (EuclideanSpace.single i 1) = EuclideanSpace.single i (a i) := by
  ext j
  by_cases hji : j = i <;> simp [diagonal_apply, PiLp.single_apply, hji]

theorem matrixForm_single (S : Matrix ι ι ℝ) (i j : ι) :
    matrixForm S (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = S i j := by
  change S.toBilin' (Pi.single i 1) (Pi.single j 1) = S i j
  exact Matrix.toBilin'_single S i j

/-- Actual singleton completion, including a zero eigenvalue. Both its
identity and norm bound follow from the original quadratic domination. -/
theorem singleton_completion (S : Matrix ι ι ℝ) (a : ι → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hdom : ∀ z : Point ι, |matrixForm S z z| ≤ D * ‖diagonal a z‖ * ‖z‖) (i : ι) :
    a i * (S i i / a i) = S i i ∧ |S i i / a i| ≤ D := by
  have hs : |S i i| ≤ D * |a i| := by
    simpa only [matrixForm_single, diagonal_single, PiLp.norm_single,
      norm_one, mul_one, Real.norm_eq_abs] using hdom (EuclideanSpace.single i 1)
  by_cases ha : a i = 0
  · have hSi : S i i = 0 := abs_eq_zero.mp (le_antisymm (by simpa [ha] using hs) (abs_nonneg _))
    simp [ha, hSi, hD]
  · constructor
    · field_simp
    · rw [abs_div]
      exact (div_le_iff₀ (abs_pos.mpr ha)).2 hs

theorem matrixForm_high_low (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (x : Point ι) (y : Point κ) :
    matrixForm S (high x) (low y) =
      ∑ i, ∑ j, x i * S (Sum.inl i) (Sum.inr j) * y j := by
  simp [matrixForm_apply, high, low, Fintype.sum_sum_type]

/-- The actual cross block inherits a dimension-free weighted bound from
the domination of the full symmetric quadratic form. Zero low eigenvalues
are allowed. The threshold separates the two actual diagonal spectra. -/
theorem high_low_bound (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (a : ι → ℝ) (b : κ → ℝ) {D tau : ℝ} (hD : 0 ≤ D) (htau : 0 ≤ tau)
    (ha : ∀ i, tau ≤ a i) (hb0 : ∀ j, 0 ≤ b j) (hb : ∀ j, b j ≤ tau)
    (hS : ∀ i j, S i j = S j i)
    (hdom : ∀ z : Point (ι ⊕ κ), |matrixForm S z z| ≤
      D * ‖diagonal (Sum.elim a b) z‖ * ‖z‖) (x : Point ι) (y : Point κ) :
    |∑ i, ∑ j, x i * S (Sum.inl i) (Sum.inr j) * y j| ≤
      D * ‖diagonal a x‖ * ‖y‖ := by
  have horder : ‖diagonal (Sum.elim a b) (low y)‖ * ‖high (κ:=κ) x‖ ≤
      ‖diagonal (Sum.elim a b) (high x)‖ * ‖low (ι:=ι) y‖ := by
    simp only [diagonal_low, diagonal_high, norm_low, norm_high]
    calc
      ‖diagonal b y‖ * ‖x‖ ≤ (tau * ‖y‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (diagonal_norm_le htau hb0 hb y) (norm_nonneg _)
      _ = (tau * ‖x‖) * ‖y‖ := by ring
      _ ≤ ‖diagonal a x‖ * ‖y‖ :=
        mul_le_mul_of_nonneg_right (le_diagonal_norm htau ha x) (norm_nonneg _)
  have hc := cross_bound (matrixForm S) (diagonal (Sum.elim a b)) hD
    (matrixForm_symmetric S hS) hdom (high_low_inner x y)
    (by rw [diagonal_high, diagonal_low]; exact high_low_inner _ _) horder
  simpa only [matrixForm_high_low, diagonal_high, norm_high, norm_low] using hc

/-- The explicit high-from-low matrix used at this split. -/
def crossCoefficients (a : ι → ℝ) (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) :
    Matrix ι κ ℝ := fun i j => 2 * S (Sum.inl i) (Sum.inr j) / a i

/-- The same chosen completion is linear in S. This is the property needed
to preserve the polynomial degree of an auxiliary linear parameter. -/
def crossCoefficientMap (a : ι → ℝ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ →ₗ[ℝ] Matrix ι κ ℝ where
  toFun := crossCoefficients a
  map_add' S T := by
    ext i j
    simp only [crossCoefficients, Matrix.add_apply]
    ring
  map_smul' c S := by
    ext i j
    simp only [crossCoefficients, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem weighted_crossCoefficients (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)
    (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (i : ι) (j : κ) :
    a i * crossCoefficients a S i j = 2 * S (Sum.inl i) (Sum.inr j) := by
  simp only [crossCoefficients]
  field_simp [ha i]

theorem crossCompletion_pair (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)
    (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (x : Point ι) (y : Point κ) :
    ⟪diagonal a x, Matrix.toEuclideanLin (crossCoefficients a S) y⟫_ℝ =
      2 * ∑ i, ∑ j, x i * S (Sum.inl i) (Sum.inr j) * y j := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, diagonal_apply]
  change (∑ i, (∑ j, crossCoefficients a S i j * y j) * (a i * x i)) = _
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hw := weighted_crossCoefficients a ha S i j
  calc
    crossCoefficients a S i j * y j * (a i * x i) =
        x i * (a i * crossCoefficients a S i j) * y j := by ring
    _ = 2 * (x i * S (Sum.inl i) (Sum.inr j) * y j) := by rw [hw]; ring

/-- Actual Euclidean operator bound for the explicitly chosen cross
completion. The only inverse is on the strictly positive high block. -/
theorem crossCompletion_norm_le (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (a : ι → ℝ) (b : κ → ℝ) {D tau : ℝ} (hD : 0 ≤ D) (htau : 0 < tau)
    (ha : ∀ i, tau ≤ a i) (hb0 : ∀ j, 0 ≤ b j) (hb : ∀ j, b j ≤ tau)
    (hS : ∀ i j, S i j = S j i)
    (hdom : ∀ z : Point (ι ⊕ κ), |matrixForm S z z| ≤
      D * ‖diagonal (Sum.elim a b) z‖ * ‖z‖) (y : Point κ) :
    ‖Matrix.toEuclideanLin (crossCoefficients a S) y‖ ≤ 2 * D * ‖y‖ := by
  let c : Point ι := Matrix.toEuclideanLin (crossCoefficients a S) y
  let v : Point ι := diagonal (fun i => (a i)⁻¹) c
  have ha0 : ∀ i, a i ≠ 0 := fun i => (htau.trans_le (ha i)).ne'
  have hLv : diagonal a v = c := by
    ext i
    simp only [v, diagonal_apply]
    field_simp [ha0 i]
  have hpair : ‖c‖ ^ 2 = 2 * ∑ i, ∑ j, v i * S (Sum.inl i) (Sum.inr j) * y j := by
    rw [← crossCompletion_pair a ha0 S v y, hLv]
    exact (real_inner_self_eq_norm_sq c).symm
  have hc := high_low_bound S a b hD htau.le ha hb0 hb hS hdom v y
  rw [hLv] at hc
  by_cases hc0 : c = 0
  · change ‖c‖ ≤ _
    simp only [hc0, norm_zero]
    positivity
  have hcp : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  have hs : ‖c‖ * ‖c‖ ≤ ‖c‖ * (2 * D * ‖y‖) := by
    nlinarith [le_abs_self (∑ i, ∑ j, v i * S (Sum.inl i) (Sum.inr j) * y j)]
  exact (mul_le_mul_iff_right₀ hcp).mp hs

open MvPolynomial

/-- The actual linear polynomial in the low variables output at a high
coordinate. Its coefficients are the explicit chosen inverse block. -/
def completionPolynomial (a : ι → ℝ) (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (i : ι) : MvPolynomial (ι ⊕ κ) ℝ :=
  ∑ j, C (crossCoefficients a S i j) * X (Sum.inr j)

def mixedPolynomial (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) :
    MvPolynomial (ι ⊕ κ) ℝ :=
  ∑ i, ∑ j, C (2 * S (Sum.inl i) (Sum.inr j)) * X (Sum.inl i) * X (Sum.inr j)

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem completionPolynomial_homogeneous (a : ι → ℝ)
    (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (i : ι) :
    (completionPolynomial a S i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact (MvPolynomial.isHomogeneous_X ℝ (Sum.inr j)).C_mul _

omit [DecidableEq ι] [DecidableEq κ] in
theorem mixedPolynomial_homogeneous (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) :
    (mixedPolynomial S).IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact ((MvPolynomial.isHomogeneous_X ℝ (Sum.inl i)).C_mul _).mul
    (MvPolynomial.isHomogeneous_X ℝ (Sum.inr j))

omit [DecidableEq ι] [DecidableEq κ] in
/-- Exact polynomial division of the full mixed quadratic block, with
the original degree and no equality modulo a sphere ideal. -/
theorem polynomial_identity (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)
    (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) :
    (∑ i, C (a i) * X (Sum.inl i) * completionPolynomial a S i) = mixedPolynomial S := by
  classical
  simp only [completionPolynomial, mixedPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  calc
    C (a i) * X (Sum.inl i) * (C (crossCoefficients a S i j) * X (Sum.inr j)) =
        C (a i * crossCoefficients a S i j) * X (Sum.inl i) * X (Sum.inr j) := by
      rw [map_mul]
      ring
    _ = _ := by rw [weighted_crossCoefficients a ha S i j]

omit [Fintype ι] [DecidableEq ι] in
theorem completionPolynomial_eval (a : ι → ℝ)
    (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (x : Point ι) (y : Point κ) (i : ι) :
    eval (Sum.elim (fun k => x k) (fun j => y j)) (completionPolynomial a S i) =
      Matrix.toEuclideanLin (crossCoefficients a S) y i := by
  simp [completionPolynomial, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

/-- The actual polynomial vector obeys the same Euclidean bound. -/
theorem completionPolynomial_norm_le (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (a : ι → ℝ) (b : κ → ℝ) {D tau : ℝ} (hD : 0 ≤ D) (htau : 0 < tau)
    (ha : ∀ i, tau ≤ a i) (hb0 : ∀ j, 0 ≤ b j) (hb : ∀ j, b j ≤ tau)
    (hS : ∀ i j, S i j = S j i)
    (hdom : ∀ z : Point (ι ⊕ κ), |matrixForm S z z| ≤
      D * ‖diagonal (Sum.elim a b) z‖ * ‖z‖) (x : Point ι) (y : Point κ) :
    ‖(WithLp.equiv 2 (ι → ℝ)).symm (fun i =>
      eval (Sum.elim (fun k => x k) (fun j => y j)) (completionPolynomial a S i))‖ ≤
      2 * D * ‖y‖ := by
  have hv : (WithLp.equiv 2 (ι → ℝ)).symm (fun i =>
      eval (Sum.elim (fun k => x k) (fun j => y j)) (completionPolynomial a S i)) =
      Matrix.toEuclideanLin (crossCoefficients a S) y := by
    ext i
    exact completionPolynomial_eval a S x y i
  rw [hv]
  exact crossCompletion_norm_le S a b hD htau ha hb0 hb hS hdom y

variable {μ : Type*} [Fintype μ]

def matrixFamily (S : μ → Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (z : μ → ℝ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := ∑ k, z k • S k

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem crossCoefficients_matrixFamily (a : ι → ℝ)
    (S : μ → Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (z : μ → ℝ) :
    crossCoefficients a (matrixFamily S z) = ∑ k, z k • crossCoefficients a (S k) := by
  change crossCoefficientMap a (∑ k, z k • S k) =
    ∑ k, z k • crossCoefficientMap a (S k)
  simp only [map_sum, map_smul]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem matrixFamily_symmetric (S : μ → Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (hS : ∀ k i j, S k i j = S k j i) (z : μ → ℝ) (i j : ι ⊕ κ) :
    matrixFamily S z i j = matrixFamily S z j i := by
  simp only [matrixFamily, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [hS k i j]

/-- An actual quadratic vector when the matrix input is an actual linear
parameter family. No nonlinear choice of completion occurs. -/
def parameterCompletionPolynomial (a : ι → ℝ)
    (S : μ → Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (i : ι) :
    MvPolynomial (μ ⊕ (ι ⊕ κ)) ℝ :=
  ∑ k, ∑ j, C (crossCoefficients a (S k) i j) * X (Sum.inl k) * X (Sum.inr (Sum.inr j))

def mixedCubicPolynomial (S : μ → Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) :
    MvPolynomial (μ ⊕ (ι ⊕ κ)) ℝ :=
  ∑ k, ∑ i, ∑ j, C (2 * S k (Sum.inl i) (Sum.inr j)) *
    X (Sum.inl k) * X (Sum.inr (Sum.inl i)) * X (Sum.inr (Sum.inr j))

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem parameterCompletionPolynomial_homogeneous (a : ι → ℝ)
    (S : μ → Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (i : ι) :
    (parameterCompletionPolynomial a S i).IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro k _
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact ((MvPolynomial.isHomogeneous_X ℝ (Sum.inl k)).C_mul _).mul
    (MvPolynomial.isHomogeneous_X ℝ (Sum.inr (Sum.inr j)))

omit [DecidableEq ι] [DecidableEq κ] in
theorem mixedCubicPolynomial_homogeneous
    (S : μ → Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) :
    (mixedCubicPolynomial S).IsHomogeneous 3 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro k _
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact (((MvPolynomial.isHomogeneous_X ℝ (Sum.inl k)).C_mul _).mul
    (MvPolynomial.isHomogeneous_X ℝ (Sum.inr (Sum.inl i)))).mul
    (MvPolynomial.isHomogeneous_X ℝ (Sum.inr (Sum.inr j)))

omit [DecidableEq ι] [DecidableEq κ] in
theorem cubic_polynomial_identity (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)
    (S : μ → Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) :
    (∑ i, C (a i) * X (Sum.inr (Sum.inl i)) * parameterCompletionPolynomial a S i) =
      mixedCubicPolynomial S := by
  classical
  simp only [parameterCompletionPolynomial, mixedCubicPolynomial, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  calc
    C (a i) * X (Sum.inr (Sum.inl i)) *
        (C (crossCoefficients a (S k) i j) * X (Sum.inl k) * X (Sum.inr (Sum.inr j))) =
        C (a i * crossCoefficients a (S k) i j) * X (Sum.inl k) *
          X (Sum.inr (Sum.inl i)) * X (Sum.inr (Sum.inr j)) := by
      rw [map_mul]
      ring
    _ = _ := by rw [weighted_crossCoefficients a ha (S k) i j]

omit [Fintype ι] [DecidableEq ι] in
theorem parameterCompletionPolynomial_eval (a : ι → ℝ)
    (S : μ → Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (z : Point μ) (x : Point ι) (y : Point κ) (i : ι) :
    eval (Sum.elim (fun k => z k) (Sum.elim (fun k => x k) (fun j => y j)))
      (parameterCompletionPolynomial a S i) =
      Matrix.toEuclideanLin (crossCoefficients a (matrixFamily S (fun k => z k))) y i := by
  conv_lhs =>
    simp only [parameterCompletionPolynomial, map_sum, map_mul, eval_C, eval_X,
      Sum.elim_inl, Sum.elim_inr]
  rw [crossCoefficients_matrixFamily, Matrix.toLpLin_apply]
  change (∑ k, ∑ j, crossCoefficients a (S k) i j * z k * y j) =
    ∑ j, (∑ k, z k • crossCoefficients a (S k)) i j * y j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- A true degree-two polynomial cross completion with its Euclidean
norm estimate for a linear parameter family. The input domination is the
natural weighted quadratic inequality; no completion is assumed. -/
theorem parameterCompletionPolynomial_norm_le
    (S : μ → Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (a : ι → ℝ) (b : κ → ℝ)
    {D tau : ℝ} (hD : 0 ≤ D) (htau : 0 < tau)
    (ha : ∀ i, tau ≤ a i) (hb0 : ∀ j, 0 ≤ b j) (hb : ∀ j, b j ≤ tau)
    (hS : ∀ k i j, S k i j = S k j i)
    (hdom : ∀ (z : Point μ) (w : Point (ι ⊕ κ)),
      |matrixForm (matrixFamily S (fun k => z k)) w w| ≤
      (D * ‖z‖) * ‖diagonal (Sum.elim a b) w‖ * ‖w‖)
    (z : Point μ) (x : Point ι) (y : Point κ) :
    ‖(WithLp.equiv 2 (ι → ℝ)).symm (fun i =>
      eval (Sum.elim (fun k => z k) (Sum.elim (fun k => x k) (fun j => y j)))
        (parameterCompletionPolynomial a S i))‖ ≤ 2 * D * ‖z‖ * ‖y‖ := by
  have hv : (WithLp.equiv 2 (ι → ℝ)).symm (fun i =>
      eval (Sum.elim (fun k => z k) (Sum.elim (fun k => x k) (fun j => y j)))
        (parameterCompletionPolynomial a S i)) =
      Matrix.toEuclideanLin (crossCoefficients a (matrixFamily S (fun k => z k))) y := by
    ext i
    exact parameterCompletionPolynomial_eval a S z x y i
  rw [hv]
  have hc := crossCompletion_norm_le (matrixFamily S (fun k => z k)) a b
    (mul_nonneg hD (norm_nonneg z)) htau ha hb0 hb
    (matrixFamily_symmetric S hS (fun k => z k)) (hdom z) y
  simpa only [mul_assoc] using hc

end Finite

end OptimalConvergenceRates.SphereDimensionBounds.WeightedQuadraticSplit
