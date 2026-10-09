/-
  Root-count-free square-function bounds for the normalized zonal filter.

  The proof packages a finite family of scalar functions as one vector in a
  Euclidean space.  The triangle inequality for the Bochner integral then
  gives contraction by a positive normalized kernel without introducing the
  cardinality of the family.  Applying the estimate twice gives the factor
  nine for the Booleanized operator `2 K - K^2`.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FiniteAtomFilter

open MvPolynomial Finset Set MeasureTheory
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

/-- A finite scalar family regarded as one Euclidean vector. -/
def finiteEuclideanVector {N : ℕ} {X : Type*}
    (b : Fin N → X → ℝ) (x : X) : EuclideanSpace ℝ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm (fun i ↦ b i x)

@[simp] theorem finiteEuclideanVector_apply {N : ℕ} {X : Type*}
    (b : Fin N → X → ℝ) (x : X) (i : Fin N) :
    finiteEuclideanVector b x i = b i x := by
  simp [finiteEuclideanVector]

theorem finiteEuclideanVector_norm_sq {N : ℕ} {X : Type*}
    (b : Fin N → X → ℝ) (x : X) :
    ‖finiteEuclideanVector b x‖ ^ 2 = ∑ i, (b i x) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [finiteEuclideanVector]

theorem continuous_finiteEuclideanVector {N : ℕ} {X : Type*}
    [TopologicalSpace X] (b : Fin N → X → ℝ)
    (hb : ∀ i, Continuous (b i)) :
    Continuous (finiteEuclideanVector b) := by
  apply (EuclideanSpace.equiv (Fin N) ℝ).symm.continuous.comp
  exact continuous_pi hb

/-- The vector-valued normalized zonal transform. -/
def normalizedZonalKernelVectorValue {n N : ℕ}
    (p k : ℕ) (base x : sphereSet n)
    (b : Fin N → sphereSet n → ℝ) : EuclideanSpace ℝ (Fin N) :=
  ∫ y : sphereSet n,
    normalizedZonalKernelSection p k base x y • finiteEuclideanVector b y
      ∂normalizedSphereMeasure n

theorem integrable_normalizedZonalKernel_smul_vector
    {n N : ℕ} (hn : 0 < n) (p k : ℕ) (base x : sphereSet n)
    (b : Fin N → sphereSet n → ℝ)
    (hb : ∀ i, Continuous (b i)) :
    Integrable (fun y : sphereSet n ↦
      normalizedZonalKernelSection p k base x y •
        finiteEuclideanVector b y)
      (normalizedSphereMeasure n) := by
  letI : CompactSpace (sphereSet n) :=
    isCompact_iff_compactSpace.mp sphereSet_compact
  letI : IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  apply Continuous.integrable_of_hasCompactSupport
  · exact (continuous_normalizedZonalKernelSection_right p k base x).smul
      (continuous_finiteEuclideanVector b hb)
  · exact (isCompact_univ : IsCompact (Set.univ : Set (sphereSet n))).of_isClosed_subset
      (isClosed_tsupport _) (Set.subset_univ _)

/-- Coordinatewise, the vector transform is the established scalar
normalized zonal transform. -/
theorem normalizedZonalKernelVectorValue_apply
    {n N : ℕ} (hn : 0 < n) (p k : ℕ) (base x : sphereSet n)
    (b : Fin N → sphereSet n → ℝ) (hb : ∀ i, Continuous (b i))
    (i : Fin N) :
    normalizedZonalKernelVectorValue p k base x b i =
      normalizedFunctionZonalKernelValue p k base (b i) x.1 := by
  rw [normalizedFunctionZonalKernelValue_eq_integral_section]
  unfold normalizedZonalKernelVectorValue
  let L := PiLp.proj (𝕜 := ℝ) (p := (2 : ENNReal)) (fun _ : Fin N ↦ ℝ) i
  have hint := integrable_normalizedZonalKernel_smul_vector hn p k base x b hb
  calc
    (∫ y : sphereSet n, normalizedZonalKernelSection p k base x y •
        finiteEuclideanVector b y ∂normalizedSphereMeasure n) i =
        L (∫ y : sphereSet n, normalizedZonalKernelSection p k base x y •
          finiteEuclideanVector b y ∂normalizedSphereMeasure n) := rfl
    _ = ∫ y : sphereSet n, L (normalizedZonalKernelSection p k base x y •
          finiteEuclideanVector b y) ∂normalizedSphereMeasure n :=
      (L.integral_comp_comm hint).symm
    _ = ∫ y : sphereSet n, normalizedZonalKernelSection p k base x y * b i y
          ∂normalizedSphereMeasure n := by
      apply integral_congr_ae
      filter_upwards with y
      simp [L, finiteEuclideanVector]

/-- A nonnegative normalized zonal row contracts the Euclidean norm of every
finite scalar family.  The constant is independent of `N`. -/
theorem normalizedZonalKernel_squareFunction_contraction
    {n N : ℕ} (hn : 2 ≤ n) (p k : ℕ) (base x : sphereSet n)
    (b : Fin N → sphereSet n → ℝ) (hb : ∀ i, Continuous (b i))
    (H : ℝ) (hH : 0 ≤ H)
    (hbound : ∀ y, ∑ i, (b i y) ^ 2 ≤ H) :
    ∑ i, (normalizedFunctionZonalKernelValue p k base (b i) x.1) ^ 2 ≤ H := by
  let v : sphereSet n → EuclideanSpace ℝ (Fin N) := finiteEuclideanVector b
  let K : sphereSet n → ℝ := fun y ↦
    normalizedZonalKernelSection p k base x y
  have hvnorm (y : sphereSet n) : ‖v y‖ ≤ Real.sqrt H := by
    have hsq : ‖v y‖ ^ 2 ≤ H := by
      simpa [v, finiteEuclideanVector_norm_sq] using hbound y
    nlinarith [Real.sq_sqrt hH, norm_nonneg (v y), Real.sqrt_nonneg H]
  have hK (y : sphereSet n) : 0 ≤ K y :=
    normalizedZonalKernelSection_nonneg (by omega) p k base x y
  have hint : Integrable (fun y : sphereSet n ↦ K y • v y)
      (normalizedSphereMeasure n) := by
    exact integrable_normalizedZonalKernel_smul_vector (by omega)
      p k base x b hb
  have hnorm :
      ‖∫ y : sphereSet n, K y • v y ∂normalizedSphereMeasure n‖ ≤
        Real.sqrt H := by
    calc
      ‖∫ y : sphereSet n, K y • v y ∂normalizedSphereMeasure n‖ ≤
          ∫ y : sphereSet n, K y * Real.sqrt H
            ∂normalizedSphereMeasure n := by
        apply norm_integral_le_of_norm_le
        · exact (integrable_normalizedZonalKernelSection_right
            (by omega) p k base x).mul_const _
        · filter_upwards with y
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hK y)]
          exact mul_le_mul_of_nonneg_left (hvnorm y) (hK y)
      _ = Real.sqrt H := by
        rw [integral_mul_const,
          integral_normalizedZonalKernelSection_eq_one hn]
        simp
  let w := normalizedZonalKernelVectorValue p k base x b
  have hw : ‖w‖ ^ 2 ≤ H := by
    have hwdef : w =
        ∫ y : sphereSet n, K y • v y ∂normalizedSphereMeasure n := rfl
    rw [hwdef]
    nlinarith [Real.sq_sqrt hH, norm_nonneg
      (∫ y : sphereSet n, K y • v y ∂normalizedSphereMeasure n)]
  calc
    ∑ i, (normalizedFunctionZonalKernelValue p k base (b i) x.1) ^ 2 =
        ‖w‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [normalizedZonalKernelVectorValue_apply (by omega) p k base x b hb i]
      simp
    _ ≤ H := hw

/-- The first normalized transform of a coefficient-integrable continuous
function is continuous, since it is the restriction of its kernel
polynomial. -/
theorem continuous_normalizedFunctionZonalKernelValue
    {n : ℕ} (p k : ℕ) (base : sphereSet n) (v : sphereSet n → ℝ)
    (hv : ZonalKernelCoeffIntegrable p k v) :
    Continuous (fun x : sphereSet n ↦
      normalizedFunctionZonalKernelValue p k base v x.1) := by
  have heval : (fun x : sphereSet n ↦
      normalizedFunctionZonalKernelValue p k base v x.1) =
      fun x : sphereSet n ↦ MvPolynomial.eval x.1
        (normalizedFunctionZonalKernelPolynomial p k base v) := by
    funext x
    exact (eval_normalizedFunctionZonalKernelPolynomial p k base v hv x.1).symm
  rw [heval]
  exact (MvPolynomial.continuous_eval _).comp continuous_subtype_val

/-- The Booleanized filter `2 K - K²` enlarges a finite square function by
at most the sharp triangle-inequality factor `9`, still independently of the
number of roots. -/
theorem booleanFilteredFunction_squareFunction_le_nine
    {n N : ℕ} (hn : 2 ≤ n) (p k : ℕ) (base : sphereSet n)
    (b : Fin N → sphereSet n → ℝ) (hb : ∀ i, Continuous (b i))
    (hcoeff : ∀ i, ZonalKernelCoeffIntegrable p k (b i))
    (H : ℝ) (hH : 0 ≤ H)
    (hbound : ∀ y, ∑ i, (b i y) ^ 2 ≤ H)
    (x : sphereSet n) :
    ∑ i, (booleanFilteredFunctionValue p k base (b i) x.1) ^ 2 ≤ 9 * H := by
  let Kb : Fin N → sphereSet n → ℝ := fun i y ↦
    normalizedFunctionZonalKernelValue p k base (b i) y.1
  have hKbcont : ∀ i, Continuous (Kb i) := fun i ↦
    continuous_normalizedFunctionZonalKernelValue p k base (b i) (hcoeff i)
  have hKb (y : sphereSet n) : ∑ i, (Kb i y) ^ 2 ≤ H :=
    normalizedZonalKernel_squareFunction_contraction hn p k base y
      b hb H hH hbound
  let u := finiteEuclideanVector Kb x
  let v : EuclideanSpace ℝ (Fin N) :=
    finiteEuclideanVector (fun i y ↦
      normalizedFunctionZonalKernelValue p k base (Kb i) y.1) x
  have hu : ‖u‖ ≤ Real.sqrt H := by
    have hu_sq : ‖u‖ ^ 2 ≤ H := by
      simpa [u, finiteEuclideanVector_norm_sq] using hKb x
    nlinarith [Real.sq_sqrt hH, norm_nonneg u, Real.sqrt_nonneg H]
  have hv : ‖v‖ ≤ Real.sqrt H := by
    have hv_sq : ‖v‖ ^ 2 ≤ H := by
      rw [finiteEuclideanVector_norm_sq]
      exact normalizedZonalKernel_squareFunction_contraction hn p k base x
        Kb hKbcont H hH hKb
    nlinarith [Real.sq_sqrt hH, norm_nonneg v, Real.sqrt_nonneg H]
  let s : EuclideanSpace ℝ (Fin N) := (2 : ℝ) • u - v
  have hs : ‖s‖ ≤ 3 * Real.sqrt H := by
    calc
      ‖s‖ = ‖(2 : ℝ) • u - v‖ := rfl
      _ ≤ ‖(2 : ℝ) • u‖ + ‖v‖ := norm_sub_le _ _
      _ = 2 * ‖u‖ + ‖v‖ := by
        rw [norm_smul]
        norm_num
      _ ≤ 2 * Real.sqrt H + Real.sqrt H := by gcongr
      _ = 3 * Real.sqrt H := by ring
  have hs_sq : ‖s‖ ^ 2 ≤ 9 * H := by
    nlinarith [Real.sq_sqrt hH, norm_nonneg s, Real.sqrt_nonneg H]
  calc
    ∑ i, (booleanFilteredFunctionValue p k base (b i) x.1) ^ 2 =
        ‖s‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [s, u, v, PiLp.sub_apply, PiLp.smul_apply,
        finiteEuclideanVector_apply, smul_eq_mul]
      unfold booleanFilteredFunctionValue Kb
      rw [Real.norm_eq_abs, sq_abs]
      ring
    _ ≤ 9 * H := hs_sq

end QuarticConvergence
end OptimalConvergenceRates

end
