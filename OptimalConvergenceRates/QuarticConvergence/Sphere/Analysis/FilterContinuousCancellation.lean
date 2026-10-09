/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Analysis/FilterContinuousCancellation.lean

  Axial-reflection cancellation for arbitrary continuous sphere functions.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Repair
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.ContinuousRootFilter

open MvPolynomial Set

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers
open SpherePolynomialQuadrature

/-- The signed one-step normalized zonal-filter error for a continuous sphere function.
This name is deliberately distinct from the finite-packing copy, so this module remains upstream of
`FinitePacking`. -/
noncomputable def packingContinuousZonalFilterError {n : ℕ}
    (p k : ℕ) (base : sphereSet n) (v : sphereSet n → ℝ) (x : sphereSet n) : ℝ :=
  normalizedFunctionZonalKernelValue p k base v x.1 - v x

/-- A continuous sphere function times a zonal-kernel section is integrable. -/
theorem packingContinuous_integrable_mul_sphereDirichletZonalKernel_section
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (v : sphereSet n → ℝ)
    (hv : Continuous v) (x : Fin n → ℝ) :
    MeasureTheory.Integrable (fun y : sphereSet n ↦ v y *
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x))
      (normalizedSphereMeasure n) := by
  letI : CompactSpace (sphereSet n) :=
    isCompact_iff_compactSpace.mp sphereSet_compact
  letI : MeasureTheory.IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  apply Continuous.integrable_of_hasCompactSupport
  · exact hv.mul (continuous_sphereDirichletZonalKernel_section p k x)
  · exact (isCompact_univ : IsCompact (Set.univ : Set (sphereSet n))).of_isClosed_subset
      (isClosed_tsupport _) (Set.subset_univ _)

/-- Reflection pairing cancels the first-order kernel increment for every continuous sphere
function. -/
theorem packingContinuous_two_mul_integral_kernel_increment_eq_symmetricIncrement
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (v : sphereSet n → ℝ)
    (hv : Continuous v) (x : sphereSet n) :
    2 * (∫ y : sphereSet n, (v y - v x) *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n) =
      ∫ y : sphereSet n,
        (v y + v (sphereAxialReflection x y) - 2 * v x) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n := by
  let f : sphereSet n → ℝ := fun y ↦
    (v y - v x) *
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
  have hf : MeasureTheory.Integrable f (normalizedSphereMeasure n) := by
    apply packingContinuous_integrable_mul_sphereDirichletZonalKernel_section
      hn p k (fun y ↦ v y - v x)
    exact hv.sub continuous_const
  have hfcomp : MeasureTheory.Integrable
      (fun y ↦ f (sphereAxialReflection x y)) (normalizedSphereMeasure n) := by
    change MeasureTheory.Integrable (f ∘ sphereAxialReflection x)
      (normalizedSphereMeasure n)
    exact ((sphereAxialReflection_measurePreserving x).integrable_comp_emb
      (sphereAxialReflection_measurableEmbedding x)).2 hf
  calc
    2 * (∫ y : sphereSet n, (v y - v x) *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n) =
        2 * ∫ y : sphereSet n, f y ∂normalizedSphereMeasure n := by rfl
    _ = (∫ y : sphereSet n, f y ∂normalizedSphereMeasure n) +
        ∫ y : sphereSet n, f (sphereAxialReflection x y)
          ∂normalizedSphereMeasure n := by
      rw [integral_comp_sphereAxialReflection]
      ring
    _ = ∫ y : sphereSet n, (f y + f (sphereAxialReflection x y))
          ∂normalizedSphereMeasure n :=
      (MeasureTheory.integral_add hf hfcomp).symm
    _ = ∫ y : sphereSet n,
        (v y + v (sphereAxialReflection x y) - 2 * v x) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      dsimp [f]
      rw [← sphereAxialReflection_coe x y]
      rw [eval_sphereDirichletZonalKernel_sphereAxialReflection]
      ring

/-- A symmetric second-difference estimate gives the corresponding integrated second-moment
remainder bound. -/
theorem packingContinuous_abs_integral_kernel_increment_le_of_symmetricIncrement
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (A : ℝ)
    (v : sphereSet n → ℝ) (hv : Continuous v) (x : sphereSet n)
    (hsymmetric : ∀ y : sphereSet n,
      |v y + v (sphereAxialReflection x y) - 2 * v x| ≤
        (2 * A) * sphereChordalSq y.1 x.1) :
    |∫ y : sphereSet n, (v y - v x) *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n| ≤
      A * continuousZonalKernelSecondMoment p k x.1 := by
  have hmajor : MeasureTheory.Integrable (fun y : sphereSet n ↦
      (2 * A) * (sphereChordalSq y.1 x.1 *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)))
      (normalizedSphereMeasure n) :=
    (integrable_sphereChordalSq_mul_sphereDirichletZonalKernel_section
      hn p k x.1).const_mul (2 * A)
  have hsymIntegral :
      |∫ y : sphereSet n,
        (v y + v (sphereAxialReflection x y) - 2 * v x) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n| ≤
        2 * (A * continuousZonalKernelSecondMoment p k x.1) := by
    calc
      |∫ y : sphereSet n,
        (v y + v (sphereAxialReflection x y) - 2 * v x) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n| ≤
          ∫ y : sphereSet n, (2 * A) *
            (sphereChordalSq y.1 x.1 *
              MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1))
              ∂normalizedSphereMeasure n := by
        change ‖∫ y : sphereSet n,
          (v y + v (sphereAxialReflection x y) - 2 * v x) *
            MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
              ∂normalizedSphereMeasure n‖ ≤ _
        apply MeasureTheory.norm_integral_le_of_norm_le hmajor
        filter_upwards with y
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (eval_sphereDirichletZonalKernel_nonneg p k y.1 x.1)]
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right (hsymmetric y)
            (eval_sphereDirichletZonalKernel_nonneg p k y.1 x.1)
      _ = 2 * (A * continuousZonalKernelSecondMoment p k x.1) := by
        rw [MeasureTheory.integral_const_mul]
        unfold continuousZonalKernelSecondMoment
        ring
  have hpair :=
    packingContinuous_two_mul_integral_kernel_increment_eq_symmetricIncrement
      hn p k v hv x
  have habs :
      2 * |∫ y : sphereSet n, (v y - v x) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n| =
        |∫ y : sphereSet n,
          (v y + v (sphereAxialReflection x y) - 2 * v x) *
            MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
              ∂normalizedSphereMeasure n| := by
    calc
      2 * |∫ y : sphereSet n, (v y - v x) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n| =
          |2 * (∫ y : sphereSet n, (v y - v x) *
            MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
              ∂normalizedSphereMeasure n)| := by
        rw [abs_mul]
        norm_num
      _ = |∫ y : sphereSet n,
          (v y + v (sphereAxialReflection x y) - 2 * v x) *
            MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
              ∂normalizedSphereMeasure n| := congrArg abs hpair
  linarith

/-- The normalized filter error is the normalized integral of increments from the evaluation
point. -/
theorem packingContinuous_filterError_eq_integral_increment
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (base : sphereSet n)
    (v : sphereSet n → ℝ) (hv : Continuous v) (x : sphereSet n)
    (hmass : continuousZonalKernelMass p k x.1 =
      continuousZonalKernelMass p k base.1) :
    packingContinuousZonalFilterError p k base v x =
      (∫ y : sphereSet n, (v y - v x) *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n) /
        continuousZonalKernelMass p k base.1 := by
  have hZpos : 0 < continuousZonalKernelMass p k base.1 :=
    continuousZonalKernelMass_pos hn p k base.1 base.2
  have hkernel := integrable_sphereDirichletZonalKernel_section hn p k x.1
  have hmul := packingContinuous_integrable_mul_sphereDirichletZonalKernel_section
    hn p k v hv x.1
  have hint : (fun y : sphereSet n ↦ (v y - v x) *
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)) =
      (fun y ↦ v y * MvPolynomial.eval y.1
        (sphereDirichletZonalKernel p k x.1) -
        v x * MvPolynomial.eval y.1
          (sphereDirichletZonalKernel p k x.1)) := by
    funext y
    ring
  have horient :
      (∫ y : sphereSet n, v y *
          MvPolynomial.eval x.1 (sphereDirichletZonalKernel p k y.1)
            ∂normalizedSphereMeasure n) =
        ∫ y : sphereSet n, v y *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [eval_sphereDirichletZonalKernel_comm]
  unfold packingContinuousZonalFilterError normalizedFunctionZonalKernelValue
  rw [horient, hint, MeasureTheory.integral_sub hmul (hkernel.const_mul (v x))]
  rw [MeasureTheory.integral_const_mul,
    show (∫ y : sphereSet n,
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
        ∂normalizedSphereMeasure n) =
      continuousZonalKernelMass p k base.1 from hmass]
  field_simp [hZpos.ne']

/-- A symmetric second-difference bound and a normalized second-moment bound give a pointwise
second-order estimate for the continuous zonal filter. -/
theorem packingContinuous_abs_filterError_le_of_symmetricIncrement
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (base : sphereSet n)
    (v : sphereSet n → ℝ) (hv : Continuous v) (x : sphereSet n)
    (A B : ℝ) (hA : 0 ≤ A)
    (hmass : continuousZonalKernelMass p k x.1 =
      continuousZonalKernelMass p k base.1)
    (hsymmetric : ∀ y : sphereSet n,
      |v y + v (sphereAxialReflection x y) - 2 * v x| ≤
        (2 * A) * sphereChordalSq y.1 x.1)
    (hmoment : continuousZonalKernelSecondMoment p k x.1 /
      continuousZonalKernelMass p k base.1 ≤ B) :
    |packingContinuousZonalFilterError p k base v x| ≤ A * B := by
  have hZpos : 0 < continuousZonalKernelMass p k base.1 :=
    continuousZonalKernelMass_pos hn p k base.1 base.2
  rw [packingContinuous_filterError_eq_integral_increment
    hn p k base v hv x hmass]
  rw [abs_div, abs_of_pos hZpos]
  have hinter :=
    packingContinuous_abs_integral_kernel_increment_le_of_symmetricIncrement
      hn p k A v hv x hsymmetric
  calc
    |∫ y : sphereSet n, (v y - v x) *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n| /
        continuousZonalKernelMass p k base.1 ≤
      (A * continuousZonalKernelSecondMoment p k x.1) /
        continuousZonalKernelMass p k base.1 :=
      div_le_div_of_nonneg_right hinter hZpos.le
    _ = A * (continuousZonalKernelSecondMoment p k x.1 /
        continuousZonalKernelMass p k base.1) := by ring
    _ ≤ A * B := mul_le_mul_of_nonneg_left hmoment hA

/-- The fixed-power second-moment estimate yields a uniform `k⁻²` error bound for every
continuous sphere function satisfying an axial symmetric-increment estimate. -/
theorem packingContinuous_exists_fixedPower_filterError_bound
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      ∀ (base : sphereSet n) (v : sphereSet n → ℝ), Continuous v →
      ∀ (x : sphereSet n) (A : ℝ), 0 ≤ A →
      (∀ y : sphereSet n,
        |v y + v (sphereAxialReflection x y) - 2 * v x| ≤
          (2 * A) * sphereChordalSq y.1 x.1) →
      |packingContinuousZonalFilterError (n + 3) k base v x| ≤
        A * (C / (k : ℝ) ^ 2) := by
  obtain ⟨C, hC, hmoment⟩ := continuousZonalKernel_fixedPower_secondMoment hn
  refine ⟨C, hC, ?_⟩
  intro k hk base v hv x A hA hsymmetric
  have hmass := continuousZonalKernelMass_eq_on_sphere
    (by omega) (sphereKernelPower n) k x base
  have hmass' : continuousZonalKernelMass (n + 3) k x.1 =
      continuousZonalKernelMass (n + 3) k base.1 := by
    simpa [sphereKernelPower] using hmass
  apply packingContinuous_abs_filterError_le_of_symmetricIncrement
    (by omega) (n + 3) k base v hv x A (C / (k : ℝ) ^ 2) hA
  · exact hmass'
  · exact hsymmetric
  · rw [← hmass']
    simpa [sphereKernelPower] using hmoment k hk x

end QuarticConvergence
end OptimalConvergenceRates
