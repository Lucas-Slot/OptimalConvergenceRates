/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Kernel/ContinuousRootFilter.lean

  Polynomial representatives of the zonal kernel and its Booleanization on
  non-polynomial sphere functions.
-/
import OptimalConvergenceRates.BasicNotions.SoSConeClosed
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Quadrature

open Set MeasureTheory MvPolynomial Finset
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers SpherePolynomialQuadrature

/-- Coefficientwise integrability needed to turn the continuous zonal-kernel
integral of an arbitrary sphere function into an ambient polynomial. Retained
smooth roots will satisfy this after their compact radial extension. -/
def ZonalKernelCoeffIntegrable {n : ℕ} (p k : ℕ) (v : sphereSet n → ℝ) : Prop :=
  ∀ α : ExpLE n (2 * (p * k)),
    Integrable (fun y : sphereSet n ↦ v y *
      legacyMvCoeff α.1 (sphereDirichletZonalKernel p k y.1))
      (normalizedSphereMeasure n)

/-- Integrate the finitely many coefficients of the zonal kernel against an
arbitrary sphere function. This is the polynomial-range adapter missing from
the existing bounded-degree sphere-polynomial operator. -/
noncomputable def functionZonalKernelPolynomial {n : ℕ}
    (p k : ℕ) (v : sphereSet n → ℝ) : MvPolynomial (Fin n) ℝ :=
  polyOfVec (2 * (p * k)) fun α ↦
    ∫ y : sphereSet n, v y *
      legacyMvCoeff α.1 (sphereDirichletZonalKernel p k y.1)
        ∂normalizedSphereMeasure n

/-- The coefficient-integrated zonal transform has the kernel section's
ambient degree bound, independently of integrability. -/
theorem functionZonalKernelPolynomial_totalDegree_le {n : ℕ}
    (p k : ℕ) (v : sphereSet n → ℝ) :
    (functionZonalKernelPolynomial p k v).totalDegree ≤ 2 * (p * k) :=
  polyOfVec_totalDegree_le _

/-- Evaluation of the coefficient-integrated polynomial is the corresponding
unnormalized continuous zonal-kernel integral. -/
theorem eval_functionZonalKernelPolynomial {n : ℕ}
    (p k : ℕ) (v : sphereSet n → ℝ)
    (hv : ZonalKernelCoeffIntegrable p k v) (x : Fin n → ℝ) :
    MvPolynomial.eval x (functionZonalKernelPolynomial p k v) =
      ∫ y : sphereSet n, v y *
        MvPolynomial.eval x (sphereDirichletZonalKernel p k y.1)
          ∂normalizedSphereMeasure n := by
  classical
  let d := 2 * (p * k)
  have hkernelDegree (y : sphereSet n) :
      (sphereDirichletZonalKernel p k y.1).totalDegree ≤ d :=
    sphereDirichletZonalKernel_totalDegree_le p k y.1
  have heval (y : sphereSet n) :
      MvPolynomial.eval x (sphereDirichletZonalKernel p k y.1) =
        ∑ α : ExpLE n d,
          legacyMvCoeff α.1 (sphereDirichletZonalKernel p k y.1) *
            α.1.prod fun i e ↦ x i ^ e := by
    calc
      MvPolynomial.eval x (sphereDirichletZonalKernel p k y.1) =
          MvPolynomial.eval x
            (polyOfVec d (coeffVec d (sphereDirichletZonalKernel p k y.1))) := by
        rw [polyOfVec_coeffVec (hkernelDegree y)]
      _ = _ := by
        unfold polyOfVec
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro α _
        rw [MvPolynomial.eval_monomial]
        rfl
  unfold functionZonalKernelPolynomial
  change MvPolynomial.eval x
      (polyOfVec d fun α ↦
        ∫ y : sphereSet n, v y *
          legacyMvCoeff α.1 (sphereDirichletZonalKernel p k y.1)
            ∂normalizedSphereMeasure n) = _
  simp only [polyOfVec, map_sum, MvPolynomial.eval_monomial]
  calc
    (∑ α : ExpLE n d,
      (∫ y : sphereSet n, v y *
        legacyMvCoeff α.1 (sphereDirichletZonalKernel p k y.1)
          ∂normalizedSphereMeasure n) *
        α.1.prod fun i e ↦ x i ^ e) =
      ∑ α : ExpLE n d,
        ∫ y : sphereSet n,
          (v y * legacyMvCoeff α.1 (sphereDirichletZonalKernel p k y.1)) *
            (α.1.prod fun i e ↦ x i ^ e)
          ∂normalizedSphereMeasure n := by
      apply Finset.sum_congr rfl
      intro α _
      rw [integral_mul_const]
    _ = ∫ y : sphereSet n,
        ∑ α : ExpLE n d,
          (v y * legacyMvCoeff α.1 (sphereDirichletZonalKernel p k y.1)) *
            (α.1.prod fun i e ↦ x i ^ e)
        ∂normalizedSphereMeasure n := by
      rw [integral_finsetSum]
      intro α _
      exact (hv α).mul_const _
    _ = ∫ y : sphereSet n, v y *
        MvPolynomial.eval x (sphereDirichletZonalKernel p k y.1)
          ∂normalizedSphereMeasure n := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [heval y, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro α _
      ring

/-- The normalized continuous zonal-kernel operator evaluated at a point. -/
noncomputable def normalizedFunctionZonalKernelValue {n : ℕ}
    (p k : ℕ) (base : sphereSet n) (v : sphereSet n → ℝ) (x : Fin n → ℝ) : ℝ :=
  (∫ y : sphereSet n, v y *
      MvPolynomial.eval x (sphereDirichletZonalKernel p k y.1)
        ∂normalizedSphereMeasure n) /
    continuousZonalKernelMass p k base.1

/-- Polynomial representative of the normalized zonal-kernel operator on an
arbitrary sphere function. -/
noncomputable def normalizedFunctionZonalKernelPolynomial {n : ℕ}
    (p k : ℕ) (base : sphereSet n) (v : sphereSet n → ℝ) :
    MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C (continuousZonalKernelMass p k base.1)⁻¹ *
    functionZonalKernelPolynomial p k v

theorem normalizedFunctionZonalKernelPolynomial_totalDegree_le {n : ℕ}
    (p k : ℕ) (base : sphereSet n) (v : sphereSet n → ℝ) :
    (normalizedFunctionZonalKernelPolynomial p k base v).totalDegree ≤
      2 * (p * k) := by
  calc
    (normalizedFunctionZonalKernelPolynomial p k base v).totalDegree ≤
        (MvPolynomial.C (continuousZonalKernelMass p k base.1)⁻¹).totalDegree +
          (functionZonalKernelPolynomial p k v).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + 2 * (p * k) := Nat.add_le_add (by simp)
      (functionZonalKernelPolynomial_totalDegree_le p k v)
    _ = 2 * (p * k) := by omega

theorem eval_normalizedFunctionZonalKernelPolynomial {n : ℕ}
    (p k : ℕ) (base : sphereSet n) (v : sphereSet n → ℝ)
    (hv : ZonalKernelCoeffIntegrable p k v) (x : Fin n → ℝ) :
    MvPolynomial.eval x (normalizedFunctionZonalKernelPolynomial p k base v) =
      normalizedFunctionZonalKernelValue p k base v x := by
  unfold normalizedFunctionZonalKernelPolynomial normalizedFunctionZonalKernelValue
  rw [map_mul, eval_C, eval_functionZonalKernelPolynomial p k v hv x]
  ring

/-- Pointwise Booleanization `2K - K²` of the normalized zonal-kernel operator. -/
noncomputable def booleanFilteredFunctionValue {n : ℕ}
    (p k : ℕ) (base : sphereSet n) (v : sphereSet n → ℝ) (x : Fin n → ℝ) : ℝ :=
  normalizedFunctionZonalKernelValue p k base v x +
    normalizedFunctionZonalKernelValue p k base v x -
    normalizedFunctionZonalKernelValue p k base
      (fun y ↦ normalizedFunctionZonalKernelValue p k base v y.1) x

/-- Ambient polynomial representative of the Boolean-filtered sphere function.
Both applications of `K` land in the same degree-`2pk` polynomial range. -/
noncomputable def booleanFilteredFunctionPolynomial {n : ℕ}
    (p k : ℕ) (base : sphereSet n) (v : sphereSet n → ℝ) :
    MvPolynomial (Fin n) ℝ :=
  normalizedFunctionZonalKernelPolynomial p k base v +
    normalizedFunctionZonalKernelPolynomial p k base v -
    normalizedFunctionZonalKernelPolynomial p k base
      (fun y ↦ MvPolynomial.eval y.1
        (normalizedFunctionZonalKernelPolynomial p k base v))

theorem booleanFilteredFunctionPolynomial_totalDegree_le {n : ℕ}
    (p k : ℕ) (base : sphereSet n) (v : sphereSet n → ℝ) :
    (booleanFilteredFunctionPolynomial p k base v).totalDegree ≤ 2 * (p * k) := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · exact (MvPolynomial.totalDegree_add _ _).trans (max_le
      (normalizedFunctionZonalKernelPolynomial_totalDegree_le p k base v)
      (normalizedFunctionZonalKernelPolynomial_totalDegree_le p k base v))
  · exact normalizedFunctionZonalKernelPolynomial_totalDegree_le p k base _

/-- The polynomial representative evaluates to the pointwise Booleanized
operator whenever both coefficientwise kernel integrals are justified. -/
theorem eval_booleanFilteredFunctionPolynomial {n : ℕ}
    (p k : ℕ) (base : sphereSet n) (v : sphereSet n → ℝ)
    (hv : ZonalKernelCoeffIntegrable p k v)
    (hKv : ZonalKernelCoeffIntegrable p k (fun y ↦
      MvPolynomial.eval y.1 (normalizedFunctionZonalKernelPolynomial p k base v)))
    (x : Fin n → ℝ) :
    MvPolynomial.eval x (booleanFilteredFunctionPolynomial p k base v) =
      booleanFilteredFunctionValue p k base v x := by
  unfold booleanFilteredFunctionPolynomial booleanFilteredFunctionValue
  rw [map_sub, map_add,
    eval_normalizedFunctionZonalKernelPolynomial p k base v hv x]
  rw [eval_normalizedFunctionZonalKernelPolynomial p k base _ hKv x]
  congr 1
  apply congrArg (fun w ↦ normalizedFunctionZonalKernelValue p k base w x)
  funext y
  exact eval_normalizedFunctionZonalKernelPolynomial p k base v hv y.1

end QuarticConvergence
end OptimalConvergenceRates

end
