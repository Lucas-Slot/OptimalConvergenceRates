/-
  Finite rotation equivariance of the normalized zonal and Boolean filters.

  A rotation is represented as a product of two axial reflections.  This
  derives the required covariance from the repository's existing reflection
  theorem, without a new change-of-variables or differentiation-under-the-
  integral argument.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FiniteAtomFilter
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FilterRotationGeometry

open MvPolynomial Finset Set

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

/-- The sphere rotation obtained by reflecting first through `b`, then
through `a`. -/
def sphereTwoReflectionRotation {n : ℕ}
    (a b : sphereSet n) (z : sphereSet n) : sphereSet n :=
  sphereAxialReflection a (sphereAxialReflection b z)

@[simp] theorem sphereTwoReflectionRotation_coe {n : ℕ}
    (a b z : sphereSet n) :
    (sphereTwoReflectionRotation a b z).1 =
      sphereForwardRotationCLM a b z.1 := by
  simp [sphereTwoReflectionRotation, sphereForwardRotationCLM,
    sphereAxialReflectionCoordinateCLM_apply]

/-- The normalized zonal operator is equivariant under every rotation written
as a product of two axial reflections. -/
theorem normalizedFunctionZonalKernelValue_sphereTwoReflectionRotation
    {n : ℕ} (p k : ℕ) (base : sphereSet n)
    (v : sphereSet n → ℝ) (a b z : sphereSet n) :
    normalizedFunctionZonalKernelValue p k base v
        (sphereTwoReflectionRotation a b z).1 =
      normalizedFunctionZonalKernelValue p k base
        (fun y ↦ v (sphereTwoReflectionRotation a b y)) z.1 := by
  unfold sphereTwoReflectionRotation
  rw [normalizedFunctionZonalKernelValue_sphereAxialReflection
    p k base v a (sphereAxialReflection b z)]
  rw [normalizedFunctionZonalKernelValue_sphereAxialReflection
    p k base (fun y ↦ v (sphereAxialReflection a y)) b z]

/-- The Boolean filter `2K-K²` inherits the same finite rotation
equivariance. -/
theorem booleanFilteredFunctionValue_sphereTwoReflectionRotation
    {n : ℕ} (p k : ℕ) (base : sphereSet n)
    (v : sphereSet n → ℝ) (a b z : sphereSet n) :
    booleanFilteredFunctionValue p k base v
        (sphereTwoReflectionRotation a b z).1 =
      booleanFilteredFunctionValue p k base
        (fun y ↦ v (sphereTwoReflectionRotation a b y)) z.1 := by
  unfold booleanFilteredFunctionValue
  rw [normalizedFunctionZonalKernelValue_sphereTwoReflectionRotation
    p k base v a b z]
  rw [normalizedFunctionZonalKernelValue_sphereTwoReflectionRotation
    p k base
      (fun y ↦ normalizedFunctionZonalKernelValue p k base v y.1) a b z]
  have hfun :
      (fun y ↦ normalizedFunctionZonalKernelValue p k base v
        (sphereTwoReflectionRotation a b y).1) =
      (fun y ↦ normalizedFunctionZonalKernelValue p k base
        (fun z ↦ v (sphereTwoReflectionRotation a b z)) y.1) := by
    funext y
    exact normalizedFunctionZonalKernelValue_sphereTwoReflectionRotation
      p k base v a b y
  rw [hfun]

end QuarticConvergence
end OptimalConvergenceRates

end
