/-
  The unconditional weighted multiplier estimate for the controlled roots.

  Exact filter/rotation commutation supplies the two-rotation square seed.
  Walsh projection preserves that seed without a root-count loss, and the
  shifted angular argument plus vector Bernstein propagation supplies every
  higher weighted parity multiplier required by the Putinar conversion.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.FilteredRootHessianCommutation
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarWeightedParityEstimate

open MvPolynomial Finset Set

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- Every controlled root package satisfies the complete weighted parity
estimate with a constant depending only on the cube dimension and the
package's controlled atom constant `C`. -/
theorem FiniteControlledRootData.controlledWeightedParityBound
    {n : ℕ} (hn : 0 < n) {C : ℝ} {k : ℕ}
    {h : MvPolynomial (Fin n) ℝ}
    (data : FiniteControlledRootData
      (2 * n + 1) C k (cubeSphereLift n h)) :
    data.HasWeightedParityBound
      (controlledWeightedParityDimensionConstant n * C) := by
  apply data.hasWeightedParityBound_of_paritySeed
  intro I a b
  apply uniformAngularSqBound_parityTerm_twoRotation_of_raw
    data.productCirclePolynomial I a b
  intro theta
  exact data.sum_eval_two_circleRotationDeriv_angle_sq_le hn b a theta

end QuarticConvergence
end OptimalConvergenceRates

end
