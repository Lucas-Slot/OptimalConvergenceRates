import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.Hierarchy

/-! The intended target is a proposition, not an asserted theorem. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Foundation

def NormalizedQuartic {n : ℕ} (p : Polynomial n) : Prop :=
  p.IsHomogeneous 4 ∧
  (∀ x : Fin n → ℝ, 0 ≤ MvPolynomial.eval x p) ∧
  IsSphereMinimum p 0 ∧ sphereSupNorm p = 1

/-- Full all-order target, with p selected before the quantifier over r.
This declaration has no proof; the project must not report it as verified. -/
def UniformQuarticLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ p : Polynomial n, NormalizedQuartic p ∧
      ∀ r : ℕ, 2 ≤ r →
        (feasibleValues r p).Nonempty ∧
        c * min (1 / (n : ℝ)) ((n : ℝ) ^ 3 / (r : ℝ) ^ 4) ≤ gap r p

end Foundation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
