/-
  Unconditional general quartic convergence for the canonical box quadratic
  module (Putinar hierarchy).
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarWeightedParity
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarConcreteEndpoint

open MvPolynomial Finset Set

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- The controlled-root weighted parity hypothesis required by the abstract
assembly is a theorem in every positive cube dimension. -/
theorem uniformControlledWeightedParityBound
    {n : ℕ} (hn : 0 < n) :
    HasUniformControlledWeightedParityBound n := by
  apply hasUniformControlledWeightedParityBound_of_mul_controlledConstant
    (controlledWeightedParityDimensionConstant_nonneg n)
  intro C k h data
  exact data.controlledWeightedParityBound hn

/-- Every nonnegative polynomial on the cube has a canonical Putinar
certificate with error `O((max d 1)^6 * polySupNorm h / r^4)`.

The constants depend only on the fixed dimension, and `r` is the total
degree of each complete quadratic-module certificate term. -/
theorem putinarExplicitRate_certificate {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (h : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        h.totalDegree ≤ d → IsNonnegOn h (Hypercube n) →
          c * max d 1 ≤ r →
          h + MvPolynomial.C
              (A * ((max d 1 : ℕ) : ℝ) ^ 6 * polySupNorm h /
                (r : ℝ) ^ 4) ∈
            BoxQuadraticModule n r :=
  putinarExplicitRate_certificate_of_controlledRoots hn
    (uniformControlledWeightedParityBound hn)

/-- For every polynomial, the canonical Putinar/Lasserre lower bound is
finite at sufficiently large total-degree order and has the general cube
`O((max d 1)^6 * oscillation / r^4)` gap. -/
theorem putinarExplicitRate_lasserreGap {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        p.totalDegree ≤ d → c * max d 1 ≤ r →
          ∃ ℓ : ℝ,
            lasserre_bound_box_qm p r = (ℓ : WithBot ℝ) ∧
              0 ≤ polyMin p - ℓ ∧
              polyMin p - ℓ ≤
                A * ((max d 1 : ℕ) : ℝ) ^ 6 *
                  (polyMax p - polyMin p) / (r : ℝ) ^ 4 :=
  putinarExplicitRate_lasserreGap_of_controlledRoots hn
    (uniformControlledWeightedParityBound hn)

end QuarticConvergence
end OptimalConvergenceRates

end
