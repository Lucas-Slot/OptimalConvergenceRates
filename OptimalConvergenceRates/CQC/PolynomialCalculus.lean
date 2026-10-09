import Mathlib.Analysis.Calculus.MeanValue
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.Radial

/-!
# Differential calculus for multivariate polynomial evaluation

This file promotes the coordinate derivative already used by the sphere
development to the strict derivative needed by the CQC regularity argument.
-/

noncomputable section

open MvPolynomial
open scoped Topology

namespace OptimalConvergenceRates

/-- The polynomial evaluation differential depends continuously on the base
point. -/
theorem continuous_mvPolynomialEvalFDeriv {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) :
    Continuous (QuarticConvergence.mvPolynomialEvalFDeriv P) := by
  unfold QuarticConvergence.mvPolynomialEvalFDeriv
  apply continuous_finset_sum
  intro i _
  exact (continuous_eval (MvPolynomial.pderiv i P)).smul continuous_const

/-- Multivariate polynomial evaluation is strictly Fréchet differentiable,
with the coordinate-gradient differential used elsewhere in the repository. -/
theorem hasStrictFDerivAt_mvPolynomial_eval {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    HasStrictFDerivAt (fun y : Fin n → ℝ ↦ MvPolynomial.eval y P)
      (QuarticConvergence.mvPolynomialEvalFDeriv P x) x := by
  apply hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
  · exact Filter.Eventually.of_forall fun y ↦
      QuarticConvergence.hasFDerivAt_mvPolynomial_eval P y
  · exact (continuous_mvPolynomialEvalFDeriv P).continuousAt

/-- A finite family of polynomial evaluations is strictly differentiable as
a map between coordinate Euclidean spaces. -/
theorem hasStrictFDerivAt_mvPolynomial_evalFamily {n m : ℕ}
    (P : Fin m → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    HasStrictFDerivAt
      (fun y : Fin n → ℝ ↦ fun i ↦ MvPolynomial.eval y (P i))
      (ContinuousLinearMap.pi fun i ↦
        QuarticConvergence.mvPolynomialEvalFDeriv (P i) x) x := by
  rw [hasStrictFDerivAt_pi]
  exact fun i ↦ hasStrictFDerivAt_mvPolynomial_eval (P i) x

end OptimalConvergenceRates

end
