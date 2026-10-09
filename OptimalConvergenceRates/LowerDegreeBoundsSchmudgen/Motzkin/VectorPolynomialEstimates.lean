/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/Motzkin/VectorPolynomialEstimates.lean

  Motzkin specializations of the shared vector-polynomial estimates.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.Defs
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Common.PolynomialTail
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Common.VectorPolynomialEstimates

open Finset

noncomputable section

namespace OptimalConvergenceRates

namespace Motzkin

/-- Uniform vector-valued Bernstein estimate at the center of the fixed Motzkin
interior interval. -/
theorem interior_bernstein_vector_first_derivative_schm
    {N k : ℕ} {M : ℝ} (P : Fin N → Polynomial ℝ)
    (hM : 0 ≤ M) (hdeg : ∀ i, (P i).natDegree ≤ k)
    (hbound : ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm (fun i : Fin N ↦ (P i).eval t) ≤ M) :
    interiorVecNorm (fun i : Fin N ↦ (Polynomial.derivative (P i)).eval 0) ≤
      8 * (k : ℝ) * M := by
  have h :=
    OptimalConvergenceRates.interior_bernstein_vector_first_derivative_radius
      P schmInteriorS_pos hM hdeg hbound
  norm_num [schmInteriorS] at h ⊢
  nlinarith

end Motzkin

end OptimalConvergenceRates

end
