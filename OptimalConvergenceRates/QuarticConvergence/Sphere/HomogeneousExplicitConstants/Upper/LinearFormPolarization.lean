import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.PolynomialMoments

/-! Linear forms and polarization reuse the existing sphere moment library. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace LinearFormPolarization
open MvPolynomial
open scoped BigOperators

abbrev linearFormPolynomial {n : ℕ} (z : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  QuarticConvergence.sphereDotPolynomial z

@[simp] theorem linearFormPolynomial_eval {n : ℕ} (z x : Fin n → ℝ) :
    eval x (linearFormPolynomial z) = ∑ i, z i * x i := by
  simp [linearFormPolynomial, QuarticConvergence.sphereDotPolynomial]

theorem exists_fin_sum_linearForm_pow_eq_of_isHomogeneous
    {n d : ℕ} (v : MvPolynomial (Fin n) ℝ) (hv : v.IsHomogeneous d) :
    ∃ (N : ℕ) (c : Fin N → ℝ) (z : Fin N → Fin n → ℝ),
      v = ∑ j, C (c j) * linearFormPolynomial (z j) ^ d :=
  QuarticConvergence.exists_fin_sum_linearForm_pow_eq_of_isHomogeneous v hv

end LinearFormPolarization
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
