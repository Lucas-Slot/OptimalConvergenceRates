import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.SphereDimensionBounds.Foundation.Hierarchy
import OptimalConvergenceRates.SphereDimensionBounds.DimensionUpperConstants

/-! Statement of the degree upper bound and the original hierarchy
passage from an actual certificate to its real-valued gap. The proposition
is proved in `DegreeUpperBound`. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.DegreeUpperTarget

open OptimalConvergenceRates.SphereDimensionBounds.Foundation DimensionUpperConstants

/-- The full oscillation-normalized certificate bound. A valid choice
is M=fmax-fmin. -/
def UniformDegreeUpperCertificateBound : Prop :=
  ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, 3 ≤ n → ∀ d : ℕ, 4 ≤ d → Even d →
    ∀ p : OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial n, p.IsHomogeneous d →
      ∀ mu M : ℝ, IsSphereMinimum p mu → 0 ≤ M →
        (∀ x ∈unitSphere n, MvPolynomial.eval x p ≤ mu+M) →
        ∀ r : ℕ, 8*n*d ≤ r →
          Feasible r p (mu-C*((d:ℝ)^4*(n:ℝ)^4*(L n)^3/(r:ℝ)^4)*M)

theorem gap_bounds_of_feasible {n r : ℕ} (p : OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial n)
    {mu eta : ℝ} (hmin : IsSphereMinimum p mu)
    (hcert : Feasible r p (mu - eta)) :
    (feasibleValues r p).Nonempty ∧ 0 ≤ gap r p ∧ gap r p ≤ eta := by
  have hne : (feasibleValues r p).Nonempty := ⟨mu-eta,hcert⟩
  have hu := sos_le_sphereMinimum hmin hne
  have hl : mu-eta ≤ sos r p :=
    le_csSup (feasibleValues_bddAbove hmin.2.choose_spec.1) hcert
  refine ⟨hne,?_,?_⟩
  · exact sub_nonneg.mpr hu
  · rw [gap,sphereMinimum_eq hmin]
    linarith

end OptimalConvergenceRates.SphereDimensionBounds.DegreeUpperTarget
