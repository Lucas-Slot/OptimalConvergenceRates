/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/ChoiLam/MainProof.lean

  Schmuedgen lower degree bound for the perturbed Choi-Lam quartic on the box.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.WeightedJet
import OptimalConvergenceRates.ExamplePolynomials.ChoiLam

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

/-!
## Target theorem

For sufficiently small positive `epsilon`, every Schmuedgen/preordering
certificate of `choiLamQuartic + epsilon` on `[-1,1]^4` has degree at least a
constant multiple of `epsilon^(-1/4)`.
-/

/-- Schmuedgen lower degree bound for the Choi-Lam interior obstruction with the
revised quarter-exponent analytic input. -/
theorem schmuedgen_interior_lower_degree_bound_quarter
    (epsilon : ℝ) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0) (r : ℕ)
    (hmem : choiLamPerturbed epsilon ∈ BoxPreordering 4 r) :
    schmInteriorLowerBoundConst4 * epsilon ^ (-(1 : ℝ) / 4) ≤ (r : ℝ) := by
  by_contra hcontra
  push_neg at hcontra
  rw [choiLamPerturbed_eq] at hmem
  exact degree_four_comparison_error_bound_quarter heps heps0 (le_of_lt hcontra) hmem

/-- Contrapositive form of the quarter-exponent lower bound. -/
theorem schmuedgen_interior_lower_degree_bound_quarter_contra
    (epsilon : ℝ) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0) (r : ℕ)
    (hr : (r : ℝ) < schmInteriorLowerBoundConst4 * epsilon ^ (-(1 : ℝ) / 4)) :
    choiLamPerturbed epsilon ∉ BoxPreordering 4 r := by
  intro hmem
  have hle := schmuedgen_interior_lower_degree_bound_quarter epsilon heps heps0 r hmem
  linarith

end OptimalConvergenceRates

end
