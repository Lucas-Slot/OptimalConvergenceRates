/-
  OptimalConvergenceRates/LowerDegreeBoundsPutinar/GloballyNonnegativeModule.lean

  Globally nonnegative multiplier relaxation of the box quadratic module.
-/
import OptimalConvergenceRates.LowerDegreeBoundsPutinar.Defs

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

variable {n : ℕ}

/-- Membership in the truncated quadratic-module relaxation with globally
nonnegative multipliers. -/
def BoxNonnegQuadraticModule (n : ℕ) (r : ℕ) : Set (MvPolynomial (Fin n) ℝ) :=
  { p | ∃ (σ₀ : MvPolynomial (Fin n) ℝ) (σ : Fin n → MvPolynomial (Fin n) ℝ),
    IsNonnegOn σ₀ Set.univ ∧
    (∀ i, IsNonnegOn (σ i) Set.univ) ∧
    σ₀.totalDegree ≤ r ∧
    (∀ i, (σ i * BoxSemialgebraicGenerator i).totalDegree ≤ r) ∧
    p = σ₀ + ∑ i : Fin n, σ i * BoxSemialgebraicGenerator i }

/-- Every SOS quadratic-module certificate is also a globally nonnegative
multiplier certificate. The converse is false in general. -/
theorem BoxQuadraticModule_subset_BoxNonnegQuadraticModule (n r : ℕ) :
    BoxQuadraticModule n r ⊆ BoxNonnegQuadraticModule n r := by
  intro p hp
  rcases hp with ⟨σ₀, σ, hsos₀, hsos, hdeg₀, hdeg, hsum⟩
  exact ⟨σ₀, σ, IsSOS_nonneg σ₀ hsos₀, fun i => IsSOS_nonneg (σ i) (hsos i),
    hdeg₀, hdeg, hsum⟩

end OptimalConvergenceRates

end
