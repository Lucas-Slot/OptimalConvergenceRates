import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.MainResultsProofs

/-! Public Motzkin box-certificate results. -/

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates.Motzkin

/-- Public explicit upper bound in the box quadratic module. The level `6*m+2`
bounds the weighted terms in the repository truncation convention. -/
theorem upperBoundMembershipBoxQMMotzkin_sixth_of_m
    (epsilon : ℝ) (heps : 0 < epsilon)
    (m : ℕ) (hm : 2 ≤ m)
    (hm_eps : (8 / epsilon) ^ ((1 : ℝ) / 6) ≤ (m : ℝ)) :
    motzkinPerturbed epsilon ∈ BoxQuadraticModule 3 (6 * m + 2) :=
  MainResultsProofs.upperBoundMembershipBoxQMMotzkin_sixth_of_m epsilon heps m hm hm_eps

/-- Public explicit upper bound in the ternary box preordering. -/
theorem upperBoundMembershipBoxPreoMotzkin_sixth_of_m
    (epsilon : ℝ) (heps : 0 < epsilon)
    (m : ℕ) (hm : 2 ≤ m)
    (hm_eps : (8 / epsilon) ^ ((1 : ℝ) / 6) ≤ (m : ℝ)) :
    motzkinPerturbed epsilon ∈ BoxPreordering 3 (6 * m + 2) :=
  MainResultsProofs.upperBoundMembershipBoxPreoMotzkin_sixth_of_m epsilon heps m hm hm_eps

/-- Public matching upper bound: Motzkin perturbations admit preordering
certificates of weighted degree `O(epsilon^(-1/6))`. -/
theorem upperBoundMembershipBoxPreoMotzkin_sixth
    (epsilon : ℝ) (heps : 0 < epsilon) (heps8 : epsilon ≤ 8) :
    ∃ r : ℕ,
      (r : ℝ) ≤ 28 * epsilon ^ (-(1 : ℝ) / 6) ∧
        motzkinPerturbed epsilon ∈ BoxPreordering 3 r :=
  MainResultsProofs.upperBoundMembershipBoxPreoMotzkin_sixth epsilon heps heps8

end OptimalConvergenceRates.Motzkin

end
