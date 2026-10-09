import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.MainProof
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.ChoiLamTight

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates.ChoiLam.MainResultsProofs

theorem lowerBoundMembershipBoxPreo_quarter
    (epsilon : ℝ) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0) (r : ℕ)
    (hmem : choiLamPerturbed epsilon ∈ BoxPreordering 4 r) :
    schmInteriorLowerBoundConst4 * epsilon ^ (-(1 : ℝ) / 4) ≤ (r : ℝ) :=
  schmuedgen_interior_lower_degree_bound_quarter epsilon heps heps0 r hmem

theorem lowerBoundMembershipBoxPreo_quarter_contra
    (epsilon : ℝ) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0) (r : ℕ)
    (hr : (r : ℝ) < schmInteriorLowerBoundConst4 * epsilon ^ (-(1 : ℝ) / 4)) :
    choiLamPerturbed epsilon ∉ BoxPreordering 4 r :=
  schmuedgen_interior_lower_degree_bound_quarter_contra epsilon heps heps0 r hr

theorem upperBoundMembershipBoxPreo_quarter_of_m
    (epsilon : ℝ) (heps : 0 < epsilon) (heps4 : epsilon ≤ 4)
    (m : ℕ) (hm : 2 ≤ m)
    (hm_eps : (4 / epsilon) ^ ((1 : ℝ) / 4) ≤ (m : ℝ)) :
    choiLamPerturbed epsilon ∈ BoxPreordering 4 (4 * (m + 1)) :=
  choiLamPerturbed_mem_BoxPreordering_tight_of_m epsilon heps heps4 m hm hm_eps

theorem upperBoundMembershipBoxPreo_quarter
    (epsilon : ℝ) (heps : 0 < epsilon) (heps4 : epsilon ≤ 4) :
    ∃ r : ℕ,
      (r : ℝ) ≤ 24 * epsilon ^ (-(1 : ℝ) / 4) ∧
        choiLamPerturbed epsilon ∈ BoxPreordering 4 r :=
  choiLamPerturbed_mem_BoxPreordering_tight epsilon heps heps4

end OptimalConvergenceRates.ChoiLam.MainResultsProofs

end
