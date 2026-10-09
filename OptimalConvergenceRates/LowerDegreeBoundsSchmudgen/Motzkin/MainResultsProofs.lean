import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.MainProof
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.UpperBound

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates.Motzkin.MainResultsProofs

theorem upperBoundMembershipBoxQMMotzkin_sixth_of_m
    (epsilon : ℝ) (heps : 0 < epsilon)
    (m : ℕ) (hm : 2 ≤ m)
    (hm_eps : (8 / epsilon) ^ ((1 : ℝ) / 6) ≤ (m : ℝ)) :
    motzkinPerturbed epsilon ∈ BoxQuadraticModule 3 (6 * m + 2) :=
  motzkinPerturbed_mem_BoxQuadraticModule_tight_of_m epsilon heps m hm hm_eps

theorem upperBoundMembershipBoxPreoMotzkin_sixth_of_m
    (epsilon : ℝ) (heps : 0 < epsilon)
    (m : ℕ) (hm : 2 ≤ m)
    (hm_eps : (8 / epsilon) ^ ((1 : ℝ) / 6) ≤ (m : ℝ)) :
    motzkinPerturbed epsilon ∈ BoxPreordering 3 (6 * m + 2) :=
  motzkinPerturbed_mem_BoxPreordering_tight_of_m epsilon heps m hm hm_eps

theorem upperBoundMembershipBoxPreoMotzkin_sixth
    (epsilon : ℝ) (heps : 0 < epsilon) (heps8 : epsilon ≤ 8) :
    ∃ r : ℕ,
      (r : ℝ) ≤ 28 * epsilon ^ (-(1 : ℝ) / 6) ∧
        motzkinPerturbed epsilon ∈ BoxPreordering 3 r :=
  motzkinPerturbed_mem_BoxPreordering_tight epsilon heps heps8

end OptimalConvergenceRates.Motzkin.MainResultsProofs

end
