import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.MainResults
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.MainResults

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.MainResultsProofs

theorem lowerBoundMembershipBoxPreoChoiLam_quarter
    (epsilon : ℝ) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0) (r : ℕ)
    (hmem : choiLamPerturbed epsilon ∈ BoxPreordering 4 r) :
    schmInteriorLowerBoundConst4 * epsilon ^ (-(1 : ℝ) / 4) ≤ (r : ℝ) :=
  schmuedgen_interior_lower_degree_bound_quarter epsilon heps heps0 r hmem

theorem lowerBoundMembershipBoxPreoChoiLam_quarter_contra
    (epsilon : ℝ) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0) (r : ℕ)
    (hr : (r : ℝ) < schmInteriorLowerBoundConst4 * epsilon ^ (-(1 : ℝ) / 4)) :
    choiLamPerturbed epsilon ∉ BoxPreordering 4 r :=
  schmuedgen_interior_lower_degree_bound_quarter_contra epsilon heps heps0 r hr

theorem upperBoundMembershipBoxPreoChoiLam_quarter_of_m
    (epsilon : ℝ) (heps : 0 < epsilon) (heps4 : epsilon ≤ 4)
    (m : ℕ) (hm : 2 ≤ m)
    (hm_eps : (4 / epsilon) ^ ((1 : ℝ) / 4) ≤ (m : ℝ)) :
    choiLamPerturbed epsilon ∈ BoxPreordering 4 (4 * (m + 1)) :=
  choiLamPerturbed_mem_BoxPreordering_tight_of_m epsilon heps heps4 m hm hm_eps

theorem upperBoundMembershipBoxPreoChoiLam_quarter
    (epsilon : ℝ) (heps : 0 < epsilon) (heps4 : epsilon ≤ 4) :
    ∃ r : ℕ,
      (r : ℝ) ≤ 24 * epsilon ^ (-(1 : ℝ) / 4) ∧
        choiLamPerturbed epsilon ∈ BoxPreordering 4 r :=
  choiLamPerturbed_mem_BoxPreordering_tight epsilon heps heps4

theorem lowerBoundMembershipBoxPreoMotzkin_sixth
    (epsilon : ℝ) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ Motzkin.motzkinEpsilon0) (r : ℕ)
    (hmem : Motzkin.motzkinPerturbed epsilon ∈ BoxPreordering 3 r) :
    Motzkin.motzkinLowerBoundConst * epsilon ^ (-(1 : ℝ) / 6) ≤ (r : ℝ) :=
  Motzkin.schmuedgen_motzkin_lower_degree_bound_sixth epsilon heps heps0 r hmem

theorem lowerBoundMembershipBoxPreoMotzkin_sixth_contra
    (epsilon : ℝ) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ Motzkin.motzkinEpsilon0) (r : ℕ)
    (hr : (r : ℝ) <
      Motzkin.motzkinLowerBoundConst * epsilon ^ (-(1 : ℝ) / 6)) :
    Motzkin.motzkinPerturbed epsilon ∉ BoxPreordering 3 r :=
  Motzkin.schmuedgen_motzkin_lower_degree_bound_sixth_contra epsilon heps heps0 r hr

theorem upperBoundMembershipBoxQMMotzkin_sixth_of_m
    (epsilon : ℝ) (heps : 0 < epsilon)
    (m : ℕ) (hm : 2 ≤ m)
    (hm_eps : (8 / epsilon) ^ ((1 : ℝ) / 6) ≤ (m : ℝ)) :
    Motzkin.motzkinPerturbed epsilon ∈ BoxQuadraticModule 3 (6 * m + 2) :=
  Motzkin.upperBoundMembershipBoxQMMotzkin_sixth_of_m epsilon heps m hm hm_eps

theorem upperBoundMembershipBoxPreoMotzkin_sixth_of_m
    (epsilon : ℝ) (heps : 0 < epsilon)
    (m : ℕ) (hm : 2 ≤ m)
    (hm_eps : (8 / epsilon) ^ ((1 : ℝ) / 6) ≤ (m : ℝ)) :
    Motzkin.motzkinPerturbed epsilon ∈ BoxPreordering 3 (6 * m + 2) :=
  Motzkin.upperBoundMembershipBoxPreoMotzkin_sixth_of_m epsilon heps m hm hm_eps

theorem upperBoundMembershipBoxPreoMotzkin_sixth
    (epsilon : ℝ) (heps : 0 < epsilon) (heps8 : epsilon ≤ 8) :
    ∃ r : ℕ,
      (r : ℝ) ≤ 28 * epsilon ^ (-(1 : ℝ) / 6) ∧
        Motzkin.motzkinPerturbed epsilon ∈ BoxPreordering 3 r :=
  Motzkin.upperBoundMembershipBoxPreoMotzkin_sixth epsilon heps heps8

end OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.MainResultsProofs

end
