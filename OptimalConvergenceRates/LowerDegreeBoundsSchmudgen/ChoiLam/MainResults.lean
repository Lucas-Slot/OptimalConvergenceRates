import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.MainResultsProofs

/-! Readable Choi--Lam box-preordering conclusions. -/

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates.ChoiLam

/-- Choi--Lam perturbations require preordering degree
`Omega(epsilon^(-1/4))`. -/
theorem lowerBoundMembershipBoxPreo_quarter
    (epsilon : ℝ) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0) (r : ℕ)
    (hmem : choiLamPerturbed epsilon ∈ BoxPreordering 4 r) :
    schmInteriorLowerBoundConst4 * epsilon ^ (-(1 : ℝ) / 4) ≤ (r : ℝ) :=
  MainResultsProofs.lowerBoundMembershipBoxPreo_quarter epsilon heps heps0 r hmem

/-- Contrapositive form of the Choi--Lam preordering lower bound. -/
theorem lowerBoundMembershipBoxPreo_quarter_contra
    (epsilon : ℝ) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0) (r : ℕ)
    (hr : (r : ℝ) < schmInteriorLowerBoundConst4 * epsilon ^ (-(1 : ℝ) / 4)) :
    choiLamPerturbed epsilon ∉ BoxPreordering 4 r :=
  MainResultsProofs.lowerBoundMembershipBoxPreo_quarter_contra epsilon heps heps0 r hr

/-- Explicit Choi--Lam preordering certificate with degree proportional to `m`. -/
theorem upperBoundMembershipBoxPreo_quarter_of_m
    (epsilon : ℝ) (heps : 0 < epsilon) (heps4 : epsilon ≤ 4)
    (m : ℕ) (hm : 2 ≤ m)
    (hm_eps : (4 / epsilon) ^ ((1 : ℝ) / 4) ≤ (m : ℝ)) :
    choiLamPerturbed epsilon ∈ BoxPreordering 4 (4 * (m + 1)) :=
  MainResultsProofs.upperBoundMembershipBoxPreo_quarter_of_m
    epsilon heps heps4 m hm hm_eps

/-- Choi--Lam perturbations admit preordering certificates of degree
`O(epsilon^(-1/4))`, matching the lower exponent. -/
theorem upperBoundMembershipBoxPreo_quarter
    (epsilon : ℝ) (heps : 0 < epsilon) (heps4 : epsilon ≤ 4) :
    ∃ r : ℕ,
      (r : ℝ) ≤ 24 * epsilon ^ (-(1 : ℝ) / 4) ∧
        choiLamPerturbed epsilon ∈ BoxPreordering 4 r :=
  MainResultsProofs.upperBoundMembershipBoxPreo_quarter epsilon heps heps4

end OptimalConvergenceRates.ChoiLam

end
