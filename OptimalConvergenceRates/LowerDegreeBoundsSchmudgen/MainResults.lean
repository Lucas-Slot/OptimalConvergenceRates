import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.MainResultsProofs

/-! Public Choi--Lam and Motzkin degree bounds for box-preordering certificates. -/

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

/-- Choi--Lam perturbations require preordering degree at least
`Omega(epsilon^(-1/4))`. -/
theorem lowerBoundMembershipBoxPreoChoiLam_quarter
    (epsilon : ℝ) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0) (r : ℕ)
    (hmem : choiLamPerturbed epsilon ∈ BoxPreordering 4 r) :
    schmInteriorLowerBoundConst4 * epsilon ^ (-(1 : ℝ) / 4) ≤ (r : ℝ) :=
  LowerDegreeBoundsSchmudgen.MainResultsProofs.lowerBoundMembershipBoxPreoChoiLam_quarter
    epsilon heps heps0 r hmem

/-- Contrapositive form of `lowerBoundMembershipBoxPreoChoiLam_quarter`. -/
theorem lowerBoundMembershipBoxPreoChoiLam_quarter_contra
    (epsilon : ℝ) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0) (r : ℕ)
    (hr : (r : ℝ) < schmInteriorLowerBoundConst4 * epsilon ^ (-(1 : ℝ) / 4)) :
    choiLamPerturbed epsilon ∉ BoxPreordering 4 r :=
  LowerDegreeBoundsSchmudgen.MainResultsProofs.lowerBoundMembershipBoxPreoChoiLam_quarter_contra
    epsilon heps heps0 r hr

/-- Choi--Lam perturbations admit explicit preordering certificates of degree
`O(epsilon^(-1/4))`. -/
theorem upperBoundMembershipBoxPreoChoiLam_quarter_of_m
    (epsilon : ℝ) (heps : 0 < epsilon) (heps4 : epsilon ≤ 4)
    (m : ℕ) (hm : 2 ≤ m)
    (hm_eps : (4 / epsilon) ^ ((1 : ℝ) / 4) ≤ (m : ℝ)) :
    choiLamPerturbed epsilon ∈ BoxPreordering 4 (4 * (m + 1)) :=
  LowerDegreeBoundsSchmudgen.MainResultsProofs.upperBoundMembershipBoxPreoChoiLam_quarter_of_m
    epsilon heps heps4 m hm hm_eps

/-- Existential form of the explicit tight Choi--Lam upper certificate. -/
theorem upperBoundMembershipBoxPreoChoiLam_quarter
    (epsilon : ℝ) (heps : 0 < epsilon) (heps4 : epsilon ≤ 4) :
    ∃ r : ℕ,
      (r : ℝ) ≤ 24 * epsilon ^ (-(1 : ℝ) / 4) ∧
        choiLamPerturbed epsilon ∈ BoxPreordering 4 r :=
  LowerDegreeBoundsSchmudgen.MainResultsProofs.upperBoundMembershipBoxPreoChoiLam_quarter
    epsilon heps heps4

/-- Motzkin perturbations require preordering degree at least
`Omega(epsilon^(-1/6))`. -/
theorem lowerBoundMembershipBoxPreoMotzkin_sixth
    (epsilon : ℝ) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ Motzkin.motzkinEpsilon0) (r : ℕ)
    (hmem : Motzkin.motzkinPerturbed epsilon ∈ BoxPreordering 3 r) :
    Motzkin.motzkinLowerBoundConst * epsilon ^ (-(1 : ℝ) / 6) ≤ (r : ℝ) :=
  LowerDegreeBoundsSchmudgen.MainResultsProofs.lowerBoundMembershipBoxPreoMotzkin_sixth
    epsilon heps heps0 r hmem

/-- Contrapositive form of `lowerBoundMembershipBoxPreoMotzkin_sixth`. -/
theorem lowerBoundMembershipBoxPreoMotzkin_sixth_contra
    (epsilon : ℝ) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ Motzkin.motzkinEpsilon0) (r : ℕ)
    (hr : (r : ℝ) <
      Motzkin.motzkinLowerBoundConst * epsilon ^ (-(1 : ℝ) / 6)) :
    Motzkin.motzkinPerturbed epsilon ∉ BoxPreordering 3 r :=
  LowerDegreeBoundsSchmudgen.MainResultsProofs.lowerBoundMembershipBoxPreoMotzkin_sixth_contra
    epsilon heps heps0 r hr

/-- Explicit upper bound for Motzkin perturbations in the box quadratic module. -/
theorem upperBoundMembershipBoxQMMotzkin_sixth_of_m
    (epsilon : ℝ) (heps : 0 < epsilon)
    (m : ℕ) (hm : 2 ≤ m)
    (hm_eps : (8 / epsilon) ^ ((1 : ℝ) / 6) ≤ (m : ℝ)) :
    Motzkin.motzkinPerturbed epsilon ∈ BoxQuadraticModule 3 (6 * m + 2) :=
  LowerDegreeBoundsSchmudgen.MainResultsProofs.upperBoundMembershipBoxQMMotzkin_sixth_of_m
    epsilon heps m hm hm_eps

/-- Explicit upper bound for Motzkin perturbations in the box preordering. -/
theorem upperBoundMembershipBoxPreoMotzkin_sixth_of_m
    (epsilon : ℝ) (heps : 0 < epsilon)
    (m : ℕ) (hm : 2 ≤ m)
    (hm_eps : (8 / epsilon) ^ ((1 : ℝ) / 6) ≤ (m : ℝ)) :
    Motzkin.motzkinPerturbed epsilon ∈ BoxPreordering 3 (6 * m + 2) :=
  LowerDegreeBoundsSchmudgen.MainResultsProofs.upperBoundMembershipBoxPreoMotzkin_sixth_of_m
    epsilon heps m hm hm_eps

/-- Motzkin perturbations admit preordering certificates of weighted degree
`O(epsilon^(-1/6))`. -/
theorem upperBoundMembershipBoxPreoMotzkin_sixth
    (epsilon : ℝ) (heps : 0 < epsilon) (heps8 : epsilon ≤ 8) :
    ∃ r : ℕ,
      (r : ℝ) ≤ 28 * epsilon ^ (-(1 : ℝ) / 6) ∧
        Motzkin.motzkinPerturbed epsilon ∈ BoxPreordering 3 r :=
  LowerDegreeBoundsSchmudgen.MainResultsProofs.upperBoundMembershipBoxPreoMotzkin_sixth
    epsilon heps heps8

end OptimalConvergenceRates

end
