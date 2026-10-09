import
  OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.SphereBallTransfers.MainResultsProofs

/-! Public hypersphere upper- and lower-bound statements for the perturbed Choi--Lam form. -/

open MvPolynomial Finset
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates.SphereBallTransfers

/-- Choi--Lam hypersphere upper bound from the explicit box certificate. -/
theorem sphereChoiLamPerturbed_upperBound_rootDegree_of_m
    (epsilon : ℝ) (heps : 0 < epsilon) (heps4 : epsilon ≤ 4)
    (m : ℕ) (hm : 2 ≤ m)
    (hm_eps : (4 / epsilon) ^ ((1 : ℝ) / 4) ≤ (m : ℝ)) :
    ChoiLamHasSphereCert (4 * (m + 1) + 4) epsilon :=
  MainResultsProofs.sphereChoiLamPerturbed_upperBound_rootDegree_of_m
    epsilon heps heps4 m hm hm_eps

/-- Choi--Lam hypersphere upper bound in root-degree form. -/
theorem sphereChoiLamPerturbed_upperBound_rootDegree
    (epsilon : ℝ) (heps : 0 < epsilon) (heps4 : epsilon ≤ 4) :
    ∃ k : ℕ,
      (k : ℝ) ≤ 32 * epsilon ^ (-(1 : ℝ) / 4) ∧
        ChoiLamHasSphereCert k epsilon :=
  MainResultsProofs.sphereChoiLamPerturbed_upperBound_rootDegree epsilon heps heps4

/-- Existing box lower bound in the total-degree convention. -/
theorem boxCert_lowerBound_totalDegree
    (delta : ℝ) (hdelta : 0 < delta) (hdelta0 : delta ≤ schmInteriorEpsilon0) (k : ℕ)
    (hcert : BoxCert k delta) :
    schmInteriorLowerBoundConst4 * delta ^ (-(1 : ℝ) / 4) ≤ (2 * k : ℕ) :=
  MainResultsProofs.boxCert_lowerBound_totalDegree delta hdelta hdelta0 k hcert

/-- Existing box lower bound in the root-degree convention used by `Tbox`. -/
theorem boxCert_lowerBound_rootDegree
    (delta : ℝ) (hdelta : 0 < delta) (hdelta0 : delta ≤ schmInteriorEpsilon0) (k : ℕ)
    (hcert : BoxCert k delta) :
    (schmInteriorLowerBoundConst4 / 2) * delta ^ (-(1 : ℝ) / 4) ≤ (k : ℝ) :=
  MainResultsProofs.boxCert_lowerBound_rootDegree delta hdelta hdelta0 k hcert

/-- Matching root-degree bounds for Choi--Lam certificates in the quadratic
module of the four-dimensional unit ball. -/
theorem ballChoiLamPerturbed_matching_rootDegree
    (epsilon : ℝ) (heps : 0 < epsilon) (heps4 : epsilon ≤ 4)
    (heps0 : epsilon ≤ schmInteriorEpsilon0 / 16) :
    (∃ k : ℕ,
      (k : ℝ) ≤ 32 * epsilon ^ (-(1 : ℝ) / 4) ∧
        Nonempty (BallCertificate k epsilon)) ∧
      ∀ k : ℕ, 2 ≤ k → Nonempty (BallCertificate k epsilon) →
        (schmInteriorLowerBoundConst4 / 2) * (16 * epsilon) ^ (-(1 : ℝ) / 4) ≤
          (k : ℝ) :=
  MainResultsProofs.ballChoiLamPerturbed_matching_rootDegree epsilon heps heps4 heps0

/-- Transfer of the Choi--Lam Schmüdgen lower bound to the sphere-to-box convention. -/
theorem sphere_lowerBound_from_existing_box
    (htransfer : SphereToBoxTransfer) {k : ℕ} {epsilon : ℝ}
    (hk : 2 ≤ k) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0 / 16) (hcert : ChoiLamHasSphereCert k epsilon) :
    (schmInteriorLowerBoundConst4 / 2) * (16 * epsilon) ^ (-(1 : ℝ) / 4) ≤
      (k : ℝ) :=
  MainResultsProofs.sphere_lowerBound_from_existing_box htransfer hk heps heps0 hcert

/-- Fourth-power hypersphere lower bound assuming the sphere-to-box transfer. -/
theorem hypersphere_lowerBound_fourthPower_of_sphereToBoxTransfer
    (htransfer : SphereToBoxTransfer) {beta delta0 : ℝ} (hbox : BoxLB4 beta delta0)
    {k : ℕ} {epsilon : ℝ} (hk : 2 ≤ k) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ delta0 / 16) (hcert : ChoiLamHasSphereCert k epsilon) :
    beta / 16 ≤ epsilon * (k : ℝ) ^ 4 :=
  MainResultsProofs.hypersphere_lowerBound_fourthPower_of_sphereToBoxTransfer
    htransfer hbox hk heps heps0 hcert

/-- Choi--Lam hypersphere lower bound assuming the sphere-to-box transfer. -/
theorem sphereChoiLamPerturbed_lowerBound_rootDegree_of_sphereToBoxTransfer
    (htransfer : SphereToBoxTransfer) {k : ℕ} {epsilon : ℝ}
    (hk : 2 ≤ k) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0 / 16) (hcert : ChoiLamHasSphereCert k epsilon) :
    (schmInteriorLowerBoundConst4 / 2) * (16 * epsilon) ^ (-(1 : ℝ) / 4) ≤
      (k : ℝ) :=
  MainResultsProofs.sphereChoiLamPerturbed_lowerBound_rootDegree_of_sphereToBoxTransfer
    htransfer hk heps heps0 hcert

/-- Fourth-power hypersphere lower bound assuming the sphere-to-ball transfer. -/
theorem hypersphere_lowerBound_fourthPower_of_sphereToBallTransfer
    (hsb : SphereToBallTransfer) {beta delta0 : ℝ} (hbox : BoxLB4 beta delta0)
    {k : ℕ} {epsilon : ℝ} (hk : 2 ≤ k) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ delta0 / 16) (hcert : ChoiLamHasSphereCert k epsilon) :
    beta / 16 ≤ epsilon * (k : ℝ) ^ 4 :=
  MainResultsProofs.hypersphere_lowerBound_fourthPower_of_sphereToBallTransfer
    hsb hbox hk heps heps0 hcert

/-- Choi--Lam hypersphere lower bound assuming the sphere-to-ball transfer. -/
theorem sphereChoiLamPerturbed_lowerBound_rootDegree_of_sphereToBallTransfer
    (hsb : SphereToBallTransfer) {k : ℕ} {epsilon : ℝ}
    (hk : 2 ≤ k) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0 / 16) (hcert : ChoiLamHasSphereCert k epsilon) :
    (schmInteriorLowerBoundConst4 / 2) * (16 * epsilon) ^ (-(1 : ℝ) / 4) ≤
      (k : ℝ) :=
  MainResultsProofs.sphereChoiLamPerturbed_lowerBound_rootDegree_of_sphereToBallTransfer
    hsb hk heps heps0 hcert

/-- Public fourth-power hypersphere lower bound. -/
theorem hypersphere_lowerBound_fourthPower
    {beta delta0 : ℝ} (hbox : BoxLB4 beta delta0)
    {k : ℕ} {epsilon : ℝ} (hk : 2 ≤ k) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ delta0 / 16) (hcert : ChoiLamHasSphereCert k epsilon) :
    beta / 16 ≤ epsilon * (k : ℝ) ^ 4 :=
  MainResultsProofs.hypersphere_lowerBound_fourthPower hbox hk heps heps0 hcert

/-- Public Choi--Lam hypersphere lower bound in root-degree form. -/
theorem sphereChoiLamPerturbed_lowerBound_rootDegree
    {k : ℕ} {epsilon : ℝ} (hk : 2 ≤ k) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0 / 16) (hcert : ChoiLamHasSphereCert k epsilon) :
    (schmInteriorLowerBoundConst4 / 2) * (16 * epsilon) ^ (-(1 : ℝ) / 4) ≤
      (k : ℝ) :=
  MainResultsProofs.sphereChoiLamPerturbed_lowerBound_rootDegree hk heps heps0 hcert

end OptimalConvergenceRates.SphereBallTransfers

end
