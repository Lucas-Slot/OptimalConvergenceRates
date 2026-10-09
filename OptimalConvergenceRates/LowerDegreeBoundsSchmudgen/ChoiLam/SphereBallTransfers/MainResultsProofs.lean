import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.SphereBallTransfers.UpperBound

open MvPolynomial Finset
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates.SphereBallTransfers.MainResultsProofs

theorem sphereChoiLamPerturbed_upperBound_rootDegree_of_m
    (epsilon : ℝ) (heps : 0 < epsilon) (heps4 : epsilon ≤ 4)
    (m : ℕ) (hm : 2 ≤ m)
    (hm_eps : (4 / epsilon) ^ ((1 : ℝ) / 4) ≤ (m : ℝ)) :
    ChoiLamHasSphereCert (4 * (m + 1) + 4) epsilon := by
  exact sphereChoiLamPerturbed_mem_of_boxPreordering
    (upperBoundMembershipBoxPreoChoiLam_quarter_of_m epsilon heps heps4 m hm hm_eps)

theorem sphereChoiLamPerturbed_upperBound_rootDegree
    (epsilon : ℝ) (heps : 0 < epsilon) (heps4 : epsilon ≤ 4) :
    ∃ k : ℕ,
      (k : ℝ) ≤ 32 * epsilon ^ (-(1 : ℝ) / 4) ∧
        ChoiLamHasSphereCert k epsilon := by
  obtain ⟨r, hr, hbox⟩ := upperBoundMembershipBoxPreoChoiLam_quarter epsilon heps heps4
  refine ⟨r + 4, ?_, sphereChoiLamPerturbed_mem_of_boxPreordering hbox⟩
  let x : ℝ := epsilon ^ (-(1 : ℝ) / 4)
  have hx_ge_half : (1 / 2 : ℝ) ≤ x := by
    have hconst : (4 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 := by
      have hpow4 := Real.rpow_le_rpow (by norm_num : 0 ≤ (4 : ℝ))
        (by norm_num : (4 : ℝ) ≤ 2 ^ 4) (by norm_num : 0 ≤ (1 : ℝ) / 4)
      norm_num at hpow4
      exact hpow4
    have hroot_le : epsilon ^ ((1 : ℝ) / 4) ≤ 2 := by
      have hpow := Real.rpow_le_rpow (le_of_lt heps) heps4
        (by norm_num : 0 ≤ (1 : ℝ) / 4)
      exact le_trans hpow hconst
    have hroot_pos : 0 < epsilon ^ ((1 : ℝ) / 4) := by positivity
    have htmp : (1 / 2 : ℝ) ≤ 1 / epsilon ^ ((1 : ℝ) / 4) :=
      one_div_le_one_div_of_le hroot_pos hroot_le
    dsimp [x]
    rw [show (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) by ring,
      Real.rpow_neg (le_of_lt heps)]
    simpa [one_div] using htmp
  have hrx : (r : ℝ) ≤ 24 * x := by simpa [x] using hr
  have hfour : (4 : ℝ) ≤ 8 * x := by nlinarith
  calc
    ((r + 4 : ℕ) : ℝ) = (r : ℝ) + 4 := by norm_num
    _ ≤ 24 * x + 4 := by linarith
    _ ≤ 32 * x := by nlinarith
    _ = 32 * epsilon ^ (-(1 : ℝ) / 4) := by rfl

theorem boxCert_lowerBound_totalDegree
    (delta : ℝ) (hdelta : 0 < delta) (hdelta0 : delta ≤ schmInteriorEpsilon0) (k : ℕ)
    (hcert : BoxCert k delta) :
    schmInteriorLowerBoundConst4 * delta ^ (-(1 : ℝ) / 4) ≤ (2 * k : ℕ) := by
  exact lowerBoundMembershipBoxPreoChoiLam_quarter delta hdelta hdelta0 (2 * k)
    (by simpa [BoxCert, Tbox] using hcert)

theorem boxCert_lowerBound_rootDegree
    (delta : ℝ) (hdelta : 0 < delta) (hdelta0 : delta ≤ schmInteriorEpsilon0) (k : ℕ)
    (hcert : BoxCert k delta) :
    (schmInteriorLowerBoundConst4 / 2) * delta ^ (-(1 : ℝ) / 4) ≤ (k : ℝ) := by
  have h := boxCert_lowerBound_totalDegree delta hdelta hdelta0 k hcert
  norm_num at h ⊢
  linarith

theorem ballChoiLamPerturbed_matching_rootDegree
    (epsilon : ℝ) (heps : 0 < epsilon) (heps4 : epsilon ≤ 4)
    (heps0 : epsilon ≤ schmInteriorEpsilon0 / 16) :
    (∃ k : ℕ,
      (k : ℝ) ≤ 32 * epsilon ^ (-(1 : ℝ) / 4) ∧
        Nonempty (BallCertificate k epsilon)) ∧
      ∀ k : ℕ, 2 ≤ k → Nonempty (BallCertificate k epsilon) →
        (schmInteriorLowerBoundConst4 / 2) * (16 * epsilon) ^ (-(1 : ℝ) / 4) ≤
          (k : ℝ) := by
  constructor
  · obtain ⟨r, hr, hbox⟩ :=
      upperBoundMembershipBoxPreoChoiLam_quarter epsilon heps heps4
    have hsphere : ChoiLamHasSphereCert (r + 4) epsilon :=
      sphereChoiLamPerturbed_mem_of_boxPreordering hbox
    have hk : 2 ≤ r + 4 := by omega
    refine ⟨r + 4, ?_, sphereToBallTransfer hk hsphere⟩
    let x : ℝ := epsilon ^ (-(1 : ℝ) / 4)
    have hx_ge_half : (1 / 2 : ℝ) ≤ x := by
      have hconst : (4 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 := by
        have hpow4 := Real.rpow_le_rpow (by norm_num : 0 ≤ (4 : ℝ))
          (by norm_num : (4 : ℝ) ≤ 2 ^ 4) (by norm_num : 0 ≤ (1 : ℝ) / 4)
        norm_num at hpow4
        exact hpow4
      have hroot_le : epsilon ^ ((1 : ℝ) / 4) ≤ 2 := by
        have hpow := Real.rpow_le_rpow (le_of_lt heps) heps4
          (by norm_num : 0 ≤ (1 : ℝ) / 4)
        exact le_trans hpow hconst
      have hroot_pos : 0 < epsilon ^ ((1 : ℝ) / 4) := by positivity
      have htmp : (1 / 2 : ℝ) ≤ 1 / epsilon ^ ((1 : ℝ) / 4) :=
        one_div_le_one_div_of_le hroot_pos hroot_le
      dsimp [x]
      rw [show (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) by ring,
        Real.rpow_neg (le_of_lt heps)]
      simpa [one_div] using htmp
    have hrx : (r : ℝ) ≤ 24 * x := by simpa [x] using hr
    have hfour : (4 : ℝ) ≤ 8 * x := by nlinarith
    calc
      ((r + 4 : ℕ) : ℝ) = (r : ℝ) + 4 := by norm_num
      _ ≤ 24 * x + 4 := by linarith
      _ ≤ 32 * x := by nlinarith
      _ = 32 * epsilon ^ (-(1 : ℝ) / 4) := by rfl
  · intro k hk hball
    have hdelta_pos : 0 < 16 * epsilon := by positivity
    have hdelta_le : 16 * epsilon ≤ schmInteriorEpsilon0 := by linarith
    exact boxCert_lowerBound_rootDegree (16 * epsilon) hdelta_pos hdelta_le k
      (ballToBoxTransfer hk hball)

theorem sphere_lowerBound_from_existing_box
    (htransfer : SphereToBoxTransfer) {k : ℕ} {epsilon : ℝ}
    (hk : 2 ≤ k) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0 / 16) (hcert : ChoiLamHasSphereCert k epsilon) :
    (schmInteriorLowerBoundConst4 / 2) * (16 * epsilon) ^ (-(1 : ℝ) / 4) ≤
      (k : ℝ) := by
  have hdelta_pos : 0 < 16 * epsilon := by positivity
  have hdelta_le : 16 * epsilon ≤ schmInteriorEpsilon0 := by linarith
  exact boxCert_lowerBound_rootDegree (16 * epsilon) hdelta_pos hdelta_le k
    (htransfer hk hcert)

theorem hypersphere_lowerBound_fourthPower_of_sphereToBoxTransfer
    (htransfer : SphereToBoxTransfer) {beta delta0 : ℝ} (hbox : BoxLB4 beta delta0)
    {k : ℕ} {epsilon : ℝ} (hk : 2 ≤ k) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ delta0 / 16) (hcert : ChoiLamHasSphereCert k epsilon) :
    beta / 16 ≤ epsilon * (k : ℝ) ^ 4 :=
  sphere_lowerBound_from_BoxLB4 htransfer hbox hk heps heps0 hcert

theorem sphereChoiLamPerturbed_lowerBound_rootDegree_of_sphereToBoxTransfer
    (htransfer : SphereToBoxTransfer) {k : ℕ} {epsilon : ℝ}
    (hk : 2 ≤ k) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0 / 16) (hcert : ChoiLamHasSphereCert k epsilon) :
    (schmInteriorLowerBoundConst4 / 2) * (16 * epsilon) ^ (-(1 : ℝ) / 4) ≤
      (k : ℝ) :=
  sphere_lowerBound_from_existing_box htransfer hk heps heps0 hcert

theorem hypersphere_lowerBound_fourthPower_of_sphereToBallTransfer
    (hsb : SphereToBallTransfer) {beta delta0 : ℝ} (hbox : BoxLB4 beta delta0)
    {k : ℕ} {epsilon : ℝ} (hk : 2 ≤ k) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ delta0 / 16) (hcert : ChoiLamHasSphereCert k epsilon) :
    beta / 16 ≤ epsilon * (k : ℝ) ^ 4 :=
  hypersphere_lowerBound_fourthPower_of_sphereToBoxTransfer
    (sphereToBoxTransfer_of_sphereToBall hsb) hbox hk heps heps0 hcert

theorem sphereChoiLamPerturbed_lowerBound_rootDegree_of_sphereToBallTransfer
    (hsb : SphereToBallTransfer) {k : ℕ} {epsilon : ℝ}
    (hk : 2 ≤ k) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0 / 16) (hcert : ChoiLamHasSphereCert k epsilon) :
    (schmInteriorLowerBoundConst4 / 2) * (16 * epsilon) ^ (-(1 : ℝ) / 4) ≤
      (k : ℝ) :=
  sphereChoiLamPerturbed_lowerBound_rootDegree_of_sphereToBoxTransfer
    (sphereToBoxTransfer_of_sphereToBall hsb) hk heps heps0 hcert

theorem hypersphere_lowerBound_fourthPower
    {beta delta0 : ℝ} (hbox : BoxLB4 beta delta0)
    {k : ℕ} {epsilon : ℝ} (hk : 2 ≤ k) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ delta0 / 16) (hcert : ChoiLamHasSphereCert k epsilon) :
    beta / 16 ≤ epsilon * (k : ℝ) ^ 4 :=
  hypersphere_lowerBound_fourthPower_of_sphereToBoxTransfer sphereToBoxTransfer hbox
    hk heps heps0 hcert

theorem sphereChoiLamPerturbed_lowerBound_rootDegree
    {k : ℕ} {epsilon : ℝ} (hk : 2 ≤ k) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0 / 16) (hcert : ChoiLamHasSphereCert k epsilon) :
    (schmInteriorLowerBoundConst4 / 2) * (16 * epsilon) ^ (-(1 : ℝ) / 4) ≤
      (k : ℝ) :=
  sphereChoiLamPerturbed_lowerBound_rootDegree_of_sphereToBoxTransfer sphereToBoxTransfer
    hk heps heps0 hcert

end OptimalConvergenceRates.SphereBallTransfers.MainResultsProofs

end
