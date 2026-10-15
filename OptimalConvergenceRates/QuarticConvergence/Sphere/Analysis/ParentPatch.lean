import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.ScaleCover

open Set
open scoped BigOperators Topology
noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence

/-- The intrinsic fourth-order normalization of `u` at center `c` and scale `R`. -/
def intrinsicRescaledPatch {n : ℕ} (u : (Fin n → ℝ) → ℝ)
    (c : Fin n → ℝ) (R : ℝ) : (Fin n → ℝ) → ℝ :=
  fun z ↦ (R ^ 4)⁻¹ * u (c + R • z)

theorem intrinsicRescaledPatch_contDiff {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 6 u) (c : Fin n → ℝ) (R : ℝ) :
    ContDiff ℝ 6 (intrinsicRescaledPatch u c R) := by
  exact contDiff_const.mul (hu.comp (by fun_prop))

theorem intrinsicRescaledPatch_nonnegative {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : ∀ x, 0 ≤ u x) (c : Fin n → ℝ) {R : ℝ} (hR : 0 < R) :
    ∀ z, 0 ≤ intrinsicRescaledPatch u c R z := by
  intro z
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hR.le 4)) (hu _)

/-- Affine rescaling cancels exactly against fourth-order amplitude normalization. -/
theorem intrinsicRescaledPatch_iteratedFDeriv_le {n j : ℕ}
    {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 6 u)
    (c : Fin n → ℝ) {R : ℝ} (hR : 0 < R) (hj : j ≤ 6)
    (z : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ j (intrinsicRescaledPatch u c R) z‖ ≤
      (R ^ 4)⁻¹ * ‖iteratedFDeriv ℝ j u (c + R • z)‖ * R ^ j := by
  let shifted : (Fin n → ℝ) → ℝ := fun w ↦ u (c + w)
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    R • ContinuousLinearMap.id ℝ (Fin n → ℝ)
  have hshift : ContDiff ℝ 6 shifted := hu.comp (by fun_prop)
  have hcomp :
      iteratedFDeriv ℝ j (shifted ∘ L) z =
        (iteratedFDeriv ℝ j shifted (L z)).compContinuousLinearMap (fun _ ↦ L) :=
    L.iteratedFDeriv_comp_right hshift z (by exact_mod_cast hj)
  have htranslate : iteratedFDeriv ℝ j shifted (L z) =
      iteratedFDeriv ℝ j u (c + L z) := by
    simpa [shifted] using iteratedFDeriv_comp_add_left (𝕜 := ℝ) j c (L z)
  have hfun : intrinsicRescaledPatch u c R = (R ^ 4)⁻¹ • (shifted ∘ L) := by
    funext x
    simp only [intrinsicRescaledPatch, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [hfun]
  have hsmoothAt : ContDiffAt ℝ j (shifted ∘ L) z :=
    ((hshift.comp L.contDiff).of_le (by exact_mod_cast hj)).contDiffAt
  rw [iteratedFDeriv_const_smul_apply hsmoothAt, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hR.le 4)), hcomp, htranslate]
  have hnormL : ‖L‖ ≤ R := by
    dsimp only [L]
    calc
      ‖R • ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤
          ‖R‖ * ‖ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ := by
        exact norm_smul_le R (ContinuousLinearMap.id ℝ (Fin n → ℝ))
      _ ≤ R * 1 := by
        rw [Real.norm_of_nonneg hR.le]
        gcongr
        exact ContinuousLinearMap.norm_id_le
      _ = R := mul_one _
  have hprod : (∏ _ : Fin j, ‖L‖) ≤ R ^ j := by
    calc
      (∏ _ : Fin j, ‖L‖) ≤ ∏ _ : Fin j, R :=
        Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg L) (fun _ _ ↦ hnormL)
      _ = R ^ j := by simp
  calc
    (R ^ 4)⁻¹ * ‖(iteratedFDeriv ℝ j u (c + L z)).compContinuousLinearMap
        (fun _ ↦ L)‖ ≤
        (R ^ 4)⁻¹ * (‖iteratedFDeriv ℝ j u (c + L z)‖ * ∏ _ : Fin j, ‖L‖) := by
      gcongr
      exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ (R ^ 4)⁻¹ * (‖iteratedFDeriv ℝ j u (c + L z)‖ * R ^ j) := by gcongr
    _ = (R ^ 4)⁻¹ * ‖iteratedFDeriv ℝ j u (c + R • z)‖ * R ^ j := by
      simp only [L, smul_apply, ContinuousLinearMap.id_apply]
      ring

theorem intrinsicRescaledPatch_iteratedFDeriv_le_of_scaled {n j : ℕ}
    {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 6 u)
    (c : Fin n → ℝ) {R M : ℝ} (hR : 0 < R) (hj : j ≤ 6)
    (z : Fin n → ℝ)
    (hscaled : ‖iteratedFDeriv ℝ j u (c + R • z)‖ * R ^ j ≤ M * R ^ 4) :
    ‖iteratedFDeriv ℝ j (intrinsicRescaledPatch u c R) z‖ ≤ M := by
  calc
    ‖iteratedFDeriv ℝ j (intrinsicRescaledPatch u c R) z‖ ≤
        (R ^ 4)⁻¹ * ‖iteratedFDeriv ℝ j u (c + R • z)‖ * R ^ j :=
      intrinsicRescaledPatch_iteratedFDeriv_le hu c hR hj z
    _ = (R ^ 4)⁻¹ * (‖iteratedFDeriv ℝ j u (c + R • z)‖ * R ^ j) := by ring
    _ ≤ (R ^ 4)⁻¹ * (M * R ^ 4) :=
      mul_le_mul_of_nonneg_left hscaled (inv_nonneg.mpr (pow_nonneg hR.le 4))
    _ = M := by field_simp [hR.ne']

/-- All derivatives through order six have their natural fourth-order scale on the intrinsic
unit ball.  The constant depends only on the already-uniform nonnegative-jet constant. -/
theorem normalized_scaledJets_on_intrinsic_ball {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C)
    (c y : Fin n → ℝ)
    (hnear : dist c y ≤ nonnegativeJetScale u c) :
    ∀ j, j ≤ 6 →
      ‖iteratedFDeriv ℝ j u y‖ * nonnegativeJetScale u c ^ j ≤
        (4 * (C + 1)) * nonnegativeJetScale u c ^ 4 := by
  let R := nonnegativeJetScale u c
  let d := dist c y
  have hC0 : 0 ≤ C := hcontrol.constant_nonneg
  have hR0 : 0 ≤ R := nonnegativeJetScale_nonneg u c
  have hR1 : R ≤ 1 := by simpa [R] using nonnegativeJetScale_le_one hu c
  have hd0 : 0 ≤ d := dist_nonneg
  have hdR : d ≤ R := by simpa [R, d] using hnear
  have hd2 : d ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hd0 hdR 2
  have hd3 : d ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ hd0 hdR 3
  have hd4 : d ^ 4 ≤ R ^ 4 := pow_le_pow_left₀ hd0 hdR 4
  have huC : u c ≤ R ^ 4 := by
    simpa [R] using value_le_nonnegativeJetScale_pow_four hu c
  have hsqrt : Real.sqrt (u c) ≤ R ^ 2 := by
    rw [← Real.sq_sqrt (Real.sqrt_nonneg (u c))]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _)
      (by simpa [R] using sqrt_sqrt_le_nonnegativeJetScale u c) 2
  intro j hj
  interval_cases j
  · change ‖iteratedFDeriv ℝ 0 u y‖ * R ^ 0 ≤ (4 * (C + 1)) * R ^ 4
    rw [pow_zero, mul_one, norm_iteratedFDeriv_zero,
      Real.norm_eq_abs, abs_of_nonneg (hu.nonnegative y)]
    have hv := abs_value_sub_le hu hcontrol c y
    have huv : u y ≤ u c +
        C * R ^ 3 * d + R ^ 2 * d ^ 2 / 2 + C * R * d ^ 3 / 6 + d ^ 4 / 6 := by
      have hupper := (le_abs_self (u y - u c)).trans hv
      have hbase := sub_le_iff_le_add.mp hupper
      nlinarith only [hbase]
    have hterm1 : C * R ^ 3 * d ≤ C * R ^ 4 := by
      calc
        C * R ^ 3 * d ≤ C * R ^ 3 * R :=
          mul_le_mul_of_nonneg_left hdR (mul_nonneg hC0 (pow_nonneg hR0 3))
        _ = C * R ^ 4 := by ring
    have hterm2 : R ^ 2 * d ^ 2 / 2 ≤ R ^ 4 / 2 := by
      calc
        R ^ 2 * d ^ 2 / 2 ≤ R ^ 2 * R ^ 2 / 2 :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hd2 (sq_nonneg R)) (by norm_num)
        _ = R ^ 4 / 2 := by ring
    have hterm3 : C * R * d ^ 3 / 6 ≤ C * R ^ 4 / 6 := by
      calc
        C * R * d ^ 3 / 6 ≤ C * R * R ^ 3 / 6 :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hd3 (mul_nonneg hC0 hR0)) (by norm_num)
        _ = C * R ^ 4 / 6 := by ring
    have hterm4 : d ^ 4 / 6 ≤ R ^ 4 / 6 :=
      div_le_div_of_nonneg_right hd4 (by norm_num)
    nlinarith [pow_nonneg hR0 4]
  · change ‖iteratedFDeriv ℝ 1 u y‖ * R ^ 1 ≤ (4 * (C + 1)) * R ^ 4
    have hdiff : ‖iteratedFDeriv ℝ 1 u y - iteratedFDeriv ℝ 1 u c‖ ≤
        (C + 2) * R ^ 2 * d := by
      have hderiv : Differentiable ℝ (iteratedFDeriv ℝ 1 u) :=
        hu.contDiff.differentiable_iteratedFDeriv (by norm_num)
      have hbound (z : Fin n → ℝ) (hz : z ∈ segment ℝ c y) :
          ‖fderiv ℝ (iteratedFDeriv ℝ 1 u) z‖ ≤ (C + 2) * R ^ 2 := by
        rw [norm_fderiv_iteratedFDeriv]
        have hcz : dist c z ≤ d := by
          simpa [d, dist_eq_norm, norm_sub_rev] using norm_sub_le_of_mem_segment hz
        have hczR : dist c z ≤ R := hcz.trans hdR
        have hvariation := norm_hessian_sub_le hu hcontrol c z
        have hcenter : ‖iteratedFDeriv ℝ 2 u c‖ ≤ R ^ 2 := by
          simpa [R] using norm_iteratedFDeriv_two_le_nonnegativeJetScale_sq u c
        calc
          ‖iteratedFDeriv ℝ 2 u z‖ =
              ‖(iteratedFDeriv ℝ 2 u z - iteratedFDeriv ℝ 2 u c) +
                iteratedFDeriv ℝ 2 u c‖ := by rw [sub_add_cancel]
          _ ≤ ‖iteratedFDeriv ℝ 2 u z - iteratedFDeriv ℝ 2 u c‖ +
              ‖iteratedFDeriv ℝ 2 u c‖ := norm_add_le _ _
          _ ≤ (C * R + dist c z) * dist c z + R ^ 2 := by
            simpa [R] using add_le_add hvariation hcenter
          _ ≤ (C + 2) * R ^ 2 := by
            have hfactor : C * R + dist c z ≤ (C + 1) * R := by linarith
            have hproduct : (C * R + dist c z) * dist c z ≤
                (C + 1) * R ^ 2 := by
              calc
                (C * R + dist c z) * dist c z ≤ (C * R + dist c z) * R :=
                  mul_le_mul_of_nonneg_left hczR
                    (add_nonneg (mul_nonneg hC0 hR0) dist_nonneg)
                _ ≤ ((C + 1) * R) * R :=
                  mul_le_mul_of_nonneg_right hfactor hR0
                _ = (C + 1) * R ^ 2 := by ring
            nlinarith
      have hmv := (convex_segment c y).norm_image_sub_le_of_norm_fderiv_le
        (s := segment ℝ c y) (x := c) (y := y) (C := (C + 2) * R ^ 2)
        (fun z _ ↦ hderiv z) hbound (left_mem_segment ℝ c y) (right_mem_segment ℝ c y)
      simpa [d, dist_eq_norm, norm_sub_rev] using hmv
    have hcenter : ‖iteratedFDeriv ℝ 1 u c‖ ≤ C * R ^ 3 := by
      calc
        ‖iteratedFDeriv ℝ 1 u c‖ ≤ C * R * Real.sqrt (u c) := by
          simpa [R] using hcontrol.first c
        _ ≤ C * R * R ^ 2 :=
          mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hC0 hR0)
        _ = C * R ^ 3 := by ring
    have hgradScale : (C + 2) * R ^ 2 * d ≤ (C + 2) * R ^ 3 := by
      calc
        (C + 2) * R ^ 2 * d ≤ (C + 2) * R ^ 2 * R :=
          mul_le_mul_of_nonneg_left hdR
            (mul_nonneg (by linarith) (sq_nonneg R))
        _ = (C + 2) * R ^ 3 := by ring
    have hy : ‖iteratedFDeriv ℝ 1 u y‖ ≤ (2 * C + 2) * R ^ 3 := by
      calc
        ‖iteratedFDeriv ℝ 1 u y‖ =
            ‖(iteratedFDeriv ℝ 1 u y - iteratedFDeriv ℝ 1 u c) +
              iteratedFDeriv ℝ 1 u c‖ := by rw [sub_add_cancel]
        _ ≤ ‖iteratedFDeriv ℝ 1 u y - iteratedFDeriv ℝ 1 u c‖ +
            ‖iteratedFDeriv ℝ 1 u c‖ := norm_add_le _ _
        _ ≤ (C + 2) * R ^ 2 * d + C * R ^ 3 := add_le_add hdiff hcenter
        _ ≤ (2 * C + 2) * R ^ 3 := by
          calc
            (C + 2) * R ^ 2 * d + C * R ^ 3 ≤
                (C + 2) * R ^ 3 + C * R ^ 3 := add_le_add hgradScale (le_refl _)
            _ = (2 * C + 2) * R ^ 3 := by ring
    have hmul := mul_le_mul_of_nonneg_right hy hR0
    norm_num only [pow_one]
    nlinarith [pow_nonneg hR0 4]
  · change ‖iteratedFDeriv ℝ 2 u y‖ * R ^ 2 ≤ (4 * (C + 1)) * R ^ 4
    have hdiff := norm_hessian_sub_le hu hcontrol c y
    have hcenter : ‖iteratedFDeriv ℝ 2 u c‖ ≤ R ^ 2 := by
      simpa [R] using norm_iteratedFDeriv_two_le_nonnegativeJetScale_sq u c
    have hy : ‖iteratedFDeriv ℝ 2 u y‖ ≤ (C + 2) * R ^ 2 := by
      calc
        ‖iteratedFDeriv ℝ 2 u y‖ =
            ‖(iteratedFDeriv ℝ 2 u y - iteratedFDeriv ℝ 2 u c) +
              iteratedFDeriv ℝ 2 u c‖ := by rw [sub_add_cancel]
        _ ≤ ‖iteratedFDeriv ℝ 2 u y - iteratedFDeriv ℝ 2 u c‖ +
            ‖iteratedFDeriv ℝ 2 u c‖ := norm_add_le _ _
        _ ≤ (C * R + d) * d + R ^ 2 := by simpa [R, d] using add_le_add hdiff hcenter
        _ ≤ (C + 2) * R ^ 2 := by nlinarith [sq_nonneg (R - d)]
    have hmul := mul_le_mul_of_nonneg_right hy (sq_nonneg R)
    nlinarith [pow_nonneg hR0 4]
  · change ‖iteratedFDeriv ℝ 3 u y‖ * R ^ 3 ≤ (4 * (C + 1)) * R ^ 4
    have hdiff := norm_iteratedFDeriv_sub_le_dist hu (j := 3) (by norm_num) c y
    have hcenter := hcontrol.third c
    have hy : ‖iteratedFDeriv ℝ 3 u y‖ ≤ (C + 1) * R := by
      calc
        ‖iteratedFDeriv ℝ 3 u y‖ =
            ‖(iteratedFDeriv ℝ 3 u y - iteratedFDeriv ℝ 3 u c) +
              iteratedFDeriv ℝ 3 u c‖ := by rw [sub_add_cancel]
        _ ≤ ‖iteratedFDeriv ℝ 3 u y - iteratedFDeriv ℝ 3 u c‖ +
            ‖iteratedFDeriv ℝ 3 u c‖ := norm_add_le _ _
        _ ≤ d + C * R := by simpa [R, d] using add_le_add hdiff hcenter
        _ ≤ (C + 1) * R := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hy (pow_nonneg hR0 3)
    nlinarith [pow_nonneg hR0 4]
  · change ‖iteratedFDeriv ℝ 4 u y‖ * R ^ 4 ≤ (4 * (C + 1)) * R ^ 4
    have hy := hu.iteratedFDeriv_le_one 4 (by norm_num) y
    have hmul := mul_le_mul_of_nonneg_right hy (pow_nonneg hR0 4)
    nlinarith [pow_nonneg hR0 4]
  · change ‖iteratedFDeriv ℝ 5 u y‖ * R ^ 5 ≤ (4 * (C + 1)) * R ^ 4
    have hy := hu.iteratedFDeriv_le_one 5 (by norm_num) y
    have hR5 : R ^ 5 ≤ R ^ 4 := by
      rw [show R ^ 5 = R ^ 4 * R by ring]
      nlinarith [pow_nonneg hR0 4]
    have hmul := mul_le_mul_of_nonneg_right hy (pow_nonneg hR0 5)
    nlinarith [pow_nonneg hR0 4]
  · change ‖iteratedFDeriv ℝ 6 u y‖ * R ^ 6 ≤ (4 * (C + 1)) * R ^ 4
    have hy := hu.iteratedFDeriv_le_one 6 (by norm_num) y
    have hR6 : R ^ 6 ≤ R ^ 4 := by
      rw [show R ^ 6 = R ^ 4 * R ^ 2 by ring]
      have hR2 : R ^ 2 ≤ 1 := by nlinarith [sq_nonneg R]
      nlinarith [pow_nonneg hR0 4]
    have hmul := mul_le_mul_of_nonneg_right hy (pow_nonneg hR0 6)
    nlinarith [pow_nonneg hR0 4]

/-- Intrinsic normalization therefore has a uniform `C⁶` bound on the Euclidean unit ball. -/
theorem intrinsicRescaledPatch_uniform_deriv_on_unitBall {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C)
    (c : Fin n → ℝ) (hR : 0 < nonnegativeJetScale u c)
    (z : Fin n → ℝ) (hz : ‖z‖ ≤ 1) :
    ∀ j, j ≤ 6 →
      ‖iteratedFDeriv ℝ j
        (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) z‖ ≤ 4 * (C + 1) := by
  intro j hj
  let R := nonnegativeJetScale u c
  have hdist : dist c (c + R • z) ≤ R := by
    rw [dist_eq_norm]
    have hsub : c - (c + R • z) = -(R • z) := by abel
    rw [hsub, norm_neg, norm_smul, Real.norm_of_nonneg
      (nonnegativeJetScale_nonneg u c)]
    simpa [R] using mul_le_mul_of_nonneg_left hz (nonnegativeJetScale_nonneg u c)
  exact intrinsicRescaledPatch_iteratedFDeriv_le_of_scaled hu.contDiff c hR hj z
    (normalized_scaledJets_on_intrinsic_ball hu hcontrol c (c + R • z) hdist j hj)
end OptimalConvergenceRates.QuarticConvergence
end
