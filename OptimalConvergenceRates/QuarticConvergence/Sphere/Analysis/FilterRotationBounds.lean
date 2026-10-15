/- Quantitative centered-pullback bounds used by the spherical filter. -/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FilterRotation

open Set

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- A globally Lipschitz derivative gives a coarse first-order Taylor
remainder bound. -/
theorem norm_sub_sub_fderiv_le_of_global_fderiv_lipschitz
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → G} {M : ℝ} (hM : 0 ≤ M) (hF : ContDiff ℝ 1 F)
    (hDFLip : ∀ u v, ‖fderiv ℝ F v - fderiv ℝ F u‖ ≤ M * ‖v - u‖)
    (x y : E) :
    ‖F y - F x - fderiv ℝ F x (y - x)‖ ≤ M * ‖y - x‖ ^ 2 := by
  let H : E → G := fun z ↦ F z - fderiv ℝ F x z
  have hHdiff : Differentiable ℝ H :=
    (hF.differentiable (by norm_num)).sub (fderiv ℝ F x).differentiable
  have hHderiv (z : E) :
      fderiv ℝ H z = fderiv ℝ F z - fderiv ℝ F x := by
    have hH : H = F - (fderiv ℝ F x : E → G) := by
      funext w
      rfl
    rw [hH]
    exact (((hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt).sub
      (fderiv ℝ F x).hasFDerivAt).fderiv
  have hHbound : ∀ z ∈ segment ℝ x y,
      ‖fderiv ℝ H z‖ ≤ M * ‖y - x‖ := by
    intro z hz
    rw [hHderiv]
    exact (hDFLip x z).trans <| by
      gcongr
      exact norm_sub_le_of_mem_segment hz
  have hmean := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ hHdiff.differentiableAt) hHbound
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  dsimp [H] at hmean
  calc
    ‖F y - F x - fderiv ℝ F x (y - x)‖ =
        ‖(F y - fderiv ℝ F x y) - (F x - fderiv ℝ F x x)‖ := by
          congr 1
          rw [map_sub]
          abel
    _ ≤ (M * ‖y - x‖) * ‖y - x‖ := hmean
    _ = M * ‖y - x‖ ^ 2 := by ring

-- Bounds on both argument maps remain explicit for symmetry with the value-map hypotheses.
set_option linter.unusedVariables false in
/-- A centered pair of inverse-like pullbacks gains two powers of the
displacement. The maps `L,R` act on arguments and `P,Q` on values. -/
theorem norm_centered_transformed_pair_le
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → G} {M B delta : ℝ}
    (hM : 0 ≤ M) (hB : 1 ≤ B) (hdelta : 0 ≤ delta)
    (hF : ContDiff ℝ 1 F)
    (hFzero : ∀ z, ‖F z‖ ≤ M)
    (hFone : ∀ z, ‖fderiv ℝ F z‖ ≤ M)
    (hFderiv_lipschitz : ∀ u v, ‖fderiv ℝ F v - fderiv ℝ F u‖ ≤ M * ‖v - u‖)
    (L R : E →L[ℝ] E) (P Q : G →L[ℝ] G)
    (hL : ‖L‖ ≤ B) (hR : ‖R‖ ≤ B)
    (hP : ‖P‖ ≤ B) (hQ : ‖Q‖ ≤ B)
    (hLd : ‖L - ContinuousLinearMap.id ℝ E‖ ≤ B * delta)
    (hRd : ‖R - ContinuousLinearMap.id ℝ E‖ ≤ B * delta)
    (hPd : ‖P - ContinuousLinearMap.id ℝ G‖ ≤ B * delta)
    (hQd : ‖Q - ContinuousLinearMap.id ℝ G‖ ≤ B * delta)
    (hLcenter :
      ‖L + R - 2 • ContinuousLinearMap.id ℝ E‖ ≤ B ^ 2 * delta ^ 2)
    (hPcenter :
      ‖P + Q - 2 • ContinuousLinearMap.id ℝ G‖ ≤ B ^ 2 * delta ^ 2)
    (z : E) (hz : ‖z‖ ≤ 1) :
    ‖P (F (L z)) + Q (F (R z)) - 2 • F z‖ ≤
      6 * B ^ 3 * M * delta ^ 2 := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hLd0 : 0 ≤ B * delta := mul_nonneg hB0 hdelta
  have hpointL : ‖L z - z‖ ≤ B * delta := by
    calc
      ‖L z - z‖ = ‖(L - ContinuousLinearMap.id ℝ E) z‖ := by simp
      _ ≤ ‖L - ContinuousLinearMap.id ℝ E‖ * ‖z‖ :=
        (L - ContinuousLinearMap.id ℝ E).le_opNorm z
      _ ≤ (B * delta) * 1 := by gcongr
      _ = B * delta := mul_one _
  have hpointR : ‖R z - z‖ ≤ B * delta := by
    calc
      ‖R z - z‖ = ‖(R - ContinuousLinearMap.id ℝ E) z‖ := by simp
      _ ≤ ‖R - ContinuousLinearMap.id ℝ E‖ * ‖z‖ :=
        (R - ContinuousLinearMap.id ℝ E).le_opNorm z
      _ ≤ (B * delta) * 1 := by gcongr
      _ = B * delta := mul_one _
  let remL : G := F (L z) - F z - fderiv ℝ F z (L z - z)
  let remR : G := F (R z) - F z - fderiv ℝ F z (R z - z)
  have hremL : ‖remL‖ ≤ M * (B * delta) ^ 2 := by
    exact
      (norm_sub_sub_fderiv_le_of_global_fderiv_lipschitz
        hM hF hFderiv_lipschitz z (L z)).trans <| by
        gcongr
  have hremR : ‖remR‖ ≤ M * (B * delta) ^ 2 := by
    exact
      (norm_sub_sub_fderiv_le_of_global_fderiv_lipschitz
        hM hF hFderiv_lipschitz z (R z)).trans <| by
        gcongr
  have hexpand :
      P (F (L z)) + Q (F (R z)) - 2 • F z =
        P remL + Q remR +
          (P + Q - 2 • ContinuousLinearMap.id ℝ G) (F z) +
          fderiv ℝ F z ((L + R - 2 • ContinuousLinearMap.id ℝ E) z) +
          (P - ContinuousLinearMap.id ℝ G)
            (fderiv ℝ F z ((L - ContinuousLinearMap.id ℝ E) z)) +
          (Q - ContinuousLinearMap.id ℝ G)
            (fderiv ℝ F z ((R - ContinuousLinearMap.id ℝ E) z)) := by
    have hFL : F (L z) = remL + F z + fderiv ℝ F z (L z - z) := by
      dsimp [remL]
      abel
    have hFR : F (R z) = remR + F z + fderiv ℝ F z (R z - z) := by
      dsimp [remR]
      abel
    rw [hFL, hFR]
    simp only [map_add, map_sub, add_apply,
      sub_apply, FunLike.coe_smul,
      ContinuousLinearMap.coe_id', Pi.smul_apply, id_eq, map_nsmul]
    abel
  have hterm (T : G →L[ℝ] G) (u : G) {a b : ℝ}
      (hT : ‖T‖ ≤ a) (hu : ‖u‖ ≤ b) (ha : 0 ≤ a) :
      ‖T u‖ ≤ a * b := by
    exact (T.le_opNorm u).trans (mul_le_mul hT hu (norm_nonneg u) ha)
  rw [hexpand]
  have hsum :
      ‖P remL + Q remR +
          (P + Q - 2 • ContinuousLinearMap.id ℝ G) (F z) +
          fderiv ℝ F z ((L + R - 2 • ContinuousLinearMap.id ℝ E) z) +
          (P - ContinuousLinearMap.id ℝ G)
            (fderiv ℝ F z ((L - ContinuousLinearMap.id ℝ E) z)) +
          (Q - ContinuousLinearMap.id ℝ G)
            (fderiv ℝ F z ((R - ContinuousLinearMap.id ℝ E) z))‖ ≤
        ‖P remL‖ + ‖Q remR‖ +
          ‖(P + Q - 2 • ContinuousLinearMap.id ℝ G) (F z)‖ +
          ‖fderiv ℝ F z ((L + R - 2 • ContinuousLinearMap.id ℝ E) z)‖ +
          ‖(P - ContinuousLinearMap.id ℝ G)
            (fderiv ℝ F z ((L - ContinuousLinearMap.id ℝ E) z))‖ +
          ‖(Q - ContinuousLinearMap.id ℝ G)
            (fderiv ℝ F z ((R - ContinuousLinearMap.id ℝ E) z))‖ := by
    have h12 : ‖P remL + Q remR‖ ≤ ‖P remL‖ + ‖Q remR‖ :=
      norm_add_le _ _
    have h123 :
        ‖P remL + Q remR +
          (P + Q - 2 • ContinuousLinearMap.id ℝ G) (F z)‖ ≤
        ‖P remL‖ + ‖Q remR‖ +
          ‖(P + Q - 2 • ContinuousLinearMap.id ℝ G) (F z)‖ :=
      (norm_add_le _ _).trans (by gcongr)
    have h1234 :
        ‖P remL + Q remR +
            (P + Q - 2 • ContinuousLinearMap.id ℝ G) (F z) +
          fderiv ℝ F z ((L + R - 2 • ContinuousLinearMap.id ℝ E) z)‖ ≤
        ‖P remL‖ + ‖Q remR‖ +
            ‖(P + Q - 2 • ContinuousLinearMap.id ℝ G) (F z)‖ +
          ‖fderiv ℝ F z ((L + R - 2 • ContinuousLinearMap.id ℝ E) z)‖ :=
      (norm_add_le _ _).trans (by gcongr)
    have h12345 :
        ‖P remL + Q remR +
              (P + Q - 2 • ContinuousLinearMap.id ℝ G) (F z) +
            fderiv ℝ F z ((L + R - 2 • ContinuousLinearMap.id ℝ E) z) +
          (P - ContinuousLinearMap.id ℝ G)
            (fderiv ℝ F z ((L - ContinuousLinearMap.id ℝ E) z))‖ ≤
        ‖P remL‖ + ‖Q remR‖ +
              ‖(P + Q - 2 • ContinuousLinearMap.id ℝ G) (F z)‖ +
            ‖fderiv ℝ F z ((L + R - 2 • ContinuousLinearMap.id ℝ E) z)‖ +
          ‖(P - ContinuousLinearMap.id ℝ G)
            (fderiv ℝ F z ((L - ContinuousLinearMap.id ℝ E) z))‖ :=
      (norm_add_le _ _).trans (by gcongr)
    exact (norm_add_le _ _).trans (by gcongr)
  apply hsum.trans
  have hBsq : B ^ 2 ≤ B ^ 3 := by nlinarith [sq_nonneg B]
  have hremCommon : B * (M * (B * delta) ^ 2) ≤
      B ^ 3 * M * delta ^ 2 := le_of_eq (by ring)
  have hcenterCommon : (B ^ 2 * delta ^ 2) * M ≤
      B ^ 3 * M * delta ^ 2 := by
    calc
      _ = B ^ 2 * M * delta ^ 2 := by ring_nf
      _ ≤ _ := by gcongr
  have hcrossCommon : (B * delta) * (M * (B * delta)) ≤
      B ^ 3 * M * delta ^ 2 := by
    calc
      _ = B ^ 2 * M * delta ^ 2 := by ring_nf
      _ ≤ _ := by gcongr
  have h1 : ‖P remL‖ ≤ B ^ 3 * M * delta ^ 2 :=
    (hterm P remL hP hremL hB0).trans hremCommon
  have h2 : ‖Q remR‖ ≤ B ^ 3 * M * delta ^ 2 :=
    (hterm Q remR hQ hremR hB0).trans hremCommon
  have h3 : ‖(P + Q - 2 • ContinuousLinearMap.id ℝ G) (F z)‖ ≤
      B ^ 3 * M * delta ^ 2 :=
    (hterm _ _ hPcenter (hFzero z) (by positivity)).trans hcenterCommon
  have h4 :
      ‖fderiv ℝ F z ((L + R - 2 • ContinuousLinearMap.id ℝ E) z)‖ ≤
        B ^ 3 * M * delta ^ 2 := by
    have hcenterZ :
        ‖(L + R - 2 • ContinuousLinearMap.id ℝ E) z‖ ≤
          B ^ 2 * delta ^ 2 := by
      calc
        _ ≤ ‖L + R - 2 • ContinuousLinearMap.id ℝ E‖ * ‖z‖ :=
          (L + R - 2 • ContinuousLinearMap.id ℝ E).le_opNorm z
        _ ≤ (B ^ 2 * delta ^ 2) * 1 := by gcongr
        _ = _ := mul_one _
    calc
      _ ≤ ‖fderiv ℝ F z‖ *
          ‖(L + R - 2 • ContinuousLinearMap.id ℝ E) z‖ :=
        (fderiv ℝ F z).le_opNorm _
      _ ≤ M * (B ^ 2 * delta ^ 2) :=
        mul_le_mul (hFone z) hcenterZ (norm_nonneg _) hM
      _ ≤ _ := by
        calc
          _ = (B ^ 2 * delta ^ 2) * M := by ring_nf
          _ ≤ _ := hcenterCommon
  have h5 : ‖(P - ContinuousLinearMap.id ℝ G)
        (fderiv ℝ F z ((L - ContinuousLinearMap.id ℝ E) z))‖ ≤
      B ^ 3 * M * delta ^ 2 := by
    have harg : ‖(L - ContinuousLinearMap.id ℝ E) z‖ ≤ B * delta := by
      simpa using hpointL
    apply (hterm _ _ hPd ?_ hLd0).trans hcrossCommon
    exact ((fderiv ℝ F z).le_opNorm _).trans <| by
      exact mul_le_mul (hFone z) harg (norm_nonneg _) hM
  have h6 : ‖(Q - ContinuousLinearMap.id ℝ G)
        (fderiv ℝ F z ((R - ContinuousLinearMap.id ℝ E) z))‖ ≤
      B ^ 3 * M * delta ^ 2 := by
    have harg : ‖(R - ContinuousLinearMap.id ℝ E) z‖ ≤ B * delta := by
      simpa using hpointR
    apply (hterm _ _ hQd ?_ hLd0).trans hcrossCommon
    exact ((fderiv ℝ F z).le_opNorm _).trans
      (mul_le_mul (hFone z) harg (norm_nonneg _) hM)
  linarith

end QuarticConvergence
end OptimalConvergenceRates

end
