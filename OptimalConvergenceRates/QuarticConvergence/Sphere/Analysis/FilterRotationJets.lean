/-
  Quantitative C2 jets of the centered inverse-rotation pullback.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FilterRotationGeometry
import Mathlib.Analysis.Normed.Operator.NormedSpace

open Set

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers
/-- The centered pair of pullbacks by the two inverse products of axial
reflections. -/
def centeredLinearPullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E → ℝ) (L R : E →L[ℝ] E) : E → ℝ := (v ∘ L) + (v ∘ R) + ((-2 : ℝ) • v)

/-- Iterated derivatives of a centered linear pullback are obtained by the
corresponding pullback actions on derivative tensors. -/
theorem iteratedFDeriv_centeredLinearPullback
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {j : ℕ} {v : E → ℝ} (hv : ContDiff ℝ j v)
    (L R : E →L[ℝ] E) (z : E) :
    iteratedFDeriv ℝ j (centeredLinearPullback v L R) z =
      iteratedDerivativePullbackAction j L (iteratedFDeriv ℝ j v (L z)) +
        iteratedDerivativePullbackAction j R (iteratedFDeriv ℝ j v (R z)) -
          (2 : ℝ) • iteratedFDeriv ℝ j v z := by
  have hL : iteratedFDeriv ℝ j (v ∘ L) z =
      (iteratedFDeriv ℝ j v (L z)).compContinuousLinearMap (fun _ ↦ L) :=
    L.iteratedFDeriv_comp_right hv z le_rfl
  have hR : iteratedFDeriv ℝ j (v ∘ R) z =
      (iteratedFDeriv ℝ j v (R z)).compContinuousLinearMap (fun _ ↦ R) :=
    R.iteratedFDeriv_comp_right hv z le_rfl
  have hvL : ContDiffAt ℝ j (v ∘ L) z := (hv.comp L.contDiff).contDiffAt
  have hvR : ContDiffAt ℝ j (v ∘ R) z := (hv.comp R.contDiff).contDiffAt
  have hvz : ContDiffAt ℝ j v z := hv.contDiffAt
  have hvLR : ContDiffAt ℝ j ((v ∘ L) + (v ∘ R)) z := by
    change ContDiffAt ℝ j (fun w ↦ (v ∘ L) w + (v ∘ R) w) z
    exact hvL.add hvR
  have hneg : ContDiffAt ℝ j ((-2 : ℝ) • v) z := by
    exact (hv.const_smul (-(2 : ℝ))).contDiffAt
  unfold centeredLinearPullback
  rw [iteratedFDeriv_add_apply hvLR hneg,
    iteratedFDeriv_add_apply hvL hvR,
    iteratedFDeriv_const_smul_apply hvz, hL, hR]
  simp [iteratedDerivativePullbackAction_apply, sub_eq_add_neg]

/-- The derivative of `D^j v` is globally Lipschitz when `D^(j+2) v` is
uniformly bounded.  Currying the derivative tensors is isometric. -/
theorem fderiv_iteratedFDeriv_lipschitz
    {n j : ℕ} {v : (Fin n → ℝ) → ℝ} {M : ℝ}
    (hv : ContDiff ℝ (j + 2) v)
    (hjet : ∀ z, ‖iteratedFDeriv ℝ (j + 2) v z‖ ≤ M)
    (x y : Fin n → ℝ) :
    ‖fderiv ℝ (iteratedFDeriv ℝ j v) y -
        fderiv ℝ (iteratedFDeriv ℝ j v) x‖ ≤ M * ‖y - x‖ := by
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ (j + 1) v) :=
    hv.differentiable_iteratedFDeriv (by
      exact_mod_cast Nat.lt_succ_self (j + 1))
  have hbase :
      ‖iteratedFDeriv ℝ (j + 1) v y -
          iteratedFDeriv ℝ (j + 1) v x‖ ≤ M * ‖y - x‖ := by
    exact convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ hdiff.differentiableAt)
      (fun z _ ↦ by
        rw [norm_fderiv_iteratedFDeriv]
        simpa [Nat.add_assoc] using hjet z)
      (Set.mem_univ x) (Set.mem_univ y)
  rw [fderiv_iteratedFDeriv]
  let curry := continuousMultilinearCurryLeftEquiv ℝ
    (fun _ : Fin (j + 1) ↦ (Fin n → ℝ)) ℝ
  change ‖curry (iteratedFDeriv ℝ (j + 1) v y) -
      curry (iteratedFDeriv ℝ (j + 1) v x)‖ ≤ _
  rw [← curry.map_sub, curry.norm_map]
  exact hbase

/-- A coarse dimension-only constant dominating all spatial and tensor
pullback norms used through derivative order two. -/
noncomputable def sphereRotationJetConstant (n : ℕ) : ℝ :=
  8 * (max 1 (sphereCoordinateNormDistortion n ^ 2)) ^ 2

theorem sphereRotationJetConstant_one_le (n : ℕ) :
    1 ≤ sphereRotationJetConstant n := by
  have hmax : 1 ≤ max 1 (sphereCoordinateNormDistortion n ^ 2) := le_max_left _ _
  dsimp [sphereRotationJetConstant]
  nlinarith [sq_nonneg (max 1 (sphereCoordinateNormDistortion n ^ 2) - 1)]

/-- For orders at most two, a tensor pullback by a map of norm at most `C`
has norm at most the coarse bound `8*C^2`. -/
theorem norm_iteratedDerivativePullbackAction_le_eight_sq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {j : ℕ} (hj : j ≤ 2) (L : E →L[ℝ] E) {C : ℝ}
    (hC : 1 ≤ C) (hL : ‖L‖ ≤ C) :
    ‖iteratedDerivativePullbackAction j L‖ ≤ 8 * C ^ 2 := by
  have hraw := norm_iteratedDerivativePullbackAction_le j L
  interval_cases j
  · calc
      _ ≤ ‖L‖ ^ 0 := hraw
      _ = 1 := by simp
      _ ≤ 8 * C ^ 2 := by nlinarith [sq_nonneg C]
  · calc
      _ ≤ ‖L‖ ^ 1 := hraw
      _ = ‖L‖ := by simp
      _ ≤ C := hL
      _ ≤ 8 * C ^ 2 := by nlinarith [sq_nonneg C]
  · calc
      _ ≤ ‖L‖ ^ 2 := hraw
      _ ≤ C ^ 2 := by gcongr
      _ ≤ 8 * C ^ 2 := by nlinarith [sq_nonneg C]

/-- The centered inverse-rotation pullback has all ambient jets through order
two bounded by `M` times chordal distance squared.  The constant depends only
on the ambient dimension and is uniform in the two sphere points. -/
theorem exists_centeredRotationPullback_c2_jet_bound
    {n : ℕ} (hn : 2 ≤ n) (v : (Fin n → ℝ) → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hv : ContDiff ℝ 4 v)
    (hjet : ∀ j, j ≤ 4 → ∀ z, ‖iteratedFDeriv ℝ j v z‖ ≤ M)
    (x y : sphereSet n) :
    ∃ a : sphereSet n,
      sphereAxialReflection a x = y ∧
      ContDiff ℝ 2 (centeredLinearPullback v
        (sphereForwardRotationCLM a x) (sphereReverseRotationCLM a x)) ∧
      ∀ j, j ≤ 2 → ∀ z, ‖z‖ ≤ 1 →
        ‖iteratedFDeriv ℝ j (centeredLinearPullback v
          (sphereForwardRotationCLM a x) (sphereReverseRotationCLM a x)) z‖ ≤
          6 * sphereRotationJetConstant n ^ 3 * M *
            sphereChordalSq y.1 x.1 := by
  let D := sphereCoordinateNormDistortion n
  let S := max 1 (D ^ 2)
  let B := sphereRotationJetConstant n
  let delta := Real.sqrt (sphereChordalSq y.1 x.1)
  have hD0 : 0 ≤ D := by
    exact sphereCoordinateNormDistortion_nonneg n
  have hS1 : 1 ≤ S := by
    exact le_max_left _ _
  have hS0 : 0 ≤ S := zero_le_one.trans hS1
  have hDsqS : D ^ 2 ≤ S := by
    exact le_max_right _ _
  have hSS : S ≤ S ^ 2 := by
    nlinarith [sq_nonneg (S - 1)]
  have hBdef : B = 8 * S ^ 2 := by
    rfl
  have hB1 : 1 ≤ B := by
    simpa [B] using sphereRotationJetConstant_one_le n
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  have hDsqB : D ^ 2 ≤ B := by
    calc
      D ^ 2 ≤ S := hDsqS
      _ ≤ S ^ 2 := hSS
      _ ≤ 8 * S ^ 2 := by nlinarith [sq_nonneg S]
      _ = B := hBdef.symm
  have hfourDsqB : 4 * D ^ 2 ≤ B := by
    calc
      4 * D ^ 2 ≤ 4 * S := by nlinarith
      _ ≤ 8 * S ^ 2 := by nlinarith [sq_nonneg S]
      _ = B := hBdef.symm
  have hdelta : 0 ≤ delta := Real.sqrt_nonneg _
  have hdeltasq : delta ^ 2 = sphereChordalSq y.1 x.1 := by
    dsimp [delta]
    exact Real.sq_sqrt (sphereChordalSq_nonneg y.1 x.1)
  obtain ⟨a, hmap, hLnormRaw, hRnormRaw, hLdiffRaw, hRdiffRaw,
      hLcenterRaw⟩ := exists_sphereRotationPair_bounds hn x y
  let L := sphereForwardRotationCLM a x
  let R := sphereReverseRotationCLM a x
  have hLnorm0 : ‖L‖ ≤ D ^ 2 := by
    simpa [L, D] using hLnormRaw
  have hRnorm0 : ‖R‖ ≤ D ^ 2 := by
    simpa [R, D] using hRnormRaw
  have hLnorm : ‖L‖ ≤ B := hLnorm0.trans hDsqB
  have hRnorm : ‖R‖ ≤ B := hRnorm0.trans hDsqB
  have hLdiff0 :
      ‖L - ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤
        (4 * D ^ 2) * delta := by
    simpa [L, D, delta] using hLdiffRaw
  have hRdiff0 :
      ‖R - ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤
        (4 * D ^ 2) * delta := by
    simpa [R, D, delta] using hRdiffRaw
  have hLdiff :
      ‖L - ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤ B * delta :=
    hLdiff0.trans (mul_le_mul_of_nonneg_right hfourDsqB hdelta)
  have hRdiff :
      ‖R - ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤ B * delta :=
    hRdiff0.trans (mul_le_mul_of_nonneg_right hfourDsqB hdelta)
  have hLcenter :
      ‖L + R - 2 • ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤
        B ^ 2 * delta ^ 2 := by
    apply (show ‖L + R - 2 • ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤
        ((4 * D ^ 2) * delta) ^ 2 by
      simpa [L, R, D, delta] using hLcenterRaw).trans
    calc
      ((4 * D ^ 2) * delta) ^ 2 ≤ (B * delta) ^ 2 := by
        gcongr
      _ = B ^ 2 * delta ^ 2 := by ring
  have hg : ContDiff ℝ 2 (centeredLinearPullback v L R) := by
    have hv2 : ContDiff ℝ 2 v := hv.of_le (by norm_num)
    unfold centeredLinearPullback
    change ContDiff ℝ 2 (fun z ↦ v (L z) + v (R z) + (-2 : ℝ) • v z)
    exact ((hv2.comp L.contDiff).add (hv2.comp R.contDiff)).add
      (hv2.const_smul (-2))
  refine ⟨a, hmap, ?_, ?_⟩
  · simpa [L, R] using hg
  · intro j hj z hz
    have hj4 : j ≤ 4 := by omega
    have hvj : ContDiff ℝ j v := hv.of_le (by exact_mod_cast hj4)
    have hF : ContDiff ℝ 1 (iteratedFDeriv ℝ j v) :=
      hv.iteratedFDeriv_right (m := 1) (i := j) (by
        exact_mod_cast (show 1 + j ≤ 4 by omega))
    have hFzero : ∀ w, ‖iteratedFDeriv ℝ j v w‖ ≤ M :=
      hjet j hj4
    have hFone : ∀ w, ‖fderiv ℝ (iteratedFDeriv ℝ j v) w‖ ≤ M := by
      intro w
      rw [norm_fderiv_iteratedFDeriv]
      exact hjet (j + 1) (by omega) w
    have hvj2 : ContDiff ℝ (j + 2) v :=
      hv.of_le (by exact_mod_cast (show j + 2 ≤ 4 by omega))
    have hFlip : ∀ u w,
        ‖fderiv ℝ (iteratedFDeriv ℝ j v) w -
          fderiv ℝ (iteratedFDeriv ℝ j v) u‖ ≤ M * ‖w - u‖ := by
      intro u w
      exact fderiv_iteratedFDeriv_lipschitz hvj2
        (fun q ↦ hjet (j + 2) (by omega) q) u w
    let P := iteratedDerivativePullbackAction j L
    let Q := iteratedDerivativePullbackAction j R
    have hPnorm : ‖P‖ ≤ B := by
      calc
        _ ≤ 8 * S ^ 2 := norm_iteratedDerivativePullbackAction_le_eight_sq
          hj L hS1 (hLnorm0.trans hDsqS)
        _ = B := hBdef.symm
    have hQnorm : ‖Q‖ ≤ B := by
      calc
        _ ≤ 8 * S ^ 2 := norm_iteratedDerivativePullbackAction_le_eight_sq
          hj R hS1 (hRnorm0.trans hDsqS)
        _ = B := hBdef.symm
    have hactionDiff :
        2 * S * ((4 * D ^ 2) * delta) ≤ B * delta := by
      calc
        2 * S * ((4 * D ^ 2) * delta) = (8 * S * D ^ 2) * delta := by ring
        _ ≤ (8 * S * S) * delta := by gcongr
        _ = B * delta := by rw [hBdef]; ring
    have hPdiff :
        ‖P - ContinuousLinearMap.id ℝ
          (ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ (Fin n → ℝ)) ℝ)‖ ≤
          B * delta := by
      apply (norm_iteratedDerivativePullbackAction_sub_id_le hj L hS1
        (hLnorm0.trans hDsqS) hLdiff0).trans
      exact hactionDiff
    have hQdiff :
        ‖Q - ContinuousLinearMap.id ℝ
          (ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ (Fin n → ℝ)) ℝ)‖ ≤
          B * delta := by
      apply (norm_iteratedDerivativePullbackAction_sub_id_le hj R hS1
        (hRnorm0.trans hDsqS) hRdiff0).trans
      exact hactionDiff
    have hPQ : P.comp Q = ContinuousLinearMap.id ℝ
        (ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ (Fin n → ℝ)) ℝ) := by
      dsimp [P, Q]
      rw [iteratedDerivativePullbackAction_comp,
        show R.comp L = ContinuousLinearMap.id ℝ (Fin n → ℝ) by
          simp [R, L],
        iteratedDerivativePullbackAction_id]
    have hPcenter :
        ‖P + Q - 2 • ContinuousLinearMap.id ℝ
          (ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ (Fin n → ℝ)) ℝ)‖ ≤
          B ^ 2 * delta ^ 2 := by
      have h := norm_clm_add_inverse_sub_two_id_le P Q hPQ hPdiff hQdiff
      calc
        _ ≤ (B * delta) * (B * delta) := h
        _ = B ^ 2 * delta ^ 2 := by ring
    have hbound := norm_centered_transformed_pair_le hM hB1 hdelta
      hF hFzero hFone hFlip L R P Q hLnorm hRnorm hPnorm hQnorm
      hLdiff hRdiff hPdiff hQdiff hLcenter hPcenter z hz
    rw [iteratedFDeriv_centeredLinearPullback hvj]
    change ‖P (iteratedFDeriv ℝ j v (L z)) +
      Q (iteratedFDeriv ℝ j v (R z)) -
        (2 : ℝ) • iteratedFDeriv ℝ j v z‖ ≤ _
    have hboundFinal := hbound.trans_eq (by rw [hdeltasq])
    simpa only [two_nsmul, two_smul] using hboundFinal

end QuarticConvergence
end OptimalConvergenceRates

end
