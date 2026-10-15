/-
  Quantitative composition estimates supporting the implicit-graph jet recurrence.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.ImplicitGraphJetBounds

open Set

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

theorem implicitGraphNormalCurvatureField_contDiff {n : ℕ}
    (input : NormalizedLocalSplitInput n) :
    ContDiff ℝ 4 (implicitGraphNormalCurvatureField input) := by
  let N : (ℝ × (Fin n → ℝ)) → ℝ := fun z ↦
    fderiv ℝ input.function z (splitNormalDirection n)
  have hN : ContDiff ℝ 5 N := by
    exact (input.contDiff.fderiv_right (m := 5) (by norm_num)).clm_apply contDiff_const
  exact (hN.fderiv_right (m := 4) (by norm_num)).clm_apply contDiff_const

theorem implicitGraphNormalTangentialField_contDiff {n : ℕ}
    (input : NormalizedLocalSplitInput n) :
    ContDiff ℝ 4 (implicitGraphNormalTangentialField input) := by
  let N : (ℝ × (Fin n → ℝ)) → ℝ := fun z ↦
    fderiv ℝ input.function z (splitNormalDirection n)
  let T : (Fin n → ℝ) →L[ℝ] (ℝ × (Fin n → ℝ)) :=
    ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)
  let precompose :
      (((ℝ × (Fin n → ℝ)) →L[ℝ] ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
    (ContinuousLinearMap.compL ℝ (Fin n → ℝ) (ℝ × (Fin n → ℝ)) ℝ).flip T
  have hN : ContDiff ℝ 5 N := by
    exact (input.contDiff.fderiv_right (m := 5) (by norm_num)).clm_apply contDiff_const
  exact precompose.contDiff.comp (hN.fderiv_right (m := 4) (by norm_num))

/-- Slicing two unit normal/tangential directions out of the ambient derivative does not
increase its norm. -/
theorem norm_iteratedFDeriv_implicitGraphNormalCurvatureField_le
    {n q : ℕ} (input : NormalizedLocalSplitInput n) (hq : q ≤ 4)
    (z : ℝ × (Fin n → ℝ)) :
    ‖iteratedFDeriv ℝ q (implicitGraphNormalCurvatureField input) z‖ ≤
      ‖iteratedFDeriv ℝ (q + 2) input.function z‖ := by
  let N : (ℝ × (Fin n → ℝ)) → ℝ := fun w ↦
    fderiv ℝ input.function w (splitNormalDirection n)
  have hN : ContDiff ℝ 5 N := by
    exact (input.contDiff.fderiv_right (m := 5) (by norm_num)).clm_apply contDiff_const
  have houter := norm_iteratedFDeriv_clm_apply_const
    (f := fderiv ℝ N) (c := splitNormalDirection n) (x := z) (n := q)
    ((hN.fderiv_right (m := 4) (by norm_num)).contDiffAt)
    (by exact_mod_cast hq)
  have hinner := norm_iteratedFDeriv_clm_apply_const
    (f := fderiv ℝ input.function) (c := splitNormalDirection n) (x := z) (n := q + 1)
    ((input.contDiff.fderiv_right (m := 5) (by norm_num)).contDiffAt)
    (by exact_mod_cast Nat.succ_le_succ hq)
  calc
    ‖iteratedFDeriv ℝ q (implicitGraphNormalCurvatureField input) z‖ ≤
        ‖splitNormalDirection n‖ * ‖iteratedFDeriv ℝ q (fderiv ℝ N) z‖ := by
      change ‖iteratedFDeriv ℝ q
          (fun y ↦ fderiv ℝ N y (splitNormalDirection n)) z‖ ≤ _
      simpa [N] using houter
    _ = ‖iteratedFDeriv ℝ (q + 1) N z‖ := by
      rw [norm_iteratedFDeriv_fderiv]
      simp [splitNormalDirection, Prod.norm_def]
    _ ≤ ‖splitNormalDirection n‖ *
        ‖iteratedFDeriv ℝ (q + 1) (fderiv ℝ input.function) z‖ := by
      simpa [N] using hinner
    _ = ‖iteratedFDeriv ℝ (q + 2) input.function z‖ := by
      rw [norm_iteratedFDeriv_fderiv]
      simp [splitNormalDirection, Prod.norm_def]

/-- The mixed normal-tangential field is another norm-one slice of the ambient Hessian. -/
theorem norm_iteratedFDeriv_implicitGraphNormalTangentialField_le
    {n q : ℕ} (input : NormalizedLocalSplitInput n) (hq : q ≤ 4)
    (z : ℝ × (Fin n → ℝ)) :
    ‖iteratedFDeriv ℝ q (implicitGraphNormalTangentialField input) z‖ ≤
      ‖iteratedFDeriv ℝ (q + 2) input.function z‖ := by
  let N : (ℝ × (Fin n → ℝ)) → ℝ := fun w ↦
    fderiv ℝ input.function w (splitNormalDirection n)
  let T : (Fin n → ℝ) →L[ℝ] (ℝ × (Fin n → ℝ)) :=
    ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)
  let precompose :
      (((ℝ × (Fin n → ℝ)) →L[ℝ] ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
    (ContinuousLinearMap.compL ℝ (Fin n → ℝ) (ℝ × (Fin n → ℝ)) ℝ).flip T
  have hT : ‖T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    change ‖((0 : ℝ), v)‖ ≤ 1 * ‖v‖
    simp [Prod.norm_def]
  have hprecompose : ‖precompose‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro L
    change ‖L.comp T‖ ≤ 1 * ‖L‖
    exact (ContinuousLinearMap.opNorm_comp_le L T).trans (by
      calc
        ‖L‖ * ‖T‖ ≤ ‖L‖ * 1 := mul_le_mul_of_nonneg_left hT (norm_nonneg L)
        _ = 1 * ‖L‖ := by ring)
  have hN : ContDiff ℝ 5 N := by
    exact (input.contDiff.fderiv_right (m := 5) (by norm_num)).clm_apply contDiff_const
  have hp := precompose.norm_iteratedFDeriv_comp_left (x := z)
    ((hN.fderiv_right (m := 4) (by norm_num)).contDiffAt)
    (by exact_mod_cast hq)
  have hinner := norm_iteratedFDeriv_clm_apply_const
    (f := fderiv ℝ input.function) (c := splitNormalDirection n) (x := z) (n := q + 1)
    ((input.contDiff.fderiv_right (m := 5) (by norm_num)).contDiffAt)
    (by exact_mod_cast Nat.succ_le_succ hq)
  calc
    ‖iteratedFDeriv ℝ q (implicitGraphNormalTangentialField input) z‖ ≤
        ‖precompose‖ * ‖iteratedFDeriv ℝ q (fderiv ℝ N) z‖ := by
      change ‖iteratedFDeriv ℝ q (precompose ∘ fderiv ℝ N) z‖ ≤ _
      simpa [precompose, T] using hp
    _ ≤ ‖iteratedFDeriv ℝ q (fderiv ℝ N) z‖ := by
      calc
        _ ≤ 1 * ‖iteratedFDeriv ℝ q (fderiv ℝ N) z‖ :=
          mul_le_mul_of_nonneg_right hprecompose (norm_nonneg _)
        _ = _ := one_mul _
    _ = ‖iteratedFDeriv ℝ (q + 1) N z‖ := by
      rw [norm_iteratedFDeriv_fderiv]
    _ ≤ ‖splitNormalDirection n‖ *
        ‖iteratedFDeriv ℝ (q + 1) (fderiv ℝ input.function) z‖ := by
      simpa [N] using hinner
    _ = ‖iteratedFDeriv ℝ (q + 2) input.function z‖ := by
      rw [norm_iteratedFDeriv_fderiv]
      simp [splitNormalDirection, Prod.norm_def]

end QuarticConvergence
end OptimalConvergenceRates

end
