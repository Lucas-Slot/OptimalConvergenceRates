/- Pullback actions on iterated derivative tensors. -/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FilterRotationBounds

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- Pullback of a homogeneous iterated derivative by a continuous linear map,
bundled as a continuous linear map in the derivative tensor. -/
noncomputable def iteratedDerivativePullbackAction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : ℕ) (L : E →L[ℝ] E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) ℝ →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) ℝ :=
  ContinuousMultilinearMap.compContinuousLinearMapL (fun _ ↦ L)

@[simp] theorem iteratedDerivativePullbackAction_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : ℕ) (L : E →L[ℝ] E)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) ℝ) :
    iteratedDerivativePullbackAction j L A =
      A.compContinuousLinearMap (fun _ ↦ L) := rfl

theorem norm_iteratedDerivativePullbackAction_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : ℕ) (L : E →L[ℝ] E) :
    ‖iteratedDerivativePullbackAction j L‖ ≤ ‖L‖ ^ j := by
  simpa [iteratedDerivativePullbackAction] using
    (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
      (G := ℝ) (fun _ : Fin j ↦ L))

@[simp] theorem iteratedDerivativePullbackAction_id
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (j : ℕ) :
    iteratedDerivativePullbackAction j (ContinuousLinearMap.id ℝ E) =
      ContinuousLinearMap.id ℝ
        (ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) ℝ) := by
  ext A m
  simp [iteratedDerivativePullbackAction]

theorem iteratedDerivativePullbackAction_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : ℕ) (L R : E →L[ℝ] E) :
    (iteratedDerivativePullbackAction j L).comp
        (iteratedDerivativePullbackAction j R) =
      iteratedDerivativePullbackAction j (R.comp L) := by
  ext A m
  simp [iteratedDerivativePullbackAction]

/-- For derivative orders at most two, the induced tensor pullback is
Lipschitz in the underlying linear map with a dimension-free coarse factor. -/
theorem norm_iteratedDerivativePullbackAction_sub_id_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {j : ℕ} (hj : j ≤ 2) (L : E →L[ℝ] E) {C d : ℝ}
    (hC : 1 ≤ C) (hL : ‖L‖ ≤ C)
    (hLd : ‖L - ContinuousLinearMap.id ℝ E‖ ≤ d) :
    ‖iteratedDerivativePullbackAction j L -
        ContinuousLinearMap.id ℝ
          (ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) ℝ)‖ ≤
      2 * C * d := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hd : 0 ≤ d := (norm_nonneg _).trans hLd
  interval_cases j
  · have hzero :
        iteratedDerivativePullbackAction 0 L =
          ContinuousLinearMap.id ℝ
            (ContinuousMultilinearMap ℝ (fun _ : Fin 0 ↦ E) ℝ) := by
      ext A m
      simp only [iteratedDerivativePullbackAction,
        ContinuousMultilinearMap.compContinuousLinearMapL_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearMap.coe_id',
        id_eq]
      congr 1
      funext i
      exact Fin.elim0 i
    rw [hzero]
    calc
      _ = 0 := by
        rw [sub_self]
        exact @norm_zero
          (ContinuousMultilinearMap ℝ (fun _ : Fin 0 ↦ E) ℝ →L[ℝ]
            ContinuousMultilinearMap ℝ (fun _ : Fin 0 ↦ E) ℝ) inferInstance
      _ ≤ _ := mul_nonneg (mul_nonneg (by norm_num) hC0) hd
  · have heq :
        iteratedDerivativePullbackAction 1 L -
            ContinuousLinearMap.id ℝ
              (ContinuousMultilinearMap ℝ (fun _ : Fin 1 ↦ E) ℝ) =
          ContinuousMultilinearMap.compContinuousLinearMapL
            (fun _ : Fin 1 ↦ L - ContinuousLinearMap.id ℝ E) := by
      ext A m
      simp only [iteratedDerivativePullbackAction, FunLike.coe_sub,
        ContinuousLinearMap.coe_id', Pi.sub_apply,
        ContinuousMultilinearMap.compContinuousLinearMapL_apply, id_eq,
        sub_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
      have h := (A.map_update_sub m 0 (L (m 0)) (m 0)).symm
      convert h using 1
      · congr 1
        · congr 1
          funext i
          fin_cases i
          simp
        · congr 1
          funext i
          fin_cases i
          simp
      · congr 1
        funext i
        fin_cases i
        simp
    rw [heq]
    have hnorm :
        ‖(ContinuousMultilinearMap.compContinuousLinearMapL
          (fun _ : Fin 1 ↦ L - ContinuousLinearMap.id ℝ E) :
            ContinuousMultilinearMap ℝ (fun _ : Fin 1 ↦ E) ℝ →L[ℝ]
              ContinuousMultilinearMap ℝ (fun _ : Fin 1 ↦ E) ℝ)‖ ≤
          ‖L - ContinuousLinearMap.id ℝ E‖ := by
      calc
        _ ≤ ∏ _ : Fin 1, ‖L - ContinuousLinearMap.id ℝ E‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
            (G := ℝ) (fun _ : Fin 1 ↦ L - ContinuousLinearMap.id ℝ E)
        _ = _ := by simp
    exact hnorm.trans (hLd.trans (by nlinarith [mul_nonneg hC0 hd]))
  · let S₀ : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ :=
        ContinuousMultilinearMap.compContinuousLinearMapL
          ![L - ContinuousLinearMap.id ℝ E, L]
    let S₁ : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ :=
        ContinuousMultilinearMap.compContinuousLinearMapL
          ![ContinuousLinearMap.id ℝ E, L - ContinuousLinearMap.id ℝ E]
    have heq :
        iteratedDerivativePullbackAction 2 L -
            ContinuousLinearMap.id ℝ
              (ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ) = S₀ + S₁ := by
      ext A m
      simp only [iteratedDerivativePullbackAction, FunLike.coe_sub,
        ContinuousLinearMap.coe_id', Pi.sub_apply,
        ContinuousMultilinearMap.compContinuousLinearMapL_apply, id_eq,
        sub_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply, add_apply,
        add_apply, S₀, S₁]
      let lm : Fin 2 → E := fun i => L (m i)
      let mid : Fin 2 → E := Function.update lm 0 (m 0)
      have hll : Function.update lm 0 (L (m 0)) = lm := by
        funext i
        fin_cases i <;> simp [lm]
      have hmm : Function.update m 1 (m 1) = m := by
        funext i
        fin_cases i <;> simp
      have hmid : Function.update m 1 (L (m 1)) = mid := by
        funext i
        fin_cases i <;> simp [lm, mid]
      have h0 : A lm - A mid =
          A (Function.update lm 0 (L (m 0) - m 0)) := by
        rw [A.map_update_sub, hll]
      have h1 : A mid - A m =
          A (Function.update m 1 (L (m 1) - m 1)) := by
        rw [A.map_update_sub, hmid, hmm]
      calc
        A lm - A m = (A lm - A mid) + (A mid - A m) := by abel
        _ = A (Function.update lm 0 (L (m 0) - m 0)) +
            A (Function.update m 1 (L (m 1) - m 1)) := by rw [h0, h1]
        _ = (A fun i => (![L - ContinuousLinearMap.id ℝ E, L] i) (m i)) +
            A (fun i => (![ContinuousLinearMap.id ℝ E,
              L - ContinuousLinearMap.id ℝ E] i) (m i)) := by
          congr 1
          · congr 1
            funext i
            fin_cases i <;> simp [lm]
          · congr 1
            funext i
            fin_cases i <;> simp
    rw [heq]
    have hS0 : ‖S₀‖ ≤ ‖L - ContinuousLinearMap.id ℝ E‖ * ‖L‖ := by
      dsimp [S₀]
      simpa using
        (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
          (G := ℝ) ![L - ContinuousLinearMap.id ℝ E, L])
    have hS1 : ‖S₁‖ ≤ ‖L - ContinuousLinearMap.id ℝ E‖ := by
      dsimp [S₁]
      calc
        _ ≤ ∏ i : Fin 2,
            ‖![ContinuousLinearMap.id ℝ E,
              L - ContinuousLinearMap.id ℝ E] i‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
            (G := ℝ) ![ContinuousLinearMap.id ℝ E,
              L - ContinuousLinearMap.id ℝ E]
        _ ≤ 1 * ‖L - ContinuousLinearMap.id ℝ E‖ := by
          rw [Fin.prod_univ_two]
          change ‖ContinuousLinearMap.id ℝ E‖ *
            ‖L - ContinuousLinearMap.id ℝ E‖ ≤
              1 * ‖L - ContinuousLinearMap.id ℝ E‖
          exact mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le
            (norm_nonneg _)
        _ = _ := one_mul _
    calc
      ‖S₀ + S₁‖ ≤ ‖S₀‖ + ‖S₁‖ := norm_add_le S₀ S₁
      _ ≤ ‖L - ContinuousLinearMap.id ℝ E‖ * ‖L‖ +
          ‖L - ContinuousLinearMap.id ℝ E‖ := add_le_add hS0 hS1
      _ ≤ d * C + d := by gcongr
      _ ≤ 2 * C * d := by nlinarith [mul_nonneg hC0 hd]

end QuarticConvergence
end OptimalConvergenceRates

end
