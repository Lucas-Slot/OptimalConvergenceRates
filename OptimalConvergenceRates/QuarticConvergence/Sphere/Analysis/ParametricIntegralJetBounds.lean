/-
  Quantitative differentiation under a fixed compact parameter integral.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.UniformSplit

open Set
open Filter
open MeasureTheory

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence


variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The derivative in the finite-dimensional parameter, leaving the integration variable fixed. -/
def parameterFDeriv (g : (D × ℝ) → F) (p : D × ℝ) : D →L[ℝ] F :=
  (fderiv ℝ g p).comp (ContinuousLinearMap.inl ℝ D ℝ)

omit [FiniteDimensional ℝ D] [CompleteSpace F] in
theorem parameterFDeriv_contDiff {m : ℕ} {g : (D × ℝ) → F}
    (hg : ContDiff ℝ (m + 1) g) :
    ContDiff ℝ m (parameterFDeriv g) := by
  let inl : D →L[ℝ] (D × ℝ) := ContinuousLinearMap.inl ℝ D ℝ
  let precompose : (((D × ℝ) →L[ℝ] F) →L[ℝ] (D →L[ℝ] F)) :=
    (ContinuousLinearMap.compL ℝ D (D × ℝ) F).flip inl
  exact precompose.contDiff.comp
    (hg.fderiv_right (m := m) (by norm_num))

omit [FiniteDimensional ℝ D] [CompleteSpace F] in
theorem parameterFDeriv_eq_fderiv_section {g : (D × ℝ) → F}
    (hg : ContDiff ℝ 1 g) (x : D) (t : ℝ) :
    parameterFDeriv g (x, t) = fderiv ℝ (fun y : D ↦ g (y, t)) x := by
  let inl : D →L[ℝ] (D × ℝ) := ContinuousLinearMap.inl ℝ D ℝ
  have hembed : HasFDerivAt (fun y : D ↦ (y, t)) inl x := by
    fun_prop
  have hchain := (hg.differentiable (by norm_num) (x, t)).hasFDerivAt.comp x hembed
  simpa [parameterFDeriv, inl, Function.comp_def] using hchain.fderiv.symm

omit [CompleteSpace F] in
/-- Differentiation under the fixed compact integral, with the derivative expressed by
`parameterFDeriv`. -/
theorem hasFDerivAt_setIntegral_Icc {g : (D × ℝ) → F}
    (hg : ContDiff ℝ 1 g) (x₀ : D) :
    HasFDerivAt
      (fun x : D ↦ ∫ t in Set.Icc (0 : ℝ) 1, g (x, t))
      (∫ t in Set.Icc (0 : ℝ) 1, parameterFDeriv g (x₀, t)) x₀ := by
  let F₀ : D → ℝ → F := fun x t ↦ g (x, t)
  let F' : D → ℝ → D →L[ℝ] F := fun x t ↦ parameterFDeriv g (x, t)
  have hF'cont : Continuous (Function.uncurry F') := by
    exact (parameterFDeriv_contDiff (m := 0) hg).continuous
  have hcompact : IsCompact (Metric.closedBall x₀ 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    (isCompact_closedBall x₀ 1).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image hF'cont.norm.continuousOn
  have hbound : ∀ x ∈ Metric.closedBall x₀ 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖F' x t‖ ≤ C := by
    intro x hx t ht
    apply hC
    exact ⟨(x, t), ⟨hx, ht⟩, rfl⟩
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := F₀) (F' := F') (x₀ := x₀)
    (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
    (s := Metric.closedBall x₀ 1) (bound := fun _ ↦ C)
  · exact Metric.closedBall_mem_nhds x₀ zero_lt_one
  · filter_upwards with x
    exact (hg.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hg.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
      |>.integrableOn_compact isCompact_Icc
  · exact (hF'cont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact fun x hx ↦ hbound x hx t ht
  · exact continuousOn_const.integrableOn_compact isCompact_Icc
  · refine Filter.Eventually.of_forall fun t x hx ↦ ?_
    simpa [F₀, F', parameterFDeriv, Function.comp_def] using
      (hg.differentiable (by norm_num) (x, t)).hasFDerivAt.comp x
        (show HasFDerivAt (fun y : D ↦ (y, t))
            (ContinuousLinearMap.inl ℝ D ℝ) x by fun_prop)

/-- A unit-length fixed parameter integral does not enlarge a uniform bound on any iterated
parameter derivative.  This is the quantitative companion to `contDiff_setIntegral_Icc`. -/
theorem norm_iteratedFDeriv_setIntegral_Icc_le (m : ℕ)
    {g : (D × ℝ) → F} (hg : ContDiff ℝ m g) (x : D) {M : ℝ}
    (hM : 0 ≤ M)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ m (fun y : D ↦ g (y, t)) x‖ ≤ M) :
    ‖iteratedFDeriv ℝ m
      (fun y : D ↦ ∫ t in Set.Icc (0 : ℝ) 1, g (y, t)) x‖ ≤ M := by
  induction m generalizing F g with
  | zero =>
      rw [norm_iteratedFDeriv_zero]
      have hnorm := MeasureTheory.norm_integral_le_of_norm_le_const
        (G := F) (C := M) (f := fun t : ℝ ↦ g (x, t))
        (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
        (by
          filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          simpa [norm_iteratedFDeriv_zero] using hbound t ht)
      calc
        _ ≤ |M| := by
          simpa [abs_of_nonneg hM, Measure.restrict_apply_univ,
            Real.volume_real_Icc_of_le zero_le_one] using hnorm
        _ = M := abs_of_nonneg hM
  | succ m ih =>
      let dg : (D × ℝ) → (D →L[ℝ] F) := parameterFDeriv g
      have hgSucc : ContDiff ℝ (m + 1) g := by
        simpa [Nat.succ_eq_add_one] using hg
      have hdg : ContDiff ℝ m dg := parameterFDeriv_contDiff hgSucc
      have hfirst : fderiv ℝ
          (fun y : D ↦ ∫ t in Set.Icc (0 : ℝ) 1, g (y, t)) =
          fun y : D ↦ ∫ t in Set.Icc (0 : ℝ) 1, dg (y, t) := by
        funext y
        exact (hasFDerivAt_setIntegral_Icc
          (hgSucc.of_le (by norm_num)) y).fderiv
      rw [← norm_iteratedFDeriv_fderiv (n := m), hfirst]
      apply ih hdg
      intro t ht
      have heq : (fun y : D ↦ dg (y, t)) =
          fderiv ℝ (fun y : D ↦ g (y, t)) := by
        funext y
        exact parameterFDeriv_eq_fderiv_section
          (hgSucc.of_le (by norm_num)) y t
      rw [heq, norm_iteratedFDeriv_fderiv]
      simpa [Nat.succ_eq_add_one] using hbound t ht

end QuarticConvergence
end OptimalConvergenceRates

end
