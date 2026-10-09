/-
  Composition bounds for the normal Hessian fields along an implicit minimizing graph.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.ImplicitGraphJetRecurrence

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

private theorem norm_multilinear_prod_le_max
    {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : ContinuousMultilinearMap ℝ E F) (g : ContinuousMultilinearMap ℝ E G) :
    ‖f.prod g‖ ≤ max ‖f‖ ‖g‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound
    (le_trans (norm_nonneg f) (le_max_left _ _))
  intro m
  rw [ContinuousMultilinearMap.prod_apply, Prod.norm_def]
  apply max_le
  · exact (f.le_opNorm m).trans
      (mul_le_mul_of_nonneg_right (le_max_left ‖f‖ ‖g‖) (by positivity))
  · exact (g.le_opNorm m).trans
      (mul_le_mul_of_nonneg_right (le_max_right ‖f‖ ‖g‖) (by positivity))

private theorem norm_iteratedFDeriv_id_le_one
    {n q : ℕ} (y : Fin n → ℝ) (hqOne : 1 ≤ q) (hq : q ≤ 5) :
    ‖iteratedFDeriv ℝ q (fun w : Fin n → ℝ ↦ w) y‖ ≤ 1 := by
  have hfd : fderiv ℝ (fun w : Fin n → ℝ ↦ w) =
      fun _ ↦ ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
    funext w
    rw [fderiv_id']
  interval_cases q
  · rw [norm_iteratedFDeriv_one, hfd]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simp
  · rw [← norm_iteratedFDeriv_fderiv (n := 1), hfd, iteratedFDeriv_const_of_ne (by norm_num)]
    simp
  · rw [← norm_iteratedFDeriv_fderiv (n := 2), hfd, iteratedFDeriv_const_of_ne (by norm_num)]
    simp
  · rw [← norm_iteratedFDeriv_fderiv (n := 3), hfd, iteratedFDeriv_const_of_ne (by norm_num)]
    simp
  · rw [← norm_iteratedFDeriv_fderiv (n := 4), hfd, iteratedFDeriv_const_of_ne (by norm_num)]
    simp

theorem implicitGraphLift_contDiff {n : ℕ} {input : NormalizedLocalSplitInput n}
    (graph : MinimizingGraphData input) :
    ContDiff ℝ 5 (implicitGraphLift graph) :=
  graph.graph_contDiff.prodMk contDiff_id

/-- A common jet bound for the graph yields the power-form jet bound for its product lift
required by the higher chain rule. -/
theorem norm_iteratedFDeriv_implicitGraphLift_le
    {n q : ℕ} {input : NormalizedLocalSplitInput n}
    (graph : MinimizingGraphData input) (y : Fin n → ℝ) {B : ℝ}
    (hB : 1 ≤ B)
    (hgraph : ∀ k, 1 ≤ k → k ≤ q →
      ‖iteratedFDeriv ℝ k graph.graph y‖ ≤ B)
    (hqOne : 1 ≤ q) (hq : q ≤ 5) :
    ‖iteratedFDeriv ℝ q (implicitGraphLift graph) y‖ ≤ B ^ q := by
  change ‖iteratedFDeriv ℝ q (fun w ↦ (graph.graph w, w)) y‖ ≤ B ^ q
  have hprod := iteratedFDeriv_prodMk (x := y) (i := q)
    graph.graph_contDiff.contDiffAt contDiff_id.contDiffAt
      (by exact_mod_cast hq)
  change iteratedFDeriv ℝ q (fun w ↦ (graph.graph w, w)) y = _ at hprod
  rw [hprod]
  calc
    ‖(iteratedFDeriv ℝ q graph.graph y).prod
        (iteratedFDeriv ℝ q (fun w : Fin n → ℝ ↦ w) y)‖ ≤
        max ‖iteratedFDeriv ℝ q graph.graph y‖
          ‖iteratedFDeriv ℝ q (fun w : Fin n → ℝ ↦ w) y‖ :=
      norm_multilinear_prod_le_max _ _
    _ ≤ B := max_le (hgraph q hqOne le_rfl)
      ((norm_iteratedFDeriv_id_le_one y hqOne hq).trans hB)
    _ = B ^ 1 := by ring
    _ ≤ B ^ q := pow_le_pow_right₀ hB hqOne

-- The lower bound on M is retained for the common chain-rule interface.
set_option linter.unusedVariables false in
/-- Quantitative chain-rule bound for the normal curvature along the graph. -/
theorem norm_iteratedFDeriv_normalCurvature_comp_graph_le
    {n q : ℕ} {input : NormalizedLocalSplitInput n}
    (graph : MinimizingGraphData input) (y : Fin n → ℝ) {M B : ℝ}
    (hM : 1 ≤ M) (hB : 1 ≤ B)
    (hambient : ∀ k, k ≤ 6 →
      ‖iteratedFDeriv ℝ k input.function (implicitGraphLift graph y)‖ ≤ M)
    (hgraph : ∀ k, 1 ≤ k → k ≤ q →
      ‖iteratedFDeriv ℝ k graph.graph y‖ ≤ B)
    (hq : q ≤ 4) :
    ‖iteratedFDeriv ℝ q
      (fun w ↦ implicitGraphNormalCurvatureField input (implicitGraphLift graph w)) y‖ ≤
        q.factorial * M * B ^ q := by
  have hcomp := norm_iteratedFDeriv_comp_le (N := 4)
    (implicitGraphNormalCurvatureField_contDiff input)
    ((implicitGraphLift_contDiff graph).of_le (by norm_num)) (by exact_mod_cast hq) y
    (C := M) (D := B)
    (fun i hi ↦
      (norm_iteratedFDeriv_implicitGraphNormalCurvatureField_le input
        (by omega : i ≤ 4) (implicitGraphLift graph y)).trans
          (hambient (i + 2) (by omega)))
    (fun i hiOne hi ↦
      norm_iteratedFDeriv_implicitGraphLift_le graph y hB
        (fun k hkOne hki ↦ hgraph k hkOne (hki.trans hi)) hiOne
        ((hi.trans hq).trans (by norm_num : 4 ≤ 5)))
  simpa only [Function.comp_apply] using hcomp

-- The lower bound on M is retained for the common chain-rule interface.
set_option linter.unusedVariables false in
/-- Quantitative chain-rule bound for the mixed normal-tangential Hessian along the graph. -/
theorem norm_iteratedFDeriv_normalTangential_comp_graph_le
    {n q : ℕ} {input : NormalizedLocalSplitInput n}
    (graph : MinimizingGraphData input) (y : Fin n → ℝ) {M B : ℝ}
    (hM : 1 ≤ M) (hB : 1 ≤ B)
    (hambient : ∀ k, k ≤ 6 →
      ‖iteratedFDeriv ℝ k input.function (implicitGraphLift graph y)‖ ≤ M)
    (hgraph : ∀ k, 1 ≤ k → k ≤ q →
      ‖iteratedFDeriv ℝ k graph.graph y‖ ≤ B)
    (hq : q ≤ 4) :
    ‖iteratedFDeriv ℝ q
      (fun w ↦ implicitGraphNormalTangentialField input (implicitGraphLift graph w)) y‖ ≤
        q.factorial * M * B ^ q := by
  have hcomp := norm_iteratedFDeriv_comp_le (N := 4)
    (implicitGraphNormalTangentialField_contDiff input)
    ((implicitGraphLift_contDiff graph).of_le (by norm_num)) (by exact_mod_cast hq) y
    (C := M) (D := B)
    (fun i hi ↦
      (norm_iteratedFDeriv_implicitGraphNormalTangentialField_le input
        (by omega : i ≤ 4) (implicitGraphLift graph y)).trans
          (hambient (i + 2) (by omega)))
    (fun i hiOne hi ↦
      norm_iteratedFDeriv_implicitGraphLift_le graph y hB
        (fun k hkOne hki ↦ hgraph k hkOne (hki.trans hi)) hiOne
        ((hi.trans hq).trans (by norm_num : 4 ≤ 5)))
  simpa only [Function.comp_apply] using hcomp

end QuarticConvergence
end OptimalConvergenceRates

end
