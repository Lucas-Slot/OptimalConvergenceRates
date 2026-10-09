/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Analysis/FilterRotation.lean

  Quantitative finite-difference lemmas used to commute the spherical filter
  with rotations.  This module deliberately stays below `FinitePacking` in
  the import graph.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.Radial
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.ContinuousRootFilter
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Reflection
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Repair
import Mathlib.Analysis.Calculus.MeanValue

open Finset MeasureTheory MvPolynomial Set
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- A global Hessian bound gives a (deliberately non-sharp) first-order
Taylor remainder bound.  The factor `1`, rather than `1 / 2`, is convenient
for the later centered pullback estimate. -/
theorem norm_sub_sub_fderiv_le_of_global_hessian_bound
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → G} {M : ℝ} (hM : 0 ≤ M) (hF : ContDiff ℝ 2 F)
    (hessian : ∀ z, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ M)
    (x y : E) :
    ‖F y - F x - fderiv ℝ F x (y - x)‖ ≤ M * ‖y - x‖ ^ 2 := by
  have hDFdiff (u v : E) :
      ‖fderiv ℝ F v - fderiv ℝ F u‖ ≤ M * ‖v - u‖ := by
    exact convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ ((hF.fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num)).differentiableAt)
      (fun z _ ↦ hessian z) (Set.mem_univ u) (Set.mem_univ v)
  let H : E → G := fun z ↦ F z - fderiv ℝ F x z
  have hHdiff : Differentiable ℝ H := by
    exact (hF.differentiable (by norm_num)).sub (fderiv ℝ F x).differentiable
  have hHderiv (z : E) :
      fderiv ℝ H z = fderiv ℝ F z - fderiv ℝ F x := by
    dsimp [H]
    simpa using (((hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt).sub
      (fderiv ℝ F x).hasFDerivAt).fderiv
  have hHbound : ∀ z ∈ segment ℝ x y,
      ‖fderiv ℝ H z‖ ≤ (M * ‖y - x‖) := by
    intro z hz
    rw [hHderiv]
    exact (hDFdiff x z).trans <| by
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

end QuarticConvergence
end OptimalConvergenceRates

end
