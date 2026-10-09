import Mathlib.Analysis.Normed.Group.Bounded
import OptimalConvergenceRates.CQC.PolynomialCalculus
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FilterRotationBounds

/-!
# Uniform Taylor bounds for polynomials on compact convex sets
-/

noncomputable section

open MvPolynomial Set

namespace OptimalConvergenceRates
namespace CQCInternal

/-- Polynomial evaluation has a uniform quadratic first-order remainder on
every compact convex set. -/
theorem exists_eval_taylor_bound {N : ℕ}
    (P : MvPolynomial (Fin N) ℝ) (A : Set (Fin N → ℝ))
    (hAcompact : IsCompact A) (hAconvex : Convex ℝ A) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ A, ∀ y ∈ A,
      |MvPolynomial.eval y P - MvPolynomial.eval x P -
          QuarticConvergence.mvPolynomialEvalFDeriv P x (y - x)| ≤
        L * ‖y - x‖ ^ 2 := by
  let F : (Fin N → ℝ) → ℝ := fun x ↦ MvPolynomial.eval x P
  have hF2 : ContDiff ℝ 2 F :=
    QuarticConvergence.mvPolynomial_eval_contDiff P 2
  have hDF1 : ContDiff ℝ 1 (fderiv ℝ F) :=
    hF2.fderiv_right (by norm_num)
  have hDDFcont : Continuous (fderiv ℝ (fderiv ℝ F)) :=
    hDF1.continuous_fderiv (by norm_num)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ x ∈ A,
      ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ B :=
    IsCompact.exists_bound_of_continuousOn
      (f := fderiv ℝ (fderiv ℝ F)) hAcompact hDDFcont.continuousOn
  let L := max B 0
  have hL : 0 ≤ L := le_max_right _ _
  have hsecond : ∀ x ∈ A, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ L := by
    intro x hx
    exact (hB x hx).trans (le_max_left _ _)
  have hDFdiff : ∀ x ∈ A, ∀ y ∈ A,
      ‖fderiv ℝ F y - fderiv ℝ F x‖ ≤ L * ‖y - x‖ := by
    intro x hx y hy
    exact hAconvex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ hDF1.differentiable (by norm_num) z)
      hsecond hx hy
  refine ⟨L, hL, ?_⟩
  intro x hx y hy
  have hseg : segment ℝ x y ⊆ A := hAconvex.segment_subset hx hy
  have hbound : ∀ z ∈ segment ℝ x y,
      ‖fderiv ℝ F z - fderiv ℝ F x‖ ≤ L * ‖y - x‖ := by
    intro z hz
    exact (hDFdiff x hx z (hseg hz)).trans <| by
      gcongr
      exact norm_sub_le_of_mem_segment hz
  have htaylor := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z _ ↦ hF2.differentiable (by norm_num) z |>.hasFDerivAt.hasFDerivWithinAt)
    hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have hfderiv (z : Fin N → ℝ) :
      fderiv ℝ F z = QuarticConvergence.mvPolynomialEvalFDeriv P z :=
    (QuarticConvergence.hasFDerivAt_mvPolynomial_eval P z).fderiv
  rw [hfderiv x] at htaylor
  change ‖F y - F x - QuarticConvergence.mvPolynomialEvalFDeriv P x (y - x)‖ ≤ _ at htaylor
  simpa [F, Real.norm_eq_abs, pow_two, mul_assoc] using htaylor

end CQCInternal
end OptimalConvergenceRates

end
