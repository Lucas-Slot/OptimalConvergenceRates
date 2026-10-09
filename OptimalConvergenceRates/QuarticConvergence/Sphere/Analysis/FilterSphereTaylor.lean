/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Analysis/FilterSphereTaylor.lean

  Ambient Taylor control of an axial second difference on the sphere.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FilterRotation

open Finset Set

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

/-- Every point of the algebraic unit sphere has product norm at most one. -/
theorem norm_coe_sphereSet_le_one {n : ℕ} (x : sphereSet n) :
    ‖x.1‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro i
  rw [Real.norm_eq_abs, abs_le]
  have hxsum : ∑ j, x.1 j ^ 2 = 1 := by
    simpa [sphereSet, sphereQuadratic, pow_two] using x.2
  have hxi : x.1 i ^ 2 ≤ 1 := by
    rw [← hxsum]
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (x.1 j))
      (Finset.mem_univ i)
  constructor <;> nlinarith [sq_nonneg (x.1 i - 1), sq_nonneg (x.1 i + 1)]

/-- Product distance between sphere points is bounded by the square root of
their chordal square. -/
theorem norm_sub_le_sqrt_sphereChordalSq {n : ℕ} (y x : sphereSet n) :
    ‖y.1 - x.1‖ ≤ Real.sqrt (sphereChordalSq y.1 x.1) := by
  rw [← dist_eq_norm]
  apply dist_le_of_sphereChordalSq_le_sq (Real.sqrt_nonneg _)
  exact (Real.sq_sqrt (sphereChordalSq_nonneg y.1 x.1)).ge

/-- Squaring the preceding product-distance estimate removes the square root. -/
theorem norm_sub_sq_le_sphereChordalSq {n : ℕ} (y x : sphereSet n) :
    ‖y.1 - x.1‖ ^ 2 ≤ sphereChordalSq y.1 x.1 := by
  have h := pow_le_pow_left₀ (norm_nonneg (y.1 - x.1))
    (norm_sub_le_sqrt_sphereChordalSq y x) 2
  simpa [Real.sq_sqrt (sphereChordalSq_nonneg y.1 x.1)] using h

/-- The two reflected displacement vectors fail to cancel by exactly the
radial chordal-square term. -/
theorem sphereAxialReflection_displacements_add {n : ℕ} (x y : sphereSet n) :
    (y.1 - x.1) + ((sphereAxialReflection x y).1 - x.1) =
      (-sphereChordalSq y.1 x.1) • x.1 := by
  funext i
  rw [sphereAxialReflection_coe]
  unfold sphereAxialReflectionRaw
  rw [sphereChordalSq_eq_two_mul_one_sub_dot y.2 x.2]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- A Hessian bound on the closed unit ball gives a Taylor remainder bound
between any two points of that ball. -/
theorem norm_sub_sub_fderiv_le_of_unitBall_hessian_bound
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → G} {M : ℝ} (hM : 0 ≤ M) (hF : ContDiff ℝ 2 F)
    (hessian : ∀ z, ‖z‖ ≤ 1 → ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ M)
    {x y : E} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖F y - F x - fderiv ℝ F x (y - x)‖ ≤ M * ‖y - x‖ ^ 2 := by
  let s : Set E := Metric.closedBall 0 1
  have hmem (z : E) (hz : ‖z‖ ≤ 1) : z ∈ s := by
    simpa [s, Metric.mem_closedBall, dist_eq_norm] using hz
  have hDFdiff (u v : E) (hu : u ∈ s) (hv : v ∈ s) :
      ‖fderiv ℝ F v - fderiv ℝ F u‖ ≤ M * ‖v - u‖ := by
    have hbound : ∀ z ∈ s, ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ M := by
      intro z hz
      apply hessian z
      simpa [s, Metric.mem_closedBall, dist_eq_norm] using hz
    exact (convex_closedBall (0 : E) 1).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ ((hF.fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num)).differentiableAt)
      hbound hu hv
  let H : E → G := fun z ↦ F z - fderiv ℝ F x z
  have hHdiff : Differentiable ℝ H := by
    exact (hF.differentiable (by norm_num)).sub (fderiv ℝ F x).differentiable
  have hHderiv (z : E) :
      fderiv ℝ H z = fderiv ℝ F z - fderiv ℝ F x := by
    dsimp [H]
    simpa using (((hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt).sub
      (fderiv ℝ F x).hasFDerivAt).fderiv
  have hHbound : ∀ z ∈ segment ℝ x y,
      ‖fderiv ℝ H z‖ ≤ M * ‖y - x‖ := by
    intro z hz
    rw [hHderiv]
    have hzball : z ∈ s :=
      (convex_closedBall (0 : E) 1).segment_subset (hmem x hx) (hmem y hy) hz
    exact (hDFdiff x z (hmem x hx) hzball).trans <| by
      gcongr
      exact norm_sub_le_of_mem_segment hz
  have hmean := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
    (s := segment ℝ x y) (x := x) (y := y) (C := M * ‖y - x‖)
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

/-- Unit-ball first- and second-derivative bounds control the axial symmetric
second difference of an ambient function by chordal distance squared. The
coarse factor four is dimension-free for the repository's product norm. -/
theorem abs_ambient_sphereAxial_secondDifference_le
    {n : ℕ} {F : (Fin n → ℝ) → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hF : ContDiff ℝ 2 F)
    (hFone : ∀ z, ‖z‖ ≤ 1 → ‖fderiv ℝ F z‖ ≤ M)
    (hFtwo : ∀ z, ‖z‖ ≤ 1 → ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ M)
    (x y : sphereSet n) :
    |F y.1 + F (sphereAxialReflection x y).1 - 2 * F x.1| ≤
      4 * M * sphereChordalSq y.1 x.1 := by
  let yr := (sphereAxialReflection x y).1
  let remY := F y.1 - F x.1 - fderiv ℝ F x.1 (y.1 - x.1)
  let remR := F yr - F x.1 - fderiv ℝ F x.1 (yr - x.1)
  have hremY : ‖remY‖ ≤ M * sphereChordalSq y.1 x.1 := by
    apply (norm_sub_sub_fderiv_le_of_unitBall_hessian_bound
      hM hF hFtwo (norm_coe_sphereSet_le_one x)
        (norm_coe_sphereSet_le_one y)).trans
    exact mul_le_mul_of_nonneg_left (norm_sub_sq_le_sphereChordalSq y x) hM
  have hreflectChord :
      sphereChordalSq yr x.1 = sphereChordalSq y.1 x.1 := by
    exact sphereChordalSq_sphereAxialReflection x y
  have hyrMem : yr ∈ sphereSet n := (sphereAxialReflection x y).2
  have hremR : ‖remR‖ ≤ M * sphereChordalSq y.1 x.1 := by
    apply (norm_sub_sub_fderiv_le_of_unitBall_hessian_bound
      hM hF hFtwo (norm_coe_sphereSet_le_one x)
        (norm_coe_sphereSet_le_one ⟨yr, hyrMem⟩)).trans
    have hsq := norm_sub_sq_le_sphereChordalSq ⟨yr, hyrMem⟩ x
    rw [hreflectChord] at hsq
    exact mul_le_mul_of_nonneg_left hsq hM
  have hlinear :
      ‖fderiv ℝ F x.1 ((y.1 - x.1) + (yr - x.1))‖ ≤
        M * sphereChordalSq y.1 x.1 := by
    calc
      _ ≤ ‖fderiv ℝ F x.1‖ * ‖(y.1 - x.1) + (yr - x.1)‖ :=
        (fderiv ℝ F x.1).le_opNorm _
      _ ≤ M * ‖(y.1 - x.1) + (yr - x.1)‖ :=
        mul_le_mul_of_nonneg_right
          (hFone x.1 (norm_coe_sphereSet_le_one x)) (norm_nonneg _)
      _ = M * (sphereChordalSq y.1 x.1 * ‖x.1‖) := by
        rw [sphereAxialReflection_displacements_add]
        simp only [norm_smul, Real.norm_eq_abs, abs_neg,
          abs_of_nonneg (sphereChordalSq_nonneg y.1 x.1)]
      _ ≤ M * (sphereChordalSq y.1 x.1 * 1) := by
        apply mul_le_mul_of_nonneg_left _ hM
        exact mul_le_mul_of_nonneg_left (norm_coe_sphereSet_le_one x)
          (sphereChordalSq_nonneg y.1 x.1)
      _ = M * sphereChordalSq y.1 x.1 := by ring
  have hexpand :
      F y.1 + F yr - 2 * F x.1 =
        remY + remR +
          fderiv ℝ F x.1 ((y.1 - x.1) + (yr - x.1)) := by
    dsimp [remY, remR]
    rw [map_add]
    ring
  rw [hexpand, ← Real.norm_eq_abs]
  calc
    ‖remY + remR + fderiv ℝ F x.1 ((y.1 - x.1) + (yr - x.1))‖ ≤
        ‖remY‖ + ‖remR‖ +
          ‖fderiv ℝ F x.1 ((y.1 - x.1) + (yr - x.1))‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le remY remR) le_rfl)
    _ ≤ M * sphereChordalSq y.1 x.1 +
        M * sphereChordalSq y.1 x.1 +
          M * sphereChordalSq y.1 x.1 := by gcongr
    _ ≤ 4 * M * sphereChordalSq y.1 x.1 := by
      have hchord := sphereChordalSq_nonneg y.1 x.1
      nlinarith [mul_nonneg hM hchord]

end QuarticConvergence
end OptimalConvergenceRates

end
