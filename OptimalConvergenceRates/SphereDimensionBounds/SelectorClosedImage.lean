import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.LinearMap
/-! Finite-dimensional closed-image lemmas used by `SelectorExistence`
to construct the polynomial selector. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.SelectorClosedImage

open Set Filter Topology

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A closed cone on which a linear map has trivial kernel has a uniform
lower norm bound. Convexity is not needed. -/
theorem cone_norm_bound (C : Set E) (hC : IsClosed C)
    (hscale : ∀ x ∈ C, ∀ t : ℝ, 0 < t → t • x ∈ C)
    (L : E →L[ℝ] F) (hker : ∀ x ∈ C, L x = 0 → x = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ x ∈ C, ‖x‖ ≤ K * ‖L x‖ := by
  have hc : IsCompact (C ∩ Metric.sphere (0 : E) 1) :=
    (isCompact_sphere (0 : E) 1).inter_left hC
  obtain ⟨d, hd, hmin⟩ := hc.exists_forall_le'
    L.continuous.norm.continuousOn (a := 0) (by
      intro x hx
      exact norm_pos_iff.mpr (by
        intro hz
        have hx0 := hker x hx.1 hz
        have hn : ‖x‖ = 1 := by simpa using hx.2
        simp [hx0] at hn))
  refine ⟨d⁻¹, inv_pos.mpr hd, ?_⟩
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hunit : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnx.le), inv_mul_cancel₀ hnx.ne']
  have hlow := hmin ((‖x‖⁻¹ : ℝ) • x)
    ⟨hscale x hx _ (inv_pos.mpr hnx), by simpa using hunit⟩
  rw [L.map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnx.le)] at hlow
  have hprod : d * ‖x‖ ≤ ‖L x‖ := by
    have h := mul_le_mul_of_nonneg_right hlow hnx.le
    convert h using 1
    field_simp
  exact (le_inv_mul_iff₀ hd).mpr hprod

/-- A uniform norm bound on a closed set suffices for closedness of its
linear image. This does not assert that every closed cone has closed image. -/
theorem isClosed_image_of_norm_bound (C : Set E) (hC : IsClosed C)
    (L : E →L[ℝ] F) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x ∈ C, ‖x‖ ≤ K * ‖L x‖) : IsClosed (L '' C) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u y hu huy
  choose x hx hLx using hu
  obtain ⟨R, hR⟩ := huy.cauchySeq.isBounded_range.exists_norm_le
  have hxball : ∀ k, x k ∈ Metric.closedBall (0 : E) (K * R) := by
    intro k
    have hr : ‖L (x k)‖ ≤ R := by simpa [hLx k] using hR (u k) (mem_range_self k)
    have hn := (hbound (x k) (hx k)).trans (mul_le_mul_of_nonneg_left hr hK)
    simpa using hn
  obtain ⟨z, _, φ, hφ, hz⟩ := (isCompact_closedBall (0 : E) (K * R)).isSeqCompact
    (x := x) hxball
  have hzC : z ∈ C := hC.mem_of_tendsto hz (Eventually.of_forall (fun k => hx (φ k)))
  refine ⟨z, hzC, ?_⟩
  apply tendsto_nhds_unique (L.continuous.tendsto z |>.comp hz)
  have heq : (fun k => L (x (φ k))) = u ∘ φ := by
    funext k
    exact hLx (φ k)
  change Tendsto (fun k => L (x (φ k))) atTop (𝓝 y)
  rw [heq]
  exact huy.comp hφ.tendsto_atTop

/-- In finite dimensions, a closed cone has closed linear image whenever
its intersection with the kernel is trivial. -/
theorem isClosed_image_of_conic_trivial_kernel (C : Set E) (hC : IsClosed C)
    (hscale : ∀ x ∈ C, ∀ t : ℝ, 0 < t → t • x ∈ C)
    (L : E →L[ℝ] F) (hker : ∀ x ∈ C, L x = 0 → x = 0) :
    IsClosed (L '' C) := by
  obtain ⟨K, hK, hbound⟩ := cone_norm_bound C hC hscale L hker
  exact isClosed_image_of_norm_bound C hC L hK.le hbound

end OptimalConvergenceRates.SphereDimensionBounds.SelectorClosedImage
