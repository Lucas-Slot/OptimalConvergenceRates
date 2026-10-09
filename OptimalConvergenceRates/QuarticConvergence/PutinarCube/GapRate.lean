/-
  Exact quartic Putinar rate stated as a hierarchy gap from the cube minimum.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.ExactRate

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- The corner witness has minimum zero on the two-dimensional cube. -/
theorem polyMin_f_zero_eq_zero : polyMin f_zero = 0 := by
  rw [f_zero_eq]
  apply le_antisymm
  · have h := polyMin_le_eval (f_eps 0) corner_11 corner_11_in_hypercube
    rw [f_eps_eval_corner] at h
    exact h
  · obtain ⟨x, hx, hmin⟩ := polyMin_mem (f_eps 0)
    rw [← hmin]
    exact f_eps_nonneg_on_hypercube 0 (by norm_num) x hx

/-- Exact quartic Putinar rate, phrased directly as the error between the
true cube minimum and the finite real hierarchy value. -/
theorem putinarCubeHierarchyExactQuarticGap :
    ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      ∃ b : ℝ,
        lasserre_bound_box_qm f_zero r = (b : WithBot ℝ) ∧
        (improvedLowerBoundConst / (r : ℝ)) ^ 4 ≤ polyMin f_zero - b ∧
        polyMin f_zero - b ≤ ((8 : ℝ) / (r : ℝ)) ^ 4 := by
  obtain ⟨r₀, hr₀, hrate⟩ := putinarCubeExactQuarticRate
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr
  obtain ⟨b, hb, hlower, hupper⟩ := hrate r hr
  exact ⟨b, hb, by simpa [polyMin_f_zero_eq_zero] using hlower,
    by simpa [polyMin_f_zero_eq_zero] using hupper⟩

end QuarticConvergence
end OptimalConvergenceRates

end
