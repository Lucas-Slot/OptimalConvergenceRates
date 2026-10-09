/-
  Exact quartic Schmüdgen rate stated as a hierarchy gap from the cube minimum.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.ExactRate

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- The Choi--Lam witness has minimum zero on the four-dimensional cube. -/
theorem polyMin_choiLamQuartic_eq_zero : polyMin choiLamQuartic = 0 := by
  apply le_antisymm
  · have h := polyMin_le_eval choiLamQuartic choiLamZeroDirection0
      choiLamZeroDirection0_mem_hypercube
    have hz : MvPolynomial.eval choiLamZeroDirection0 choiLamQuartic = 0 := by
      simpa [choiLamZeroDirection] using
        choiLamQuartic_zero_on_direction (0 : Fin 4)
    rw [hz] at h
    exact h
  · obtain ⟨x, _, hmin⟩ := polyMin_mem choiLamQuartic
    rw [← hmin]
    exact choiLamQuartic_nonneg_global x

/-- Exact quartic Schmüdgen rate, phrased directly as the error between the
true cube minimum and the finite real hierarchy value. -/
theorem schmudgenCubeHierarchyExactQuarticGap :
    ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      ∃ b : ℝ,
        lasserre_bound_box_preo choiLamQuartic r = (b : WithBot ℝ) ∧
        (schmInteriorLowerBoundConst4 / (r : ℝ)) ^ 4 ≤
          polyMin choiLamQuartic - b ∧
        polyMin choiLamQuartic - b ≤ ((24 : ℝ) / (r : ℝ)) ^ 4 := by
  obtain ⟨r₀, hr₀, hrate⟩ := schmudgenCubeExactQuarticRate
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr
  obtain ⟨b, hb, hlower, hupper⟩ := hrate r hr
  exact ⟨b, hb, by simpa [polyMin_choiLamQuartic_eq_zero] using hlower,
    by simpa [polyMin_choiLamQuartic_eq_zero] using hupper⟩

end QuarticConvergence
end OptimalConvergenceRates

end
