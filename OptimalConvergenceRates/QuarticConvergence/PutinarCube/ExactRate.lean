/-
  Public two-sided quartic rate for the sharp Putinar cube witness.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.Optimality
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.RateThreshold
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.WitnessUpper

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

private theorem withBot_eq_coe_of_coe_le (a : ℝ) (x : WithBot ℝ)
    (h : (a : WithBot ℝ) ≤ x) :
    ∃ b : ℝ, x = (b : WithBot ℝ) := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h
  | coe b => exact ⟨b, rfl⟩

/-- The quadratic-module hierarchy has exact quartic convergence on the
corner witness: its finite hierarchy gap is bounded above and below by
positive multiples of `r⁻⁴`. -/
theorem putinarCubeExactQuarticRate :
    ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      ∃ b : ℝ,
        lasserre_bound_box_qm f_zero r = (b : WithBot ℝ) ∧
        (improvedLowerBoundConst / (r : ℝ)) ^ 4 ≤ -b ∧
        -b ≤ ((8 : ℝ) / (r : ℝ)) ^ 4 := by
  obtain ⟨rLower, hrLowerPos, hrLower⟩ :=
    exists_nat_for_div_pow_four_le improvedLowerBoundConst_pos improvedEpsilon0_pos
  obtain ⟨rUpper, hrUpperPos, hrUpper⟩ :=
    exists_nat_for_div_pow_four_le (by norm_num : (0 : ℝ) < 8) (by norm_num : (0 : ℝ) < 1)
  refine ⟨max rLower rUpper, hrLowerPos.trans_le (le_max_left _ _), ?_⟩
  intro r hr
  have hrL : rLower ≤ r := (le_max_left _ _).trans hr
  have hrU : rUpper ≤ r := (le_max_right _ _).trans hr
  have hrPos : 0 < r := hrLowerPos.trans_le hrL
  have hlower := putinarCubeQuarticGapLower_of_small r hrPos (hrLower r hrL)
  have hupper := putinarCubeQuarticGapUpper_of_large r hrPos (hrUpper r hrU)
  obtain ⟨b, hb⟩ := withBot_eq_coe_of_coe_le
    (-(((8 : ℝ) / (r : ℝ)) ^ 4)) (lasserre_bound_box_qm f_zero r) hupper
  refine ⟨b, hb, ?_, ?_⟩
  · rw [hb, WithBot.coe_le_coe] at hlower
    linarith
  · rw [hb, WithBot.coe_le_coe] at hupper
    linarith

end QuarticConvergence
end OptimalConvergenceRates

end
