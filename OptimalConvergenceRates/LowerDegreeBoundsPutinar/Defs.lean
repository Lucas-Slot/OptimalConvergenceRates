/-
  OptimalConvergenceRates/LowerDegreeBoundsPutinar/Defs.lean

  Constants and shared setup for the improved Putinar lower bound for the corner polynomial.
-/
import OptimalConvergenceRates.ExamplePolynomials.BoxCorner
import Mathlib.Analysis.SpecialFunctions.Exp

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

/-! ## Constants -/

/-- Absolute constant in the weighted vertical endpoint estimate. -/
def verticalEndpointConst : ℝ := 100 * Real.exp 12

theorem verticalEndpointConst_pos : 0 < verticalEndpointConst := by
  unfold verticalEndpointConst
  positivity

theorem one_le_verticalEndpointConst : 1 ≤ verticalEndpointConst := by
  unfold verticalEndpointConst
  calc (1 : ℝ) ≤ 100 * 1 := by norm_num
    _ ≤ 100 * Real.exp 12 := by
        apply mul_le_mul_of_nonneg_left
        · calc (1 : ℝ) ≤ Real.exp 0 := by simp
            _ ≤ Real.exp 12 := Real.exp_le_exp.mpr (by norm_num)
        · norm_num

/-- Absolute constant in the horizontal Markov-control estimate. -/
def horizontalControlConst : ℝ := 100 * Real.exp 12

theorem horizontalControlConst_pos : 0 < horizontalControlConst := by
  unfold horizontalControlConst
  positivity

theorem one_le_horizontalControlConst : 1 ≤ horizontalControlConst := by
  unfold horizontalControlConst
  calc (1 : ℝ) ≤ 100 * 1 := by norm_num
    _ ≤ 100 * Real.exp 12 := by
        apply mul_le_mul_of_nonneg_left
        · calc (1 : ℝ) ≤ Real.exp 0 := by simp
            _ ≤ Real.exp 12 := Real.exp_le_exp.mpr (by norm_num)
        · norm_num

/-- A small absolute constant for the improved lower bound.

The value is intentionally weak. It is chosen after the absolute vertical and
horizontal constants so the final arithmetic can absorb both error terms. -/
def improvedLowerBoundConst : ℝ :=
  min (1 / 1000000)
    (min (1 / (36 * verticalEndpointConst ^ 2))
      (1 / (36 * horizontalControlConst ^ 2)))

theorem improvedLowerBoundConst_pos : 0 < improvedLowerBoundConst := by
  unfold improvedLowerBoundConst
  apply lt_min
  · norm_num
  · apply lt_min
    · exact one_div_pos.mpr (mul_pos (by norm_num) (sq_pos_of_pos verticalEndpointConst_pos))
    · exact one_div_pos.mpr (mul_pos (by norm_num) (sq_pos_of_pos horizontalControlConst_pos))

theorem improvedLowerBoundConst_le_millionth : improvedLowerBoundConst ≤ 1 / 1000000 := by
  unfold improvedLowerBoundConst
  exact min_le_left _ _

theorem improvedLowerBoundConst_le_one : improvedLowerBoundConst ≤ 1 := by
  exact improvedLowerBoundConst_le_millionth.trans (by norm_num)

theorem improvedLowerBoundConst_le_half : improvedLowerBoundConst ≤ 1 / 2 := by
  unfold improvedLowerBoundConst
  exact (min_le_left _ _).trans (by norm_num)

theorem improvedLowerBoundConst_le_vertical_sq :
    improvedLowerBoundConst ≤ 1 / (36 * verticalEndpointConst ^ 2) := by
  unfold improvedLowerBoundConst
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem improvedLowerBoundConst_le_horizontal_sq :
    improvedLowerBoundConst ≤ 1 / (36 * horizontalControlConst ^ 2) := by
  unfold improvedLowerBoundConst
  exact (min_le_right _ _).trans (min_le_right _ _)

/-- The small-ε threshold used by the improved lower-bound theorem. -/
def improvedEpsilon0 : ℝ := (improvedLowerBoundConst / 4) ^ 4

theorem improvedEpsilon0_pos : 0 < improvedEpsilon0 := by
  unfold improvedEpsilon0
  apply pow_pos
  linarith [improvedLowerBoundConst_pos]

/-! ## Corner and outside-corner points -/

/-- The anisotropic outside point `(1 + a, 1 - b)` used in the proof. -/
def outsideCornerPoint (a b : ℝ) : Fin 2 → ℝ := ![1 + a, 1 - b]

theorem outsideCornerPoint_val_0 (a b : ℝ) :
    outsideCornerPoint a b 0 = 1 + a := by
  simp [outsideCornerPoint, Matrix.cons_val_zero]

theorem outsideCornerPoint_val_1 (a b : ℝ) :
    outsideCornerPoint a b 1 = 1 - b := by
  simp [outsideCornerPoint, Matrix.cons_val_one]

/-- The first generator at `(1+a, 1-b)` is negative for `a > 0`. -/
theorem gen0_outsideCornerPoint (a b : ℝ) :
    MvPolynomial.eval (outsideCornerPoint a b) (BoxSemialgebraicGenerator (0 : Fin 2))
      = -(2 * a + a ^ 2) := by
  rw [BoxSemialgebraicGenerator_eval, outsideCornerPoint_val_0]
  ring

/-- The second generator at `(1+a, 1-b)` is `2b - b²`. -/
theorem gen1_outsideCornerPoint (a b : ℝ) :
    MvPolynomial.eval (outsideCornerPoint a b) (BoxSemialgebraicGenerator (1 : Fin 2))
      = 2 * b - b ^ 2 := by
  rw [BoxSemialgebraicGenerator_eval, outsideCornerPoint_val_1]
  ring

/-- The test polynomial at `(1+a, 1-b)`. -/
theorem f_eps_outsideCornerPoint (ε a b : ℝ) :
    MvPolynomial.eval (outsideCornerPoint a b) (f_eps ε)
      = -(2 * a + a ^ 2) * (2 * b - b ^ 2) + ε := by
  rw [f_eps_eval, outsideCornerPoint_val_0, outsideCornerPoint_val_1]
  ring

end OptimalConvergenceRates

end

