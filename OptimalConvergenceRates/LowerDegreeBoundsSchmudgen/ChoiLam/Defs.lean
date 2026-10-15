/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/ChoiLam/Defs.lean

  Constants for the Choi-Lam Schmuedgen interior obstruction.
-/
import OptimalConvergenceRates.BasicNotions.SumsOfSquares
import OptimalConvergenceRates.BasicNotions.SOSVector
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

/-! ## Constants -/

/-- Radius of the small interior box used around the origin. -/
def schmInteriorS : ℝ := 1 / 4

/-- Uniform lower bound for all box preordering weights on `|x_i| <= schmInteriorS`. -/
def schmInteriorAlpha0 : ℝ := (1 - schmInteriorS ^ 2) ^ 4

/-- Small constant used to keep the weighted-jet degree regime uniform. -/
def weightedJetGamma0 : ℝ := 1 / 1000000

/-- Absolute constant used in coefficient-error estimates. -/
def jetErrorConst : ℝ := 1000000

/-- The lower-bound constant used in the public theorem.

It is intentionally very small so later arithmetic can absorb fixed factors,
including the `r` versus `2*k` convention difference. -/
def schmInteriorLowerBoundConst : ℝ :=
  min weightedJetGamma0 (Real.sqrt (1 / (4 * jetErrorConst)))

/-- Small epsilon threshold used by the lower-bound theorem. -/
def schmInteriorEpsilon0 : ℝ := (schmInteriorLowerBoundConst / 4) ^ 4

theorem schmInteriorS_pos : 0 < schmInteriorS := by
  unfold schmInteriorS
  norm_num

theorem schmInteriorS_lt_half : schmInteriorS < 1 / 2 := by
  unfold schmInteriorS
  norm_num

theorem schmInteriorS_nonneg : 0 ≤ schmInteriorS :=
  le_of_lt schmInteriorS_pos

theorem schmInteriorAlpha0_pos : 0 < schmInteriorAlpha0 := by
  unfold schmInteriorAlpha0
  apply pow_pos
  unfold schmInteriorS
  norm_num


theorem one_half_le_schmInteriorAlpha0 : (1 / 2 : ℝ) ≤ schmInteriorAlpha0 := by
  unfold schmInteriorAlpha0 schmInteriorS
  norm_num

/-- A deliberately coarse absolute constant absorbing the local weight lower bound. -/
def schmInteriorLocalControlConst : ℝ := 100

theorem schmInteriorLocalControlConst_pos : 0 < schmInteriorLocalControlConst := by
  unfold schmInteriorLocalControlConst
  norm_num

theorem one_le_schmInteriorLocalControlConst : 1 ≤ schmInteriorLocalControlConst := by
  unfold schmInteriorLocalControlConst
  norm_num

theorem weightedJetGamma0_pos : 0 < weightedJetGamma0 := by
  unfold weightedJetGamma0
  norm_num

theorem jetErrorConst_pos : 0 < jetErrorConst := by
  unfold jetErrorConst
  norm_num

theorem schmInteriorLowerBoundConst_pos : 0 < schmInteriorLowerBoundConst := by
  unfold schmInteriorLowerBoundConst
  apply lt_min
  · exact weightedJetGamma0_pos
  · apply Real.sqrt_pos_of_pos
    exact one_div_pos.mpr (mul_pos (by norm_num) jetErrorConst_pos)

theorem schmInteriorEpsilon0_pos : 0 < schmInteriorEpsilon0 := by
  unfold schmInteriorEpsilon0
  apply pow_pos
  exact div_pos schmInteriorLowerBoundConst_pos (by norm_num)

theorem schmInteriorLowerBoundConst_le_gamma :
    schmInteriorLowerBoundConst ≤ weightedJetGamma0 := by
  unfold schmInteriorLowerBoundConst
  exact min_le_left _ _

end OptimalConvergenceRates

end
