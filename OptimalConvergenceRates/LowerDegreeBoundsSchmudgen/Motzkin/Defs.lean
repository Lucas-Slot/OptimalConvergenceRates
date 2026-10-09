/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/Motzkin/Defs.lean

  The Motzkin sextic and constants for its Schmuedgen degree lower bound.
-/
import OptimalConvergenceRates.BasicNotions.BoxCones
import OptimalConvergenceRates.BasicNotions.SoSConeClosed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

namespace Motzkin

/-! ## Local analytic constants -/

/-- Radius of the small interior box used around the origin. -/
def schmInteriorS : ℝ := 1 / 4

/-- Uniform lower bound for all box-preordering weights on the small box. -/
def schmInteriorAlpha0 : ℝ := (1 - schmInteriorS ^ 2) ^ 4

/-- Coarse absolute constant used in the Motzkin local-control estimates. -/
def schmInteriorLocalControlConst : ℝ := 100

theorem schmInteriorS_pos : 0 < schmInteriorS := by
  unfold schmInteriorS
  norm_num

theorem schmInteriorS_lt_half : schmInteriorS < 1 / 2 := by
  unfold schmInteriorS
  norm_num

theorem schmInteriorS_nonneg : 0 ≤ schmInteriorS :=
  schmInteriorS_pos.le

theorem schmInteriorAlpha0_pos : 0 < schmInteriorAlpha0 := by
  unfold schmInteriorAlpha0
  apply pow_pos
  unfold schmInteriorS
  norm_num

theorem one_half_le_schmInteriorAlpha0 : (1 / 2 : ℝ) ≤ schmInteriorAlpha0 := by
  unfold schmInteriorAlpha0 schmInteriorS
  norm_num

theorem schmInteriorLocalControlConst_pos : 0 < schmInteriorLocalControlConst := by
  unfold schmInteriorLocalControlConst
  norm_num

theorem one_le_schmInteriorLocalControlConst : 1 ≤ schmInteriorLocalControlConst := by
  unfold schmInteriorLocalControlConst
  norm_num

/-- The homogeneous ternary Motzkin sextic. -/
def motzkinSextic : MvPolynomial (Fin 3) ℝ :=
  X (0 : Fin 3) ^ 4 * X (1 : Fin 3) ^ 2
    + X (0 : Fin 3) ^ 2 * X (1 : Fin 3) ^ 4
    + X (2 : Fin 3) ^ 6
    - 3 * X (0 : Fin 3) ^ 2 * X (1 : Fin 3) ^ 2 * X (2 : Fin 3) ^ 2

/-- The Motzkin sextic perturbed by a positive constant. -/
def motzkinPerturbed (epsilon : ℝ) : MvPolynomial (Fin 3) ℝ :=
  motzkinSextic + C epsilon

theorem motzkinSextic_eval (v : Fin 3 → ℝ) :
    eval v motzkinSextic =
      v 0 ^ 4 * v 1 ^ 2 + v 0 ^ 2 * v 1 ^ 4 + v 2 ^ 6
        - 3 * v 0 ^ 2 * v 1 ^ 2 * v 2 ^ 2 := by
  simp [motzkinSextic, map_add, map_sub, map_mul, map_pow, eval_X]

theorem motzkinPerturbed_eval (epsilon : ℝ) (v : Fin 3 → ℝ) :
    eval v (motzkinPerturbed epsilon) = eval v motzkinSextic + epsilon := by
  simp [motzkinPerturbed]

/-- The first coordinate-axis zero of the Motzkin sextic. -/
def motzkinAxisX : Fin 3 → ℝ := ![1, 0, 0]

/-- The second coordinate-axis zero of the Motzkin sextic. -/
def motzkinAxisY : Fin 3 → ℝ := ![0, 1, 0]

/-- The four remaining zero directions, represented without normalization. -/
def motzkinSignDirection (s t : Fin 2) : Fin 3 → ℝ :=
  fun i ↦ if i = 0 then 1 else if i = 1 then
    (if s = 0 then 1 else -1) else (if t = 0 then 1 else -1)

theorem motzkinSextic_eval_axisX : eval motzkinAxisX motzkinSextic = 0 := by
  rw [motzkinSextic_eval]
  change (1 : ℝ) ^ 4 * 0 ^ 2 + 1 ^ 2 * 0 ^ 4 + 0 ^ 6
    - 3 * 1 ^ 2 * 0 ^ 2 * 0 ^ 2 = 0
  norm_num

theorem motzkinSextic_eval_axisY : eval motzkinAxisY motzkinSextic = 0 := by
  rw [motzkinSextic_eval]
  change (0 : ℝ) ^ 4 * 1 ^ 2 + 0 ^ 2 * 1 ^ 4 + 0 ^ 6
    - 3 * 0 ^ 2 * 1 ^ 2 * 0 ^ 2 = 0
  norm_num

theorem motzkinSextic_eval_signDirection (s t : Fin 2) :
    eval (motzkinSignDirection s t) motzkinSextic = 0 := by
  fin_cases s <;> fin_cases t <;> rw [motzkinSextic_eval] <;>
    change (1 : ℝ) ^ 4 * (_ : ℝ) ^ 2 + 1 ^ 2 * (_ : ℝ) ^ 4 + (_ : ℝ) ^ 6
      - 3 * 1 ^ 2 * (_ : ℝ) ^ 2 * (_ : ℝ) ^ 2 = 0 <;>
    norm_num [motzkinSignDirection]

/-- A fixed radius used for local certificate estimates. -/
def motzkinLocalRadius : ℝ := 1 / 2


/-- The positive coefficient-space distance from the Motzkin form to cubic SOS forms. -/
noncomputable def motzkinSosDistance : ℝ :=
  sInf {d : ℝ | ∃ S : MvPolynomial (Fin 3) ℝ,
    Nonempty (DegreeBoundedSOS S 3) ∧ d = coeffL1Distance motzkinSextic S}

theorem motzkinLocalRadius_pos : 0 < motzkinLocalRadius := by
  norm_num [motzkinLocalRadius]

end Motzkin

end OptimalConvergenceRates

end
