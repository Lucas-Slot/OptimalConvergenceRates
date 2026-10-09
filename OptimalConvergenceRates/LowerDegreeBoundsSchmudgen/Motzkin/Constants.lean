/- Derived constants for the Motzkin Schmuedgen lower bound. -/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.DegreeSix
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.Separation

noncomputable section

namespace OptimalConvergenceRates

namespace Motzkin

/-- The explicit coefficient-error constant supplied by the degree-six comparison. -/
noncomputable def motzkinJetErrorConst : ℝ :=
  motzkinDegreeSixNormConst *
    (27 * (2352 * (700 * (motzkinLowJetConst + motzkinHighJetConst) ^ 2)))

theorem motzkinJetErrorConst_pos : 0 < motzkinJetErrorConst := by
  unfold motzkinJetErrorConst
  exact mul_pos motzkinDegreeSixNormConst_pos
    (mul_pos (by norm_num) (mul_pos (by norm_num)
      (mul_pos (by norm_num)
        (sq_pos_of_pos (add_pos motzkinLowJetConst_pos motzkinHighJetConst_pos)))))

/-- The positive sixth-root degree constant, capped to satisfy the jet smallness condition. -/
noncomputable def motzkinLowerBoundConst : ℝ :=
  min (1 / 8)
    ((motzkinSosDistance / (2 * motzkinJetErrorConst)) ^ ((1 : ℝ) / 3))

theorem motzkinLowerBoundConst_pos : 0 < motzkinLowerBoundConst := by
  unfold motzkinLowerBoundConst
  apply lt_min
  · norm_num
  · apply Real.rpow_pos_of_pos
    exact div_pos motzkinSosDistance_pos
      (mul_pos (by norm_num) motzkinJetErrorConst_pos)

theorem motzkinLowerBoundConst_nonneg : 0 ≤ motzkinLowerBoundConst :=
  motzkinLowerBoundConst_pos.le

theorem motzkinLowerBoundConst_le_eighth :
    motzkinLowerBoundConst ≤ 1 / 8 := by
  exact min_le_left _ _

theorem motzkinLowerBoundConst_cube_le_distance :
    motzkinLowerBoundConst ^ 3 ≤
      motzkinSosDistance / (2 * motzkinJetErrorConst) := by
  have hratio : 0 < motzkinSosDistance / (2 * motzkinJetErrorConst) :=
    div_pos motzkinSosDistance_pos
      (mul_pos (by norm_num) motzkinJetErrorConst_pos)
  have hle : motzkinLowerBoundConst ≤
      (motzkinSosDistance / (2 * motzkinJetErrorConst)) ^ ((1 : ℝ) / 3) := by
    exact min_le_right _ _
  calc
    motzkinLowerBoundConst ^ 3 ≤
        ((motzkinSosDistance / (2 * motzkinJetErrorConst)) ^
          ((1 : ℝ) / 3)) ^ 3 :=
      pow_le_pow_left₀ motzkinLowerBoundConst_nonneg hle 3
    _ = motzkinSosDistance / (2 * motzkinJetErrorConst) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hratio.le]
      norm_num

/-- Perturbations below this threshold have sixth root below the analytic radius. -/
noncomputable def motzkinEpsilon0 : ℝ := (1 / 16 : ℝ) ^ 6

theorem motzkinEpsilon0_pos : 0 < motzkinEpsilon0 := by
  exact pow_pos (by norm_num) 6

end Motzkin

end OptimalConvergenceRates

end
