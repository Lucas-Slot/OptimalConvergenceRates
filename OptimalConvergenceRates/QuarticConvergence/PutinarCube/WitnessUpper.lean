/-
  Matching quartic upper bound for the sharp Putinar cube witness.
-/
import OptimalConvergenceRates.LowerDegreeBoundsPutinar.MatchingUpperBound

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

private theorem scale_mul_fourth_power_rpow (K : ℝ) (hK : 0 < K)
    (r : ℕ) (hr : 0 < r) :
    K * ((K / (r : ℝ)) ^ 4) ^ (-(1 : ℝ) / 4) = r := by
  have hrReal : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hratio : 0 < K / (r : ℝ) := div_pos hK hrReal
  rw [← Real.rpow_natCast (K / (r : ℝ)) 4,
    ← Real.rpow_mul hratio.le]
  rw [show ((4 : ℕ) : ℝ) * (-(1 : ℝ) / 4) = -1 by norm_num,
    Real.rpow_neg_one]
  field_simp

/-- The existing matching certificate for the corner perturbation gives an
`O(r⁻⁴)` upper gap at every sufficiently large concrete order. -/
theorem putinarCubeQuarticGapUpper_of_large (r : ℕ) (hr : 0 < r)
    (hsmall : ((8 : ℝ) / (r : ℝ)) ^ 4 ≤ 1) :
    ↑(-(((8 : ℝ) / (r : ℝ)) ^ 4)) ≤ lasserre_bound_box_qm f_zero r := by
  let epsilon : ℝ := ((8 : ℝ) / (r : ℝ)) ^ 4
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    exact pow_pos (div_pos (by norm_num) (Nat.cast_pos.mpr hr)) _
  obtain ⟨s, hs, hmem⟩ :=
    f_eps_mem_BoxQuadraticModule_matching_upper epsilon hepsilon hsmall
  have hscale : (8 : ℝ) * epsilon ^ (-(1 : ℝ) / 4) = r := by
    exact scale_mul_fourth_power_rpow 8 (by norm_num) r hr
  have hsrReal : (s : ℝ) ≤ r := hs.trans_eq hscale
  have hsr : s ≤ r := by exact_mod_cast hsrReal
  apply lasserre_bound_box_qm_ge_feasible
  have hmem' := BoxQuadraticModule_mono hsr hmem
  convert hmem' using 1
  simp [epsilon, f_zero, f_eps, map_neg]

end QuarticConvergence
end OptimalConvergenceRates

end
