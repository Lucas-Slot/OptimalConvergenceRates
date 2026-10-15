/-
  OptimalConvergenceRates/QuarticConvergence/PutinarCube/Optimality.lean

  Sharp fixed-objective lower bounds obtained from the existing perturbation
  degree obstructions.
-/
import OptimalConvergenceRates.LowerDegreeBoundsPutinar.MainResults
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.MainResults

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- The improved perturbation obstruction gives a quartic lower bound for the
quadratic-module hierarchy at every order for which the corresponding
perturbation lies in the certified small-parameter range. -/
theorem putinarCubeQuarticGapLower_of_small (r : ℕ) (hr : 0 < r)
    (hsmall : (improvedLowerBoundConst / (r : ℝ)) ^ 4 ≤ improvedEpsilon0) :
    lasserre_bound_box_qm f_zero r ≤
      ↑(-(improvedLowerBoundConst / (r : ℝ)) ^ 4) := by
  have hrPos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hcPos : 0 < improvedLowerBoundConst := improvedLowerBoundConst_pos
  suffices key : ∀ l : ℝ, (f_zero - MvPolynomial.C l) ∈ BoxQuadraticModule 2 r →
      l ≤ -(improvedLowerBoundConst / (r : ℝ)) ^ 4 by
    unfold lasserre_bound_box_qm
    split_ifs with hne
    · exact WithBot.coe_le_coe.mpr (csSup_le hne fun l hl ↦ key l hl)
    · exact bot_le
  intro l hl
  have hfl : f_zero - MvPolynomial.C l = f_eps (-l) := by
    simp [f_zero, f_eps, map_neg]
    ring
  rw [hfl] at hl
  have hlNonneg : 0 ≤ -l := by
    have h := BoxQuadraticModule_subset_nonneg hl corner_11 corner_11_in_hypercube
    rw [f_eps_eval_corner] at h
    exact h
  by_cases hlZero : l = 0
  · subst hlZero
    rw [neg_zero, ← f_zero_eq] at hl
    exact (f_not_in_quadratic_module r hl).elim
  have hlPos : 0 < -l := lt_of_le_of_ne hlNonneg fun h ↦ hlZero (by linarith)
  by_cases hlSmall : -l ≤ improvedEpsilon0
  · have hdegree := improvedLowerBoundMembershipBoxQM (-l) hlPos hlSmall r hl
    have hrootPos : 0 < (-l) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hlPos _
    have hratio : improvedLowerBoundConst / (r : ℝ) ≤
        (-l) ^ ((1 : ℝ) / 4) := by
      rw [div_le_iff₀ hrPos]
      rw [show (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) by ring,
        Real.rpow_neg hlPos.le] at hdegree
      rw [mul_inv_le_iff₀ hrootPos] at hdegree
      simpa [mul_comm] using hdegree
    have hpow := pow_le_pow_left₀ (div_nonneg hcPos.le hrPos.le) hratio 4
    have hrootPow : ((-l) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = -l := by
      rw [← Real.rpow_natCast ((-l) ^ ((1 : ℝ) / 4)) 4,
        ← Real.rpow_mul hlPos.le]
      norm_num
    rw [hrootPow] at hpow
    linarith
  · push Not at hlSmall
    linarith

end QuarticConvergence
end OptimalConvergenceRates

end
