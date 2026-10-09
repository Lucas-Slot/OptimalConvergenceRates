/-
  OptimalConvergenceRates/ScaledRobinson/MainResults.lean

  Main theorem and dyadic corollary for scaled Robinson polynomials in the
  unit-ball quadratic module, restricted to the small-scale high-order regime.
-/
import OptimalConvergenceRates.ScaledRobinson.Homogenization

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace ScaledRobinson

/-- Pointwise explicit formula for the scaled Robinson polynomial. -/
theorem eval_scaledRobinson_eq_explicit (eps x y : ℝ) :
    MvPolynomial.eval ![x, y] (scaledRobinson eps) =
      (x / eps) ^ 6 + (y / eps) ^ 6 + 1 -
        ((x / eps) ^ 4 * (y / eps) ^ 2 + (x / eps) ^ 4 +
          (x / eps) ^ 2 * (y / eps) ^ 4 + (y / eps) ^ 4 +
          (x / eps) ^ 2 + (y / eps) ^ 2) +
        3 * (x / eps) ^ 2 * (y / eps) ^ 2 := by
  have hthree :
      MvPolynomial.eval ![x, y] ((MvPolynomial.bind₁ fun i : Fin 2 =>
        MvPolynomial.C eps⁻¹ * MvPolynomial.X i) (3 : MvPolynomial (Fin 2) ℝ)) = 3 := by
    rw [show (3 : MvPolynomial (Fin 2) ℝ) = MvPolynomial.C (3 : ℝ) from
      (MvPolynomial.C_eq_coe_nat 3).symm]
    simp
  simp [scaledRobinson, scale2, robinson, div_eq_mul_inv, hthree]
  ring_nf

/--
Small-scale exact unit-ball membership criterion for the scaled Robinson polynomial.

The assumption `eps < 1/100` keeps the public theorem in the high-order regime,
so the statement only quantifies over orders `r >= 4` and does not need the
order-three boundary cases.
-/
theorem scaledRobinson_mem_unitBallQuadraticModule_iff
    (eps : ℝ) (r : ℕ) (hEps : 0 < eps) (_hEpsSmall : eps < (100 : ℝ)⁻¹)
    (hr : 4 ≤ r) :
    scaledRobinson eps ∈ UnitBallQuadraticModule r ↔
      eps⁻¹ ^ 2 ≤ 4 * ((r : ℝ) - 3) * ((r : ℝ) - 2) := by
  have hLam : 0 < eps⁻¹ ^ 2 := sq_pos_of_ne_zero (inv_ne_zero (ne_of_gt hEps))
  rw [scaledRobinson_mem_unitBallQuadraticModule_iff_robinson_mem_ball hEps r]
  exact robinson_mem_ballQuadraticModule_iff_threshold_of_four_le hLam hr

/--
Small-scale exact least unit-ball representation order among orders `r >= 4`.

This is the clean least-order statement used for the main result; it deliberately
avoids any claim about orders `0, 1, 2, 3`.
-/
theorem scaledRobinson_isLeastUnitBallOrder_ge_four
    (eps : ℝ) (hEps : 0 < eps) (hEpsSmall : eps < (100 : ℝ)⁻¹) :
    4 ≤ 3 + Nat.ceil ((Real.sqrt (1 + eps⁻¹ ^ 2) - 1) / 2) ∧
      scaledRobinson eps ∈
        UnitBallQuadraticModule
          (3 + Nat.ceil ((Real.sqrt (1 + eps⁻¹ ^ 2) - 1) / 2)) ∧
      ∀ r : ℕ, 4 ≤ r →
        scaledRobinson eps ∈ UnitBallQuadraticModule r →
          3 + Nat.ceil ((Real.sqrt (1 + eps⁻¹ ^ 2) - 1) / 2) ≤ r := by
  let lambda : ℝ := eps⁻¹ ^ 2
  let r0 : ℕ := 3 + Nat.ceil ((Real.sqrt (1 + lambda) - 1) / 2)
  have hLam : 0 < lambda := by
    dsimp [lambda]
    exact sq_pos_of_ne_zero (inv_ne_zero (ne_of_gt hEps))
  have hLamGt2 : 2 < lambda := by
    dsimp [lambda]
    exact two_lt_eps_inv_sq_of_lt_inv_hundred hEps hEpsSmall
  have hTarget : ballTargetOrder lambda = r0 := by
    change (if lambda ≤ 2 then 3 else 3 + Nat.ceil ((Real.sqrt (1 + lambda) - 1) / 2)) = r0
    simp [not_le_of_gt hLamGt2, r0]
  have hr0_ge4 : 4 ≤ r0 := by
    rw [← hTarget]
    unfold ballTargetOrder
    simp [not_le_of_gt hLamGt2]
    have hApos : 0 < (Real.sqrt (1 + lambda) - 1) / 2 := by
      have hsqrt_gt : 1 < Real.sqrt (1 + lambda) := by
        rw [Real.lt_sqrt (by norm_num)]
        linarith
      linarith
    have hceil_pos : 1 ≤ Nat.ceil ((Real.sqrt (1 + lambda) - 1) / 2) := by
      exact Nat.succ_le_of_lt (Nat.ceil_pos.mpr hApos)
    omega
  have hmem : scaledRobinson eps ∈ UnitBallQuadraticModule r0 := by
    rw [scaledRobinson_mem_unitBallQuadraticModule_iff eps r0 hEps hEpsSmall hr0_ge4]
    exact (ballTargetOrder_le_iff hLam hr0_ge4).mp (by rw [hTarget])
  refine ⟨by simpa [r0, lambda] using hr0_ge4, by simpa [r0, lambda] using hmem, ?_⟩
  intro r hr hmemr
  have hineq := (scaledRobinson_mem_unitBallQuadraticModule_iff eps r hEps hEpsSmall hr).mp hmemr
  have hr0_le : r0 ≤ r := by
    rw [← hTarget]
    exact (ballTargetOrder_le_iff hLam hr).mpr (by simpa [lambda] using hineq)
  simpa [r0, lambda] using hr0_le

/-- Least termwise certificate-degree bound in the small-scale high-order regime. -/
theorem scaledRobinson_least_termwise_certificateDegree_ge_four
    (eps : ℝ) (_hEps : 0 < eps) (_hEpsSmall : eps < (100 : ℝ)⁻¹) :
    2 * (3 + Nat.ceil ((Real.sqrt (1 + eps⁻¹ ^ 2) - 1) / 2)) =
      6 + 2 * Nat.ceil ((Real.sqrt (1 + eps⁻¹ ^ 2) - 1) / 2) := by
  omega

/-- Dyadic high-order exact least unit-ball representation order, stated with `eps = 2^(1-k)`. -/
theorem scaledRobinson_isLeastUnitBallOrder_ge_four_two_zpow_one_sub_natCast
    (k : ℕ) (hk : 8 ≤ k) :
    4 ≤ 2 ^ (k - 2) + 3 ∧
      scaledRobinson ((2 : ℝ) ^ (1 - (k : ℤ))) ∈
        UnitBallQuadraticModule (2 ^ (k - 2) + 3) ∧
      ∀ r : ℕ, 4 ≤ r →
        scaledRobinson ((2 : ℝ) ^ (1 - (k : ℤ))) ∈ UnitBallQuadraticModule r →
          2 ^ (k - 2) + 3 ≤ r := by
  let eps : ℝ := (2 : ℝ) ^ (1 - (k : ℤ))
  have hk2 : 2 ≤ k := by omega
  have hEps : 0 < eps := by dsimp [eps]; positivity
  have heps : eps = (2 * ((2 ^ (k - 2) : ℕ) : ℝ))⁻¹ := by
    dsimp [eps]
    rw [show (1 : ℤ) - (k : ℤ) = -((k - 1 : ℕ) : ℤ) by omega]
    rw [zpow_neg, zpow_natCast]
    congr 1
    rw [show k - 1 = k - 2 + 1 by omega]
    norm_num [pow_succ]
    ring
  have hpow64 : 64 ≤ 2 ^ (k - 2) := by
    rw [show (64 : ℕ) = 2 ^ 6 by norm_num]
    exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega : 6 ≤ k - 2)
  have hsmall : eps < (100 : ℝ)⁻¹ := by
    rw [heps]
    have hden_gt : (100 : ℝ) < 2 * ((2 ^ (k - 2) : ℕ) : ℝ) := by
      have hpow64R : (64 : ℝ) ≤ (2 ^ (k - 2) : ℕ) := by exact_mod_cast hpow64
      nlinarith
    simpa [one_div] using
      one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 100) hden_gt
  have hleast := scaledRobinson_isLeastUnitBallOrder_ge_four eps hEps hsmall
  have hLamGt2 : 2 < eps⁻¹ ^ 2 := two_lt_eps_inv_sq_of_lt_inv_hundred hEps hsmall
  have htarget : 3 + Nat.ceil ((Real.sqrt (1 + eps⁻¹ ^ 2) - 1) / 2) =
      2 ^ (k - 2) + 3 := by
    have hball : scaledRobinsonOrder eps =
        3 + Nat.ceil ((Real.sqrt (1 + eps⁻¹ ^ 2) - 1) / 2) := by
      unfold scaledRobinsonOrder ballTargetOrder
      rw [if_neg (not_le_of_gt hLamGt2)]
    have hscaled := scaledRobinsonOrder_two_zpow_one_sub_natCast (k := k) hk2
    have hscaled_eps : scaledRobinsonOrder eps = 2 ^ (k - 2) + 3 := by
      simpa [eps] using hscaled
    rw [← hball]
    exact hscaled_eps
  rcases hleast with ⟨hr0, hmem, hleast_min⟩
  rw [htarget] at hr0 hmem hleast_min
  refine ⟨?_, ?_, ?_⟩
  · simpa [eps] using hr0
  · simpa [eps] using hmem
  · intro r hr hmemr
    simpa [eps] using hleast_min r hr (by simpa [eps] using hmemr)

/-- Dyadic least termwise certificate-degree bound in the high-order range. -/
theorem scaledRobinson_least_termwise_certificateDegree_two_zpow_one_sub_natCast
    (k : ℕ) (hk : 2 ≤ k) :
    2 * (2 ^ (k - 2) + 3) = 2 ^ (k - 1) + 6 := by
  rw [show k - 1 = k - 2 + 1 by omega, Nat.pow_succ]
  omega

end ScaledRobinson
end OptimalConvergenceRates

end
