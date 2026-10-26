import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
/-! A uniform binomial bound used in the finite hypergraph counting proof. -/

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

theorem factorial_power_lower_bound (k : ℕ) :
    (k : ℝ) ^ k ≤ (3 : ℝ) ^ k * (k.factorial : ℝ) := by
  have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hp := Real.pow_div_factorial_le_exp (k : ℝ)
    (Nat.cast_nonneg k : (0 : ℝ) ≤ k) k
  have hpow := pow_le_pow_left₀ (Real.exp_pos 1).le he k
  have heq : Real.exp (k : ℝ) = Real.exp 1 ^ k := by
    simpa only [mul_one] using Real.exp_nat_mul 1 k
  rw [heq] at hp
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < (k.factorial : ℝ))).mp (hp.trans hpow)

theorem binomial_le_three_mul_div_pow (n k : ℕ) (hk : 0 < k) :
    (n.choose k : ℝ) ≤ (3 * (n : ℝ) / (k : ℝ)) ^ k := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkpow : (0 : ℝ) < (k : ℝ) ^ k := pow_pos hkpos _
  have hfpos : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  apply (Nat.choose_le_pow_div k n).trans
  apply (div_le_iff₀ hfpos).mpr
  apply (mul_le_mul_iff_left₀ hkpow).mp
  have hfact := mul_le_mul_of_nonneg_left (factorial_power_lower_bound k)
    (pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) k)
  have heq : ((3 * (n : ℝ) / (k : ℝ)) ^ k * (k.factorial : ℝ)) * (k : ℝ) ^ k =
      (n : ℝ) ^ k * ((3 : ℝ) ^ k * (k.factorial : ℝ)) := by
    rw [div_pow, mul_pow]
    field_simp [hkpos.ne'] <;> ring
  rw [heq]
  exact hfact

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
