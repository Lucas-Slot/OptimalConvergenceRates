import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
/-! Exact scalar normalization of the finite triple-system event counts. -/

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

theorem real_choose_three (n : ℕ) :
    (n.choose 3 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 := by
  rw [Nat.cast_choose_eq_descPochhammer_div ℝ n 3]
  norm_num [descPochhammer_eval_eq_prod_range, Finset.prod_range_succ]

theorem real_choose_three_pos (N : ℕ) (hN : 3 ≤ N) : 0 < (N.choose 3 : ℝ) := by
  exact_mod_cast Nat.choose_pos hN

/-- Sampling three distinct vertices makes containment no more likely
than three independent samples with replacement. -/
theorem choose_three_ratio_le_cube (v N : ℕ) (hN : 3 ≤ N) (hvN : v ≤ N) :
    (v.choose 3 : ℝ) / (N.choose 3 : ℝ) ≤ ((v : ℝ) / (N : ℝ)) ^ 3 := by
  by_cases hv : v < 3
  · rw [Nat.choose_eq_zero_of_lt hv]
    simp only [Nat.cast_zero, zero_div]
    positivity
  · have hv3 : (3 : ℝ) ≤ v := by exact_mod_cast (by omega : 3 ≤ v)
    have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have hvNreal : (v : ℝ) ≤ N := by exact_mod_cast hvN
    have hN0 : (0 : ℝ) < N := by linarith
    have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
    have hN2 : (0 : ℝ) < (N : ℝ) - 2 := by linarith
    have hq : (0 : ℝ) ≤ (v : ℝ) / N := by positivity
    have h1 : ((v : ℝ) - 1) / ((N : ℝ) - 1) ≤ (v : ℝ) / N := by
      apply (div_le_div_iff₀ hN1 hN0).mpr
      nlinarith
    have h2 : ((v : ℝ) - 2) / ((N : ℝ) - 2) ≤ (v : ℝ) / N := by
      apply (div_le_div_iff₀ hN2 hN0).mpr
      nlinarith
    have hratio : (v.choose 3 : ℝ) / (N.choose 3 : ℝ) =
        ((v : ℝ) / N) * (((v : ℝ) - 1) / ((N : ℝ) - 1)) *
          (((v : ℝ) - 2) / ((N : ℝ) - 2)) := by
      rw [real_choose_three, real_choose_three]
      field_simp [hN0.ne', hN1.ne', hN2.ne']
    rw [hratio]
    calc
      ((v : ℝ) / N) * (((v : ℝ) - 1) / ((N : ℝ) - 1)) *
          (((v : ℝ) - 2) / ((N : ℝ) - 2)) ≤
          ((v : ℝ) / N) * ((v : ℝ) / N) * ((v : ℝ) / N) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hq) h2
        · exact div_nonneg (by linarith) hN2.le
        · exact mul_nonneg hq hq
      _ = ((v : ℝ) / N) ^ 3 := by ring

/-- Exact cancellation of unconstrained sample coordinates in an event
count. The alphabet size can be any nonzero real number. -/
theorem normalized_cylinder_count (C D B T : ℝ) (hT : T ≠ 0)
    (a m : ℕ) (ha : a ≤ m) :
    (C * D * (B ^ a * T ^ (m - a))) / T ^ m = C * D * (B / T) ^ a := by
  have hpow : T ^ m = T ^ a * T ^ (m - a) := by
    rw [← pow_add, Nat.add_sub_of_le ha]
  rw [hpow, div_pow]
  field_simp <;> ring

/-- The exact natural-number obstruction count, divided by the number of
all triple systems, is the familiar binomial multiplicity times a containment power. -/
theorem normalized_triple_count (N a v : ℕ) (hN : 3 ≤ N) (ha : a ≤ 8 * N) :
    (((8 * N).choose a * N.choose v *
      (v.choose 3 ^ a * N.choose 3 ^ (8 * N - a)) : ℕ) : ℝ) /
        (N.choose 3 : ℝ) ^ (8 * N) =
      ((8 * N).choose a : ℝ) * (N.choose v : ℝ) *
        ((v.choose 3 : ℝ) / (N.choose 3 : ℝ)) ^ a := by
  simp only [Nat.cast_mul, Nat.cast_pow]
  exact normalized_cylinder_count _ _ _ _ (real_choose_three_pos N hN).ne' a (8 * N) ha

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
