import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
/-!
# Dimension-free scalar constants for a fixed-power Dirichlet kernel

Only numerical tail estimates are proved here. Connecting them to spherical
polar-coordinate integrals and the external positive-kernel repair operator
remains separate work; these declarations assert no integral or SOS bound.
-/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds

/-- Exact power bookkeeping for the angular second-moment tail. -/
theorem dirichlet_second_tail_power_identity (n : ℕ) (hn : 2 ≤ n) :
    (4 : ℝ) ^ (2 * (n + 3)) * (2 : ℝ) ^ (n - 2) * 32768 =
      (32 : ℝ) ^ (n + 5) := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
    show (32768 : ℝ) = 2 ^ 15 by norm_num,
    show (32 : ℝ) = 2 ^ 5 by norm_num]
  simp only [← pow_mul, ← pow_add]
  congr 1
  omega

/-- Exact power bookkeeping for the angular fourth-moment tail. -/
theorem dirichlet_fourth_tail_power_identity (n : ℕ) (hn : 2 ≤ n) :
    (4 : ℝ) ^ (2 * (n + 3)) * (2 : ℝ) ^ (n - 2) * 32 =
      (32 : ℝ) ^ (n + 3) := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
    show (32 : ℝ) = 2 ^ 5 by norm_num]
  simp only [← pow_mul, ← pow_add]
  congr 1
  omega

def dirichletSecondTailConstant (n : ℕ) : ℝ :=
  (((n : ℝ) - 1) / ((n : ℝ) + 5)) *
    (Real.pi ^ (2 * (n + 3)) * (Real.pi / 2) ^ (n - 2) / (32 : ℝ) ^ (n + 5))

def dirichletFourthTailConstant (n : ℕ) : ℝ :=
  (((n : ℝ) - 1) / ((n : ℝ) + 3)) *
    (Real.pi ^ (2 * (n + 3)) * (Real.pi / 2) ^ (n - 2) / (32 : ℝ) ^ (n + 3))

theorem dirichlet_second_tail_constant_nonneg (n : ℕ) (hn : 3 ≤ n) :
    0 ≤ dirichletSecondTailConstant n := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hsub : 0 ≤ (n : ℝ) - 1 := by linarith
  unfold dirichletSecondTailConstant
  positivity

theorem dirichlet_fourth_tail_constant_nonneg (n : ℕ) (hn : 3 ≤ n) :
    0 ≤ dirichletFourthTailConstant n := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hsub : 0 ≤ (n : ℝ) - 1 := by linarith
  unfold dirichletFourthTailConstant
  positivity

theorem dirichlet_second_tail_constant_le (n : ℕ) (hn : 3 ≤ n) :
    dirichletSecondTailConstant n ≤ 1 / 32768 := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hratio : ((n : ℝ) - 1) / ((n : ℝ) + 5) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    linarith
  have hpi2 : Real.pi / 2 ≤ 2 := by linarith [Real.pi_lt_four]
  have hnum : Real.pi ^ (2 * (n + 3)) * (Real.pi / 2) ^ (n - 2) ≤
      (4 : ℝ) ^ (2 * (n + 3)) * (2 : ℝ) ^ (n - 2) := by
    apply mul_le_mul (pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_four.le _)
      (pow_le_pow_left₀ (by positivity) hpi2 _) (by positivity) (by positivity)
  unfold dirichletSecondTailConstant
  calc
    _ ≤ 1 * ((4 : ℝ) ^ (2 * (n + 3)) * (2 : ℝ) ^ (n - 2) /
        (32 : ℝ) ^ (n + 5)) := by
      apply mul_le_mul hratio (div_le_div_of_nonneg_right hnum (by positivity))
        (by positivity) (by norm_num)
    _ = 1 / 32768 := by
      rw [one_mul]
      apply (div_eq_div_iff (by positivity) (by norm_num : (32768 : ℝ) ≠ 0)).2
      simpa only [one_mul] using dirichlet_second_tail_power_identity n (by omega)

theorem dirichlet_fourth_tail_constant_le (n : ℕ) (hn : 3 ≤ n) :
    dirichletFourthTailConstant n ≤ 1 / 32 := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hratio : ((n : ℝ) - 1) / ((n : ℝ) + 3) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    linarith
  have hpi2 : Real.pi / 2 ≤ 2 := by linarith [Real.pi_lt_four]
  have hnum : Real.pi ^ (2 * (n + 3)) * (Real.pi / 2) ^ (n - 2) ≤
      (4 : ℝ) ^ (2 * (n + 3)) * (2 : ℝ) ^ (n - 2) := by
    apply mul_le_mul (pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_four.le _)
      (pow_le_pow_left₀ (by positivity) hpi2 _) (by positivity) (by positivity)
  unfold dirichletFourthTailConstant
  calc
    _ ≤ 1 * ((4 : ℝ) ^ (2 * (n + 3)) * (2 : ℝ) ^ (n - 2) /
        (32 : ℝ) ^ (n + 3)) := by
      apply mul_le_mul hratio (div_le_div_of_nonneg_right hnum (by positivity))
        (by positivity) (by norm_num)
    _ = 1 / 32 := by
      rw [one_mul]
      apply (div_eq_div_iff (by positivity) (by norm_num : (32 : ℝ) ≠ 0)).2
      simpa only [one_mul] using dirichlet_fourth_tail_power_identity n (by omega)

/-- The numerical second-moment constant after splitting at radius `32/k`. -/
theorem dirichlet_second_moment_constant_le (n : ℕ) (hn : 3 ≤ n) :
    (32 : ℝ) ^ 2 + dirichletSecondTailConstant n ≤ 1025 := by
  have h := dirichlet_second_tail_constant_le n hn
  norm_num at h ⊢
  linarith

/-- The numerical fourth-moment constant after splitting at radius `32/k`. -/
theorem dirichlet_fourth_moment_constant_le (n : ℕ) (hn : 3 ≤ n) :
    (32 : ℝ) ^ 4 + dirichletFourthTailConstant n ≤ 1048577 := by
  have h := dirichlet_fourth_tail_constant_le n hn
  norm_num at h ⊢
  linarith

/-- Scalar half-contraction at bandwidth `46*D`; this asserts no kernel estimate. -/
theorem kernel_repair_bandwidth_half (D : ℝ) (hD : 0 < D) :
    1025 * D ^ 2 / (46 * D) ^ 2 ≤ 1 / 2 := by
  apply (div_le_iff₀ (sq_pos_of_pos (by positivity : (0 : ℝ) < 46 * D))).2
  nlinarith [sq_nonneg D]

end OptimalConvergenceRates.SphereDimensionBounds
