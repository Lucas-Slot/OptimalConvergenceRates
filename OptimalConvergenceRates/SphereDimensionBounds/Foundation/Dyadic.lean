import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
/-!
# Finite dyadic estimates for the sphere-SOS transfer

This file isolates an integer induction and its real-valued consequence.
It supplies no analytic transfer theorem or Boolean hard-instance existence.
The module remains separate from the unproved end-to-end research target.
-/

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

/-- Integer division loses at most a factor two once the numerator is at least
the positive denominator. This supplies the linear lower bound on `K`. -/
theorem nat_le_twice_mul_div (N D : ℕ) (hD : 0 < D) (hN : D ≤ N) :
    N ≤ 2 * D * (N / D) := by
  have hquot : 1 ≤ N / D := (Nat.one_le_div_iff hD).2 hN
  have hrem : N % D < D := Nat.mod_lt N hD
  have hdecomp : N % D + D * (N / D) = N := Nat.mod_add_div N D
  have hmul : D ≤ D * (N / D) := by
    simpa using Nat.mul_le_mul_left D hquot
  nlinarith only [hrem, hdecomp, hmul]

/-- The polynomial factor in the transfer error is dominated by `4 ^ n`
from the explicit base point `n = 16` onwards. -/
theorem dyadic_polynomial_le (n : ℕ) (hn : 16 ≤ n) :
    688128 * n * (n + 1) ^ 2 ≤ 4 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have htwo : 2 ≤ n := by omega
      have hsquare : 4 ≤ n ^ 2 := by
        simpa using Nat.pow_le_pow_left htwo 2
      have hstep : (n + 2) ^ 2 ≤ 4 * n * (n + 1) := by
        nlinarith only [hsquare]
      have hpoly : (n + 1) * (n + 2) ^ 2 ≤ 4 * (n * (n + 1) ^ 2) := by
        have hmul := Nat.mul_le_mul_left (n + 1) hstep
        nlinarith only [hmul]
      calc
        688128 * (n + 1) * (n + 1 + 1) ^ 2 =
            688128 * ((n + 1) * (n + 2) ^ 2) := by ring
        _ ≤ 688128 * (4 * (n * (n + 1) ^ 2)) :=
          Nat.mul_le_mul_left 688128 hpoly
        _ = 4 * (688128 * n * (n + 1) ^ 2) := by ring
        _ ≤ 4 * 4 ^ n := Nat.mul_le_mul_left 4 ih
        _ = 4 ^ (n + 1) := by rw [pow_succ]; ring

/-- The exact real-valued estimate needed after bounding the exponential factor
in the transfer error by `4 ^ (-n)`. -/
theorem dyadic_error_bound (n : ℕ) (hn : 16 ≤ n) :
    (6 : ℝ) * ((n : ℝ) + 1) ^ 2 / (4 : ℝ) ^ n ≤
      1 / (114688 * (n : ℝ)) := by
  have hnat := dyadic_polynomial_le n hn
  have hreal : (688128 : ℝ) * (n : ℝ) * ((n : ℝ) + 1) ^ 2 ≤
      (4 : ℝ) ^ n := by
    exact_mod_cast hnat
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hpow : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  apply (div_le_div_iff₀ hpow (by positivity)).2
  nlinarith only [hreal]

/-- The exponential factor in the transfer error is bounded by `4 ^ (-N)`.

The exponent `M` is kept symbolic. In particular this theorem never computes
the enormous dimension threshold used by the explicit construction. -/
theorem dyadic_amplification_bound (N K M : ℕ) (hM : 2 ≤ M)
    (hpower : 3 * N ≤ (M - 2) * K) :
    (2 : ℝ) ^ N * (4 / (2 : ℝ) ^ M) ^ K ≤ 1 / (4 : ℝ) ^ N := by
  have hfactor : (2 : ℝ) ^ M = (2 : ℝ) ^ (M - 2) * 4 := by
    calc
      (2 : ℝ) ^ M = (2 : ℝ) ^ ((M - 2) + 2) := by congr 1; omega
      _ = (2 : ℝ) ^ (M - 2) * 4 := by rw [pow_add]; norm_num
  have hratio : (4 : ℝ) / (2 : ℝ) ^ M = 1 / (2 : ℝ) ^ (M - 2) := by
    rw [hfactor]
    field_simp [pow_ne_zero (M - 2) (by norm_num : (2 : ℝ) ≠ 0)] <;> ring
  have hformula : ((4 : ℝ) / (2 : ℝ) ^ M) ^ K =
      1 / (2 : ℝ) ^ ((M - 2) * K) := by
    rw [hratio, one_div_pow, ← pow_mul]
  have hpow : (2 : ℝ) ^ (3 * N) ≤ (2 : ℝ) ^ ((M - 2) * K) :=
    pow_le_pow_right₀ (by norm_num) hpower
  have hcmp : 1 / (2 : ℝ) ^ ((M - 2) * K) ≤ 1 / (2 : ℝ) ^ (3 * N) :=
    one_div_le_one_div_of_le (by positivity) hpow
  have hsplit : (2 : ℝ) ^ (3 * N) = (2 : ℝ) ^ N * (4 : ℝ) ^ N := by
    calc
      (2 : ℝ) ^ (3 * N) = ((2 : ℝ) ^ 3) ^ N := pow_mul _ _ _
      _ = ((2 : ℝ) * 4) ^ N := by norm_num
      _ = (2 : ℝ) ^ N * (4 : ℝ) ^ N := mul_pow _ _ _
  calc
    (2 : ℝ) ^ N * (4 / (2 : ℝ) ^ M) ^ K =
        (2 : ℝ) ^ N * (1 / (2 : ℝ) ^ ((M - 2) * K)) := by rw [hformula]
    _ ≤ (2 : ℝ) ^ N * (1 / (2 : ℝ) ^ (3 * N)) :=
      mul_le_mul_of_nonneg_left hcmp (by positivity)
    _ = 1 / (4 : ℝ) ^ N := by
      rw [hsplit]
      field_simp [pow_ne_zero N (by norm_num : (2 : ℝ) ≠ 0),
        pow_ne_zero N (by norm_num : (4 : ℝ) ≠ 0)]

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
