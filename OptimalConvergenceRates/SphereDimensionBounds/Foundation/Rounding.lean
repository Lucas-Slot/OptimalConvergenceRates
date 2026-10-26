import OptimalConvergenceRates.SphereDimensionBounds.Foundation.ScalarAlgebra

/-! Rounding real coordinates to signs in the quartic construction. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

def roundSign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

theorem roundSign_sq (x : ℝ) : roundSign x ^ 2 = 1 := by
  unfold roundSign
  split <;> norm_num

theorem roundSign_abs (x : ℝ) : |roundSign x| = 1 := by
  unfold roundSign
  split <;> norm_num

theorem roundSign_mul_abs (x : ℝ) : roundSign x * |x| = x := by
  by_cases hx : 0 ≤ x
  · simp [roundSign, hx, abs_of_nonneg hx]
  · simp [roundSign, hx, abs_of_neg (lt_of_not_ge hx)]

theorem abs_sub_one_le_abs_sq_sub_one {u : ℝ} (hu : 0 ≤ u) :
    |u - 1| ≤ |u ^ 2 - 1| := by
  have hf : u ^ 2 - 1 = (u - 1) * (u + 1) := by ring
  rw [hf, abs_mul, abs_of_nonneg (by linarith : 0 ≤ u + 1)]
  have h := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ u + 1)
    (abs_nonneg (u - 1))
  simpa using h

theorem abs_mul_sub_one_le_errors {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |u * v - 1| ≤ |u ^ 2 - 1| + |v ^ 2 - 1| := by
  have hulo := neg_le_abs (u ^ 2 - 1)
  have huhi := le_abs_self (u ^ 2 - 1)
  have hvlo := neg_le_abs (v ^ 2 - 1)
  have hvhi := le_abs_self (v ^ 2 - 1)
  apply abs_le.mpr
  by_cases huv : u ≤ v
  · have hlow : u ^ 2 ≤ u * v := by nlinarith [mul_nonneg hu (sub_nonneg.mpr huv)]
    have hhigh : u * v ≤ v ^ 2 := by nlinarith [mul_nonneg hv (sub_nonneg.mpr huv)]
    constructor <;> nlinarith [abs_nonneg (u ^ 2 - 1), abs_nonneg (v ^ 2 - 1)]
  · have hvu : v ≤ u := le_of_not_ge huv
    have hlow : v ^ 2 ≤ u * v := by nlinarith [mul_nonneg hv (sub_nonneg.mpr hvu)]
    have hhigh : u * v ≤ u ^ 2 := by nlinarith [mul_nonneg hu (sub_nonneg.mpr hvu)]
    constructor <;> nlinarith [abs_nonneg (u ^ 2 - 1), abs_nonneg (v ^ 2 - 1)]

theorem roundSign_error (x : ℝ) : |roundSign x - x| ≤ |x ^ 2 - 1| := by
  have heq : roundSign x - x = roundSign x * (1 - |x|) := by
    rw [mul_sub, mul_one, roundSign_mul_abs]
  calc
    |roundSign x - x| = abs (1 - abs x) := by rw [heq, abs_mul, roundSign_abs, one_mul]
    _ = abs (abs x - 1) := abs_sub_comm 1 |x|
    _ ≤ abs ((abs x) ^ 2 - 1) := abs_sub_one_le_abs_sq_sub_one (abs_nonneg x)
    _ = |x ^ 2 - 1| := by rw [sq_abs]

theorem roundSign_product_error (x y : ℝ) :
    |roundSign x * roundSign y - x * y| ≤ |x ^ 2 - 1| + |y ^ 2 - 1| := by
  have hprod : x * y = (roundSign x * roundSign y) * (|x| * |y|) := by
    calc
      x * y = (roundSign x * |x|) * (roundSign y * |y|) := by
        rw [roundSign_mul_abs, roundSign_mul_abs]
      _ = (roundSign x * roundSign y) * (|x| * |y|) := by ring
  have heq : roundSign x * roundSign y - x * y =
      (roundSign x * roundSign y) * (1 - |x| * |y|) := by rw [hprod]; ring
  calc
    |roundSign x * roundSign y - x * y| = abs (1 - abs x * abs y) := by
      rw [heq, abs_mul, abs_mul, roundSign_abs, roundSign_abs, one_mul, one_mul]
    _ = abs (abs x * abs y - 1) := abs_sub_comm 1 (|x| * |y|)
    _ ≤ abs ((abs x) ^ 2 - 1) + abs ((abs y) ^ 2 - 1) :=
      abs_mul_sub_one_le_errors (abs_nonneg x) (abs_nonneg y)
    _ = |x ^ 2 - 1| + |y ^ 2 - 1| := by rw [sq_abs, sq_abs]

theorem rounded_clause_bound (x y z b : ℝ) (hb : |b| = 1) :
    (roundSign x * roundSign y - b * roundSign z) ^ 2 ≤
      2 * (x * y - b * z) ^ 2 +
        6 * ((x ^ 2 - 1) ^ 2 + (y ^ 2 - 1) ^ 2 + (z ^ 2 - 1) ^ 2) := by
  have herr : |(roundSign x * roundSign y - b * roundSign z) - (x * y - b * z)| ≤
      |x ^ 2 - 1| + |y ^ 2 - 1| + |z ^ 2 - 1| := by
    have heq : (roundSign x * roundSign y - b * roundSign z) - (x * y - b * z) =
        (roundSign x * roundSign y - x * y) - b * (roundSign z - z) := by ring
    rw [heq]
    calc
      |(roundSign x * roundSign y - x * y) - b * (roundSign z - z)| ≤
          |roundSign x * roundSign y - x * y| + |b * (roundSign z - z)| :=
        by simpa using (abs_sub_le (roundSign x * roundSign y - x * y) (0 : ℝ)
          (b * (roundSign z - z)))
      _ = |roundSign x * roundSign y - x * y| + |roundSign z - z| := by
        rw [abs_mul, hb, one_mul]
      _ ≤ |x ^ 2 - 1| + |y ^ 2 - 1| + |z ^ 2 - 1| :=
        add_le_add (roundSign_product_error x y) (roundSign_error z)
  simpa only [sq_abs] using rounding_clause_bound
    (roundSign x * roundSign y - b * roundSign z) (x * y - b * z)
    |x ^ 2 - 1| |y ^ 2 - 1| |z ^ 2 - 1| herr

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
