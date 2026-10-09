import OptimalConvergenceRates.GeneralArchimedean.Defs
import Mathlib.Data.Real.Sqrt

/-!
# Inverting logarithmic-over-quadratic rates

Elementary real inequalities turning lower bounds of the form
`c * (log x)^(2k) / x^2 ≤ epsilon` into lower bounds on `x`.
-/

noncomputable section

namespace OptimalConvergenceRates.GeneralArchimedean

private theorem log_inv_le_scale_log_of_rate
    {c epsilon x : ℝ} {q : ℕ}
    (hc : 0 < c) (hx : 0 < x)
    (hlog : 1 ≤ Real.log x)
    (hrate : c * Real.log x ^ q / x ^ 2 ≤ epsilon) :
    Real.log epsilon⁻¹ ≤ (2 + |Real.log c|) * Real.log x := by
  have hxSq : 0 < x ^ 2 := sq_pos_of_pos hx
  have hlogPow : 1 ≤ Real.log x ^ q := one_le_pow₀ hlog
  have hcMul : c ≤ c * Real.log x ^ q := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlogPow hc.le
  have hrateMul : c * Real.log x ^ q ≤ epsilon * x ^ 2 :=
    (div_le_iff₀ hxSq).mp hrate
  have hbase : c / x ^ 2 ≤ epsilon :=
    (div_le_iff₀ hxSq).mpr (hcMul.trans hrateMul)
  have hlogBase : Real.log (c / x ^ 2) ≤ Real.log epsilon :=
    Real.log_le_log (div_pos hc hxSq) hbase
  rw [Real.log_div hc.ne' (pow_ne_zero 2 hx.ne'), Real.log_pow] at hlogBase
  norm_num at hlogBase
  have habsMul : |Real.log c| ≤ |Real.log c| * Real.log x := by
    nlinarith [mul_nonneg (abs_nonneg (Real.log c)) (sub_nonneg.mpr hlog)]
  rw [Real.log_inv]
  nlinarith [neg_le_abs (Real.log c)]

/-- Inversion of a fourth-power logarithmic-over-quadratic lower rate. -/
theorem inverseSqrtLogSq_le_of_logFour_rate
    {c epsilon x : ℝ}
    (hc : 0 < c) (hepsilon : 0 < epsilon) (hepsilonOne : epsilon ≤ 1)
    (hx : 0 < x) (hlog : 1 ≤ Real.log x)
    (hrate : c * Real.log x ^ 4 / x ^ 2 ≤ epsilon) :
    Real.sqrt c / (2 + |Real.log c|) ^ 2 * Real.log epsilon⁻¹ ^ 2 /
        Real.sqrt epsilon ≤ x := by
  let B : ℝ := 2 + |Real.log c|
  have hB : 0 < B := by dsimp [B]; positivity
  have hlogEpsilon : Real.log epsilon ≤ 0 :=
    Real.log_nonpos hepsilon.le hepsilonOne
  have hlogInv : 0 ≤ Real.log epsilon⁻¹ := by
    rw [Real.log_inv]
    exact neg_nonneg.mpr hlogEpsilon
  have hcompare : Real.log epsilon⁻¹ ≤ B * Real.log x := by
    simpa only [B] using
      log_inv_le_scale_log_of_rate hc hx hlog hrate
  have hcompareSq : Real.log epsilon⁻¹ ^ 2 ≤ B ^ 2 * Real.log x ^ 2 := by
    calc
      Real.log epsilon⁻¹ ^ 2 ≤ (B * Real.log x) ^ 2 :=
        (sq_le_sq₀ hlogInv (mul_nonneg hB.le (zero_le_one.trans hlog))).mpr hcompare
      _ = B ^ 2 * Real.log x ^ 2 := by ring
  have hxSq : 0 < x ^ 2 := sq_pos_of_pos hx
  have hrateMul : c * Real.log x ^ 4 ≤ epsilon * x ^ 2 :=
    (div_le_iff₀ hxSq).mp hrate
  have hroot : Real.sqrt c * Real.log x ^ 2 ≤ Real.sqrt epsilon * x := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) hx.le)).mp
    calc
      (Real.sqrt c * Real.log x ^ 2) ^ 2 = c * Real.log x ^ 4 := by
        rw [mul_pow, Real.sq_sqrt hc.le]
        ring
      _ ≤ epsilon * x ^ 2 := hrateMul
      _ = (Real.sqrt epsilon * x) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hepsilon.le]
  have hnumerator :
      Real.sqrt c / B ^ 2 * Real.log epsilon⁻¹ ^ 2 ≤
        Real.sqrt c * Real.log x ^ 2 := by
    calc
      Real.sqrt c / B ^ 2 * Real.log epsilon⁻¹ ^ 2 ≤
          Real.sqrt c / B ^ 2 * (B ^ 2 * Real.log x ^ 2) :=
        mul_le_mul_of_nonneg_left hcompareSq (div_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
      _ = Real.sqrt c * Real.log x ^ 2 := by
        field_simp
  calc
    Real.sqrt c / B ^ 2 * Real.log epsilon⁻¹ ^ 2 / Real.sqrt epsilon ≤
        (Real.sqrt c * Real.log x ^ 2) / Real.sqrt epsilon :=
      div_le_div_of_nonneg_right hnumerator (Real.sqrt_nonneg _)
    _ ≤ x := by
      apply (div_le_iff₀ (Real.sqrt_pos.2 hepsilon)).mpr
      simpa only [mul_comm] using hroot

/-- Inversion of a second-power logarithmic-over-quadratic lower rate. -/
theorem inverseSqrtLog_le_of_logTwo_rate
    {c epsilon x : ℝ}
    (hc : 0 < c) (hepsilon : 0 < epsilon) (hepsilonOne : epsilon ≤ 1)
    (hx : 0 < x) (hlog : 1 ≤ Real.log x)
    (hrate : c * Real.log x ^ 2 / x ^ 2 ≤ epsilon) :
    Real.sqrt c / (2 + |Real.log c|) * Real.log epsilon⁻¹ /
        Real.sqrt epsilon ≤ x := by
  let B : ℝ := 2 + |Real.log c|
  have hB : 0 < B := by dsimp [B]; positivity
  have hlogEpsilon : Real.log epsilon ≤ 0 :=
    Real.log_nonpos hepsilon.le hepsilonOne
  have hlogInv : 0 ≤ Real.log epsilon⁻¹ := by
    rw [Real.log_inv]
    exact neg_nonneg.mpr hlogEpsilon
  have hcompare : Real.log epsilon⁻¹ ≤ B * Real.log x := by
    simpa only [B] using
      log_inv_le_scale_log_of_rate hc hx hlog hrate
  have hxSq : 0 < x ^ 2 := sq_pos_of_pos hx
  have hrateMul : c * Real.log x ^ 2 ≤ epsilon * x ^ 2 :=
    (div_le_iff₀ hxSq).mp hrate
  have hroot : Real.sqrt c * Real.log x ≤ Real.sqrt epsilon * x := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans hlog))
      (mul_nonneg (Real.sqrt_nonneg _) hx.le)).mp
    calc
      (Real.sqrt c * Real.log x) ^ 2 = c * Real.log x ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hc.le]
      _ ≤ epsilon * x ^ 2 := hrateMul
      _ = (Real.sqrt epsilon * x) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hepsilon.le]
  have hnumerator :
      Real.sqrt c / B * Real.log epsilon⁻¹ ≤ Real.sqrt c * Real.log x := by
    calc
      Real.sqrt c / B * Real.log epsilon⁻¹ ≤
          Real.sqrt c / B * (B * Real.log x) :=
        mul_le_mul_of_nonneg_left hcompare (div_nonneg (Real.sqrt_nonneg _) hB.le)
      _ = Real.sqrt c * Real.log x := by field_simp
  calc
    Real.sqrt c / B * Real.log epsilon⁻¹ / Real.sqrt epsilon ≤
        (Real.sqrt c * Real.log x) / Real.sqrt epsilon :=
      div_le_div_of_nonneg_right hnumerator (Real.sqrt_nonneg _)
    _ ≤ x := by
      apply (div_le_iff₀ (Real.sqrt_pos.2 hepsilon)).mpr
      simpa only [mul_comm] using hroot

end OptimalConvergenceRates.GeneralArchimedean

end
