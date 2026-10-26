import Mathlib.Analysis.Real.Pi.Bounds
import OptimalConvergenceRates.SphereDimensionBounds.LocalizationKernelParameters
import OptimalConvergenceRates.SphereDimensionBounds.DimensionUpperConstants

/-! The retained upper coefficient for the actual spectral localization
moment. No comparison with the older auxiliary momentBound is assumed. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.LocalizationUpperCoefficient

open DimensionUpperConstants TaylorKernelData LocalizationKernelParameters

theorem twelve_scale_le_pi_scale (n r : ℕ) :
    (12*(n:ℝ)/(r:ℝ))^4≤(4*Real.pi*(n:ℝ)/(r:ℝ))^4 := by
  have hpi : (12:ℝ)≤4*Real.pi := by linarith [Real.pi_gt_three]
  have hnr : 0≤(n:ℝ)/(r:ℝ) := div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg r)
  have hscaled := mul_le_mul_of_nonneg_right hpi hnr
  have hbase : 12*(n:ℝ)/(r:ℝ)≤4*Real.pi*(n:ℝ)/(r:ℝ) := by
    simpa only [mul_div_assoc] using hscaled
  exact pow_le_pow_left₀ (by positivity) hbase 4

/-- Actual nonnegative localization moment with the proved (12n/r)^4
rate yields the unchanged absolute PDF upper coefficient. No older
momentBase/momentBound estimate is supplied or used. -/
theorem upper_error_coefficient_bound (n d r : ℕ) {momentValue tau beta : ℝ}
    (hMoment0 : 0 ≤ momentValue) (hMoment : momentValue ≤ (12 * (n : ℝ) / (r : ℝ)) ^ 4)
    (htau : tau ≤ (d : ℝ) ^ 4 / 24) (hbeta : beta ≤ (d : ℝ) ^ 4 / 3) :
    2*momentValue*(tau+totalShift n*beta)≤
      absoluteUpperConstant*((d:ℝ)^4*(n:ℝ)^4*(L n)^3/(r:ℝ)^4) := by
  have hG1 := one_le_totalShift n
  have hG0 : 0≤totalShift n := by linarith
  have hscaled := mul_le_mul_of_nonneg_right hG1
    (by positivity : (0:ℝ)≤(d:ℝ)^4/24)
  have hbetaG := mul_le_mul_of_nonneg_left hbeta hG0
  have hcoeff : tau+totalShift n*beta≤(3/8:ℝ)*totalShift n*(d:ℝ)^4 := by
    nlinarith
  have hMomentPi := hMoment.trans (twelve_scale_le_pi_scale n r)
  calc
    2*momentValue*(tau+totalShift n*beta)≤
        2*momentValue*((3/8:ℝ)*totalShift n*(d:ℝ)^4) :=
      mul_le_mul_of_nonneg_left hcoeff (by positivity)
    _≤2*(4*Real.pi*(n:ℝ)/(r:ℝ))^4*((3/8:ℝ)*totalShift n*(d:ℝ)^4) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hMomentPi (by norm_num : (0:ℝ)≤2)) (by positivity)
    _=(192*Real.pi^4*(d:ℝ)^4*(n:ℝ)^4/(r:ℝ)^4)*totalShift n := by ring
    _≤(192*Real.pi^4*(d:ℝ)^4*(n:ℝ)^4/(r:ℝ)^4)*(5476140000*(L n)^3) :=
      mul_le_mul_of_nonneg_left (totalShift_le n) (by positivity)
    _=absoluteUpperConstant*((d:ℝ)^4*(n:ℝ)^4*(L n)^3/(r:ℝ)^4) := by
      unfold absoluteUpperConstant
      ring

/-- The numerical wrapper consumed by the actual general-degree Taylor
transfer, with its actual sphere fourth moment and actual beta(d). -/
theorem actual_kernel_error_coefficient_bound {n : ℕ} (hn : 0 < n) (d r m : ℕ)
    (hd : 4 ≤ d) (chi : Polynomial ℝ)
    (hMoment : fourthMoment hn m chi ≤ (12 * (n : ℝ) / (r : ℝ)) ^ 4) :
    2*fourthMoment hn m chi*((d.choose 4:ℝ)+totalShift n*GlobalCubicCorrection.beta d)≤
      absoluteUpperConstant*((d:ℝ)^4*(n:ℝ)^4*(L n)^3/(r:ℝ)^4) :=
  upper_error_coefficient_bound n d r (fourthMoment_nonneg hn m chi) hMoment
    (choose_four_bound d) (GlobalCubicCorrection.beta_le_fourth hd)

end OptimalConvergenceRates.SphereDimensionBounds.LocalizationUpperCoefficient
