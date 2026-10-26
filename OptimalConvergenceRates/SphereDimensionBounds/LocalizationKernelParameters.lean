import OptimalConvergenceRates.SphereDimensionBounds.AngularWeightShift
import Mathlib.Data.Nat.Choose.Bounds

/-! Exact ceiling, physical-degree and moment constants for the actual
dimension-optimal localization kernel. The shifted angular quotient is
an explicit input; spectral construction supplies it separately. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.LocalizationKernelParameters

open Polynomial TaylorKernelData AngularWeightShift

def nu (n : ℕ) : ℕ := (n+3)/4
def multiplier (n : ℕ) : ℕ := 3*nu n
def effectiveDimension (n : ℕ) : ℕ := n+12*nu n
def residualOrder (n r : ℕ) : ℕ := r-9*nu n

theorem nu_pos {n : ℕ} (hn : 3 ≤ n) : 1≤nu n := by unfold nu;omega

theorem nu_upper {n : ℕ} (hn : 3 ≤ n) : 5*nu n≤2*n := by unfold nu;omega

theorem dimension_lower {n : ℕ} (hn : 3 ≤ n) : 15≤effectiveDimension n := by
  have h := nu_pos hn
  unfold effectiveDimension
  omega

theorem dimension_upper {n : ℕ} (hn : 3 ≤ n) : 5*effectiveDimension n≤29*n := by
  have h := nu_upper hn
  unfold effectiveDimension
  omega

theorem order_threshold {n d r : ℕ} (hd : 4 ≤ d) (hr : 8 * n * d ≤ r) : 32*n≤r := by
  nlinarith

theorem order_lower {n d r : ℕ} (hn : 3 ≤ n) (hd : 4 ≤ d) (hr : 8 * n * d ≤ r) :
    71*r≤80*residualOrder n r := by
  have h1 := nu_upper hn
  have h2 := order_threshold hd hr
  unfold residualOrder
  omega

theorem order_ge_dimension {n d r : ℕ} (hn : 3 ≤ n) (hd : 4 ≤ d) (hr : 8 * n * d ≤ r) :
    3*effectiveDimension n≤residualOrder n r := by
  have h1 := nu_upper hn
  have h2 := order_threshold hd hr
  unfold residualOrder effectiveDimension
  omega

theorem physical_root_budget {n d r : ℕ} (hn : 3 ≤ n) (hd : 4 ≤ d) (hr : 8 * n * d ≤ r) :
    3*multiplier n+residualOrder n r=r := by
  have h1 := nu_upper hn
  have h2 := order_threshold hd hr
  unfold multiplier residualOrder
  omega

theorem shifted_dimension (n : ℕ) : n+4*multiplier n-2=effectiveDimension n-2 := by
  unfold multiplier effectiveDimension
  omega

/-- A rational comparison with slack: the actual spectral constant is
smaller than the retained (12n/r)^4 bound. -/
theorem spectral_rate_bound {N ell n r : ℝ} (hN : 0 ≤ N) (hn : 0 ≤ n)
    (hell : 0 < ell) (hr : 0 < r) (hDim : 5 * N ≤ 29 * n) (hOrd : 71 * r ≤ 80 * ell) :
    (256/25:ℝ)*N^4/ell^4≤(12*n/r)^4 := by
  have hc1 := mul_le_mul_of_nonneg_right hDim hr.le
  have hc2 := mul_le_mul_of_nonneg_left hOrd hn
  have hcross : N*r≤((20/3:ℝ)*n)*ell := by
    nlinarith only [hc1,hc2,mul_nonneg hn hell.le]
  have hratio : N/ell≤(20/3:ℝ)*(n/r) := by
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ hell hr).mpr
    exact hcross
  have hpow := pow_le_pow_left₀ (div_nonneg hN hell.le) hratio 4
  calc
    (256/25:ℝ)*N^4/ell^4=(256/25:ℝ)*(N/ell)^4 := by ring
    _≤(256/25:ℝ)*((20/3:ℝ)*(n/r))^4 := mul_le_mul_of_nonneg_left hpow (by norm_num)
    _≤(12*n/r)^4 := by
      have hc : (256/25:ℝ)*(20/3:ℝ)^4≤(12:ℝ)^4 := by norm_num
      convert mul_le_mul_of_nonneg_right hc (pow_nonneg (div_nonneg hn hr.le) 4) using 1 <;> ring

theorem parameter_rate_bound {n d r : ℕ} (hn : 3 ≤ n) (hd : 4 ≤ d) (hr : 8 * n * d ≤ r) :
    (256/25:ℝ)*(effectiveDimension n:ℝ)^4/(residualOrder n r:ℝ)^4≤
      (12*(n:ℝ)/(r:ℝ))^4 := by
  have hD := dimension_lower hn
  have hL := order_ge_dimension hn hd hr
  have hR := order_threshold hd hr
  apply spectral_rate_bound (by positivity) (by positivity)
    (by exact_mod_cast (show 0<residualOrder n r by omega))
    (by exact_mod_cast (show 0<r by omega))
  · exact_mod_cast dimension_upper hn
  · exact_mod_cast order_lower hn hd hr

theorem actual_moment_bound {n d r : ℕ} (hn : 3 ≤ n) (hd : 4 ≤ d) (hr : 8 * n * d ≤ r)
    (chi : Polynomial ℝ) (hchi : chi ≠ 0)
    (hquotient : 4 * normalizedZonalFunctional (effectiveDimension n - 2) ((1 - X) ^ 2 * chi ^ 2) /
      normalizedZonalFunctional (effectiveDimension n - 2) (chi ^ 2) ≤
        (256 / 25 : ℝ) * (effectiveDimension n : ℝ) ^ 4 / (residualOrder n r : ℝ) ^ 4) :
    fourthMoment (by omega : 0<n) (multiplier n) chi≤(12*(n:ℝ)/(r:ℝ))^4 := by
  have hshift := fourthMoment_eq_shifted_ratio (by omega : 2≤n) (multiplier n) chi hchi
  rw [shifted_dimension] at hshift
  rw [hshift]
  exact hquotient.trans (parameter_rate_bound hn hd hr)

theorem choose_four_bound (d : ℕ) : (d.choose 4:ℝ)≤(d:ℝ)^4/24 := by
  convert (Nat.choose_le_pow_div (α:=ℝ) 4 d) using 1 <;> norm_num

theorem moment_smallness {n d r : ℕ} (hn : 0 < n) (hd : 0 < d) (hr : 8 * n * d ≤ r)
    (momentValue : ℝ) (hmu0 : 0 ≤ momentValue) (hmu : momentValue ≤ (12 * (n : ℝ) / (r : ℝ)) ^ 4) :
    (d.choose 4:ℝ)*momentValue≤27/128 := by
  have hnr : 0<(n:ℝ) := by exact_mod_cast hn
  have hdr : 0<(d:ℝ) := by exact_mod_cast hd
  have hrr : 0<(r:ℝ) := by exact_mod_cast (show 0<r by nlinarith)
  have hrReal : 8*(n:ℝ)*(d:ℝ)≤r := by exact_mod_cast hr
  have hratio : (d:ℝ)*(12*(n:ℝ)/(r:ℝ))≤3/2 := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hrr).mpr
    nlinarith
  have hratio0 : 0≤(d:ℝ)*(12*(n:ℝ)/(r:ℝ)) := by positivity
  have hp := pow_le_pow_left₀ hratio0 hratio 4
  calc
    (d.choose 4:ℝ)*momentValue≤((d:ℝ)^4/24)*(12*(n:ℝ)/(r:ℝ))^4 :=
      mul_le_mul (choose_four_bound d) hmu hmu0 (by positivity)
    _=((d:ℝ)*(12*(n:ℝ)/(r:ℝ)))^4/24 := by ring
    _≤(3/2:ℝ)^4/24 := div_le_div_of_nonneg_right hp (by norm_num)
    _=27/128 := by norm_num

theorem actual_moment_smallness {n d r : ℕ} (hn : 3 ≤ n) (hd : 4 ≤ d) (hr : 8 * n * d ≤ r)
    (chi : Polynomial ℝ) (hchi : chi ≠ 0)
    (hquotient : 4 * normalizedZonalFunctional (effectiveDimension n - 2) ((1 - X) ^ 2 * chi ^ 2) /
      normalizedZonalFunctional (effectiveDimension n - 2) (chi ^ 2) ≤
        (256 / 25 : ℝ) * (effectiveDimension n : ℝ) ^ 4 / (residualOrder n r : ℝ) ^ 4) :
    (d.choose 4:ℝ)*fourthMoment (by omega : 0<n) (multiplier n) chi≤27/128 := by
  exact moment_smallness (by omega) (by omega) hr _ (fourthMoment_nonneg _ _ _)
    (actual_moment_bound hn hd hr chi hchi hquotient)

theorem actual_moment_quarter {n d r : ℕ} (hn : 3 ≤ n) (hd : 4 ≤ d) (hr : 8 * n * d ≤ r)
    (chi : Polynomial ℝ) (hchi : chi ≠ 0)
    (hquotient : 4 * normalizedZonalFunctional (effectiveDimension n - 2) ((1 - X) ^ 2 * chi ^ 2) /
      normalizedZonalFunctional (effectiveDimension n - 2) (chi ^ 2) ≤
        (256 / 25 : ℝ) * (effectiveDimension n : ℝ) ^ 4 / (residualOrder n r : ℝ) ^ 4) :
    (d.choose 4:ℝ)*fourthMoment (by omega : 0<n) (multiplier n) chi≤1/4 :=
  (actual_moment_smallness hn hd hr chi hchi hquotient).trans (by norm_num)

end OptimalConvergenceRates.SphereDimensionBounds.LocalizationKernelParameters
