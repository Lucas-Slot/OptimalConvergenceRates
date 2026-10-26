import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
/-! Exact dimension and order arithmetic for the sphere upper bound.
Subsequent modules construct the kernel and local SOS certificate. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.DimensionUpperConstants

def L (n : ℕ) : ℝ := 1+(Nat.clog 2 n : ℝ)
def nu (n : ℕ) : ℕ := (n+3)/4
def selectorShift (n : ℕ) : ℝ := (383+531200*(L n)^2)/3
def radialShift (n : ℕ) : ℝ := 15211*((Nat.clog 2 n : ℝ)+2)
def totalShift (n : ℕ) : ℝ := (radialShift n+1)*selectorShift n
def momentBase (n r : ℕ) : ℝ :=
  Real.pi*((n:ℝ)+12*(nu n:ℝ)+1)/(2*(r:ℝ)+(n:ℝ)-6*(nu n:ℝ)-2)
def momentBound (n r : ℕ) : ℝ := (momentBase n r)^4
def absoluteUpperConstant : ℝ := 192*Real.pi^4*5476140000

theorem one_le_L (n : ℕ) : 1 ≤ L n := by
  have hJ : (0:ℝ) ≤ (Nat.clog 2 n:ℝ) := Nat.cast_nonneg _
  unfold L
  linarith

theorem selectorShift_le (n : ℕ) : selectorShift n ≤ 180000*(L n)^2 := by
  have h := one_le_L n
  unfold selectorShift
  nlinarith [sq_nonneg (L n-1)]

theorem radialShift_add_one_le (n : ℕ) : radialShift n+1 ≤ 30423*L n := by
  have hJ : (0:ℝ) ≤ (Nat.clog 2 n:ℝ) := Nat.cast_nonneg _
  unfold radialShift L
  linarith

theorem totalShift_le (n : ℕ) : totalShift n ≤ 5476140000*(L n)^3 := by
  have hL := one_le_L n
  have hS : 0 ≤ selectorShift n := by unfold selectorShift; positivity
  have h := mul_le_mul (radialShift_add_one_le n) (selectorShift_le n) hS (by positivity)
  unfold totalShift
  convert h using 1; ring

theorem one_le_totalShift (n : ℕ) : 1 ≤ totalShift n := by
  have hS : 1 ≤ selectorShift n := by
    unfold selectorShift
    nlinarith [sq_nonneg (L n)]
  have hZ : 0 ≤ radialShift n := by unfold radialShift; positivity
  unfold totalShift
  nlinarith

theorem ceiling_dimension_bounds (n : ℕ) (hn : 3 ≤ n) :
    n+12*nu n+1 ≤ 6*n ∧ 6*nu n+2 ≤ 3*n := by
  unfold nu
  constructor <;> omega

theorem physical_order_bounds (n d r : ℕ) (hn : 3 ≤ n) (hd : 4 ≤ d) (hr : 8 * n * d ≤ r) :
    0<(r:ℝ) ∧
    (31/16:ℝ)*(r:ℝ) ≤ 2*(r:ℝ)+(n:ℝ)-6*(nu n:ℝ)-2 := by
  have hr32 : 32*n ≤ r := by nlinarith
  have hr32R : (32:ℝ)*(n:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr32
  have hnR : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hceil : 6*(nu n:ℝ)+2 ≤ 3*(n:ℝ) := by
    exact_mod_cast (ceiling_dimension_bounds n hn).2
  constructor <;> linarith

theorem momentBase_nonneg (n d r : ℕ) (hn : 3 ≤ n) (hd : 4 ≤ d) (hr : 8 * n * d ≤ r) :
    0 ≤ momentBase n r := by
  have hp := physical_order_bounds n d r hn hd hr
  have hden : 0<2*(r:ℝ)+(n:ℝ)-6*(nu n:ℝ)-2 := by linarith [hp.1]
  unfold momentBase
  exact div_nonneg (by positivity) hden.le

theorem degree_mul_momentBase_le (n d r : ℕ) (hn : 3 ≤ n) (hd : 4 ≤ d)
    (hr : 8 * n * d ≤ r) : (d:ℝ)*momentBase n r ≤ 48/31 := by
  have hp := physical_order_bounds n d r hn hd hr
  have hden : 0<2*(r:ℝ)+(n:ℝ)-6*(nu n:ℝ)-2 := by linarith [hp.1]
  have hnum : (n:ℝ)+12*(nu n:ℝ)+1 ≤ 6*(n:ℝ) := by
    exact_mod_cast (ceiling_dimension_bounds n hn).1
  have hnum0 : 0 ≤ (n:ℝ)+12*(nu n:ℝ)+1 := by positivity
  have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hnum0
  have hpiN : Real.pi*((n:ℝ)+12*(nu n:ℝ)+1) ≤ 24*(n:ℝ) :=
    hpi.trans (by linarith)
  have hdn : (8:ℝ)*(n:ℝ)*(d:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have htop : (d:ℝ)*Real.pi*((n:ℝ)+12*(nu n:ℝ)+1) ≤ 3*(r:ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hpiN (Nat.cast_nonneg d : (0:ℝ) ≤ d)
    nlinarith
  unfold momentBase
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hden).2
  linarith [hp.2]

theorem taylor_smallness (n d r : ℕ) (hn : 3 ≤ n) (hd : 4 ≤ d) (hr : 8 * n * d ≤ r) :
    (d:ℝ)^4/24*momentBound n r ≤ 1/4 := by
  have hpow := pow_le_pow_left₀
    (mul_nonneg (Nat.cast_nonneg d) (momentBase_nonneg n d r hn hd hr))
    (degree_mul_momentBase_le n d r hn hd hr) 4
  calc
    (d:ℝ)^4/24*momentBound n r=((d:ℝ)*momentBase n r)^4/24 := by
      unfold momentBound
      ring
    _  ≤  (48/31:ℝ)^4/24 := div_le_div_of_nonneg_right hpow (by norm_num)
    _  ≤  1/4 := by norm_num

theorem momentBound_le (n d r : ℕ) (hn : 3 ≤ n) (hd : 4 ≤ d) (hr : 8 * n * d ≤ r) :
    momentBound n r ≤ (4*Real.pi*(n:ℝ)/(r:ℝ))^4 := by
  have hp := physical_order_bounds n d r hn hd hr
  have hden : 0<2*(r:ℝ)+(n:ℝ)-6*(nu n:ℝ)-2 := by linarith [hp.1]
  have hnum : (n:ℝ)+12*(nu n:ℝ)+1 ≤ 6*(n:ℝ) := by
    exact_mod_cast (ceiling_dimension_bounds n hn).1
  have hden2 : (3/2:ℝ)*(r:ℝ) ≤ 2*(r:ℝ)+(n:ℝ)-6*(nu n:ℝ)-2 := by linarith [hp.2]
  have hbase : momentBase n r ≤ 4*Real.pi*(n:ℝ)/(r:ℝ) := by
    unfold momentBase
    apply (div_le_iff₀ hden).2
    calc
      Real.pi*((n:ℝ)+12*(nu n:ℝ)+1)  ≤  Real.pi*(6*(n:ℝ)) :=
        mul_le_mul_of_nonneg_left hnum Real.pi_pos.le
      _ = (4*Real.pi*(n:ℝ)/(r:ℝ))*((3/2:ℝ)*(r:ℝ)) := by
        field_simp [hp.1.ne']
        ring
      _  ≤  _ := mul_le_mul_of_nonneg_left hden2 (by positivity)
  exact pow_le_pow_left₀ (momentBase_nonneg n d r hn hd hr) hbase 4

theorem absoluteUpperConstant_pos : 0 < absoluteUpperConstant := by
  unfold absoluteUpperConstant
  positivity

/-- The exact numerical coefficient in the PDF. Kernel and local-SOS
existence are not conclusions of this arithmetic theorem. -/
theorem upper_error_coefficient_bound (n d r : ℕ) (hn : 3 ≤ n) (hd : 4 ≤ d)
    (hr : 8 * n * d ≤ r) {tau beta : ℝ} (htau0 : 0 ≤ tau) (hbeta0 : 0 ≤ beta)
    (htau : tau ≤ (d : ℝ) ^ 4 / 24) (hbeta : beta ≤ (d : ℝ) ^ 4 / 3) :
    2*momentBound n r*(tau+totalShift n*beta) ≤
      absoluteUpperConstant*((d:ℝ)^4*(n:ℝ)^4*(L n)^3/(r:ℝ)^4) := by
  have hG1 := one_le_totalShift n
  have hG0 : 0 ≤ totalShift n := by linarith
  have hscaled := mul_le_mul_of_nonneg_right hG1
    (by positivity : (0:ℝ) ≤ (d:ℝ)^4/24)
  have hbetaG := mul_le_mul_of_nonneg_left hbeta hG0
  have hcoeff : tau+totalShift n*beta ≤ (3/8:ℝ)*totalShift n*(d:ℝ)^4 := by
    nlinarith
  have hcoeff0 : 0 ≤ tau+totalShift n*beta := by positivity
  calc
    2*momentBound n r*(tau+totalShift n*beta) ≤
        2*(4*Real.pi*(n:ℝ)/(r:ℝ))^4*((3/8:ℝ)*totalShift n*(d:ℝ)^4) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (momentBound_le n d r hn hd hr)
        (by norm_num : (0:ℝ) ≤ 2)) hcoeff hcoeff0 (by positivity)
    _ = (192*Real.pi^4*(d:ℝ)^4*(n:ℝ)^4/(r:ℝ)^4)*totalShift n := by ring
    _ ≤ (192*Real.pi^4*(d:ℝ)^4*(n:ℝ)^4/(r:ℝ)^4)*
        (5476140000*(L n)^3) :=
      mul_le_mul_of_nonneg_left (totalShift_le n) (by positivity)
    _ = absoluteUpperConstant*((d:ℝ)^4*(n:ℝ)^4*(L n)^3/(r:ℝ)^4) := by
      unfold absoluteUpperConstant
      ring

end OptimalConvergenceRates.SphereDimensionBounds.DimensionUpperConstants
