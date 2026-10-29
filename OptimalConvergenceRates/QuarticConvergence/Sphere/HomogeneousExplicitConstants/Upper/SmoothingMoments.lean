import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.SphereAngularMoments

/-! Exact first two moments of the polynomial smoothing kernel.
These are actual integrals through the sphere/angular identification. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace SmoothingMoments

open Polynomial SphereAngularMoments

def kernelPower (k : ℕ) : Polynomial ℝ := (1+X)^k
def mass (s k : ℕ) : ℝ := normalizedZonalFunctional s (kernelPower k)
def first (s k : ℕ) : ℝ := normalizedZonalFunctional s (X*kernelPower k)
def second (s k : ℕ) : ℝ := normalizedZonalFunctional s (X^2*kernelPower k)

theorem kernelPower_derivative (k : ℕ) :
    (1-X^2)*(kernelPower k).derivative=C (k:ℝ)*(kernelPower k-X*kernelPower k) := by
  cases k with
  | zero => simp [kernelPower]
  | succ k =>
    simp only [kernelPower,Polynomial.derivative_pow,Polynomial.derivative_add,
      Polynomial.derivative_one,Polynomial.derivative_X,zero_add,mul_one,
      Nat.add_sub_cancel]
    rw [pow_succ]
    ring

theorem kernelPower_X_derivative (k : ℕ) :
    (1-X^2)*(X*kernelPower k).derivative=
      kernelPower k+C (k:ℝ)*(X*kernelPower k)-C ((k:ℝ)+1)*(X^2*kernelPower k) := by
  rw [Polynomial.derivative_mul,Polynomial.derivative_X,one_mul,mul_add]
  have h := kernelPower_derivative k
  calc
    _=(kernelPower k-X^2*kernelPower k)+X*((1-X^2)*(kernelPower k).derivative) := by ring
    _=_ := by rw [h,map_add,map_one];ring

theorem first_relation (s k : ℕ) :
    ((k:ℝ)+(s:ℝ)+1)*first s k=(k:ℝ)*mass s k := by
  have h := angular_stokes s (kernelPower k)
  rw [kernelPower_derivative,←Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul,map_sub] at h
  change (k:ℝ)*(mass s k-first s k)=((s:ℝ)+1)*first s k at h
  linarith

theorem second_relation (s k : ℕ) :
    ((k:ℝ)+(s:ℝ)+2)*second s k=mass s k+(k:ℝ)*first s k := by
  have h := angular_stokes s (X*kernelPower k)
  rw [kernelPower_X_derivative,map_sub,map_add,
    ←Polynomial.smul_eq_C_mul,←Polynomial.smul_eq_C_mul,map_smul,map_smul,
    smul_eq_mul,smul_eq_mul] at h
  have heq : X*(X*kernelPower k)=X^2*kernelPower k := by ring
  rw [heq] at h
  change mass s k+(k:ℝ)*first s k-((k:ℝ)+1)*second s k=
    ((s:ℝ)+1)*second s k at h
  linarith

theorem mass_pos (s k : ℕ) : 0 < mass s k := by
  change 0 < (∫ theta in (0:ℝ)..Real.pi,
    (kernelPower k).eval (Real.cos theta)*Real.sin theta^s)/weightedCosineIntegral s 0
  apply div_pos _ (weightedCosineIntegral_mass_pos s)
  apply intervalIntegral.integral_pos Real.pi_pos
    (show Continuous (fun theta : ℝ ↦
      (kernelPower k).eval (Real.cos theta)*Real.sin theta^s) by fun_prop).continuousOn
  · intro theta htheta
    simp only [kernelPower,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_one,Polynomial.eval_X]
    exact mul_nonneg (pow_nonneg (by linarith [Real.neg_one_le_cos theta]) _)
      (pow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi htheta.1.le htheta.2) _)
  · refine ⟨Real.pi/2,⟨by positivity,by linarith [Real.pi_pos]⟩,?_⟩
    simp [kernelPower]

theorem first_normalized (s k : ℕ) :
    first s k/mass s k=(k:ℝ)/((k:ℝ)+(s:ℝ)+1) := by
  have h := first_relation s k
  have hden : (0:ℝ)<(k:ℝ)+(s:ℝ)+1 := by positivity
  field_simp [(mass_pos s k).ne',hden.ne']
  nlinarith

theorem second_normalized (s k : ℕ) :
    second s k/mass s k=((k:ℝ)^2+(k:ℝ)+(s:ℝ)+1)/
      (((k:ℝ)+(s:ℝ)+1)*((k:ℝ)+(s:ℝ)+2)) := by
  have hfirst := first_relation s k
  have hsecond := second_relation s k
  have hden1 : (0:ℝ)<(k:ℝ)+(s:ℝ)+1 := by positivity
  have hden2 : (0:ℝ)<(k:ℝ)+(s:ℝ)+2 := by positivity
  field_simp [(mass_pos s k).ne',hden1.ne',hden2.ne']
  linear_combination ((k:ℝ)+(s:ℝ)+1)*hsecond+(k:ℝ)*hfirst

theorem quadratic_eigenvalue (s k : ℕ) :
    (((s:ℝ)+2)*(second s k/mass s k)-1)/((s:ℝ)+1)=
      (k:ℝ)*((k:ℝ)-1)/(((k:ℝ)+(s:ℝ)+1)*((k:ℝ)+(s:ℝ)+2)) := by
  rw [second_normalized]
  have hden1 : (0:ℝ)<(k:ℝ)+(s:ℝ)+1 := by positivity
  have hden2 : (0:ℝ)<(k:ℝ)+(s:ℝ)+2 := by positivity
  have hden3 : (0:ℝ)<(s:ℝ)+1 := by positivity
  field_simp [hden1.ne',hden2.ne',hden3.ne']
  ring

end SmoothingMoments
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
