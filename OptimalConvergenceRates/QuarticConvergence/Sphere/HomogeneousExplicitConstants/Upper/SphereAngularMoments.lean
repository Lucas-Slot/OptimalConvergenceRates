import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.SphereMoments
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.ZonalMoments

/-! Identification of actual sphere polynomial averages with the normalized
angular functional, by the proved coordinate moment recurrence. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace SphereAngularMoments

open scoped BigOperators InnerProductSpace
open MeasureTheory SphereMeasure SphereMoments Polynomial

theorem integrable_zonal {n : ℕ} (hn : 0 < n) (x : E n) (p : Polynomial ℝ) :
    Integrable (fun y : Sphere n ↦ p.eval ⟪x,y.1⟫_ℝ) (surface n) := by
  apply integrable_continuous hn
  fun_prop

def zonalIntegral {n : ℕ} (hn : 0 < n) (x : E n) : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ y : Sphere n,p.eval ⟪x,y.1⟫_ℝ ∂surface n
  map_add' p q := by
    simp only [Polynomial.eval_add]
    exact integral_add (integrable_zonal hn x p) (integrable_zonal hn x q)
  map_smul' r p := by
    simp only [Polynomial.smul_eq_C_mul,Polynomial.eval_mul,Polynomial.eval_C,
      RingHom.id_apply,smul_eq_mul]
    exact integral_const_mul _ _

@[simp] theorem zonalIntegral_X_pow {n : ℕ} (hn : 0 < n) (x : E n) (m : ℕ) :
    zonalIntegral hn x (X^m)=linearMoment m x := by
  simp [zonalIntegral,linearMoment]

theorem zonalIntegral_eq_angular {n : ℕ} (hn : 2 ≤ n) (x : Sphere n) :
    zonalIntegral (by omega : 0 < n) x.1=normalizedZonalFunctional (n-2) := by
  let hnpos : 0 < n := by omega
  let a : Fin n := ⟨0,hnpos⟩
  apply polynomial_functional_eq_zonal_of_recurrence
  · have h := linearMoment_zero hnpos x.1
    simpa only [←zonalIntegral_X_pow hnpos x.1 0,pow_zero] using h
  · have h := linearMoment_odd x.1 (by decide : Odd 1)
    simpa only [←zonalIntegral_X_pow hnpos x.1 1,pow_one] using h
  · intro m
    rw [zonalIntegral_X_pow,zonalIntegral_X_pow,
      unit_linearMoment a x (m+2),unit_linearMoment a x m]
    have h := coordinateMoment_recurrence hnpos a m
    have hidx : m+(n-2)+2=m+n := by omega
    simpa only [hidx,Nat.cast_add,Nat.cast_one,mul_comm] using h

theorem integral_zonal_eq_angular {n : ℕ} (hn : 2 ≤ n) (x : Sphere n) (p : Polynomial ℝ) :
    (∫ y : Sphere n,p.eval ⟪x.1,y.1⟫_ℝ ∂surface n)=
      normalizedZonalFunctional (n-2) p := by
  exact DFunLike.congr_fun (zonalIntegral_eq_angular hn x) p

theorem angular_stokes (s : ℕ) (p : Polynomial ℝ) :
    normalizedZonalFunctional s ((1-X^2)*p.derivative)=
      ((s:ℝ)+1)*normalizedZonalFunctional s (X*p) := by
  let L := normalizedZonalFunctional s
  change L ((1-X^2)*p.derivative)=((s:ℝ)+1)*L (X*p)
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.derivative_add,mul_add,map_add]
    rw [hp,hq]
  | monomial m a =>
    rw [←Polynomial.C_mul_X_pow_eq_monomial]
    cases m with
    | zero =>
      simp only [pow_zero,mul_one,Polynomial.derivative_C,mul_zero,map_zero]
      have hz : L X=0 := by
        have he := normalizedZonalFunctional_X_pow s 1
        simp only [pow_one] at he
        change normalizedZonalFunctional s X=0
        rw [he]
        exact normalizedCosineMoment_odd s 0
      rw [mul_comm X (C a),←Polynomial.smul_eq_C_mul,map_smul,hz,smul_eq_mul,mul_zero,mul_zero]
    | succ m =>
      rw [Polynomial.derivative_C_mul,Polynomial.derivative_X_pow]
      simp only [Nat.add_sub_cancel]
      have hid : (1-X^2)*(C a*(C ((m+1:ℕ):ℝ)*X^m))=
          C (a*((m:ℝ)+1))*X^m-C (a*((m:ℝ)+1))*X^(m+2) := by
        simp only [Nat.cast_add,Nat.cast_one,pow_add,map_mul,map_add,map_one]
        ring
      rw [hid,map_sub,←Polynomial.smul_eq_C_mul,←Polynomial.smul_eq_C_mul,
        map_smul,map_smul,smul_eq_mul,smul_eq_mul]
      have hid2 : X*(C a*X^(m+1))=C a*X^(m+2) := by rw [pow_succ,pow_succ];ring
      rw [hid2,←Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul]
      have hrec := normalizedCosineMoment_recurrence s m
      simp only [L,normalizedZonalFunctional_X_pow]
      push_cast at hrec
      linear_combination -a*hrec

end SphereAngularMoments
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
