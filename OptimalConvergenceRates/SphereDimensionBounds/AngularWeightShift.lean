import OptimalConvergenceRates.SphereDimensionBounds.TaylorKernelData
import OptimalConvergenceRates.SphereDimensionBounds.AngularPolynomialPositivity
import OptimalConvergenceRates.SphereDimensionBounds.SphereAngularMoments

/-! Exact change of angular weight for the actual localization kernel.
All normalization constants cancel in the actual fourth-moment ratio. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.AngularWeightShift

open scoped BigOperators InnerProductSpace
open MeasureTheory Polynomial SphereMeasure SphereMoments SphereAngularMoments
  TaylorKernelData AngularPolynomialPositivity

theorem zonal_weight_shift (s k : ℕ) (p : Polynomial ℝ) :
    normalizedZonalFunctional s ((1-X^2)^k*p)=
      (weightedCosineIntegral (s+2*k) 0/weightedCosineIntegral s 0)*
        normalizedZonalFunctional (s+2*k) p := by
  have heval (theta : ℝ) :
      ((1-X^2)^k*p).eval (Real.cos theta)*Real.sin theta^s=
        p.eval (Real.cos theta)*Real.sin theta^(s+2*k) := by
    have hb : 1-Real.cos theta^2=Real.sin theta^2 := by
      nlinarith [Real.sin_sq_add_cos_sq theta]
    simp only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_sub,
      Polynomial.eval_one,Polynomial.eval_X,hb]
    rw [←pow_mul,pow_add]
    ring
  change (∫theta in (0:ℝ)..Real.pi,
      ((1-X^2)^k*p).eval (Real.cos theta)*Real.sin theta^s)/weightedCosineIntegral s 0=_
  simp_rw [heval]
  change (∫theta in (0:ℝ)..Real.pi,p.eval (Real.cos theta)*Real.sin theta^(s+2*k))/
      weightedCosineIntegral s 0=
    (weightedCosineIntegral (s+2*k) 0/weightedCosineIntegral s 0)*
      ((∫theta in (0:ℝ)..Real.pi,p.eval (Real.cos theta)*Real.sin theta^(s+2*k))/
        weightedCosineIntegral (s+2*k) 0)
  field_simp [(weightedCosineIntegral_mass_pos s).ne',
    (weightedCosineIntegral_mass_pos (s+2*k)).ne']

theorem rawKernel_eq (m : ℕ) (chi : Polynomial ℝ) :
    rawKernel m chi=(1-X^2)^(2*m)*chi^2 := by
  simp only [rawKernel,rawRoot,mul_pow,←pow_mul]
  rw [Nat.mul_comm m 2]

def shiftFactor (n m : ℕ) : ℝ :=
  weightedCosineIntegral (n+4*m-2) 0/weightedCosineIntegral (n-2) 0

theorem shiftFactor_pos (n m : ℕ) : 0<shiftFactor n m :=
  div_pos (weightedCosineIntegral_mass_pos _) (weightedCosineIntegral_mass_pos _)

theorem rawKernel_weight_shift {n : ℕ} (hn : 2 ≤ n) (m : ℕ) (chi p : Polynomial ℝ) :
    normalizedZonalFunctional (n-2) (p*rawKernel m chi)=
      shiftFactor n m*normalizedZonalFunctional (n+4*m-2) (p*chi^2) := by
  have hid : p*rawKernel m chi=(1-X^2)^(2*m)*(p*chi^2) := by rw [rawKernel_eq];ring
  rw [hid,zonal_weight_shift]
  have hidx : n-2+2*(2*m)=n+4*m-2 := by omega
  simp only [hidx,shiftFactor]

theorem normalizingMass_eq_angular {n : ℕ} (hn : 2 ≤ n) (m : ℕ) (chi : Polynomial ℝ) :
    normalizingMass (by omega : 0<n) m chi=
      normalizedZonalFunctional (n-2) (rawKernel m chi) := by
  exact integral_zonal_eq_angular hn (axisSphere ⟨0,by omega⟩) _

theorem normalizingMass_shift {n : ℕ} (hn : 2 ≤ n) (m : ℕ) (chi : Polynomial ℝ) :
    normalizingMass (by omega : 0<n) m chi=
      shiftFactor n m*normalizedZonalFunctional (n+4*m-2) (chi^2) := by
  rw [normalizingMass_eq_angular hn]
  simpa only [one_mul] using rawKernel_weight_shift hn m chi 1

theorem normalizingMass_pos {n : ℕ} (hn : 2 ≤ n) (m : ℕ)
    (chi : Polynomial ℝ) (hchi : chi ≠ 0) :
    0<normalizingMass (by omega : 0<n) m chi := by
  rw [normalizingMass_shift hn]
  exact mul_pos (shiftFactor_pos n m) (zonal_square_pos _ chi hchi)

theorem fourthMoment_eq_angular_ratio {n : ℕ} (hn : 2 ≤ n) (m : ℕ)
    (chi : Polynomial ℝ) :
    fourthMoment (by omega : 0<n) m chi=
      4*normalizedZonalFunctional (n-2) ((1-X)^2*rawKernel m chi)/
        normalizingMass (by omega : 0<n) m chi := by
  rw [fourthMoment_eq_zonal]
  calc
    _=normalizedZonalFunctional (n-2) (chordMomentPolynomial (by omega : 0<n) m chi) :=
      integral_zonal_eq_angular hn (axisSphere ⟨0,by omega⟩) _
    _=_ := by
      have hid : chordMomentPolynomial (by omega : 0<n) m chi=
          C (4*(normalizingMass (by omega : 0<n) m chi)⁻¹)*((1-X)^2*rawKernel m chi) := by
        simp only [chordMomentPolynomial,normalizedKernel,map_mul]
        ring
      rw [hid,←Polynomial.smul_eq_C_mul,map_smul]
      simp only [smul_eq_mul,div_eq_mul_inv]
      ring

/-- Literal equality between the actual normalized spherical chordal
fourth moment and the shifted angular quotient. -/
theorem fourthMoment_eq_shifted_ratio {n : ℕ} (hn : 2 ≤ n) (m : ℕ)
    (chi : Polynomial ℝ) (hchi : chi ≠ 0) :
    fourthMoment (by omega : 0<n) m chi=
      4*normalizedZonalFunctional (n+4*m-2) ((1-X)^2*chi^2)/
        normalizedZonalFunctional (n+4*m-2) (chi^2) := by
  rw [fourthMoment_eq_angular_ratio hn,rawKernel_weight_shift hn,normalizingMass_shift hn]
  have hp := (zonal_square_pos (n+4*m-2) chi hchi).ne'
  have hf := (shiftFactor_pos n m).ne'
  field_simp [hp,hf]

theorem fourthMoment_le_of_shifted_ratio {n : ℕ} (hn : 2 ≤ n) (m : ℕ)
    (chi : Polynomial ℝ) (hchi : chi ≠ 0) (b : ℝ)
    (hbound : 4 * normalizedZonalFunctional (n + 4 * m - 2) ((1 - X) ^ 2 * chi ^ 2) /
      normalizedZonalFunctional (n + 4 * m - 2) (chi ^ 2) ≤ b) :
    fourthMoment (by omega : 0<n) m chi≤b := by
  rw [fourthMoment_eq_shifted_ratio hn m chi hchi]
  exact hbound

end OptimalConvergenceRates.SphereDimensionBounds.AngularWeightShift
