import OptimalConvergenceRates.SphereDimensionBounds.TaylorKernelOperator
import OptimalConvergenceRates.SphereDimensionBounds.SphereSOSFunctions

/-! Actual positive-image certificates for the Taylor kernel. The only
local premise is a literal universal bounded-SOS certificate for cubics
with a nonnegative quartic radial correction. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.TaylorKernelImages

open scoped BigOperators InnerProductSpace
open MeasureTheory MvPolynomial OptimalConvergenceRates.SphereDimensionBounds.Foundation SphereMeasure SpherePolynomialSpace CubicTaylorBounds DegreeTaylorBounds
  TaylorKernelData TaylorKernelOperator KernelAbsorption ChebyshevSOSKernel SphereSOSFunctions

abbrev Poly (n : ℕ) := OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial n

def LocalCertificate (n m : ℕ) (gamma : ℝ) : Prop :=
  ∀ v : Poly n,v.totalDegree≤3 → ∀ eta : ℝ,0≤eta →
    (∀ h : Fin n → ℝ,0≤eval h v+eta*(∑ i,h i^2)^2) →
    BoundedSOS (2*m+2) ((radiusPolynomial n)^(2*m)*(v+C (gamma*eta)*(radiusPolynomial n)^2))

def chordSection {n : ℕ} (P : Polynomial ℝ) : C(Sphere n,C(Sphere n,ℝ)) :=
  (⟨fun z : Sphere n×Sphere n => ‖z.2.1-z.1.1‖^4*P.eval ⟪z.2.1,z.1.1⟫_ℝ,
    by fun_prop⟩ : C(Sphere n×Sphere n,ℝ)).curry

@[simp] theorem chordSection_apply {n : ℕ} (P : Polynomial ℝ) (y x : Sphere n) :
    chordSection P y x=‖x.1-y.1‖^4*P.eval ⟪x.1,y.1⟫_ℝ := rfl

def correctedSection {n : ℕ} (P : Polynomial ℝ) (p : Poly n) (c : ℝ) :
    C(Sphere n,C(Sphere n,ℝ)) := taylorSection P p+c • chordSection P

theorem correctedSection_apply {n : ℕ} (P : Polynomial ℝ) (p : Poly n) (c : ℝ) (y x : Sphere n) :
    correctedSection P p c y x=(evalForm (cubicModel y.1 p) (x.1-y.1)+c*‖x.1-y.1‖^4)*P.eval ⟪x.1,y.1⟫_ℝ := by
  simp only [correctedSection,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    smul_eq_mul,section_apply,chordSection_apply]
  ring

theorem chord_average {n : ℕ} (hn : 0 < n) (m : ℕ) (chi : Polynomial ℝ) :
    integralMap hn (chordSection (normalizedKernel hn m chi))=
      ContinuousMap.const (Sphere n) (fourthMoment hn m chi) := by
  ext x
  change (∫ y : Sphere n,chordSection (normalizedKernel hn m chi) y ∂surface n) x=_
  rw [ContinuousMap.integral_apply (integrable_continuous hn _ (chordSection _).continuous)]
  exact fourthMoment_independent hn m chi x

theorem corrected_average {n : ℕ} (hn : 0 < n) (m : ℕ) (chi : Polynomial ℝ) (p : Poly n) (c : ℝ) :
    integralMap hn (correctedSection (normalizedKernel hn m chi) p c)=
      integralMap hn (taylorSection (normalizedKernel hn m chi) p)+
        ContinuousMap.const (Sphere n) (c*fourthMoment hn m chi) := by
  rw [correctedSection,map_add,map_smul,chord_average]
  congr 1

theorem translation_eval {n : ℕ} (y x : E n) (v : Poly n) :
    eval (fun i => x i) (AffineKernelBridge.translation n (fun i => y i) v)=evalForm v (x-y) := by
  rw [AffineKernelBridge.translation,BivariateTaylorPolynomial.eval_substitution]
  apply congrArg (fun z => eval z v)
  funext i
  simp only [eval_sub,eval_X,eval_C,PiLp.sub_apply]

theorem chordPole_eval_squared {n : ℕ} (y x : E n) :
    eval (fun i => x i) (chordPole (fun i => y i))^2=‖x-y‖^4 := by
  have he : eval (fun i => x i) (chordPole (fun i => y i))=∑ i,(x i-y i)^2 := by
    simp [chordPole]
  rw [he]
  exact (GlobalCubicCorrection.norm_fourth_eq_sumsq_sq (x-y)).symm

theorem translatedLocal_eval {n : ℕ} (y x : E n) (v : Poly n) (c : ℝ) :
    eval (fun i => x i) (AffineKernelBridge.translatedLocal (fun i => y i) v c)=
      evalForm v (x-y)+c*‖x-y‖^4 := by
  simp only [AffineKernelBridge.translatedLocal,eval_add,eval_mul,eval_C,eval_pow,
    translation_eval,chordPole_eval_squared]

def localSectionPolynomial {n : ℕ} (hn : 0 < n) (m : ℕ) (chi : Polynomial ℝ)
    (y : E n) (p : Poly n) (c : ℝ) : Poly n :=
  C ((normalizingMass hn m chi)⁻¹)*
    (kernelNumerator (dotPole (fun i => y i)) (chiSection y chi) m^2*
      AffineKernelBridge.translatedLocal (fun i => y i) (cubicModel y p) c)

theorem localSectionPolynomial_eval {n : ℕ} (hn : 0 < n) (m : ℕ) (chi : Polynomial ℝ)
    (y x : Sphere n) (p : Poly n) (c : ℝ) :
    eval (fun i => x.1 i) (localSectionPolynomial hn m chi y.1 p c)=
      correctedSection (normalizedKernel hn m chi) p c y x := by
  rw [localSectionPolynomial,eval_mul,eval_C,eval_mul,eval_pow,
    numeratorSection_eval,translatedLocal_eval,correctedSection_apply]
  simp only [normalizedKernel,Polynomial.eval_mul,Polynomial.eval_C,rawKernel,Polynomial.eval_pow]
  ring

theorem localSectionPolynomial_feasible {n d ell : ℕ} (hn : 0 < n) (hd : 4 ≤ d) (hell : 2 ≤ ell)
    (m : ℕ) (chi : Polynomial ℝ) (hchi : chi.natDegree ≤ ell - 2)
    (hZ : 0 < normalizingMass hn m chi) (gamma : ℝ) (hlocal : LocalCertificate n m gamma)
    (p : Poly n) (hp : p.IsHomogeneous d) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z : Fin n → ℝ,(∑ i,z i^2)=1 → |eval z p|≤M)
    (hpos : ∀ z : Fin n → ℝ,(∑ i,z i^2)=1 → 0≤eval z p) (y : Sphere n) :
    Feasible (3*m+ell) (localSectionPolynomial hn m chi y.1 p (gamma*(GlobalCubicCorrection.beta d*M))) 0 := by
  let eta := GlobalCubicCorrection.beta d*M
  have heta : 0≤eta := mul_nonneg (GlobalCubicCorrection.beta_pos hd).le hM
  have hsource : ∀ h : Fin n → ℝ,0≤eval h (cubicModel y.1 p)+eta*(∑ i,h i^2)^2 := by
    intro h
    have hh := GlobalCubicCorrection.correctedCubic_nonneg hn hd p hp M hM hbound hpos
      y.1 (sphere_norm_one y) h
    simpa only [GlobalCubicCorrection.correctedCubic,eval_add,eval_mul,eval_C,
      eval_pow,radiusPolynomial_eval,eta] using hh
  have hcert := hlocal (cubicModel y.1 p) (cubicModel_degree y.1 p) eta heta hsource
  have hf := AffineKernelBridge.translated_kernel_feasible (fun i => y.1 i)
    (coordinates_unitSphere y) (cubicModel y.1 p) (chiSection y.1 chi)
    (cubicModel_degree y.1 p) (chiSection_degree y.1 chi hchi) hell m (gamma*eta) hcert
  simpa only [localSectionPolynomial,mul_zero,eta] using hf.scale (inv_nonneg.mpr hZ.le)

theorem average_local_images {n d ell : ℕ} (hn : 0 < n) (hd : 4 ≤ d) (hell : 2 ≤ ell)
    (m : ℕ) (chi : Polynomial ℝ) (hchi : chi.natDegree ≤ ell - 2)
    (hZ : 0 < normalizingMass hn m chi) (gamma : ℝ) (hlocal : LocalCertificate n m gamma)
    (p : Poly n) (hp : p.IsHomogeneous d) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z : Fin n → ℝ,(∑ i,z i^2)=1 → |eval z p|≤M)
    (hpos : ∀ z : Fin n → ℝ,(∑ i,z i^2)=1 → 0≤eval z p) :
    SphereSOS (3*m+ell) (integralMap hn (correctedSection (normalizedKernel hn m chi) p
      (gamma*(GlobalCubicCorrection.beta d*M)))) := by
  apply SphereSOSFunctions.integral hn _ (correctedSection _ _ _).continuous
  intro y
  have hs := of_feasible (localSectionPolynomial_feasible hn hd hell m chi hchi hZ gamma hlocal
    p hp M hM hbound hpos y)
  convert hs using 1
  ext x
  exact (localSectionPolynomial_eval hn m chi y x p _).symm

/-- The positive image premise of the finite-dimensional inverse theorem
is derived from the actual local certificate, not assumed. -/
theorem positive_image {n d ell : ℕ} (hn : 0 < n) (hd : 4 ≤ d) (hell : 2 ≤ ell)
    (m : ℕ) (chi : Polynomial ℝ) (hchi : chi.natDegree ≤ ell - 2)
    (hZ : 0 < normalizingMass hn m chi) (gamma : ℝ) (hlocal : LocalCertificate n m gamma)
    (F : homogeneousSpace n d) (hF : ∀ x : Sphere n,0≤F.1 x) :
    SphereSOS (3*m+ell) ((operator hn (normalizedKernel hn m chi) F).1+
      ContinuousMap.const (Sphere n) ((gamma*GlobalCubicCorrection.beta d*fourthMoment hn m chi)*‖F‖)) := by
  let p := representativeLinear n d F
  have hbound : ∀ z : Fin n → ℝ,(∑ i,z i^2)=1 → |eval z p|≤‖F‖ := by
    intro z hz
    exact homogeneousRepresentative_bound F (coordinateSphere z hz)
  have hpos : ∀ z : Fin n → ℝ,(∑ i,z i^2)=1 → 0≤eval z p := by
    intro z hz
    have he : eval z p=F.1 (coordinateSphere z hz) := representativeLinear_eval F (coordinateSphere z hz)
    rw [he]
    exact hF (coordinateSphere z hz)
  have hs := average_local_images hn hd hell m chi hchi hZ gamma hlocal p
    (representativeLinear_homogeneous F) ‖F‖ (norm_nonneg _) hbound hpos
  rw [corrected_average] at hs
  convert hs using 1
  ext x
  change integralMap hn (taylorSection (normalizedKernel hn m chi) p) x+
    (gamma*GlobalCubicCorrection.beta d*fourthMoment hn m chi)*‖F‖=
    integralMap hn (taylorSection (normalizedKernel hn m chi) p) x+
      gamma*(GlobalCubicCorrection.beta d*‖F‖)*fourthMoment hn m chi
  ring

end OptimalConvergenceRates.SphereDimensionBounds.TaylorKernelImages
