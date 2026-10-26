import OptimalConvergenceRates.SphereDimensionBounds.TaylorKernelNorm
import OptimalConvergenceRates.SphereDimensionBounds.TaylorKernelImages
import OptimalConvergenceRates.SphereDimensionBounds.PositiveTaylorInverse

/-! Actual local-to-global Taylor-kernel transfer. The local bounded-SOS
certificate and an arbitrary polynomial kernel with positive ACTUAL
normalization are explicit inputs. The averaged operator, its range,
norm error, positive image, inverse repair and original Feasible output
are all constructed and proved. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.TaylorKernelTransfer

open scoped BigOperators
open MvPolynomial OptimalConvergenceRates.SphereDimensionBounds.Foundation SphereMeasure SpherePolynomialSpace TaylorKernelData
  TaylorKernelOperator TaylorKernelImages SphereSOSFunctions

abbrev Poly (n : ℕ) := OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial n

theorem function_certificate_one {n l ell : ℕ} (hn : 0 < n) (hd : 4 ≤ 2 * l) (hell : 2 ≤ ell)
    (m : ℕ) (chi : Polynomial ℝ) (hchi : chi.natDegree ≤ ell - 2)
    (hZ : 0 < normalizingMass hn m chi) (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hlocal : LocalCertificate n m gamma)
    (hquarter : ((2 * l).choose 4 : ℝ) * fourthMoment hn m chi ≤ 1 / 4)
    (F : homogeneousSpace n (2 * l)) (hFn : ‖F‖ ≤ 1) (hF : ∀ x : Sphere n,0≤F.1 x) :
    SphereSOS (3*m+ell) (F.1+ContinuousMap.const (Sphere n)
      (2*(((2*l).choose 4:ℝ)+gamma*GlobalCubicCorrection.beta (2*l))*fourthMoment hn m chi)) := by
  let mu := fourthMoment hn m chi
  let t := ((2*l).choose 4:ℝ)*mu
  let q := gamma*GlobalCubicCorrection.beta (2*l)*mu
  let one := constantOne n l
  let K : Set (homogeneousSpace n (2*l)) := {G | SphereSOS (3*m+ell) G.1}
  have hmu : 0 ≤ mu := fourthMoment_nonneg hn m chi
  have ht0 : 0≤t := mul_nonneg (Nat.cast_nonneg _) hmu
  have hq0 : 0≤q := mul_nonneg (mul_nonneg hgamma (GlobalCubicCorrection.beta_pos hd).le) hmu
  have hadd : ∀ x∈K,∀ y∈K,x+y∈K := by
    intro x hx y hy
    exact SphereSOSFunctions.add hx hy
  have hconst : ∀ c : ℝ,0≤c → c • one∈K := by
    intro c hc
    have hs : SphereSOS (3*m+ell) (ContinuousMap.const (Sphere n) c) := constant c hc
    change SphereSOS (3*m+ell) (c • one).1
    convert hs using 1
    ext x
    change c*(constantOne n l).1 x=c
    rw [constantOne_apply,mul_one]
  have hnear : ∀ G : homogeneousSpace n (2*l),
      ‖G-operator hn (normalizedKernel hn m chi) G‖≤t*‖G‖ :=
    TaylorKernelNorm.near_identity hn hd m chi hZ
  have himage : ∀ G : homogeneousSpace n (2*l),(∀ x : Sphere n,0≤evaluation n (2*l) G x) →
      operator hn (normalizedKernel hn m chi) G+(q*‖G‖) • one∈K := by
    intro G hG
    have hs := positive_image hn hd hell m chi hchi hZ gamma hlocal G hG
    change SphereSOS (3*m+ell) (operator hn (normalizedKernel hn m chi) G+(q*‖G‖) • one).1
    convert hs using 1
    ext x
    change (operator hn (normalizedKernel hn m chi) G).1 x+
      (q*‖G‖)*(constantOne n l).1 x=_
    rw [constantOne_apply,mul_one]
    rfl
  have hs := PositiveTaylorInverse.certificate_of_positive_images (evaluation n (2*l)) one
    (fun x => constantOne_apply n l x) (constantOne_norm_le_one n l)
    evaluation_bound K hadd hconst (operator hn (normalizedKernel hn m chi)) ht0 hquarter hq0
    hnear himage F hFn hF
  change SphereSOS (3*m+ell) (F+(2*(t+q)) • one).1 at hs
  convert hs using 1
  ext x
  change F.1 x+2*(((2*l).choose 4:ℝ)+gamma*GlobalCubicCorrection.beta (2*l))*fourthMoment hn m chi=
    F.1 x+(2*(t+q))*(constantOne n l).1 x
  rw [constantOne_apply]
  dsimp only [t,q,mu]
  ring

theorem function_certificate_bound {n l ell : ℕ} (hn : 0 < n) (hd : 4 ≤ 2 * l) (hell : 2 ≤ ell)
    (m : ℕ) (chi : Polynomial ℝ) (hchi : chi.natDegree ≤ ell - 2)
    (hZ : 0 < normalizingMass hn m chi) (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hlocal : LocalCertificate n m gamma)
    (hquarter : ((2 * l).choose 4 : ℝ) * fourthMoment hn m chi ≤ 1 / 4)
    (F : homogeneousSpace n (2 * l)) (M : ℝ) (hM : 0 ≤ M) (hFn : ‖F‖ ≤ M)
    (hF : ∀ x : Sphere n,0≤F.1 x) :
    SphereSOS (3*m+ell) (F.1+ContinuousMap.const (Sphere n)
      (2*(((2*l).choose 4:ℝ)+gamma*GlobalCubicCorrection.beta (2*l))*fourthMoment hn m chi*M)) := by
  by_cases hM0 : M=0
  · have hF0 : F=0 := norm_eq_zero.mp (le_antisymm (by simpa only [hM0] using hFn) (norm_nonneg _))
    have hz : F.1+ContinuousMap.const (Sphere n)
        (2*(((2*l).choose 4:ℝ)+gamma*GlobalCubicCorrection.beta (2*l))*fourthMoment hn m chi*M)=0 := by
      ext x
      simp [hF0,hM0]
    rw [hz]
    exact SphereSOSFunctions.zero
  · have hMpos : 0<M := lt_of_le_of_ne hM (Ne.symm hM0)
    let G : homogeneousSpace n (2*l) := M⁻¹ • F
    have hGn : ‖G‖≤1 := by
      calc
        ‖G‖≤‖M⁻¹‖*‖F‖ := NormedSpace.norm_smul_le (M⁻¹:ℝ) F
        _=M⁻¹*‖F‖ := by rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hM)]
        _≤M⁻¹*M := mul_le_mul_of_nonneg_left hFn (inv_nonneg.mpr hM)
        _=1 := inv_mul_cancel₀ hM0
    have hG : ∀ x : Sphere n,0≤G.1 x := by
      intro x
      change 0≤M⁻¹*F.1 x
      exact mul_nonneg (inv_nonneg.mpr hM) (hF x)
    have hs := function_certificate_one hn hd hell m chi hchi hZ gamma hgamma hlocal hquarter G hGn hG
    have hscaled := SphereSOSFunctions.smul hs M hM
    convert hscaled using 1
    ext x
    change F.1 x+(2*(((2*l).choose 4:ℝ)+gamma*GlobalCubicCorrection.beta (2*l))*fourthMoment hn m chi)*M=
      M*(M⁻¹*F.1 x+2*(((2*l).choose 4:ℝ)+gamma*GlobalCubicCorrection.beta (2*l))*fourthMoment hn m chi)
    have hcancel : M*(M⁻¹*F.1 x)=F.1 x := by rw [←mul_assoc,mul_inv_cancel₀ hM0,one_mul]
    linear_combination -hcancel

/-- Proposition1.18 in the original Feasible convention. Both analytic
moment quantities are the actual arbitrary-chi sphere integrals. The
literal local universal SOS hypothesis remains explicit. -/
theorem feasible_of_local_certificate {n l ell : ℕ} (hn : 0 < n) (hd : 4 ≤ 2 * l) (hell : 2 ≤ ell)
    (m : ℕ) (chi : Polynomial ℝ) (hchi : chi.natDegree ≤ ell - 2)
    (hZ : 0 < normalizingMass hn m chi) (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hlocal : LocalCertificate n m gamma)
    (hquarter : ((2 * l).choose 4 : ℝ) * fourthMoment hn m chi ≤ 1 / 4) (hlr : l ≤ 3 * m + ell)
    (p : Poly n) (hp : p.IsHomogeneous (2 * l)) (M : ℝ) (hM : 0 ≤ M)
    (hpos : ∀ z : Fin n → ℝ,(∑ i,z i^2)=1 → 0≤eval z p)
    (hbound : ∀ z : Fin n → ℝ,(∑ i,z i^2)=1 → eval z p≤M) :
    Feasible (3*m+ell) p
      (-(2*(((2*l).choose 4:ℝ)+gamma*GlobalCubicCorrection.beta (2*l))*fourthMoment hn m chi*M)) := by
  let F : homogeneousSpace n (2*l) := ⟨restriction n p,⟨p,hp,rfl⟩⟩
  have hFn : ‖F‖≤M := by
    apply (ContinuousMap.norm_le F.1 hM).mpr
    intro x
    change ‖eval (fun i => x.1 i) p‖≤M
    rw [Real.norm_eq_abs,abs_of_nonneg (hpos _ (coordinates_unitSphere x))]
    exact hbound _ (coordinates_unitSphere x)
  have hF : ∀ x : Sphere n,0≤F.1 x := fun x => hpos _ (coordinates_unitSphere x)
  have hs := function_certificate_bound hn hd hell m chi hchi hZ gamma hgamma hlocal hquarter F M hM hFn hF
  let c := 2*(((2*l).choose 4:ℝ)+gamma*GlobalCubicCorrection.beta (2*l))*fourthMoment hn m chi*M
  have heq : restriction n (p-C (-c)*(radiusPolynomial n)^l)=F.1+ContinuousMap.const (Sphere n) c := by
    ext x
    have hrad : eval (fun i => x.1 i) (radiusPolynomial n)=1 := by
      simpa only [radiusPolynomial_eval,unitSphere,Set.mem_ofPred_eq] using coordinates_unitSphere x
    change eval (fun i => x.1 i) (p-C (-c)*(radiusPolynomial n)^l)=eval (fun i => x.1 i) p+c
    rw [eval_sub,eval_mul,eval_C,eval_pow,hrad,one_pow,mul_one]
    ring
  apply homogeneous_feasible_of_sphereSOS (by omega : 1≤3*m+ell) hlr p hp (-c)
  rw [heq]
  exact hs

/-- The same literal original-sphere certificate in the arbitrary even
degree notation used by the requested final upper theorem. -/
theorem feasible_of_local_even_degree {n d ell : ℕ} (hn : 0 < n) (hd : 4 ≤ d) (heven : Even d)
    (hell : 2 ≤ ell) (m : ℕ) (chi : Polynomial ℝ) (hchi : chi.natDegree ≤ ell - 2)
    (hZ : 0 < normalizingMass hn m chi) (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hlocal : LocalCertificate n m gamma)
    (hquarter : (d.choose 4 : ℝ) * fourthMoment hn m chi ≤ 1 / 4) (horder : d / 2 ≤ 3 * m + ell)
    (p : Poly n) (hp : p.IsHomogeneous d) (M : ℝ) (hM : 0 ≤ M)
    (hpos : ∀ z : Fin n → ℝ,(∑ i,z i^2)=1 → 0≤eval z p)
    (hbound : ∀ z : Fin n → ℝ,(∑ i,z i^2)=1 → eval z p≤M) :
    Feasible (3*m+ell) p
      (-(2*((d.choose 4:ℝ)+gamma*GlobalCubicCorrection.beta d)*fourthMoment hn m chi*M)) := by
  rcases heven with ⟨l,hl⟩
  have hdeq : d=2*l := by omega
  have hd' : 4≤2*l := by omega
  have hp' : p.IsHomogeneous (2*l) := by simpa only [←hdeq] using hp
  have hquarter' : ((2*l).choose 4:ℝ)*fourthMoment hn m chi≤1/4 := by
    simpa only [←hdeq] using hquarter
  have horder' : l≤3*m+ell := by omega
  have hs := feasible_of_local_certificate hn hd' hell m chi hchi hZ gamma hgamma hlocal hquarter'
    horder' p hp' M hM hpos hbound
  simpa only [←hdeq] using hs

end OptimalConvergenceRates.SphereDimensionBounds.TaylorKernelTransfer
