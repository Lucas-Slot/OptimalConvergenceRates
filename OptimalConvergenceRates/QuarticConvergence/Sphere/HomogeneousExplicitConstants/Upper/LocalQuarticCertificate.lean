import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.RadialDiscriminantCertificate
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.SelectorExistence
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.SelectorRemainderSOS

/-! Complete actual homogeneous local quartic certificate: the selector,
radial quadratic-cubic certificate and scalar remainder are constructed,
including zero leading coefficient and zero correction. -/
noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace LocalQuarticCertificate
open scoped BigOperators InnerProductSpace
open MvPolynomial ChebyshevSOSKernel WeightedQuadraticSplit OrderedCubicExpansion
  RadialSpectralNode RadialDiscriminantCertificate SelectorSchur
abbrev Poly (n : ℕ):=MvPolynomial (Fin n) ℝ

def localBudget (n : ℕ):ℝ:=(radialBudget n+1)*SelectorExistence.selectorBudget n

theorem selectorBudget_nonnegative (n : ℕ):0≤SelectorExistence.selectorBudget n:=by
  unfold SelectorExistence.selectorBudget
  positivity

theorem lift_schurA {n : ℕ} (a : ℝ) (l H u : Poly n) :
    lift (schurA a l H u)=schurA a (lift l) (lift H) (lift u):=by
  simp only [schurA,map_sub,map_mul,map_pow,SortedRadialCertificate.lift_constant]
  have ht:lift (2:Poly n)=2:=by
    change (rename Fin.succ) (C (2:ℝ))=C (2:ℝ)
    exact rename_C Fin.succ 2
  rw [ht]

theorem lift_schurD {n : ℕ} (a : ℝ) (l B u : Poly n) :
    lift (schurD a l B u)=schurD a (lift l) (lift B) (lift u):=by
  simp [schurD,lift]

/-- The full original homogeneous local quartic certificate, with actual
finite polynomial roots of degree3s+2 and pure transverse multiplierR3s. -/
theorem local_quartic_boundedSOS {n s : ℕ} (hn : 2 ≤ n) (hs : n ≤ 2 * s) (a M : ℝ)
    (l H B C0 : Poly n) (hl : l.IsHomogeneous 1) (hH : H.IsHomogeneous 2)
    (hB : B.IsHomogeneous 3) (hC : C0.IsHomogeneous 4)
    (hp : ∀ (z : ℝ) (x : Fin n → ℝ), 0 ≤ QuarticCoefficientBounds.quartic a
      (eval x l) (eval x H) (eval x B) (eval x C0) z)
    (hM : 0 ≤ M) (hCM:∀x:Fin n→ℝ,eval x C0≤M*(∑i,x i^2)^2):
    BoundedSOS (3*s+2) ((lift (Foundation.radiusPolynomial n))^(3*s)*
      (QuarticDivisionSOS.model a l H B C0-lift C0+
       C (localBudget n*M)*(lift (Foundation.radiusPolynomial n))^2)):=by
  let S:=SelectorExistence.selectorBudget n
  let Z:=radialBudget n
  let R:=Foundation.radiusPolynomial n
  let z:Poly (n+1):=X 0
  have hS:0≤S:=selectorBudget_nonnegative n
  have hSM:0≤S*M:=mul_nonneg hS hM
  obtain ⟨u,hu,hG⟩:=SelectorExistence.exists_quadratic_selector (by omega : 0<n) a M l H B C0 hl
    hH hB hC hp hM hCM
  have ha0:0≤a:=(QuarticCoefficientBounds.extreme_coefficients_nonneg (fun z↦hp z (fun _↦0))).1
  have hRval(x:Point (Fin n)):(∑i,x i^2)=‖x‖^2:=(norm_sq x).symm
  have hradius:BoundedSOS (3*s) ((lift R)^(3*s)):=RadialNodeSOS.radius_power_boundedSOS
    lift_radius_sos
  by_cases ha:a=0
  · have hpoint(x:Fin n→ℝ):eval x l=0 ∧ eval x u=0 ∧ 0≤eval x H ∧
        0≤S*M*(∑i,x i^2)^2 ∧ (eval x B)^2≤4*eval x H*(S*M*(∑i,x i^2)^2):=by
      apply SelectorRemainderSOS.zero_leading_scalar
      simpa only [ha] using hG x
    have hl0:l=0:=by apply MvPolynomial.funext;intro x;simpa using (hpoint x).1
    have hH0:∀x:Fin n→ℝ,0≤eval x H:=fun x↦(hpoint x).2.2.1
    have hd:∀x:Point (Fin n),(eval (fun i↦x i) B)^2≤4*(S*M)*eval (fun i↦x i) H*‖x‖^4:=by
      intro x
      have hh:=(hpoint (fun i↦x i)).2.2.2.2
      rw [hRval] at hh
      convert hh using 1
      ring
    have hrad:=discriminant_boundedSOS hn hs H B hH hB hH0 hSM hd
    have hpad:BoundedSOS (3*s+2) (C (S*M)*(lift R)^(3*s+2)):=
      (RadialNodeSOS.radius_power_boundedSOS (s:=3*s+2) lift_radius_sos).scale (S*M) hSM
    convert hrad.add hpad using 1
    have hpow:(lift R)^(3*s+2)=(lift R)^(3*s)*(lift R)^2:=pow_add _ _ _
    rw [hpow]
    dsimp [QuarticDivisionSOS.model,QuarticDivisionSOS.s,QuarticDivisionSOS.tr,
      SelectorFunctional.s,SelectorFunctional.transverse,localBudget,S,Z,R,z,lift]
    rw [ha,hl0]
    simp only [map_zero,mul_zero,zero_mul,zero_add,add_zero,map_add,map_mul,map_one]
    ring
  have hap:0<a:=lt_of_le_of_ne ha0 (Ne.symm ha)
  let A:=schurA a l H u
  let D:=schurD a l B u
  have hA:A.IsHomogeneous 2:=schurA_homogeneous a hl hH hu
  have hD:D.IsHomogeneous 3:=schurD_homogeneous a hl hB hu
  have hbnds:=polynomial_selector_bounds a S M hap l H B u R (by
    intro x
    simpa only [R,S,Foundation.radiusPolynomial,
      SphereBallTransfers.sphereQuadratic,eval_sum,eval_pow,eval_X] using hG x)
  have hA0:∀x:Fin n→ℝ,0≤eval x A:=fun x↦(hbnds x).1
  have hd:∀x:Point (Fin n),(eval (fun i↦x i) D)^2≤4*(S*M)*eval (fun i↦x i) A*‖x‖^4:=by
    intro x
    have hh:=(hbnds (fun i↦x i)).2.2
    have hv:eval (fun i↦x i) R=‖x‖^2:=by
      simpa only [R,Foundation.radiusPolynomial,
        SphereBallTransfers.sphereQuadratic,eval_sum,eval_pow,eval_X] using (norm_sq x).symm
    rw [hv] at hh
    convert hh using 1
    ring
  have hrad:=discriminant_boundedSOS hn hs A D hA hD hA0 hSM hd
  obtain ⟨b,hb,hrem⟩:=SelectorRemainderSOS.selector_remainder_exists_squares a S M hap hS hM l H B
    u hu hG
  have hremsos:BoundedSOS 2 (C (S*M)*R^2-C (1/a)*u^2):=by
    rw [hrem]
    exact BoundedSOS.of_family b (fun i↦(hb i).totalDegree_le)
  have hremLift:=hremsos.rename Fin.succ
  have hsquare:BoundedSOS 2 ((squareRoot a z (lift l) (lift u))^2):=
    BoundedSOS.square _ (squareRoot_degree a (isHomogeneous_X ℝ _) hl.rename_isHomogeneous
      hu.rename_isHomogeneous)
  have hid:(QuarticDivisionSOS.model a l H B C0-lift C0+C (localBudget n*M)*(lift R)^2)=
      squareRoot a z (lift l) (lift u)^2+
        (z^2*lift A+z*lift D+C (Z*S*M)*(lift R)^2)+
        (C (S*M)*(lift R)^2-C (1/a)*(lift u)^2):=by
    have hh:=SelectorRemainderSOS.polynomial_completion_budget_sharp a S M Z hap z
      (lift l) (lift H) (lift B) (lift C0) (lift u) (lift R)
    rw [←lift_schurA,←lift_schurD] at hh
    convert hh using 1
    · dsimp [QuarticDivisionSOS.model,QuarticDivisionSOS.s,QuarticDivisionSOS.tr,
        SelectorFunctional.s, SelectorFunctional.transverse, SelectorSchur.model, localBudget, S,
          Z, z, lift]
      ring
  have hremLift':BoundedSOS 2 (C (S*M)*(lift R)^2-C (1/a)*(lift u)^2):=by
    change BoundedSOS 2 (lift (C (S*M)*R^2-C (1/a)*u^2)) at hremLift
    simpa only [map_sub,map_mul,map_pow,SortedRadialCertificate.lift_constant] using hremLift
  have hother':BoundedSOS (3*s+2) ((lift R)^(3*s)*
      (squareRoot a z (lift l) (lift u)^2+(C (S*M)*(lift R)^2-C (1/a)*(lift u)^2))):=
    hradius.mul (hsquare.add hremLift')
  have hrad':BoundedSOS (3*s+2) ((lift R)^(3*s)*(z^2*lift A+z*lift D+C (Z*S*M)*(lift R)^2)):=by
    convert hrad using 1
    congr 3
    dsimp [Z]
    ring
  convert hrad'.add hother' using 1
  rw [hid]
  ring

end LocalQuarticCertificate
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
