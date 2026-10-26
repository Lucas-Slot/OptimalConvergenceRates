import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.SphereDimensionBounds.LocalQuarticCertificate
import OptimalConvergenceRates.SphereDimensionBounds.CubicHomogenization
import OptimalConvergenceRates.SphereDimensionBounds.NonnegativeCubicSOS
import OptimalConvergenceRates.SphereDimensionBounds.TaylorKernelImages
import OptimalConvergenceRates.SphereDimensionBounds.DimensionUpperConstants
import OptimalConvergenceRates.SphereDimensionBounds.LocalizationKernelParameters

/-! The complete actual universal local cubic certificate used by the
original sphere SOS hierarchy, with the exact multiplier and log-cubed
correction from the dimension-optimal upper proof. -/
noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.LocalCubicCertificate
open scoped BigOperators
open MvPolynomial ChebyshevSOSKernel RadialSpectralNode LocalQuarticCertificate
abbrev Poly (n : ℕ):=MvPolynomial (Fin n) ℝ

theorem dehomogenize_lift {n : ℕ} (p : Poly n):NonnegativeCubicSOS.dehomogenize (lift p)=p:=by
  induction p using MvPolynomial.induction_on with
  | C c=>simp [NonnegativeCubicSOS.dehomogenize,lift]
  | add p q hp hq=>simp only [map_add,hp,hq]
  | mul_X p i hp=>
    simp only [map_mul,hp]
    congr 1
    simp [NonnegativeCubicSOS.dehomogenize,NonnegativeCubicSOS.dehomogenizeVariables,lift]

theorem dehomogenize_model {n : ℕ} (a : ℝ) (l H B C0 : Poly n) :
    NonnegativeCubicSOS.dehomogenize (QuarticDivisionSOS.model a l H B C0)=C a+l+H+B+C0:=by
  change NonnegativeCubicSOS.dehomogenize
    (C a*(X (0:Fin (n+1)))^4+(X (0:Fin (n+1)))^3*lift l+
      (X (0:Fin (n+1)))^2*lift H+X (0:Fin (n+1))*lift B+lift C0)=_
  have hz:NonnegativeCubicSOS.dehomogenize (X (0:Fin (n+1)))=1:=by
    simp [NonnegativeCubicSOS.dehomogenize,NonnegativeCubicSOS.dehomogenizeVariables]
  have hc(c:ℝ):NonnegativeCubicSOS.dehomogenize (C c:Poly (n+1))=C c:=by
    simp [NonnegativeCubicSOS.dehomogenize]
  simp only [map_add,map_mul,map_pow,dehomogenize_lift,hz,hc,one_pow,mul_one,one_mul]

/-- The universal actual local cubic certificate with a general smoothing
parameter satisfying the original-dimensional inequality n<=2s. -/
theorem cubic_radial_boundedSOS {n s : ℕ} (hn : 2 ≤ n) (hs : n ≤ 2 * s)
    (v : Poly n) (hv : v.totalDegree ≤ 3) (eta : ℝ) (heta : 0 ≤ eta)
    (hsource:∀h:Fin n→ℝ,0≤eval h v+eta*(∑i,h i^2)^2):
    BoundedSOS (3*s+2) ((OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n)^(3*s)*
      (v+C (localBudget n*eta)*(OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n)^2)):=by
  let a:=v.coeff 0
  let l:=homogeneousComponent 1 v
  let H:=homogeneousComponent 2 v
  let B:=homogeneousComponent 3 v
  let R:=OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n
  let C0:Poly n:=C eta*R^2
  have hl:l.IsHomogeneous 1:=homogeneousComponent_isHomogeneous _ _
  have hH:H.IsHomogeneous 2:=homogeneousComponent_isHomogeneous _ _
  have hB:B.IsHomogeneous 3:=homogeneousComponent_isHomogeneous _ _
  have hC:C0.IsHomogeneous 4:=((HomogeneousSphereBounds.radius_homogeneous n).pow 2).C_mul eta
  have hp:∀(z:ℝ)(x:Fin n→ℝ),0≤QuarticCoefficientBounds.quartic a
      (eval x l) (eval x H) (eval x B) (eval x C0) z:=by
    intro z x
    have hh:=CubicHomogenization.model_nonnegative v hv eta heta hsource (Option.elim' z x)
    rw [CubicHomogenization.model_eval] at hh
    simpa only [a,l,H,B,C0,R,QuarticCoefficientBounds.quartic,Option.elim'_none,
      Option.elim'_some,eval_mul,eval_C,eval_pow,OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial,eval_sum,eval_X] using hh
  have hCM:∀x:Fin n→ℝ,eval x C0≤eta*(∑i,x i^2)^2:=by
    intro x
    simp [C0,R,OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial]
  have hcert:=local_quartic_boundedSOS hn hs a eta l H B C0 hl hH hB hC hp heta hCM
  have hout:=AffineKernelBridge.boundedSOS_affine_substitution (NonnegativeCubicSOS.dehomogenizeVariables n)
    (NonnegativeCubicSOS.dehomogenizeVariables_degree n) hcert
  change BoundedSOS (3*s+2) (NonnegativeCubicSOS.dehomogenize _) at hout
  have hc(c:ℝ):NonnegativeCubicSOS.dehomogenize (C c:Poly (n+1))=C c:=by
    simp [NonnegativeCubicSOS.dehomogenize]
  simp only [map_mul,map_pow,map_add,map_sub,dehomogenize_lift,dehomogenize_model,hc] at hout
  convert hout using 1
  rw [CubicHomogenization.cubic_component_decomposition v hv]
  dsimp [a,l,H,B,R]
  simp only [map_mul]
  ring

theorem localBudget_eq_totalShift (n : ℕ):localBudget n=DimensionUpperConstants.totalShift n:=by
  unfold localBudget RadialDiscriminantCertificate.radialBudget SelectorExistence.selectorBudget
    DimensionUpperConstants.totalShift DimensionUpperConstants.radialShift
    DimensionUpperConstants.selectorShift DimensionUpperConstants.L
  ring

/-- The exact unconditional local input to the actual degree-d original
sphere SOS upper bound. Only the original transverse dimension n>=3 is
assumed; no selector, matrix smoothing, radial or SOS premise remains. -/
theorem local_certificate {n : ℕ} (hn : 3 ≤ n) :
    TaylorKernelImages.LocalCertificate n (LocalizationKernelParameters.multiplier n)
      (DimensionUpperConstants.totalShift n):=by
  intro v hv eta heta hsource
  have hs:n≤2*(2*LocalizationKernelParameters.nu n):=by
    unfold LocalizationKernelParameters.nu
    omega
  have hh:=cubic_radial_boundedSOS (by omega : 2≤n) hs v hv eta heta hsource
  rw [localBudget_eq_totalShift] at hh
  simpa only [LocalizationKernelParameters.multiplier,Nat.mul_assoc,Nat.mul_comm 3 2,
    Nat.mul_left_comm 3 2] using hh

end OptimalConvergenceRates.SphereDimensionBounds.LocalCubicCertificate
