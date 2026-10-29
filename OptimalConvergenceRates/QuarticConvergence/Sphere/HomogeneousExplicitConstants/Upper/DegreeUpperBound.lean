import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.TaylorKernelTransfer
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.LocalizationKernelExistence
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.LocalizationUpperCoefficient
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.LocalCubicCertificate
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.DegreeUpperTarget

/-! The unconditional upper bound in the original sphere hierarchy.
The actual local certificate and actual concentrated kernel are instantiated.
Minimum centering and value weakening preserve the exact original order and
free equality-multiplier budget, including zero oscillation. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace DegreeUpperBound

open scoped BigOperators
open MvPolynomial Foundation DimensionUpperConstants HomogeneousSphereBounds
  RadialHierarchyBridge TaylorKernelData TaylorKernelImages LocalizationKernelParameters

abbrev Poly (n : ℕ) := Foundation.Polynomial n

def errorBound (n d r : ℕ) (M : ℝ) : ℝ :=
  absoluteUpperConstant*((d:ℝ)^4*(n:ℝ)^4*(L n)^3/(r:ℝ)^4)*M

/-- Lowering the feasible value adds just one constant square; both
the root order and the equality multiplier are unchanged. -/
theorem feasible_value_mono {n r : ℕ} {p : Poly n} {lam lam' : ℝ}
    (hp : Feasible r p lam) (hle : lam' ≤ lam) : Feasible r p lam' := by
  have hcert := hp.add (SphereBallTransfers.sphereSOSMod_const (sub_nonneg.mpr hle))
  convert hcert using 1
  rw [map_sub]
  ring

/-- Undo actual homogeneous minimum centering using the exact radial
geometric sum. No new squares or larger free multiplier are introduced. -/
theorem centered_feasible_to_original {n r l : ℕ} (hlr : l ≤ r) (p : Poly n)
    (mu eta : ℝ) (hp : Feasible r (centeredForm p mu l) (-eta)) :
    Feasible r p (mu-eta) := by
  have hcert := hp.add_relation_mul (C mu * radialGeometricSum n l)
  convert hcert using 1
  dsimp only [centeredForm, SphereBallTransfers.sphereRelation]
  rw [map_sub, map_neg]
  have hgeom := radialGeometricSum_identity n l
  dsimp only [radiusPolynomial] at hgeom ⊢
  linear_combination (C mu) * hgeom

/-- The actual concentrated kernel is instantiated here. This intermediate
lemma exposes only the literal local universal certificate as an input. -/
theorem certificate_of_local {n d r : ℕ} (hn : 3 ≤ n) (hd : 4 ≤ d) (heven : Even d)
    (hr : 8 * n * d ≤ r)
    (hlocal : LocalCertificate n (multiplier n) (totalShift n))
    (p : Poly n) (hp : p.IsHomogeneous d) (mu M : ℝ) (hmin : IsSphereMinimum p mu)
    (hM : 0 ≤ M) (hupper : ∀ x ∈ unitSphere n, eval x p ≤ mu + M) :
    Feasible r p (mu-errorBound n d r M) := by
  obtain ⟨chi,hchi,hZ,hMoment,hquarter⟩ := LocalizationKernelExistence.exists_kernel_quarter hn hd
    hr
  have hphysical := physical_root_budget hn hd hr
  have hDim := dimension_lower hn
  have hOrd := order_ge_dimension hn hd hr
  have hell : 2 ≤ residualOrder n r := by omega
  have hdle : d ≤ r := by nlinarith
  have hhalf : 2*(d/2)=d := by rcases heven with ⟨k,hk⟩;omega
  have hphalf : p.IsHomogeneous (2*(d/2)) := by simpa only [hhalf] using hp
  have hcenter : (centeredForm p mu (d/2)).IsHomogeneous d := by
    simpa only [hhalf] using centeredForm_homogeneous p hphalf mu
  have hpos : ∀ x : Fin n → ℝ,(∑ i,x i^2)=1 → 0 ≤ eval x (centeredForm p mu (d/2)) := by
    intro x hx
    exact (centeredForm_minimum_zero (m:=d/2) p hmin).1 x hx
  have hbound : ∀ x : Fin n → ℝ,(∑ i,x i^2)=1 → eval x (centeredForm p mu (d/2)) ≤ M := by
    intro x hx
    rw [centeredForm_eval_sphere p mu x hx]
    linarith [hupper x hx]
  have horder : d/2 ≤ 3*multiplier n+residualOrder n r := by
    rw [hphysical]
    exact (Nat.div_le_self d 2).trans hdle
  have hgamma : 0 ≤ totalShift n := (by linarith [one_le_totalShift n])
  have hs := TaylorKernelTransfer.feasible_of_local_even_degree (by omega : 0<n) hd heven hell
    (multiplier n) chi hchi hZ (totalShift n) hgamma hlocal hquarter horder
    (centeredForm p mu (d/2)) hcenter M hM hpos hbound
  rw [hphysical] at hs
  have horiginal := centered_feasible_to_original ((Nat.div_le_self d 2).trans hdle) p mu
    (2*((d.choose 4:ℝ)+totalShift n*GlobalCubicCorrection.beta d)*
      fourthMoment (by omega : 0<n) (multiplier n) chi*M) hs
  have hcoefficient := LocalizationUpperCoefficient.actual_kernel_error_coefficient_bound
    (by omega : 0<n) d r (multiplier n) hd chi hMoment
  have heta : 2*((d.choose 4:ℝ)+totalShift n*GlobalCubicCorrection.beta d)*
      fourthMoment (by omega : 0<n) (multiplier n) chi*M ≤ errorBound n d r M := by
    unfold errorBound
    convert mul_le_mul_of_nonneg_right hcoefficient hM using 1
    ring
  exact feasible_value_mono horiginal (by linarith)

/-- The unconditional original-sphere upper certificate, with the minimum
and any valid oscillation envelope M, at every r≥8nd. -/
theorem upper_certificate {n d r : ℕ} (hn : 3 ≤ n) (hd : 4 ≤ d) (heven : Even d)
    (hr : 8 * n * d ≤ r) (p : Poly n) (hp : p.IsHomogeneous d) (mu M : ℝ)
    (hmin : IsSphereMinimum p mu) (hM : 0 ≤ M)
    (hupper : ∀ x ∈ unitSphere n, eval x p ≤ mu + M) :
    Feasible r p (mu-errorBound n d r M) :=
  certificate_of_local hn hd heven hr (LocalCubicCertificate.local_certificate hn)
    p hp mu M hmin hM hupper

/-- The complete requested upper target, with the retained explicit
absolute constant and no unproved local or kernel premises. -/
theorem uniform_degree_upper_bound : DegreeUpperTarget.UniformDegreeUpperCertificateBound := by
  refine ⟨absoluteUpperConstant,absoluteUpperConstant_pos,?_⟩
  intro n hn d hd heven p hp mu M hmin hM hupper r hr
  exact upper_certificate hn hd heven hr p hp mu M hmin hM hupper

/-- Nonempty original feasible values and the nonnegative gap upper bound,
including zero oscillation. -/
theorem gap_bounds {n d r : ℕ} (hn : 3 ≤ n) (hd : 4 ≤ d) (heven : Even d)
    (hr : 8 * n * d ≤ r) (p : Poly n) (hp : p.IsHomogeneous d) (mu M : ℝ)
    (hmin : IsSphereMinimum p mu) (hM : 0 ≤ M)
    (hupper : ∀ x ∈ unitSphere n, eval x p ≤ mu + M) :
    (feasibleValues r p).Nonempty ∧ 0 ≤ gap r p ∧ gap r p ≤ errorBound n d r M :=
  DegreeUpperTarget.gap_bounds_of_feasible p hmin (upper_certificate hn hd heven hr p hp mu M hmin
    hM hupper)

end DegreeUpperBound
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
