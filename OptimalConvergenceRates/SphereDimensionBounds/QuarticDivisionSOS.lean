import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.SphereDimensionBounds.QuarticCubicDivision
import OptimalConvergenceRates.SphereDimensionBounds.SelectorFunctional
import OptimalConvergenceRates.SphereDimensionBounds.ChebyshevSOSKernel

/-! Actual quadratic-root SOS completion with a controlled nonnegative
quartic error. This is the direct input to finite-dual centering. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.QuarticDivisionSOS
open scoped BigOperators
open MvPolynomial WeightedQuadraticSplit QuarticCubicDivision ChebyshevSOSKernel

abbrev Poly (n : ℕ):=MvPolynomial (Fin n) ℝ
abbrev s (n : ℕ):Poly (n+1):=SelectorFunctional.s n
abbrev tr {n : ℕ}:Poly n→ₐ[ℝ]Poly (n+1):=SelectorFunctional.transverse

def model {n : ℕ} (a : ℝ) (l H B C0 : Poly n):Poly (n+1):=
  C a*s n^4+s n^3*tr l+s n^2*tr H+s n*tr B+tr C0

def errorQuartic {n : ℕ} (M : ℝ) (C0 : Poly n) (b : Fin n → Poly n):Poly n:=
  C M*(OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n)^2+C (1/4:ℝ)*(∑ i,b i^2)-C0

def roots {n : ℕ} (a M : ℝ) (u b : Fin n → Poly n):Option (Fin n)→Poly (n+1)
  | none=>C (Real.sqrt a)*s n^2-C (Real.sqrt M)*tr (OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n)
  | some i=>s n*tr (u i)+C (1/2:ℝ)*tr (b i)

theorem roots_homogeneous {n : ℕ} (a M : ℝ) (u b : Fin n → Poly n)
    (hu : ∀ i, (u i).IsHomogeneous 1) (hb : ∀ i, (b i).IsHomogeneous 2) (i : Option (Fin n)) :
    (roots a M u b i).IsHomogeneous 2:=by
  have hs:(s n).IsHomogeneous 1:=isHomogeneous_X ℝ 0
  have hR:(OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n).IsHomogeneous 2:=SelectorFunctional.radius_homogeneous n
  cases i with
  | none=>exact ((hs.pow 2).C_mul _).sub (hR.rename_isHomogeneous.C_mul _)
  | some i=>exact (hs.mul (hu i).rename_isHomogeneous).add ((hb i).rename_isHomogeneous.C_mul _)

theorem errorQuartic_homogeneous {n : ℕ} (M : ℝ) (C0 : Poly n) (b : Fin n → Poly n)
    (hC : C0.IsHomogeneous 4) (hb : ∀ i, (b i).IsHomogeneous 2) :
    (errorQuartic M C0 b).IsHomogeneous 4:=by
  have hR:(OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n).IsHomogeneous 2:=SelectorFunctional.radius_homogeneous n
  exact (((hR.pow 2).C_mul M).add ((IsHomogeneous.sum _ _ _ (fun i _=>(hb i).pow 2)).C_mul (1/4:ℝ))).sub hC

/-- Exact actual polynomial SOS completion. In particular it includes
zero leading coefficient; no Schur inverse or strict positivity is used. -/
theorem completion_identity {n : ℕ} (a M : ℝ) (ha : 0 ≤ a) (hM : 0 ≤ M)
    (l H B C0 : Poly n) (u b : Fin n → Poly n)
    (hA : (∑ i, u i ^ 2) = correctedQuadratic a M H) (hB : (∑ i, u i * b i) = B) :
    model a l H B C0-s n^3*tr l+tr (errorQuartic M C0 b)=∑ i,roots a M u b i^2:=by
  apply MvPolynomial.funext
  intro x
  let y:Fin n→ℝ:=fun i=>x i.succ
  let z:=x 0
  let R:ℝ:=∑ i,(y i)^2
  have hau:=congrArg (eval y) hA
  simp only [map_sum,map_pow,correctedQuadratic,map_add,map_mul,eval_C,OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial_eval] at hau
  have hbu:=congrArg (eval y) hB
  simp only [map_sum,map_mul] at hbu
  have hpoint(i:Fin n):(z*eval y (u i)+(1/2:ℝ)*eval y (b i))^2=
      z^2*(eval y (u i))^2+z*(eval y (u i)*eval y (b i))+(1/4:ℝ)*(eval y (b i))^2:=by ring
  have hsum:(∑ i,(z*eval y (u i)+(1/2:ℝ)*eval y (b i))^2)=
      z^2*(∑ i,(eval y (u i))^2)+z*(∑ i,eval y (u i)*eval y (b i))+
        (1/4:ℝ)*(∑ i,(eval y (b i))^2):=by
    simp_rw [hpoint]
    simp only [Finset.sum_add_distrib,←Finset.mul_sum]
  simp only [model,errorQuartic,roots,Fintype.sum_option,map_sub,map_add,map_sum,map_pow,map_mul,
    eval_C,s,SelectorFunctional.s,tr,SelectorFunctional.transverse,rename_C,eval_rename,eval_X,
    OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial_eval]
  change a*z^4+z^3*eval y l+z^2*eval y H+z*eval y B+eval y C0-z^3*eval y l+
      (M*R^2+(1/4:ℝ)*(∑ i,(eval y (b i))^2)-eval y C0)=
      (Real.sqrt a*z^2-Real.sqrt M*R)^2+∑ i,(z*eval y (u i)+(1/2:ℝ)*eval y (b i))^2
  rw [hsum,hau,hbu,Real.sqrt_mul ha]
  have ha2:=Real.sq_sqrt ha
  have hM2:=Real.sq_sqrt hM
  linear_combination -(z^4)*ha2-(R^2)*hM2

/-- The error is bounded pointwise by the original bottom bound and the
proved cubic division norm, rather than by an SOS-order assumption. -/
theorem errorQuartic_bounds {n : ℕ} (M : ℝ) (C0 : Poly n) (b : Fin n → Poly n)
    (hC0 : ∀ x:Fin n→ℝ,0≤eval x C0)
    (hCM:∀ x:Fin n→ℝ,eval x C0≤M*(∑ i,x i^2)^2)
    (hb:∀ x:Point (Fin n),(∑ i,(eval (fun j=>x j) (b i))^2)≤
      6400*((Nat.clog 2 n:ℝ)+1)^2*M*‖x‖^4) :
    ∀ x:Fin n→ℝ,0≤eval x (errorQuartic M C0 b) ∧
      eval x (errorQuartic M C0 b)≤(1+1600*((Nat.clog 2 n:ℝ)+1)^2)*M*(∑ i,x i^2)^2:=by
  intro x
  have hnorm:‖OrderedCubicExpansion.evaluationPoint x‖^4=(∑ i,x i^2)^2:=by
    rw [show (4:ℕ)=2*2 by norm_num,pow_mul,norm_sq]
    rfl
  have hbound:=hb (OrderedCubicExpansion.evaluationPoint x)
  rw [hnorm] at hbound
  change (∑ i,(eval x (b i))^2)≤_ at hbound
  have hnon:0≤∑ i,(eval x (b i))^2:=Finset.sum_nonneg (fun i _=>sq_nonneg _)
  have hc:=hC0 x
  have hcu:=hCM x
  simp only [errorQuartic,map_sub,map_add,map_mul,map_sum,map_pow,eval_C,OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial_eval]
  constructor <;> nlinarith

/-- Every actual nonnegative quartic family has the explicit quadratic
SOS completion with a controlled homogeneous quartic error. -/
theorem exists_error_sos {n : ℕ} (hn : 0 < n) (a M : ℝ) (l H B C0 : Poly n)
    (hH : H.IsHomogeneous 2) (hB : B.IsHomogeneous 3) (hC : C0.IsHomogeneous 4)
    (hp :∀ (z : ℝ) (x : Fin n → ℝ), 0 ≤ QuarticCoefficientBounds.quartic a
      (eval x l) (eval x H) (eval x B) (eval x C0) z)
    (hM : 0 ≤ M) (hCM : ∀ x:Fin n→ℝ,eval x C0≤M*(∑ i,x i^2)^2) :
    ∃ Q:Poly n,Q.IsHomogeneous 4 ∧
      (∀ x:Fin n→ℝ,0≤eval x Q ∧ eval x Q≤
        (1+1600*((Nat.clog 2 n:ℝ)+1)^2)*M*(∑ i,x i^2)^2) ∧
      BoundedSOS 2 (model a l H B C0-s n^3*tr l+tr Q):=by
  obtain ⟨ha,u,b,hu,hb,hA,hdiv,hbound⟩:=exists_quartic_cubic_division hn a M l H B C0 hH hB hp hM hCM
  have hC0:∀ x:Fin n→ℝ,0≤eval x C0:=by
    intro x
    simpa [QuarticCoefficientBounds.quartic] using hp 0 x
  refine ⟨errorQuartic M C0 b,errorQuartic_homogeneous M C0 b hC hb,
    errorQuartic_bounds M C0 b hC0 hCM hbound,?_⟩
  rw [completion_identity a M ha hM l H B C0 u b hA hdiv]
  apply BoundedSOS.of_family
  intro i
  exact (roots_homogeneous a M u b hu hb i).totalDegree_le

end OptimalConvergenceRates.SphereDimensionBounds.QuarticDivisionSOS
