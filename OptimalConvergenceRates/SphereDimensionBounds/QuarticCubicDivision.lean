import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.SphereDimensionBounds.CubicDiscriminantDivision
import OptimalConvergenceRates.SphereDimensionBounds.QuarticCoefficientBounds

/-! The actual polynomial division input for the all-pole selector proof,
derived from a globally nonnegative univariate-quartic family. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.QuarticCubicDivision
open scoped BigOperators
open MvPolynomial WeightedQuadraticSplit

local instance (priority := 2000) finOrderDecidableEq (n : ℕ) : DecidableEq (Fin n) :=
  (inferInstance : LinearOrder (Fin n)).toDecidableEq

def correctedQuadratic {n : ℕ} (a M : ℝ) (H : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ:=
  H+C (2*Real.sqrt (a*M))*OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n

theorem correctedQuadratic_homogeneous {n : ℕ} (a M : ℝ) (H : MvPolynomial (Fin n) ℝ)
    (hH : H.IsHomogeneous 2) : (correctedQuadratic a M H).IsHomogeneous 2:=by
  apply hH.add
  apply IsHomogeneous.C_mul
  apply IsHomogeneous.sum
  intro i _
  exact (isHomogeneous_X ℝ i).pow 2

/-- Actual global quartic nonnegativity implies both the nonnegative
corrected quadratic and the cubic discriminant bound. -/
theorem correctedQuadratic_bounds {n : ℕ} (a M : ℝ) (l H B C0 : MvPolynomial (Fin n) ℝ)
    (hp :∀ (s : ℝ) (x : Fin n → ℝ), 0 ≤ QuarticCoefficientBounds.quartic a
      (eval x l) (eval x H) (eval x B) (eval x C0) s)
    (hM : 0 ≤ M) (hCM : ∀ x:Fin n→ℝ,eval x C0≤M*(∑ i,x i^2)^2) :
    0≤a ∧ (∀ x:Fin n→ℝ,0≤eval x (correctedQuadratic a M H)) ∧
      ∀ x:Point (Fin n),(eval (fun i=>x i) B)^2≤
        4*M*eval (fun i=>x i) (correctedQuadratic a M H)*‖x‖^4:=by
  have hb:=QuarticCoefficientBounds.polynomial_radial_bounds a M l H B C0
    (OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n) hp hM
    (by intro x;rw [OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial_eval];positivity)
    (by simpa only [OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial_eval] using hCM)
  refine ⟨(hb (fun _=>0)).1,?_,?_⟩
  · intro x
    simpa only [correctedQuadratic,map_add,map_mul,eval_C] using (hb x).2.1
  · intro x
    have hh:=(hb (fun i=>x i)).2.2
    have hR:eval (fun i=>x i) (OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n)=‖x‖^2:=by
      rw [OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial_eval,←norm_sq]
    have hA:eval (fun i=>x i) (correctedQuadratic a M H)=
        eval (fun i=>x i) H+2*Real.sqrt (a*M)*eval (fun i=>x i) (OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n):=by
      simp only [correctedQuadratic,map_add,map_mul,eval_C]
    rw [←hA,hR] at hh
    convert hh using 1
    ring

/-- The actual cubic division used after centering a quartic functional.
Every linear factor, quadratic vector, identity and logarithmic bound is
constructed from global nonnegativity and the original bottom bound. -/
theorem exists_quartic_cubic_division {n : ℕ} (hn : 0 < n) (a M : ℝ)
    (l H B C0 : MvPolynomial (Fin n) ℝ) (hH : H.IsHomogeneous 2) (hB : B.IsHomogeneous 3)
    (hp :∀ (s : ℝ) (x : Fin n → ℝ), 0 ≤ QuarticCoefficientBounds.quartic a
      (eval x l) (eval x H) (eval x B) (eval x C0) s)
    (hM : 0 ≤ M) (hCM : ∀ x:Fin n→ℝ,eval x C0≤M*(∑ i,x i^2)^2) :
    0≤a ∧ ∃ (u b:Fin n→MvPolynomial (Fin n) ℝ),
      (∀ i,(u i).IsHomogeneous 1) ∧ (∀ i,(b i).IsHomogeneous 2) ∧
      (∑ i,u i^2)=correctedQuadratic a M H ∧ (∑ i,u i*b i)=B ∧
      ∀ x:Point (Fin n),(∑ i,(eval (fun j=>x j) (b i))^2)≤
        6400*((Nat.clog 2 n:ℝ)+1)^2*M*‖x‖^4:=by
  obtain ⟨ha,hA,hdisc⟩:=correctedQuadratic_bounds a M l H B C0 hp hM hCM
  exact ⟨ha,CubicDiscriminantDivision.exists_division_of_discriminant hn
    (correctedQuadratic a M H) B (correctedQuadratic_homogeneous a M H hH) hB hA hM hdisc⟩

end OptimalConvergenceRates.SphereDimensionBounds.QuarticCubicDivision
