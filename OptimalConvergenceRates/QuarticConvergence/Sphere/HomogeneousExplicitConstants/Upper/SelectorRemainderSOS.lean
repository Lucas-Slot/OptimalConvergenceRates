import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.QuadraticBoundSOS

/-! The exact final scalar remainder and sharp budget identity in the
local selector-to-radial-SOS assembly. Selector existence and the radial
quadratic-cubic certificate are not premises hidden in these claims. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace SelectorRemainderSOS

open scoped BigOperators
open MvPolynomial SelectorSchur QuadraticBoundSOS

/-- Replacing the old conditioned remainder by its exact quadratic
factorization saves one copy of the selector bottom budget. -/
theorem polynomial_completion_budget_sharp {ι : Type*}
    (a S M Z : ℝ) (ha : 0 < a) (s l H B C0 u R : MvPolynomial ι ℝ) :
    model a s l H B C0-C0+C ((Z+1)*S*M)*R^2 =
      squareRoot a s l u^2+
        (s^2*schurA a l H u+s*schurD a l B u+C (Z*S*M)*R^2)+
        (C (S*M)*R^2-C (1/a)*u^2) := by
  rw [polynomial_completion a ((Z+1)*S*M) ha s l H B C0 u R]
  simp only [map_add,map_mul,map_one]
  ring

/-- From an actual polynomial PSD selector, the scalar Schur remainder
is already a global SOS with quadratic roots; no radial multiplier or
strictly positive lower spectral bound is required. -/
theorem selector_remainder_exists_squares {n : ℕ}
    (a S M : ℝ) (ha : 0 < a) (hS : 0 ≤ S) (hM : 0 ≤ M)
    (l H B u : MvPolynomial (Fin n) ℝ) (hu : u.IsHomogeneous 2)
    (hG : ∀ x : Fin n→ℝ,(selectorMatrix a (eval x l) (eval x H) (eval x B)
      (eval x u) (S*M*(∑ i,x i^2)^2)).PosSemidef) :
    ∃ b : (Fin n×Fin n)→MvPolynomial (Fin n) ℝ,
      (∀ i,(b i).IsHomogeneous 2) ∧
      C (S*M)*(Foundation.radiusPolynomial n)^2-C (1/a)*u^2=∑ i,b i^2 := by
  apply scaled_quadratic_difference_exists_squares u hu ha (mul_nonneg hS hM)
  intro x
  exact (selector_scalar_bounds ha (hG x)).2.1

/-- A zero leading selector entry really forces the full leading row to
vanish and leaves the required quadratic-cubic discriminant inequality. -/
theorem zero_leading_scalar {l H B u F : ℝ}
    (hG : (selectorMatrix 0 l H B u F).PosSemidef) :
    l=0 ∧ u=0 ∧ 0≤H ∧ 0≤F ∧ B^2≤4*H*F := by
  have hl := discrim_le_zero (a:=0) (b:=l) (c:=H-2*u) (fun x ↦ by
    simpa using selectorMatrix_quadratic_nonneg hG x 1 0)
  have hu := discrim_le_zero (a:=0) (b:=2*u) (c:=F) (fun x ↦ by
    simpa using selectorMatrix_quadratic_nonneg hG x 0 1)
  have hl0 : l=0 := by
    simp only [discrim,zero_mul,sub_zero] at hl
    nlinarith [sq_nonneg l]
  have hu0 : u=0 := by
    simp only [discrim,zero_mul,sub_zero] at hu
    nlinarith [sq_nonneg u]
  have hH := selectorMatrix_quadratic_nonneg hG 0 1 0
  have hF := selectorMatrix_quadratic_nonneg hG 0 0 1
  have hd := discrim_le_zero (a:=H) (b:=B) (c:=F) (fun x ↦ by
    simpa only [hu0,zero_mul,mul_zero,sub_zero,zero_add,add_zero,mul_one,
      one_pow,pow_two] using selectorMatrix_quadratic_nonneg hG 0 x 1)
  refine ⟨hl0,hu0,?_,?_,?_⟩
  · simpa [hu0] using hH
  · simpa using hF
  · simpa only [discrim,sub_nonpos] using hd

end SelectorRemainderSOS
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
