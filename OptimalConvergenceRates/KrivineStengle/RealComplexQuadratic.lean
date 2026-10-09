/-
  OptimalConvergenceRates/KrivineStengle/RealComplexQuadratic.lean

  Quadratic splitting over the real-complex extension.
-/
import OptimalConvergenceRates.KrivineStengle.RealComplex
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.QuadraticDiscriminant

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-- Every degree-two polynomial over `R[i]` splits. -/
theorem realComplex_splits_of_natDegree_eq_two
    (p : (RealComplex R)[X]) (hp : p.natDegree = 2) : p.Splits := by
  have hp0 : p ≠ 0 := by
    intro h
    rw [h] at hp
    simp at hp
  have ha : p.coeff 2 ≠ 0 := by
    rw [← hp, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hp0
  have hpoly :
      p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
    calc
      p = ∑ i ∈ Finset.range (p.natDegree + 1), C (p.coeff i) * X ^ i :=
        p.as_sum_range_C_mul_X_pow
      _ = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
        rw [hp]
        norm_num [Finset.sum_range_succ]
        ring
  obtain ⟨s, hs⟩ :=
    realComplex_isSquare
      (discrim (p.coeff 2) (p.coeff 1) (p.coeff 0))
  obtain ⟨x, hx⟩ := exists_quadratic_eq_zero ha ⟨s, hs⟩
  refine Splits.of_natDegree_eq_two (f := p) (x := x) hp ?_
  rw [hpoly]
  simpa [pow_two] using hx

end OptimalConvergenceRates.KrivineStengle

end
