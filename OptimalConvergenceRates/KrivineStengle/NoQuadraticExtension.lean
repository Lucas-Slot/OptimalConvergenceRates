/-
  OptimalConvergenceRates/KrivineStengle/NoQuadraticExtension.lean

  Splitting of all quadratic polynomials rules out finite extensions of
  degree two.  Applied to `R[i]`, this is the quadratic obstruction used
  after the real-closed-field Sylow argument.
-/
import OptimalConvergenceRates.KrivineStengle.RealComplexQuadratic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u v

variable {K : Type u} {L : Type v}
  [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- If every quadratic polynomial over a field splits, that field has no
finite extension of degree two. -/
theorem finrank_ne_two_of_splits_degree_two
    (hsplit : ∀ p : K[X], p.natDegree = 2 → p.Splits) :
    Module.finrank K L ≠ 2 := by
  intro htwo
  have hsurj : Function.Surjective (algebraMap K L) := by
    intro x
    have hx : IsIntegral K x := IsIntegral.of_finite K x
    have hdiv : (minpoly K x).natDegree ∣ 2 := by
      rw [← htwo]
      exact minpoly.degree_dvd hx
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hdegree | hdegree
    · apply minpoly.mem_range_of_degree_eq_one K x
      exact (degree_eq_iff_natDegree_eq (minpoly.ne_zero hx)).mpr hdegree
    · have hs := hsplit (minpoly K x) hdegree
      have hdegreeOne : (minpoly K x).degree = 1 :=
        hs.degree_eq_one_of_irreducible (minpoly.irreducible hx)
      have hnatDegreeOne : (minpoly K x).natDegree = 1 :=
        (degree_eq_iff_natDegree_eq (minpoly.ne_zero hx)).mp hdegreeOne
      omega
  let e : K ≃ₐ[K] L := AlgEquiv.ofBijective (Algebra.ofId K L)
    ⟨(algebraMap K L).injective, hsurj⟩
  have hone : Module.finrank K L = 1 := by
    have h := LinearEquiv.finrank_eq e.toLinearEquiv
    simpa using h.symm
  omega

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]
  {E : Type v} [Field E] [Algebra (RealComplex R) E]
  [FiniteDimensional (RealComplex R) E]

/-- The real-complex field `R[i]` has no finite extension of degree two. -/
theorem realComplex_finrank_ne_two :
    Module.finrank (RealComplex R) E ≠ 2 :=
  finrank_ne_two_of_splits_degree_two realComplex_splits_of_natDegree_eq_two

end OptimalConvergenceRates.KrivineStengle

end
