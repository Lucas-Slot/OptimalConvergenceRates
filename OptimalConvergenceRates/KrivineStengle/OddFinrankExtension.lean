/-
  OptimalConvergenceRates/KrivineStengle/OddFinrankExtension.lean

  A finite odd-degree extension of a real-closed ordered field is trivial.
  This is the real-field input for the Sylow argument in the proof that
  adjoining a square root of `-1` gives an algebraically closed field.
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsRealClosed.Basic

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u v

variable {R : Type u} {E : Type v}
  [Field R] [IsRealClosed R]
  [Field E] [Algebra R E] [FiniteDimensional R E]

/-- In a finite odd-degree extension of a real-closed field, every element
already lies in the image of the base field. -/
theorem mem_range_algebraMap_of_odd_finrank
    (hodd : Odd (Module.finrank R E)) (x : E) :
    x ∈ (algebraMap R E).range := by
  have hx : IsIntegral R x := IsIntegral.of_finite R x
  have hdeg : Odd (minpoly R x).natDegree :=
    hodd.of_dvd_nat (minpoly.degree_dvd hx)
  obtain ⟨r, hr⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree hdeg
  have hdegree : (minpoly R x).degree = 1 :=
    degree_eq_one_of_irreducible_of_root (minpoly.irreducible hx) hr
  exact minpoly.mem_range_of_degree_eq_one R x hdegree

/-- The scalar embedding of a finite odd-degree extension of a real-closed
field is surjective. -/
theorem algebraMap_surjective_of_odd_finrank
    (hodd : Odd (Module.finrank R E)) :
    Function.Surjective (algebraMap R E) := by
  intro x
  exact mem_range_algebraMap_of_odd_finrank hodd x

/-- A finite odd-degree extension of a real-closed field is isomorphic to
the base field as an algebra. -/
def oddFinrankAlgEquiv (hodd : Odd (Module.finrank R E)) : R ≃ₐ[R] E :=
  AlgEquiv.ofBijective (Algebra.ofId R E)
    ⟨(algebraMap R E).injective, algebraMap_surjective_of_odd_finrank hodd⟩

/-- In particular, a finite odd-degree extension of a real-closed field has
degree one. -/
theorem finrank_eq_one_of_odd_finrank
    (hodd : Odd (Module.finrank R E)) : Module.finrank R E = 1 := by
  have h := LinearEquiv.finrank_eq (oddFinrankAlgEquiv hodd).toLinearEquiv
  simpa using h.symm

end OptimalConvergenceRates.KrivineStengle

end
