/-
  OptimalConvergenceRates/KrivineStengle/RealClosedGalois.lean

  Finite Galois theory over a real-closed field.  A Sylow two-subgroup
  fixes an odd-degree extension, hence fixes only the base field.
-/
import OptimalConvergenceRates.KrivineStengle.OddFinrankExtension
import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Sylow

noncomputable section

namespace OptimalConvergenceRates.KrivineStengle

universe u v

open IntermediateField

variable {G : Type*} [Group G] [Finite G]

/-- The index of a Sylow two-subgroup of a finite group is odd. -/
theorem sylowTwo_index_odd (P : Sylow 2 G) : Odd P.index := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  exact P.not_dvd_index heven.two_dvd

variable {R : Type u} {E : Type v}
  [Field R] [IsRealClosed R]
  [Field E] [Algebra R E] [FiniteDimensional R E] [IsGalois R E]

/-- A Sylow two-subgroup of a finite Galois extension of a real-closed
field fixes only the base field. -/
theorem sylowTwo_fixedField_eq_bot (P : Sylow 2 Gal(E/R)) :
    fixedField (P : Subgroup Gal(E/R)) = ⊥ := by
  have hdegree :
      Module.finrank R (fixedField (P : Subgroup Gal(E/R))) = P.index := by
    calc
      Module.finrank R (fixedField (P : Subgroup Gal(E/R))) =
          (fixedField (P : Subgroup Gal(E/R))).fixingSubgroup.index :=
        IntermediateField.finrank_eq_fixingSubgroup_index E _
      _ = P.index := by
        rw [IntermediateField.fixingSubgroup_fixedField]
  apply IntermediateField.finrank_eq_one_iff.mp
  apply finrank_eq_one_of_odd_finrank
  rw [hdegree]
  exact sylowTwo_index_odd P

/-- Consequently, a Sylow two-subgroup is the whole Galois group. -/
theorem sylowTwo_eq_top (P : Sylow 2 Gal(E/R)) :
    (P : Subgroup Gal(E/R)) = ⊤ := by
  have h := congrArg IntermediateField.fixingSubgroup
    (sylowTwo_fixedField_eq_bot P)
  rw [IntermediateField.fixingSubgroup_fixedField,
    IntermediateField.fixingSubgroup_bot] at h
  exact h

/-- Every finite Galois group over a real-closed field is a two-group. -/
theorem finiteGalois_isPGroup_two : IsPGroup 2 Gal(E/R) := by
  let P : Sylow 2 Gal(E/R) := default
  have htop : IsPGroup 2 (⊤ : Subgroup Gal(E/R)) := by
    rw [← sylowTwo_eq_top P]
    exact P.isPGroup'
  exact htop.of_equiv Subgroup.topEquiv

end OptimalConvergenceRates.KrivineStengle

end
