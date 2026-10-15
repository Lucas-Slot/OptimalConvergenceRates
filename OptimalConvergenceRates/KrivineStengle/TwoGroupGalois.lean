/-
  OptimalConvergenceRates/KrivineStengle/TwoGroupGalois.lean

  A finite Galois two-extension is trivial when its base field has no
  quadratic extensions.
-/
import OptimalConvergenceRates.KrivineStengle.NoQuadraticExtension
import OptimalConvergenceRates.KrivineStengle.PGroupIndex
import Mathlib.FieldTheory.KrullTopology

noncomputable section

namespace OptimalConvergenceRates.KrivineStengle

universe u v

open IntermediateField

variable {K : Type u} {E : Type v}
  [Field K] [Field E] [Algebra K E]
  [FiniteDimensional K E] [IsGalois K E]

/-- A finite Galois two-extension is trivial if none of its intermediate
fields has degree two over the base. -/
theorem finrank_eq_one_of_isPGroup_two_of_no_quadratic
    (hgroup : IsPGroup 2 Gal(E/K))
    (hno : ∀ L : IntermediateField K E, Module.finrank K L ≠ 2) :
    Module.finrank K E = 1 := by
  by_contra hdegree
  have hcard : Nat.card Gal(E/K) ≠ 1 := by
    rwa [IsGalois.card_aut_eq_finrank]
  letI : Nontrivial Gal(E/K) :=
    Finite.one_lt_card_iff_nontrivial.mp
      (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Nat.card_pos.ne', hcard⟩)
  obtain ⟨J, -, hindex⟩ :=
    IsPGroup.exists_le_index_eq_prime hgroup (H := (⊥ : Subgroup Gal(E/K))) bot_ne_top
  let L : IntermediateField K E := fixedField J
  have hfinrank : Module.finrank K L = J.index := by
    calc
      Module.finrank K L = L.fixingSubgroup.index :=
        IntermediateField.finrank_eq_fixingSubgroup_index E L
      _ = J.index := by
        dsimp [L]
        rw [IntermediateField.fixingSubgroup_fixedField]
  exact hno L (hfinrank.trans hindex)

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]
  {F : Type v} [Field F] [Algebra (RealComplex R) F]
  [FiniteDimensional (RealComplex R) F] [IsGalois (RealComplex R) F]

/-- A finite Galois two-extension of R[i] is trivial. -/
theorem realComplex_finrank_eq_one_of_isPGroup_two
    (hgroup : IsPGroup 2 Gal(F/RealComplex R)) :
    Module.finrank (RealComplex R) F = 1 :=
  finrank_eq_one_of_isPGroup_two_of_no_quadratic hgroup
    (fun _ ↦ realComplex_finrank_ne_two)

end OptimalConvergenceRates.KrivineStengle

end
