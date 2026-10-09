/-
  OptimalConvergenceRates/KrivineStengle/RealComplexAlgebraicClosed.lean

  Algebraic closedness of the quadratic extension R[i] of a real-closed
  ordered field, via finite normal closures and Sylow theory.
-/
import OptimalConvergenceRates.KrivineStengle.RealClosedGalois
import OptimalConvergenceRates.KrivineStengle.TwoGroupGalois
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Closure

noncomputable section

open Polynomial
open scoped IntermediateField

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-- Every nonconstant polynomial over R[i] has a root. -/
theorem realComplex_exists_root (p : (RealComplex R)[X])
    (hp : p.degree ≠ 0) : ∃ x : RealComplex R, p.IsRoot x := by
  let A := AlgebraicClosure (RealComplex R)
  letI : Algebra.IsAlgebraic R A :=
    Algebra.IsAlgebraic.trans R (RealComplex R) A
  letI : Normal R A := IsAlgClosure.normal R A
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero A p hp
  let f : RealComplex R →ₐ[R] A :=
    IsScalarTower.toAlgHom R (RealComplex R) A
  let C₀ : IntermediateField R A := f.fieldRange
  let K₀ : IntermediateField R A := C₀ ⊔ R⟮z⟯
  letI : FiniteDimensional R C₀ := f.toLinearMap.finiteDimensional_range
  letI : FiniteDimensional R R⟮z⟯ :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral z)
  letI : FiniteDimensional R K₀ :=
    IntermediateField.finiteDimensional_sup C₀ R⟮z⟯
  let E₀ : IntermediateField R A := IntermediateField.normalClosure R K₀ A
  letI : IsGalois R E₀ := ⟨⟩
  have hC₀E : C₀ ≤ E₀ := by
    exact le_sup_left.trans (IntermediateField.le_normalClosure K₀)
  let cMap : RealComplex R →+* E₀ :=
    (algebraMap (RealComplex R) A).codRestrict E₀ fun c ↦ by
      apply hC₀E
      exact ⟨c, rfl⟩
  letI : Algebra (RealComplex R) E₀ := cMap.toAlgebra
  letI : IsScalarTower R (RealComplex R) E₀ :=
    IsScalarTower.of_algebraMap_eq' (by ext; rfl)
  have hzK : z ∈ K₀ := by
    change z ∈ C₀ ⊔ R⟮z⟯
    exact (le_sup_right : R⟮z⟯ ≤ C₀ ⊔ R⟮z⟯)
      (IntermediateField.mem_adjoin_simple_self R z)
  have hzE : z ∈ E₀ := IntermediateField.le_normalClosure K₀ hzK
  letI : FiniteDimensional (RealComplex R) E₀ :=
    FiniteDimensional.right R (RealComplex R) E₀
  letI : IsGalois (RealComplex R) E₀ :=
    IsGalois.tower_top_of_isGalois R (RealComplex R) E₀
  let zE : E₀ := ⟨z, hzE⟩
  have hzRoot : p.aeval zE = 0 := by
    apply E₀.val.injective
    calc
      E₀.val (p.aeval zE) = p.aeval z := by
        simpa [zE] using
          (map_aeval_eq_aeval_map
            (R := RealComplex R) (S := E₀)
            (T := RealComplex R) (U := A)
            (φ := RingHom.id (RealComplex R)) (ψ := E₀.val.toRingHom)
            (by ext c; rfl) p zE)
      _ = 0 := hz
      _ = E₀.val 0 := (map_zero E₀.val).symm
  have hgroupR : IsPGroup 2 Gal(E₀/R) := finiteGalois_isPGroup_two
  let restrict : Gal(E₀/RealComplex R) →* Gal(E₀/R) :=
    { toFun := fun σ ↦ σ.restrictScalars R
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hrestrict : Function.Injective restrict := by
    intro σ τ h
    exact (AlgEquiv.restrictScalars_injective R) h
  have hgroupC : IsPGroup 2 Gal(E₀/RealComplex R) :=
    IsPGroup.of_injective hgroupR restrict hrestrict
  have hfinrank : Module.finrank (RealComplex R) E₀ = 1 :=
    realComplex_finrank_eq_one_of_isPGroup_two hgroupC
  have hbot :
      (⊥ : IntermediateField (RealComplex R) E₀) = ⊤ :=
    IntermediateField.bot_eq_top_iff_finrank_eq_one.mpr hfinrank
  have hsurj : Function.Surjective (algebraMap (RealComplex R) E₀) := by
    intro x
    have hx : x ∈ (⊥ : IntermediateField (RealComplex R) E₀) := by
      rw [hbot]
      trivial
    exact hx
  obtain ⟨x, hx⟩ := hsurj zE
  refine ⟨x, ?_⟩
  rw [IsRoot.def]
  apply (algebraMap (RealComplex R) E₀).injective
  calc
    algebraMap (RealComplex R) E₀ (p.eval x) =
        (p.map (algebraMap (RealComplex R) E₀)).eval
          (algebraMap (RealComplex R) E₀ x) := by
      exact (eval_map_apply (p := p)
        (f := algebraMap (RealComplex R) E₀) x).symm
    _ = (p.map (algebraMap (RealComplex R) E₀)).eval zE := by rw [hx]
    _ = p.aeval zE := by rw [eval_map_algebraMap]
    _ = 0 := hzRoot
    _ = algebraMap (RealComplex R) E₀ 0 := (map_zero _).symm

/-- The quadratic extension R[i] of a real-closed field is algebraically
closed. -/
instance realComplex_isAlgClosed : IsAlgClosed (RealComplex R) :=
  IsAlgClosed.of_exists_root (k := RealComplex R) fun p _ hp ↦
    realComplex_exists_root p (degree_pos_of_irreducible hp).ne'

end OptimalConvergenceRates.KrivineStengle

end
