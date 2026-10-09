/-
  OptimalConvergenceRates/KrivineStengle/OddRootClosure.lean

  Odd-degree root closure forced by maximality of an ordered algebraic extension.
-/
import OptimalConvergenceRates.KrivineStengle.MaximalOrderedClosureProperties
import OptimalConvergenceRates.KrivineStengle.OddDegreeOrderExtension

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

namespace MaximalOrderedAlgebraicExtension

/-- Every odd-degree polynomial over a maximal ordered algebraic extension has a root. -/
theorem exists_isRoot_of_odd_natDegree
    (R : MaximalOrderedAlgebraicExtension F) :
    letI : LinearOrder R.carrier := R.orderData.order
    letI : IsStrictOrderedRing R.carrier := R.orderData.strictOrderedRing
    ∀ {p : R.carrier[X]}, Odd p.natDegree → ∃ x : R.carrier, p.IsRoot x := by
  letI : LinearOrder R.carrier := R.orderData.order
  letI : IsStrictOrderedRing R.carrier := R.orderData.strictOrderedRing
  intro p hpOdd
  obtain ⟨r, hr, hrOdd, hrp⟩ :=
    exists_irreducible_factor_of_odd_natDegree hpOdd
  let m : R.carrier[X] := r * C (leadingCoeff r)⁻¹
  have hmIrr : Irreducible m := by
    exact irreducible_mul_leadingCoeff_inv.mpr hr
  have hmMonic : m.Monic := by
    exact monic_mul_leadingCoeff_inv hr.ne_zero
  have hlc : leadingCoeff r ≠ 0 := leadingCoeff_ne_zero.mpr hr.ne_zero
  have hmDegree : m.natDegree = r.natDegree := by
    exact natDegree_mul_C (inv_ne_zero hlc)
  have hmOdd : Odd m.natDegree := by
    rw [hmDegree]
    exact hrOdd
  have hmDvdR : m ∣ r := by
    exact (dvd_mul_leadingCoeff_inv hr.ne_zero).mp dvd_rfl
  have hmDvdP : m ∣ p := hmDvdR.trans hrp
  letI : Fact (Irreducible m) := ⟨hmIrr⟩
  obtain ⟨D⟩ :=
    nonempty_orderedExtensionData_adjoinRoot_of_irreducible_of_odd_natDegree
      m hmIrr hmOdd
  let L := AdjoinRoot m
  letI : Module.Finite R.carrier L := hmMonic.finite_adjoinRoot
  letI : Algebra.IsAlgebraic R.carrier L := inferInstance
  let i : L →ₐ[R.carrier] AlgebraicClosure F := IsAlgClosed.lift
  let N : IntermediateField R.carrier (AlgebraicClosure F) := i.fieldRange
  let e : L ≃ₐ[R.carrier] N := AlgEquiv.ofInjectiveField i
  let DN : OrderedExtensionData R.carrier N := D.transport R.carrier e
  have hN : N.restrictScalars F = R.carrier := R.restrictScalars_eq_carrier DN
  have hpL : aeval (AdjoinRoot.root m) p = 0 := by
    obtain ⟨q, rfl⟩ := hmDvdP
    rw [map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
  have hpOmega : aeval (i (AdjoinRoot.root m)) p = 0 := by
    rw [Polynomial.aeval_algHom_apply, hpL, map_zero]
  have hrootN : i (AdjoinRoot.root m) ∈ N := ⟨AdjoinRoot.root m, rfl⟩
  have hsets : (N : Set (AlgebraicClosure F)) =
      (R.carrier : Set (AlgebraicClosure F)) := by
    exact congrArg (fun E : IntermediateField F (AlgebraicClosure F) ↦
      (E : Set (AlgebraicClosure F))) hN
  have hrootN' : i (AdjoinRoot.root m) ∈
      (N : Set (AlgebraicClosure F)) := hrootN
  rw [hsets] at hrootN'
  let x : R.carrier := ⟨i (AdjoinRoot.root m), hrootN'⟩
  refine ⟨x, ?_⟩
  apply Polynomial.isRoot_of_aeval_algebraMap_eq_zero (S := AlgebraicClosure F)
  simpa [x] using hpOmega

end MaximalOrderedAlgebraicExtension

end OptimalConvergenceRates.KrivineStengle

end
