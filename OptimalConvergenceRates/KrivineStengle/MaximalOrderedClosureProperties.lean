/-
  OptimalConvergenceRates/KrivineStengle/MaximalOrderedClosureProperties.lean

  Closure properties forced by maximality of an ordered algebraic extension.
-/
import OptimalConvergenceRates.KrivineStengle.MaximalOrderedAlgebraicExtension
import OptimalConvergenceRates.KrivineStengle.PositiveRootExtension

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

namespace MaximalOrderedAlgebraicExtension

/-- Every positive element of a maximal ordered algebraic extension is a square. -/
theorem isSquare_of_pos (R : MaximalOrderedAlgebraicExtension F) :
    letI : LinearOrder R.carrier := R.orderData.order
    letI : IsStrictOrderedRing R.carrier := R.orderData.strictOrderedRing
    ∀ {a : R.carrier}, 0 < a → IsSquare a := by
  letI : LinearOrder R.carrier := R.orderData.order
  letI : IsStrictOrderedRing R.carrier := R.orderData.strictOrderedRing
  intro a ha
  obtain ⟨L, fieldL, algebraL, hAlg, ⟨D⟩, r, hr⟩ :=
    exists_algebraic_orderedExtension_with_sq_eq ha
  letI : Algebra.IsAlgebraic R.carrier L := hAlg
  let i : L →ₐ[R.carrier] AlgebraicClosure F := IsAlgClosed.lift
  let N : IntermediateField R.carrier (AlgebraicClosure F) := i.fieldRange
  let e : L ≃ₐ[R.carrier] N := AlgEquiv.ofInjectiveField i
  let DN : OrderedExtensionData R.carrier N := D.transport R.carrier e
  have hN : N.restrictScalars F = R.carrier := R.restrictScalars_eq_carrier DN
  have hirN : i r ∈ N := ⟨r, rfl⟩
  have hsets : (N : Set (AlgebraicClosure F)) =
      (R.carrier : Set (AlgebraicClosure F)) := by
    exact congrArg (fun E : IntermediateField F (AlgebraicClosure F) ↦
      (E : Set (AlgebraicClosure F))) hN
  have hirN' : i r ∈ (N : Set (AlgebraicClosure F)) := hirN
  rw [hsets] at hirN'
  have hirR : i r ∈ R.carrier := hirN'
  let s : R.carrier := ⟨i r, hirR⟩
  rw [isSquare_iff_exists_sq]
  refine ⟨s, ?_⟩
  apply R.carrier.val.injective
  have himage := congrArg i hr
  simpa [s] using himage.symm

/-- Every nonnegative element of a maximal ordered algebraic extension is a square. -/
theorem isSquare_of_nonneg (R : MaximalOrderedAlgebraicExtension F) :
    letI : LinearOrder R.carrier := R.orderData.order
    letI : IsStrictOrderedRing R.carrier := R.orderData.strictOrderedRing
    ∀ {a : R.carrier}, 0 ≤ a → IsSquare a := by
  letI : LinearOrder R.carrier := R.orderData.order
  letI : IsStrictOrderedRing R.carrier := R.orderData.strictOrderedRing
  intro a ha
  rcases ha.eq_or_lt with rfl | ha
  · simp
  · exact R.isSquare_of_pos ha

end MaximalOrderedAlgebraicExtension

end OptimalConvergenceRates.KrivineStengle

end
