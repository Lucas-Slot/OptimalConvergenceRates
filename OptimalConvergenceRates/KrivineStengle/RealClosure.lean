/-
  OptimalConvergenceRates/KrivineStengle/RealClosure.lean

  Existence of an ordered real-closed extension of every ordered field.
-/
import OptimalConvergenceRates.KrivineStengle.OddRootClosure
import OptimalConvergenceRates.KrivineStengle.SignTransfer
import Mathlib.FieldTheory.IsRealClosed.Basic

noncomputable section

namespace OptimalConvergenceRates.KrivineStengle

namespace MaximalOrderedAlgebraicExtension

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- A maximal ordered algebraic extension is real closed. -/
theorem isRealClosed (R : MaximalOrderedAlgebraicExtension F) :
    letI : LinearOrder R.carrier := R.orderData.order
    letI : IsStrictOrderedRing R.carrier := R.orderData.strictOrderedRing
    IsRealClosed R.carrier := by
  letI : LinearOrder R.carrier := R.orderData.order
  letI : IsStrictOrderedRing R.carrier := R.orderData.strictOrderedRing
  exact IsRealClosed.of_linearOrderedField R.isSquare_of_nonneg
    R.exists_isRoot_of_odd_natDegree

end MaximalOrderedAlgebraicExtension

/-- Every ordered field admits an order-preserving embedding into a real-closed field. -/
theorem orderedRealClosureExistence : OrderedRealClosureExistenceStatement := by
  intro F _ _ _
  obtain ⟨R⟩ := exists_maximalOrderedAlgebraicExtension F
  letI : LinearOrder R.carrier := R.orderData.order
  letI : IsStrictOrderedRing R.carrier := R.orderData.strictOrderedRing
  let hRealClosed : IsRealClosed R.carrier := R.isRealClosed
  let embedding : F →+*o R.carrier :=
    { toRingHom := algebraMap F R.carrier
      monotone' := fun _ _ h ↦ R.orderData.algebraMap_monotone h }
  exact ⟨{
    Carrier := R.carrier
    field := inferInstance
    order := R.orderData.order
    strictOrderedRing := R.orderData.strictOrderedRing
    realClosed := hRealClosed
    embedding := embedding
  }⟩

end OptimalConvergenceRates.KrivineStengle

end
