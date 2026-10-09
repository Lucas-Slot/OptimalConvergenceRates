/-
  OptimalConvergenceRates/KrivineStengle/MaximalOrderedAlgebraicExtension.lean

  A maximal ordered algebraic extension inside the canonical algebraic closure.
-/
import OptimalConvergenceRates.KrivineStengle.MaximalOrderedSubfield
import OptimalConvergenceRates.KrivineStengle.OrderedTower
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

noncomputable section

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable (F : Type u) [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- A maximal intermediate field of the canonical algebraic closure that admits an order
extending the given order on `F`. -/
structure MaximalOrderedAlgebraicExtension where
  carrier : IntermediateField F (AlgebraicClosure F)
  orderData : OrderedExtensionData F carrier
  maximal : Maximal (fun E : IntermediateField F (AlgebraicClosure F) ↦
    Nonempty (OrderedExtensionData F E)) carrier

/-- Every ordered field has a maximal ordered algebraic extension inside its canonical
algebraic closure. -/
theorem exists_maximalOrderedAlgebraicExtension :
    Nonempty (MaximalOrderedAlgebraicExtension F) := by
  obtain ⟨M, ⟨E⟩, hM⟩ :=
    exists_maximal_orderableIntermediateField (F := F) (A := AlgebraicClosure F)
  exact ⟨⟨M, E, hM⟩⟩

namespace MaximalOrderedAlgebraicExtension

variable {F}

/-- The chosen carrier is algebraic over the original field. -/
theorem isAlgebraic (R : MaximalOrderedAlgebraicExtension F) :
    Algebra.IsAlgebraic F R.carrier := by
  infer_instance

/-- Maximality reformulated for a further intermediate field over the chosen carrier: if its
order extends the chosen order, restricting scalars gives no larger `F`-field. -/
theorem restrictScalars_eq_carrier (R : MaximalOrderedAlgebraicExtension F)
    {N : IntermediateField R.carrier (AlgebraicClosure F)} :
    letI : LinearOrder R.carrier := R.orderData.order
    letI : IsStrictOrderedRing R.carrier := R.orderData.strictOrderedRing
    OrderedExtensionData R.carrier N → N.restrictScalars F = R.carrier := by
  letI : LinearOrder R.carrier := R.orderData.order
  letI : IsStrictOrderedRing R.carrier := R.orderData.strictOrderedRing
  intro D
  have hle : R.carrier ≤ N.restrictScalars F := by
    intro x hx
    change (x : AlgebraicClosure F) ∈ N
    simpa using N.algebraMap_mem ⟨x, hx⟩
  have horder : Nonempty (OrderedExtensionData F (N.restrictScalars F)) :=
    ⟨R.orderData.transIntermediate F D⟩
  exact (R.maximal.eq_of_le horder hle).symm

end MaximalOrderedAlgebraicExtension

end OptimalConvergenceRates.KrivineStengle

end
