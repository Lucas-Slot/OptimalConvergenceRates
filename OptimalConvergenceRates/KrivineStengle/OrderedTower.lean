/-
  OptimalConvergenceRates/KrivineStengle/OrderedTower.lean

  Composition of compatible orders along towers of field extensions.
-/
import OptimalConvergenceRates.KrivineStengle.OrderExtension
import Mathlib.FieldTheory.IntermediateField.Basic

noncomputable section

namespace OptimalConvergenceRates.KrivineStengle

universe u v w

variable (F : Type u) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {L : Type v} [Field L] [Algebra F L]
variable {K : Type w} [Field K] [Algebra F K] [Algebra L K] [IsScalarTower F L K]

/-- Compose compatible orders along a tower `F → L → K`. -/
def OrderedExtensionData.trans (E : OrderedExtensionData F L) :
    letI : LinearOrder L := E.order
    letI : IsStrictOrderedRing L := E.strictOrderedRing
    OrderedExtensionData L K → OrderedExtensionData F K := by
  letI : LinearOrder L := E.order
  letI : IsStrictOrderedRing L := E.strictOrderedRing
  intro D
  refine ⟨D.order, D.strictOrderedRing, ?_⟩
  intro a b hab
  have hL : algebraMap F L a ≤ algebraMap F L b := E.algebraMap_monotone hab
  have hK := D.algebraMap_monotone hL
  simpa only [IsScalarTower.algebraMap_apply F L K] using hK

variable {A : Type w} [Field A] [Algebra F A]

/-- Compose an order on an intermediate field with an order on a further intermediate field,
then view the result after restricting scalars back to `F`. -/
def OrderedExtensionData.transIntermediate
    {M : IntermediateField F A} (E : OrderedExtensionData F M)
    {N : IntermediateField M A} :
    letI : LinearOrder M := E.order
    letI : IsStrictOrderedRing M := E.strictOrderedRing
    OrderedExtensionData M N → OrderedExtensionData F (N.restrictScalars F) := by
  letI : LinearOrder M := E.order
  letI : IsStrictOrderedRing M := E.strictOrderedRing
  intro D
  refine ⟨D.order, D.strictOrderedRing, ?_⟩
  intro a b hab
  change @LE.le N D.order.toLE
    (algebraMap M N (algebraMap F M a))
    (algebraMap M N (algebraMap F M b))
  exact D.algebraMap_monotone (E.algebraMap_monotone hab)

end OptimalConvergenceRates.KrivineStengle

end
