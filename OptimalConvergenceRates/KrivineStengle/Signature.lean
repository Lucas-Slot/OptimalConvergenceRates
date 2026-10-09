/-
  OptimalConvergenceRates/KrivineStengle/Signature.lean

  Ordered signs and signatures of diagonal forms.
-/
import OptimalConvergenceRates.KrivineStengle.HermiteTrace
import Mathlib.Algebra.Order.Hom.Ring

noncomputable section

namespace OptimalConvergenceRates.KrivineStengle

/-- The contribution of one diagonal coefficient to a quadratic-form signature. -/
def orderedSign {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (a : F) : ℤ :=
  if 0 < a then 1 else if a < 0 then -1 else 0

@[simp] theorem orderedSign_eq_one_iff {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {a : F} : orderedSign a = 1 ↔ 0 < a := by
  by_cases hpos : 0 < a
  · simp [orderedSign, hpos]
  · by_cases hneg : a < 0
    · simp [orderedSign, hpos, hneg]
    · simp [orderedSign, hpos, hneg]

@[simp] theorem orderedSign_eq_neg_one_iff {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {a : F} : orderedSign a = -1 ↔ a < 0 := by
  by_cases hneg : a < 0
  · have hpos : ¬0 < a := not_lt_of_ge hneg.le
    simp [orderedSign, hpos, hneg]
  · by_cases hpos : 0 < a
    · simp [orderedSign, hpos, hneg]
    · simp [orderedSign, hpos, hneg]

@[simp] theorem orderedSign_zero {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] : orderedSign (0 : F) = 0 := by
  simp [orderedSign]

/-- Ordered field embeddings preserve the three-valued ordered sign. -/
theorem orderedSign_map {F E : Type*}
    [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    [Field E] [LinearOrder E] [IsStrictOrderedRing E]
    (i : F →+*o E) (a : F) : orderedSign (i a) = orderedSign a := by
  have hinj : Function.Injective i := i.toRingHom.injective
  have hstrict : StrictMono i := i.monotone'.strictMono_of_injective hinj
  simp only [orderedSign, ← map_zero i, hstrict.lt_iff_lt]

/-- Signature of a diagonal quadratic form. -/
def diagonalSignature {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {n : ℕ} (diagonal : Fin n → F) : ℤ :=
  ∑ i, orderedSign (diagonal i)

theorem diagonalSignature_map {F E : Type*}
    [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    [Field E] [LinearOrder E] [IsStrictOrderedRing E]
    (i : F →+*o E) {n : ℕ} (diagonal : Fin n → F) :
    diagonalSignature (fun j ↦ i (diagonal j)) = diagonalSignature diagonal := by
  simp [diagonalSignature, orderedSign_map]

theorem diagonalSignature_append {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {m n : ℕ} (left : Fin m → F) (right : Fin n → F) :
    diagonalSignature (Sum.elim left right ∘ finSumFinEquiv.symm) =
      diagonalSignature left + diagonalSignature right := by
  change (∑ i : Fin (m + n), orderedSign (Sum.elim left right (finSumFinEquiv.symm i))) =
    (∑ i, orderedSign (left i)) + ∑ i, orderedSign (right i)
  calc
    (∑ i : Fin (m + n), orderedSign (Sum.elim left right (finSumFinEquiv.symm i))) =
        ∑ s : Fin m ⊕ Fin n, orderedSign (Sum.elim left right s) :=
      Equiv.sum_comp finSumFinEquiv.symm (fun s ↦ orderedSign (Sum.elim left right s))
    _ = _ := by simp

end OptimalConvergenceRates.KrivineStengle

end
