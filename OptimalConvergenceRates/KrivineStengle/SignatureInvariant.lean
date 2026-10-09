/-
  OptimalConvergenceRates/KrivineStengle/SignatureInvariant.lean

  Identification of intrinsic quadratic-form signature with diagonal signature.
-/
import OptimalConvergenceRates.KrivineStengle.DiagonalInertiaValues

noncomputable section

open QuadraticMap

namespace OptimalConvergenceRates.KrivineStengle

universe u v

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- The sum of ordered signs is the number of positive entries minus the number of negative
entries. -/
theorem sum_orderedSign_eq_card_sub_card (diagonal : I → F) :
    ∑ i, orderedSign (diagonal i) =
      ((positiveCoordinates diagonal).card : ℤ) -
        ((negativeCoordinates diagonal).card : ℤ) := by
  classical
  calc
    ∑ i, orderedSign (diagonal i) =
        ∑ i, ((if 0 < diagonal i then 1 else 0) +
          (if diagonal i < 0 then -1 else 0) : ℤ) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hpos : 0 < diagonal i
      · simp [orderedSign, hpos, not_lt_of_ge hpos.le]
      · by_cases hneg : diagonal i < 0
        · simp [orderedSign, hpos, hneg]
        · simp [orderedSign, hpos, hneg]
    _ = ((positiveCoordinates diagonal).card : ℤ) -
        ((negativeCoordinates diagonal).card : ℤ) := by
      rw [Finset.sum_add_distrib]
      have hneg :
          (∑ i : I, if diagonal i < 0 then (-1 : ℤ) else 0) =
            -((negativeCoordinates diagonal).card : ℤ) := by
        rw [← Finset.sum_filter]
        simp [negativeCoordinates]
      rw [hneg, sub_eq_add_neg]
      simp [positiveCoordinates]

/-- The intrinsic signature of a diagonal weighted-squares form is its elementary diagonal
signature. -/
theorem signature_weightedSumSquares {n : ℕ} (diagonal : Fin n → F) :
    signature (weightedSumSquares F diagonal) = diagonalSignature diagonal := by
  rw [signature, positiveIndex_weightedSumSquares,
    negativeIndex_weightedSumSquares, diagonalSignature,
    sum_orderedSign_eq_card_sub_card]

/-- Equivalent diagonalizations have the same diagonal signature. -/
theorem diagonalSignature_eq_of_isometry {n : ℕ}
    (Q : QuadraticForm F (Fin n → F)) (diagonal : Fin n → F)
    (e : (Fin n → F) ≃ₗ[F] (Fin n → F))
    (he : ∀ x, weightedSumSquares F diagonal (e x) = Q x) :
    diagonalSignature diagonal = signature Q := by
  rw [← signature_weightedSumSquares diagonal]
  exact (signature_congr e he).symm

/-- In particular, any two diagonalizations of the same quadratic form have equal diagonal
signature. -/
theorem diagonalSignature_eq_of_two_isometries {n : ℕ}
    (Q : QuadraticForm F (Fin n → F))
    (left right : Fin n → F)
    (eLeft eRight : (Fin n → F) ≃ₗ[F] (Fin n → F))
    (hLeft : ∀ x, weightedSumSquares F left (eLeft x) = Q x)
    (hRight : ∀ x, weightedSumSquares F right (eRight x) = Q x) :
    diagonalSignature left = diagonalSignature right := by
  rw [diagonalSignature_eq_of_isometry Q left eLeft hLeft,
    diagonalSignature_eq_of_isometry Q right eRight hRight]

end OptimalConvergenceRates.KrivineStengle

end
