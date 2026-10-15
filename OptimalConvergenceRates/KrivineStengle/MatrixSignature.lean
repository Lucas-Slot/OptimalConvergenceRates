/-
  OptimalConvergenceRates/KrivineStengle/MatrixSignature.lean

  Basis-independent signature of a finite symmetric matrix.
-/
import Mathlib.LinearAlgebra.Matrix.Reindex
import OptimalConvergenceRates.KrivineStengle.SignatureInvariant

noncomputable section

open Matrix QuadraticMap

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Signature of a matrix, defined through its associated quadratic form. -/
def matrixSignature {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : ℤ :=
  signature M.toQuadraticForm'


/-- The intrinsic matrix signature of a diagonal matrix is the sum of
the ordered signs of its diagonal entries. -/
theorem matrixSignature_diagonal {n : ℕ} (d : Fin n → F) :
    matrixSignature (Matrix.diagonal d) = diagonalSignature d := by
  rw [matrixSignature, ← signature_weightedSumSquares]
  apply signature_congr (LinearEquiv.refl F (Fin n → F))
  intro x
  simp [weightedSumSquares_apply, Matrix.toQuadraticForm', Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply,
    Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring
/-- Simultaneously relabeling the rows and columns does not change matrix signature. -/
theorem matrixSignature_reindex {n m : ℕ} (e : Fin n ≃ Fin m)
    (M : Matrix (Fin n) (Fin n) F) :
    matrixSignature (Matrix.reindex e e M) = matrixSignature M := by
  rw [matrixSignature, matrixSignature]
  apply signature_congr
    (LinearEquiv.piCongrLeft F (fun _ : Fin n ↦ F) e.symm)
  intro x
  simp only [Matrix.toQuadraticForm', Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply,
    smul_eq_mul, Matrix.reindex_apply, Matrix.submatrix_apply,
    LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft'_symm_apply]
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [← e.sum_comp]
  simp [Equiv.piCongrLeft'_symm, Equiv.piCongrLeft'_apply]

/-- Every symmetric matrix admits a diagonalization whose elementary diagonal signature is
its intrinsic matrix signature. -/
theorem exists_diagonalization_with_signature {n : ℕ}
    (M : Matrix (Fin n) (Fin n) F) (hM : M.IsSymm) :
    ∃ (diagonal : Fin (Module.finrank F (Fin n → F)) → F)
      (e : (Fin n → F) ≃ₗ[F]
        (Fin (Module.finrank F (Fin n → F)) → F)),
      (∀ x, weightedSumSquares F diagonal (e x) = M.toQuadraticForm' x) ∧
        diagonalSignature diagonal = matrixSignature M := by
  obtain ⟨diagonal, e, he⟩ := exists_matrix_diagonalization M hM
  refine ⟨diagonal, e, he, ?_⟩
  rw [matrixSignature]
  exact ((signature_congr e he).trans
    (signature_weightedSumSquares diagonal)).symm

/-- The diagonal signature attached to a symmetric matrix is independent of the chosen
diagonalization. -/
theorem diagonalSignature_eq_matrixSignature_of_isometry {n m : ℕ}
    (M : Matrix (Fin n) (Fin n) F) (diagonal : Fin m → F)
    (e : (Fin n → F) ≃ₗ[F] (Fin m → F))
    (he : ∀ x, weightedSumSquares F diagonal (e x) = M.toQuadraticForm' x) :
    diagonalSignature diagonal = matrixSignature M := by
  rw [matrixSignature]
  exact ((signature_congr e he).trans
    (signature_weightedSumSquares diagonal)).symm

end OptimalConvergenceRates.KrivineStengle

end

noncomputable section

open QuadraticMap

namespace OptimalConvergenceRates.KrivineStengle

universe u v

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem positiveIndex_le_finrank (Q : QuadraticForm F V) :
    positiveIndex Q ≤ Module.finrank F V := by
  obtain ⟨S, _, hS⟩ := exists_positiveSubspace_finrank_eq_positiveIndex Q
  rw [← hS]
  exact Submodule.finrank_le S

theorem negativeIndex_le_finrank (Q : QuadraticForm F V) :
    negativeIndex Q ≤ Module.finrank F V := by
  exact positiveIndex_le_finrank (-Q)

theorem signature_bounds (Q : QuadraticForm F V) :
    -(Module.finrank F V : ℤ) ≤ signature Q ∧
      signature Q ≤ (Module.finrank F V : ℤ) := by
  have hp := positiveIndex_le_finrank Q
  have hn := negativeIndex_le_finrank Q
  simp only [signature]
  omega

/-- The signature of a `d`-dimensional matrix lies in the finite interval
`[-d,d]`. No symmetry hypothesis is needed for this intrinsic bound. -/
theorem matrixSignature_bounds {d : ℕ} (M : Matrix (Fin d) (Fin d) F) :
    -(d : ℤ) ≤ matrixSignature M ∧ matrixSignature M ≤ (d : ℤ) := by
  simpa [matrixSignature] using signature_bounds M.toQuadraticForm'

end OptimalConvergenceRates.KrivineStengle

end
