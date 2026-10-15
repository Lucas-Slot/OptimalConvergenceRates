/-
  OptimalConvergenceRates/KrivineStengle/SignatureDiagonalization.lean

  Diagonalization of finite quadratic forms over ordered fields.
-/
import OptimalConvergenceRates.KrivineStengle.Signature
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

noncomputable section

open Matrix QuadraticMap

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- A finite quadratic form over an ordered field is linearly equivalent to a diagonal
weighted sum of squares. This is the generic diagonalization theorem needed before defining
matrix inertia; Mathlib's orthogonal-basis construction supplies the change of basis. -/
theorem exists_quadraticForm_diagonalization {n : ℕ}
    (Q : QuadraticForm F (Fin n → F)) :
    ∃ (diagonal : Fin (Module.finrank F (Fin n → F)) → F)
      (e : (Fin n → F) ≃ₗ[F]
        (Fin (Module.finrank F (Fin n → F)) → F)),
      ∀ x, weightedSumSquares F diagonal (e x) = Q x := by
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨diagonal, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares
  exact ⟨diagonal, e.toLinearEquiv, e.map_app⟩

/-- Matrix form of generic quadratic-form diagonalization. The symmetry hypothesis records
the intended Hermite-matrix use; the quadratic map itself only depends on the symmetric part. -/
theorem exists_matrix_diagonalization {n : ℕ} (M : Matrix (Fin n) (Fin n) F)
    (_hM : M.IsSymm) :
    ∃ (diagonal : Fin (Module.finrank F (Fin n → F)) → F)
      (e : (Fin n → F) ≃ₗ[F]
        (Fin (Module.finrank F (Fin n → F)) → F)),
      ∀ x, weightedSumSquares F diagonal (e x) = M.toQuadraticForm' x :=
  exists_quadraticForm_diagonalization M.toQuadraticForm'

/-- Evaluation of a diagonal quadratic form as an ordinary finite sum. -/
theorem weightedSumSquares_eq_sum {n : ℕ} (diagonal x : Fin n → F) :
    weightedSumSquares F diagonal x = ∑ i, diagonal i * x i ^ 2 := by
  simp [weightedSumSquares_apply, pow_two]

end OptimalConvergenceRates.KrivineStengle

end
