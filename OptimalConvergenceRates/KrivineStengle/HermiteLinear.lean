import OptimalConvergenceRates.KrivineStengle.HermiteTraceIsometry
import OptimalConvergenceRates.KrivineStengle.StrictRootCounting

noncomputable section

open Matrix Polynomial QuadraticMap

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F]

private theorem adjoinRoot_X_sub_C_root_eq (a : F) :
    AdjoinRoot.root (X - C a) = algebraMap F (AdjoinRoot (X - C a)) a := by
  rw [AdjoinRoot.algebraMap_eq]
  apply sub_eq_zero.mp
  have heval :
      (X - C a : F[X]).eval₂ (AdjoinRoot.of (X - C a))
        (AdjoinRoot.root (X - C a)) =
        AdjoinRoot.root (X - C a) - AdjoinRoot.of (X - C a) a := by
    simp only [eval₂_sub, eval₂_X, eval₂_C]
  rw [← heval]
  exact AdjoinRoot.eval₂_root (X - C a)

private theorem adjoinRoot_X_sub_C_aeval_eq (a : F) (h : F[X]) :
    aeval (AdjoinRoot.root (X - C a)) h =
      algebraMap F (AdjoinRoot (X - C a)) (h.eval a) := by
  rw [adjoinRoot_X_sub_C_root_eq]
  simp [aeval_def]

/-- The Hermite matrix of a linear polynomial is the one-by-one matrix containing
`h(a)`. -/
theorem hermiteTraceMatrix_X_sub_C (a : F) (h : F[X]) :
    hermiteTraceMatrix (X - C a) h (monic_X_sub_C a) =
      Matrix.diagonal
        (fun _ : Fin (X - C a).natDegree ↦ h.eval a) := by
  letI : Module.Free F (AdjoinRoot (X - C a)) :=
    (monic_X_sub_C a).free_adjoinRoot
  letI : Module.Finite F (AdjoinRoot (X - C a)) :=
    (AdjoinRoot.powerBasis' (monic_X_sub_C a)).finite
  ext i j
  have hdegree : (X - C a : F[X]).natDegree = 1 := natDegree_X_sub_C a
  have hi : (i : ℕ) = 0 := by omega
  have hj : (j : ℕ) = 0 := by omega
  have hij : i = j := Fin.ext (hi.trans hj.symm)
  subst j
  simp only [hermiteTraceMatrix, hi, zero_add, pow_zero, mul_one, Matrix.diagonal_apply_eq]
  rw [adjoinRoot_X_sub_C_aeval_eq,
    Algebra.trace_algebraMap, (AdjoinRoot.powerBasis' (monic_X_sub_C a)).finrank]
  simp

variable [LinearOrder F] [IsStrictOrderedRing F]

/-- Hermite's root-sign identity for a monic linear polynomial. -/
theorem hermiteSignature_X_sub_C (a : F) (h : F[X]) :
    hermiteSignature (X - C a) h (monic_X_sub_C a) = orderedSign (h.eval a) := by
  rw [hermiteSignature, hermiteTraceMatrix_X_sub_C, matrixSignature_diagonal]
  simp [diagonalSignature]

/-- Root-sign sum for a linear polynomial. -/
theorem rootSignSum_X_sub_C (a : F) (h : F[X]) :
    rootSignSum (X - C a) h = orderedSign (h.eval a) := by
  simp [rootSignSum, roots_X_sub_C]

/-- Hermite's root-sign identity for a monic linear polynomial, in the form used by
strict root counting. -/
theorem hermiteSignature_eq_rootSignSum_X_sub_C (a : F) (h : F[X]) :
    hermiteSignature (X - C a) h (monic_X_sub_C a) =
      rootSignSum (X - C a) h := by
  rw [hermiteSignature_X_sub_C, rootSignSum_X_sub_C]

end OptimalConvergenceRates.KrivineStengle

end

noncomputable section

open Matrix Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- The Hermite signature of the monic constant polynomial `1` is zero. -/
theorem hermiteSignature_one (h : F[X]) :
    hermiteSignature 1 h monic_one = 0 := by
  rw [hermiteSignature,
    hermiteTraceMatrix_eq_of_natDegree_eq_zero 1 h monic_one (by simp)]
  have hzero : matrixSignature (0 : Matrix (Fin 0) (Fin 0) F) = 0 := by
    calc
      matrixSignature (0 : Matrix (Fin 0) (Fin 0) F) =
        matrixSignature (Matrix.diagonal (fun _ : Fin 0 ↦ (0 : F))) := by
        congr 1
        ext i
        exact Fin.elim0 i
      _ = diagonalSignature (fun _ : Fin 0 ↦ (0 : F)) :=
        matrixSignature_diagonal _
      _ = 0 := by simp [diagonalSignature]
  rw [show (1 : F[X]).natDegree = 0 by simp]
  exact hzero

/-- The polynomial `1` has no roots, so its root-sign sum is zero. -/
theorem rootSignSum_one (h : F[X]) : rootSignSum 1 h = 0 := by
  simp [rootSignSum]

/-- Hermite's root-sign identity for the monic constant polynomial `1`. -/
theorem hermiteSignature_eq_rootSignSum_one (h : F[X]) :
    hermiteSignature 1 h monic_one = rootSignSum 1 h := by
  rw [hermiteSignature_one, rootSignSum_one]

end OptimalConvergenceRates.KrivineStengle

end
