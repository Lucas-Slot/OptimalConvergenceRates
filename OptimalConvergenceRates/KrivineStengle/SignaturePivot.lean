/-
  OptimalConvergenceRates/KrivineStengle/SignaturePivot.lean

  A finite family of constant congruences that exposes a nonzero diagonal
  pivot in every nonzero symmetric matrix.
-/
import OptimalConvergenceRates.KrivineStengle.GuardedMatrixCongruence

noncomputable section

open Matrix MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

def guardedMatrixReindex {n d : ℕ} (e : Fin d ≃ Fin d)
    (M : Matrix (Fin d) (Fin d) (GuardedRational n)) :
    Matrix (Fin d) (Fin d) (GuardedRational n) :=
  Matrix.reindex e e M

theorem guardedMatrixReindex_valid {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F) (e : Fin d ≃ Fin d)
    {M : Matrix (Fin d) (Fin d) (GuardedRational n)}
    (hM : GuardedMatrixValid coeff x M) :
    GuardedMatrixValid coeff x (guardedMatrixReindex e M) := by
  intro i j
  exact hM (e.symm i) (e.symm j)

@[simp] theorem eval_guardedMatrixReindex {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F) (e : Fin d ≃ Fin d)
    (M : Matrix (Fin d) (Fin d) (GuardedRational n)) :
    evalGuardedMatrix coeff x (guardedMatrixReindex e M) =
      Matrix.reindex e e (evalGuardedMatrix coeff x M) := by
  rfl

theorem guardedMatrixReindex_isSymm {n d : ℕ} (e : Fin d ≃ Fin d)
    {M : Matrix (Fin d) (Fin d) (GuardedRational n)} (hM : M.IsSymm) :
    (guardedMatrixReindex e M).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact hM.apply (e.symm i) (e.symm j)

/-- Candidate `(i,j)`. If `i=j`, move diagonal entry `i` to position zero.
If `i≠j`, first replace basis vector `e_i` by `e_i+e_j`, then move the
resulting diagonal entry to position zero. -/
def guardedPivotMatrix {n k : ℕ} (p : Fin (k + 1) × Fin (k + 1))
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) (GuardedRational n)) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) (GuardedRational n) :=
  if _h : p.1 = p.2 then
    guardedMatrixReindex (Equiv.swap 0 p.1) (symmetrizeGuardedMatrix M)
  else
    guardedMatrixReindex (Equiv.swap 0 p.1)
      (guardedTransvectionCongruence p.2 p.1 M)

theorem guardedPivotMatrix_valid {n k : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (p : Fin (k + 1) × Fin (k + 1))
    {M : Matrix (Fin (k + 1)) (Fin (k + 1)) (GuardedRational n)}
    (hM : GuardedMatrixValid coeff x M) :
    GuardedMatrixValid coeff x (guardedPivotMatrix p M) := by
  by_cases hp : p.1 = p.2
  · simp only [guardedPivotMatrix, dif_pos hp]
    exact guardedMatrixReindex_valid coeff x _ (symmetrizeGuardedMatrix_valid coeff x hM)
  · simp only [guardedPivotMatrix, dif_neg hp]
    exact guardedMatrixReindex_valid coeff x _
      (guardedTransvectionCongruence_valid coeff x p.2 p.1 hM)

theorem guardedPivotMatrix_isSymm {n k : ℕ}
    (p : Fin (k + 1) × Fin (k + 1))
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) (GuardedRational n)) :
    (guardedPivotMatrix p M).IsSymm := by
  by_cases hp : p.1 = p.2
  · simp only [guardedPivotMatrix, dif_pos hp]
    exact guardedMatrixReindex_isSymm _
      (symmetrizeGuardedMatrix_isSymm M)
  · simp only [guardedPivotMatrix, dif_neg hp]
    exact guardedMatrixReindex_isSymm _
      (guardedTransvectionCongruence_isSymm p.2 p.1 M)

theorem eval_guardedPivotMatrix {n k : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (p : Fin (k + 1) × Fin (k + 1))
    {M : Matrix (Fin (k + 1)) (Fin (k + 1)) (GuardedRational n)}
    (hM : GuardedMatrixValid coeff x M)
    (hsymm : (evalGuardedMatrix coeff x M).IsSymm) :
    evalGuardedMatrix coeff x (guardedPivotMatrix p M) =
      if _h : p.1 = p.2 then
        Matrix.reindex (Equiv.swap 0 p.1) (Equiv.swap 0 p.1)
          (evalGuardedMatrix coeff x M)
      else
        Matrix.reindex (Equiv.swap 0 p.1) (Equiv.swap 0 p.1)
          ((Matrix.transvection p.2 p.1 (1 : F))ᵀ *
            evalGuardedMatrix coeff x M *
              Matrix.transvection p.2 p.1 (1 : F)) := by
  by_cases hp : p.1 = p.2
  · simp only [guardedPivotMatrix, dif_pos hp, eval_guardedMatrixReindex]
    rw [eval_symmetrizeGuardedMatrix coeff x M hsymm]
  · simp only [guardedPivotMatrix, dif_neg hp,
      eval_guardedMatrixReindex]
    rw [eval_guardedTransvectionCongruence coeff x p.2 p.1 hM hsymm]

theorem matrixSignature_eval_guardedPivotMatrix {n k : ℕ}
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (p : Fin (k + 1) × Fin (k + 1))
    {M : Matrix (Fin (k + 1)) (Fin (k + 1)) (GuardedRational n)}
    (hM : GuardedMatrixValid coeff x M)
    (hsymm : (evalGuardedMatrix coeff x M).IsSymm) :
    matrixSignature (evalGuardedMatrix coeff x (guardedPivotMatrix p M)) =
      matrixSignature (evalGuardedMatrix coeff x M) := by
  rw [eval_guardedPivotMatrix coeff x p hM hsymm]
  by_cases hp : p.1 = p.2
  · rw [dif_pos hp]
    exact matrixSignature_reindex _ _
  · rw [dif_neg hp]
    rw [matrixSignature_reindex]
    exact matrixSignature_transvection_congruence _ p.2 p.1 (Ne.symm hp)

end OptimalConvergenceRates.KrivineStengle

end

noncomputable section

open Matrix MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

theorem eval_guardedPivotMatrix_zero_zero {n k : ℕ}
    {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (p : Fin (k + 1) × Fin (k + 1))
    {M : Matrix (Fin (k + 1)) (Fin (k + 1)) (GuardedRational n)}
    (hM : GuardedMatrixValid coeff x M)
    (hsymm : (evalGuardedMatrix coeff x M).IsSymm) :
    evalGuardedMatrix coeff x (guardedPivotMatrix p M) 0 0 =
      if p.1 = p.2 then
        evalGuardedMatrix coeff x M p.1 p.1
      else
        evalGuardedMatrix coeff x M p.1 p.1 +
          evalGuardedMatrix coeff x M p.1 p.2 +
          evalGuardedMatrix coeff x M p.2 p.1 +
          evalGuardedMatrix coeff x M p.2 p.2 := by
  rw [eval_guardedPivotMatrix coeff x p hM hsymm]
  by_cases hp : p.1 = p.2
  · simp [hp, Matrix.reindex_apply, Equiv.swap_apply_left]
  · rw [dif_neg hp, if_neg hp]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_swap,
      Equiv.swap_apply_left]
    have htranspose :
        (Matrix.transvection p.2 p.1 (1 : F))ᵀ =
          Matrix.transvection p.1 p.2 (1 : F) := by
      ext a b
      simp [Matrix.transvection, Matrix.single, Matrix.one_apply, eq_comm, and_comm]
    rw [htranspose, Matrix.mul_assoc]
    simp only [Matrix.transvection_mul_apply_same,
      Matrix.mul_transvection_apply_same, one_mul]
    ring

end OptimalConvergenceRates.KrivineStengle

end

noncomputable section

open Matrix MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

theorem exists_guardedPivotMatrix_eval_zero_zero_ne_zero
    {n k : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    {M : Matrix (Fin (k + 1)) (Fin (k + 1)) (GuardedRational n)}
    (hvalid : GuardedMatrixValid coeff x M)
    (hsymm : (evalGuardedMatrix coeff x M).IsSymm)
    (hne : evalGuardedMatrix coeff x M ≠ 0) :
    ∃ p : Fin (k + 1) × Fin (k + 1),
      evalGuardedMatrix coeff x (guardedPivotMatrix p M) 0 0 ≠ 0 := by
  classical
  let A := evalGuardedMatrix coeff x M
  by_cases hdiag : ∃ i : Fin (k + 1), A i i ≠ 0
  · obtain ⟨i, hi⟩ := hdiag
    refine ⟨(i, i), ?_⟩
    rw [eval_guardedPivotMatrix_zero_zero coeff x (i, i) hvalid hsymm]
    simpa using hi
  · have hdiag_zero (i : Fin (k + 1)) : A i i = 0 := by
      by_contra hi
      exact hdiag ⟨i, hi⟩
    have hentry : ∃ i j : Fin (k + 1), A i j ≠ 0 := by
      by_contra h
      push_neg at h
      apply hne
      ext i j
      exact h i j
    obtain ⟨i, j, hij_entry⟩ := hentry
    have hij : i ≠ j := by
      intro h
      subst j
      exact hij_entry (hdiag_zero i)
    refine ⟨(i, j), ?_⟩
    rw [eval_guardedPivotMatrix_zero_zero coeff x (i, j) hvalid hsymm,
      if_neg hij]
    change A i i + A i j + A j i + A j j ≠ 0
    have hsymmA : A j i = A i j := hsymm.apply i j
    rw [hdiag_zero i, hdiag_zero j, hsymmA]
    have htwo : (2 : F) ≠ 0 := by norm_num
    convert mul_ne_zero htwo hij_entry using 1; ring

end OptimalConvergenceRates.KrivineStengle

end
