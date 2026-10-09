/-
  OptimalConvergenceRates/KrivineStengle/TraceZeroBlock.lean

  Signature cancellation for the real two-dimensional blocks contributed by
  conjugate nonreal roots in Hermite's trace form.
-/
import OptimalConvergenceRates.KrivineStengle.MatrixSignature
import OptimalConvergenceRates.KrivineStengle.OrderedSignCalculus

noncomputable section

open Matrix QuadraticMap

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- The shear used to diagonalize a nonzero trace-zero binary block. -/
def traceZeroBlockShear (t : F) : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) where
  toFun x := ![x 0 + t * x 1, x 1]
  invFun y := ![y 0 - t * y 1, y 1]
  left_inv x := by
    ext i
    fin_cases i <;> simp
  right_inv y := by
    ext i
    fin_cases i <;> simp
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp <;> ring

/-- The sum-and-difference coordinates used when the first diagonal entry vanishes. -/
def traceZeroBlockRotate : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) where
  toFun x := ![x 0 + x 1, x 0 - x 1]
  invFun y := ![(y 0 + y 1) / 2, (y 0 - y 1) / 2]
  left_inv x := by
    ext i
    fin_cases i <;> simp
  right_inv y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp <;> ring

set_option maxHeartbeats 800000 in
-- Matrix-coordinate normalization in these binary-form identities is elaboration-intensive.
private theorem traceZeroBlock_diagonalization_of_ne_zero
    (a b : F) (ha : a ≠ 0) (x : Fin 2 → F) :
    weightedSumSquares F ![a, -(a ^ 2 + b ^ 2) / a]
        (traceZeroBlockShear (b / a) x) =
      (!![a, b; b, -a] : Matrix (Fin 2) (Fin 2) F).toQuadraticMap' x := by
  simp [weightedSumSquares_apply, Fin.sum_univ_two, smul_eq_mul,
    traceZeroBlockShear, Matrix.toQuadraticMap',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply',
    dotProduct, Matrix.mulVec, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  field_simp
  ring

set_option maxHeartbeats 800000 in
-- Matrix-coordinate normalization in these binary-form identities is elaboration-intensive.
private theorem traceZeroBlock_diagonalization_zero_left (b : F)
    (x : Fin 2 → F) :
    weightedSumSquares F ![b / 2, -(b / 2)] (traceZeroBlockRotate x) =
      (!![0, b; b, 0] : Matrix (Fin 2) (Fin 2) F).toQuadraticMap' x := by
  simp [weightedSumSquares_apply, Fin.sum_univ_two, smul_eq_mul,
    traceZeroBlockRotate, Matrix.toQuadraticMap',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply',
    dotProduct, Matrix.mulVec, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

/-- Every symmetric two-by-two matrix with trace zero has signature zero. -/
theorem matrixSignature_traceZero_two (a b : F) :
    matrixSignature (!![a, b; b, -a] : Matrix (Fin 2) (Fin 2) F) = 0 := by
  by_cases ha : a = 0
  · subst a
    simp only [neg_zero]
    by_cases hb : b = 0
    · subst b
      rw [show (!![(0 : F), 0; 0, 0] : Matrix (Fin 2) (Fin 2) F) =
          Matrix.diagonal (fun _ ↦ 0) by ext i j <;> fin_cases i <;> fin_cases j <;> simp]
      rw [matrixSignature_diagonal]
      simp [diagonalSignature]
    · have hdiag := diagonalSignature_eq_matrixSignature_of_isometry
          (!![(0 : F), b; b, 0] : Matrix (Fin 2) (Fin 2) F)
          ![b / 2, -(b / 2)] traceZeroBlockRotate
          (traceZeroBlock_diagonalization_zero_left b)
      rw [← hdiag, diagonalSignature, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rcases lt_trichotomy 0 b with hpos | hzero | hneg
      · have hhalf_pos : 0 < b / 2 := div_pos hpos (by norm_num)
        rw [orderedSign_eq_one_iff.mpr hhalf_pos,
          orderedSign_eq_neg_one_iff.mpr (neg_neg_of_pos hhalf_pos)]
        norm_num
      · exact (hb hzero.symm).elim
      · have hhalf_neg : b / 2 < 0 := div_neg_of_neg_of_pos hneg (by norm_num)
        rw [orderedSign_eq_neg_one_iff.mpr hhalf_neg,
          orderedSign_eq_one_iff.mpr (neg_pos_of_neg hhalf_neg)]
        norm_num
  · have hdiag := diagonalSignature_eq_matrixSignature_of_isometry
        (!![a, b; b, -a] : Matrix (Fin 2) (Fin 2) F)
        ![a, -(a ^ 2 + b ^ 2) / a]
        (traceZeroBlockShear (b / a))
        (traceZeroBlock_diagonalization_of_ne_zero a b ha)
    rw [← hdiag]
    rw [diagonalSignature, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hsumsq : 0 < a ^ 2 + b ^ 2 :=
      add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg b)
    rcases lt_trichotomy 0 a with hpos | hzero | hneg
    · have hsecond_neg : -(a ^ 2 + b ^ 2) / a < 0 :=
        div_neg_of_neg_of_pos (neg_neg_of_pos hsumsq) hpos
      rw [orderedSign_eq_one_iff.mpr hpos,
        orderedSign_eq_neg_one_iff.mpr hsecond_neg]
      norm_num
    · exact (ha hzero.symm).elim
    · have hsecond_pos : 0 < -(a ^ 2 + b ^ 2) / a :=
        div_pos_of_neg_of_neg (neg_neg_of_pos hsumsq) hneg
      rw [orderedSign_eq_neg_one_iff.mpr hneg,
        orderedSign_eq_one_iff.mpr hsecond_pos]
      norm_num

set_option maxHeartbeats 800000 in
-- Matrix-coordinate normalization in these binary-form identities is elaboration-intensive.
private theorem twoByTwo_diagonalization_of_left_ne_zero
    (a b c : F) (ha : a ≠ 0) (x : Fin 2 → F) :
    weightedSumSquares F ![a, c - b ^ 2 / a]
        (traceZeroBlockShear (b / a) x) =
      (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) F).toQuadraticMap' x := by
  simp [weightedSumSquares_apply, Fin.sum_univ_two, smul_eq_mul,
    traceZeroBlockShear, Matrix.toQuadraticMap',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply',
    dotProduct, Matrix.mulVec, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  field_simp
  ring

set_option maxHeartbeats 800000 in
-- Matrix-coordinate normalization in these binary-form identities is elaboration-intensive.
private theorem twoByTwo_diagonalization_of_left_zero
    (b c : F) (hb : b ≠ 0) (x : Fin 2 → F) :
    weightedSumSquares F ![b / 2, -(b / 2)]
        ((traceZeroBlockShear (c / (2 * b))).trans traceZeroBlockRotate x) =
      (!![0, b; b, c] : Matrix (Fin 2) (Fin 2) F).toQuadraticMap' x := by
  simp [weightedSumSquares_apply, Fin.sum_univ_two, smul_eq_mul,
    LinearEquiv.trans_apply, traceZeroBlockShear, traceZeroBlockRotate,
    Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  field_simp
  ring

/-- A symmetric two-by-two matrix with negative determinant has signature zero. -/
theorem matrixSignature_two_of_det_neg (a b c : F)
    (hdet : a * c - b ^ 2 < 0) :
    matrixSignature (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) F) = 0 := by
  by_cases ha : a = 0
  · subst a
    have hb : b ≠ 0 := by
      intro hb
      subst b
      simp at hdet
    have hdiag := diagonalSignature_eq_matrixSignature_of_isometry
      (!![(0 : F), b; b, c] : Matrix (Fin 2) (Fin 2) F)
      ![b / 2, -(b / 2)]
      ((traceZeroBlockShear (c / (2 * b))).trans traceZeroBlockRotate)
      (twoByTwo_diagonalization_of_left_zero b c hb)
    rw [← hdiag, diagonalSignature, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rcases lt_trichotomy 0 b with hpos | hzero | hneg
    · have hhalf_pos : 0 < b / 2 := div_pos hpos (by norm_num)
      rw [orderedSign_eq_one_iff.mpr hhalf_pos,
        orderedSign_eq_neg_one_iff.mpr (neg_neg_of_pos hhalf_pos)]
      norm_num
    · exact (hb hzero.symm).elim
    · have hhalf_neg : b / 2 < 0 := div_neg_of_neg_of_pos hneg (by norm_num)
      rw [orderedSign_eq_neg_one_iff.mpr hhalf_neg,
        orderedSign_eq_one_iff.mpr (neg_pos_of_neg hhalf_neg)]
      norm_num
  · have hdiag := diagonalSignature_eq_matrixSignature_of_isometry
      (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) F)
      ![a, c - b ^ 2 / a] (traceZeroBlockShear (b / a))
      (twoByTwo_diagonalization_of_left_ne_zero a b c ha)
    rw [← hdiag, diagonalSignature, Fin.sum_univ_two]
    have hsecond : c - b ^ 2 / a = (a * c - b ^ 2) / a := by
      field_simp
    rw [hsecond]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rcases lt_trichotomy 0 a with hpos | hzero | hneg
    · have hquot : (a * c - b ^ 2) / a < 0 :=
        div_neg_of_neg_of_pos hdet hpos
      rw [orderedSign_eq_one_iff.mpr hpos,
        orderedSign_eq_neg_one_iff.mpr hquot]
      norm_num
    · exact (ha hzero.symm).elim
    · have hquot : 0 < (a * c - b ^ 2) / a :=
        div_pos_of_neg_of_neg hdet hneg
      rw [orderedSign_eq_neg_one_iff.mpr hneg,
        orderedSign_eq_one_iff.mpr hquot]
      norm_num

end OptimalConvergenceRates.KrivineStengle

end
