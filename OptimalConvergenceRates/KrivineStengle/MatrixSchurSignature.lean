/-
  OptimalConvergenceRates/KrivineStengle/MatrixSchurSignature.lean

  The one-pivot Schur-complement identity for matrix signature.
-/
import OptimalConvergenceRates.KrivineStengle.MatrixSignature
import OptimalConvergenceRates.KrivineStengle.SignatureProduct
import Mathlib.Tactic.FieldSimp

noncomputable section

open Matrix QuadraticMap

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Delete the zeroth row and column. -/
def matrixTail {k : ℕ} (M : Matrix (Fin (k + 1)) (Fin (k + 1)) F) :
    Matrix (Fin k) (Fin k) F :=
  fun i j ↦ M i.succ j.succ

/-- Schur complement of the zeroth entry. It is used only on branches where
that entry is nonzero. -/
def matrixSchurComplement {k : ℕ}
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) F) :
    Matrix (Fin k) (Fin k) F :=
  fun i j ↦ M i.succ j.succ - M i.succ 0 * M 0 j.succ / M 0 0

theorem matrixSchurComplement_isSymm {k : ℕ}
    {M : Matrix (Fin (k + 1)) (Fin (k + 1)) F} (hM : M.IsSymm) :
    (matrixSchurComplement M).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [matrixSchurComplement]
  rw [hM.apply i.succ j.succ, hM.apply i.succ 0, hM.apply 0 j.succ]
  ring

private def headTailLinear {k : ℕ}
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) F) :
    (Fin k → F) →ₗ[F] F where
  toFun y := ∑ j, M 0 j.succ * y j
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Complete the square at the zeroth coordinate. -/
def matrixPivotEquiv {k : ℕ}
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) F) :
    (Fin (k + 1) → F) ≃ₗ[F] (Fin 1 → F) × (Fin k → F) where
  toFun x :=
    (fun _ ↦ x 0 + headTailLinear M (fun j ↦ x j.succ) / M 0 0,
      fun j ↦ x j.succ)
  invFun z := Fin.cases
    (z.1 0 - headTailLinear M z.2 / M 0 0) z.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [headTailLinear]
    · simp
  right_inv z := by
    apply Prod.ext
    · funext i
      fin_cases i
      simp [headTailLinear]
    · funext i
      simp
  map_add' x y := by
    apply Prod.ext
    · funext i
      fin_cases i
      change x 0 + y 0 +
          headTailLinear M ((fun j ↦ x j.succ) + (fun j ↦ y j.succ)) / M 0 0 = _
      rw [map_add]
      simp
      ring
    · funext i
      simp
  map_smul' c x := by
    apply Prod.ext
    · funext i
      fin_cases i
      change c * x 0 +
          headTailLinear M (c • (fun j ↦ x j.succ)) / M 0 0 = _
      rw [map_smul]
      simp
      ring
    · funext i
      simp

private theorem matrixQuadratic_split {k : ℕ}
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (hM : M.IsSymm)
    (x : Fin (k + 1) → F) :
    M.toQuadraticForm' x =
      M 0 0 * x 0 ^ 2 +
        2 * x 0 * headTailLinear M (fun j ↦ x j.succ) +
        (matrixTail M).toQuadraticForm' (fun j ↦ x j.succ) := by
  simp only [Matrix.toQuadraticForm', Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec, matrixTail,
    headTailLinear, pow_two]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hrow (i : Fin k) : M i.succ 0 = M 0 i.succ := hM.apply 0 i.succ
  simp_rw [Fin.sum_univ_succ]
  simp only [hrow]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hcross :
      (∑ i : Fin k, x i.succ * (M 0 i.succ * x 0)) =
        x 0 * ∑ i : Fin k, M 0 i.succ * x i.succ := by
    calc
      _ = ∑ i : Fin k, (M 0 i.succ * x i.succ) * x 0 := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i : Fin k, M 0 i.succ * x i.succ) * x 0 := by
        rw [Finset.sum_mul]
      _ = _ := by ring
  rw [hcross]
  change x 0 * (M 0 0 * x 0) +
      x 0 * (∑ i : Fin k, M 0 i.succ * x i.succ) +
      (x 0 * (∑ i : Fin k, M 0 i.succ * x i.succ) +
        ∑ i : Fin k, x i.succ *
          ∑ j : Fin k, M i.succ j.succ * x j.succ) =
    (M 0 0 * (x 0 * x 0) +
      2 * x 0 * (∑ i : Fin k, M 0 i.succ * x i.succ)) +
      ∑ i : Fin k, x i.succ *
        ∑ j : Fin k, M i.succ j.succ * x j.succ
  ring

private theorem matrixSchurQuadratic {k : ℕ}
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (hM : M.IsSymm)
    (y : Fin k → F) :
    (matrixSchurComplement M).toQuadraticForm' y =
      (matrixTail M).toQuadraticForm' y -
        (headTailLinear M y) ^ 2 / M 0 0 := by
  have hrank :
      (∑ i, y i * ∑ j,
        (M 0 i.succ * M 0 j.succ / M 0 0) * y j) =
        (∑ i, M 0 i.succ * y i) ^ 2 / M 0 0 := by
    let B := ∑ j, M 0 j.succ * y j
    calc
      (∑ i, y i * ∑ j,
          (M 0 i.succ * M 0 j.succ / M 0 0) * y j) =
          ∑ i, (M 0 i.succ * y i) * (M 0 0)⁻¹ * B := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [B, div_eq_mul_inv]
        rw [Finset.mul_sum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = B * (M 0 0)⁻¹ * B := by
        rw [← Finset.sum_mul]
        rw [← Finset.sum_mul]
      _ = B ^ 2 / M 0 0 := by
        simp only [div_eq_mul_inv, pow_two]
        ring
  simp only [Matrix.toQuadraticForm', Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec,
    matrixSchurComplement, matrixTail, headTailLinear]
  have hcol (i : Fin k) : M i.succ 0 = M 0 i.succ :=
    hM.apply 0 i.succ
  simp_rw [hcol, sub_mul, Finset.sum_sub_distrib, mul_sub]
  rw [Finset.sum_sub_distrib, hrank]
  rfl

private theorem matrixPivotEquiv_isometry {k : ℕ}
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) F)
    (hM : M.IsSymm) (hpivot : M 0 0 ≠ 0)
    (x : Fin (k + 1) → F) :
    ((weightedSumSquares F (fun _ : Fin 1 ↦ M 0 0)).prod
      (matrixSchurComplement M).toQuadraticForm')
        (matrixPivotEquiv M x) = M.toQuadraticForm' x := by
  let y : Fin k → F := fun j ↦ x j.succ
  let b : F := headTailLinear M y
  rw [QuadraticMap.prod_apply]
  rw [matrixQuadratic_split M hM x]
  change weightedSumSquares F (fun _ : Fin 1 ↦ M 0 0)
      (fun _ ↦ x 0 + headTailLinear M y / M 0 0) +
      (matrixSchurComplement M).toQuadraticForm' y = _
  rw [matrixSchurQuadratic M hM y]
  simp only [weightedSumSquares_apply, Fin.sum_univ_one, smul_eq_mul,
    y]
  field_simp [hpivot]
  ring

/-- A nonzero symmetric pivot splits off its ordered sign and leaves its
Schur complement. This is the recursive invariant used by the finite
signature decision procedure. -/
theorem matrixSignature_eq_orderedSign_add_schur {k : ℕ}
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) F)
    (hM : M.IsSymm) (hpivot : M 0 0 ≠ 0) :
    matrixSignature M =
      orderedSign (M 0 0) + matrixSignature (matrixSchurComplement M) := by
  rw [matrixSignature, matrixSignature]
  calc
    signature M.toQuadraticForm' =
        signature ((weightedSumSquares F (fun _ : Fin 1 ↦ M 0 0)).prod
          (matrixSchurComplement M).toQuadraticForm') :=
      signature_congr (matrixPivotEquiv M)
        (matrixPivotEquiv_isometry M hM hpivot)
    _ = signature (weightedSumSquares F (fun _ : Fin 1 ↦ M 0 0)) +
        signature (matrixSchurComplement M).toQuadraticForm' :=
      signature_prod _ _
    _ = orderedSign (M 0 0) +
        signature (matrixSchurComplement M).toQuadraticForm' := by
      rw [signature_weightedSumSquares, diagonalSignature,
        Fin.sum_univ_one]

end OptimalConvergenceRates.KrivineStengle

end
