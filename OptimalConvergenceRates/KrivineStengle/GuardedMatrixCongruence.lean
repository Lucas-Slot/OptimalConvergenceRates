/-
  OptimalConvergenceRates/KrivineStengle/GuardedMatrixCongruence.lean

  Specialization-safe constant congruences of guarded rational matrices.
-/
import OptimalConvergenceRates.KrivineStengle.GuardedSchurComplement
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

noncomputable section

open Matrix MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

def guardedMatrixTranspose {n d : ℕ}
    (M : Matrix (Fin d) (Fin d) (GuardedRational n)) :
    Matrix (Fin d) (Fin d) (GuardedRational n) := Mᵀ

def guardedConstantMatrix {n d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) (GuardedRational n) :=
  fun i j ↦ GuardedRational.ofPolynomial (C (A i j))

def guardedMatrixCongruence {n d : ℕ}
    (P M : Matrix (Fin d) (Fin d) (GuardedRational n)) :
    Matrix (Fin d) (Fin d) (GuardedRational n) :=
  guardedMatrixMul (guardedMatrixTranspose P) (guardedMatrixMul M P)

theorem guardedMatrixTranspose_valid {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    {M : Matrix (Fin d) (Fin d) (GuardedRational n)}
    (hM : GuardedMatrixValid coeff x M) :
    GuardedMatrixValid coeff x (guardedMatrixTranspose M) := by
  intro i j
  exact hM j i

@[simp] theorem eval_guardedMatrixTranspose {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (M : Matrix (Fin d) (Fin d) (GuardedRational n)) :
    evalGuardedMatrix coeff x (guardedMatrixTranspose M) =
      (evalGuardedMatrix coeff x M)ᵀ := by
  rfl

theorem guardedConstantMatrix_valid {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F) (A : Matrix (Fin d) (Fin d) ℝ) :
    GuardedMatrixValid coeff x (guardedConstantMatrix (n := n) A) := by
  intro i j
  exact GuardedRational.valid_ofPolynomial coeff x _

@[simp] theorem eval_guardedConstantMatrix {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F) (A : Matrix (Fin d) (Fin d) ℝ) :
    evalGuardedMatrix coeff x (guardedConstantMatrix (n := n) A) = A.map coeff := by
  ext i j
  simp [evalGuardedMatrix, guardedConstantMatrix]

theorem guardedMatrixCongruence_valid {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    {P M : Matrix (Fin d) (Fin d) (GuardedRational n)}
    (hP : GuardedMatrixValid coeff x P) (hM : GuardedMatrixValid coeff x M) :
    GuardedMatrixValid coeff x (guardedMatrixCongruence P M) :=
  (guardedMatrixTranspose_valid coeff x hP).mul coeff x (hM.mul coeff x hP)

theorem eval_guardedMatrixCongruence {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    {P M : Matrix (Fin d) (Fin d) (GuardedRational n)}
    (hP : GuardedMatrixValid coeff x P) (hM : GuardedMatrixValid coeff x M) :
    evalGuardedMatrix coeff x (guardedMatrixCongruence P M) =
      (evalGuardedMatrix coeff x P)ᵀ * evalGuardedMatrix coeff x M *
        evalGuardedMatrix coeff x P := by
  rw [guardedMatrixCongruence,
    evalGuardedMatrix_mul coeff x (guardedMatrixTranspose_valid coeff x hP)
      (hM.mul coeff x hP),
    evalGuardedMatrix_mul coeff x hM hP,
    eval_guardedMatrixTranspose]
  rw [Matrix.mul_assoc]

/-- Replace the lower triangle by the transpose of the upper triangle. This
keeps a raw guarded matrix definitionally symmetric while preserving its
specialization whenever that specialization was already symmetric. -/
def symmetrizeGuardedMatrix {n d : ℕ}
    (M : Matrix (Fin d) (Fin d) (GuardedRational n)) :
    Matrix (Fin d) (Fin d) (GuardedRational n) :=
  fun i j ↦ if i ≤ j then M i j else M j i

theorem symmetrizeGuardedMatrix_isSymm {n d : ℕ}
    (M : Matrix (Fin d) (Fin d) (GuardedRational n)) :
    (symmetrizeGuardedMatrix M).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  by_cases hij : i ≤ j
  · by_cases hji : j ≤ i
    · have h : i = j := le_antisymm hij hji
      subst j
      simp [symmetrizeGuardedMatrix]
    · simp [symmetrizeGuardedMatrix, hij, hji]
  · have hji : j ≤ i := le_of_not_ge hij
    simp [symmetrizeGuardedMatrix, hij, hji]

theorem symmetrizeGuardedMatrix_valid {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    {M : Matrix (Fin d) (Fin d) (GuardedRational n)}
    (hM : GuardedMatrixValid coeff x M) :
    GuardedMatrixValid coeff x (symmetrizeGuardedMatrix M) := by
  intro i j
  by_cases hij : i ≤ j
  · simpa [symmetrizeGuardedMatrix, hij] using hM i j
  · simpa [symmetrizeGuardedMatrix, hij] using hM j i

theorem eval_symmetrizeGuardedMatrix {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (M : Matrix (Fin d) (Fin d) (GuardedRational n))
    (hM : (evalGuardedMatrix coeff x M).IsSymm) :
    evalGuardedMatrix coeff x (symmetrizeGuardedMatrix M) =
      evalGuardedMatrix coeff x M := by
  ext i j
  by_cases hij : i ≤ j
  · simp [evalGuardedMatrix, symmetrizeGuardedMatrix, hij]
  · simp only [evalGuardedMatrix, symmetrizeGuardedMatrix, ite_eq_right hij]
    exact hM.apply i j

theorem matrixCongruence_isSymm {d : ℕ} {F : Type*} [CommRing F]
    (P : Matrix (Fin d) (Fin d) F)
    {M : Matrix (Fin d) (Fin d) F} (hM : M.IsSymm) :
    (Pᵀ * M * P).IsSymm := by
  rw [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, hM.eq, Matrix.mul_assoc]

def guardedTransvection {n d : ℕ} (i j : Fin d) :
    Matrix (Fin d) (Fin d) (GuardedRational n) :=
  guardedConstantMatrix (Matrix.transvection i j (1 : ℝ))

theorem guardedTransvection_valid {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F) (i j : Fin d) :
    GuardedMatrixValid coeff x (guardedTransvection (n := n) i j) :=
  guardedConstantMatrix_valid coeff x _

@[simp] theorem eval_guardedTransvection {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F) (i j : Fin d) :
    evalGuardedMatrix coeff x (guardedTransvection (n := n) i j) =
      Matrix.transvection i j (1 : F) := by
  rw [guardedTransvection, eval_guardedConstantMatrix]
  ext a b
  simp [Matrix.transvection, Matrix.single, Matrix.one_apply]

/-- A guarded transvection congruence, normalized to a raw symmetric matrix. -/
def guardedTransvectionCongruence {n d : ℕ} (i j : Fin d)
    (M : Matrix (Fin d) (Fin d) (GuardedRational n)) :
    Matrix (Fin d) (Fin d) (GuardedRational n) :=
  symmetrizeGuardedMatrix
    (guardedMatrixCongruence (guardedTransvection (n := n) i j) M)

theorem guardedTransvectionCongruence_isSymm {n d : ℕ} (i j : Fin d)
    (M : Matrix (Fin d) (Fin d) (GuardedRational n)) :
    (guardedTransvectionCongruence i j M).IsSymm :=
  symmetrizeGuardedMatrix_isSymm _

theorem guardedTransvectionCongruence_valid {n d : ℕ}
    {F : Type*} [Field F] (coeff : ℝ →+* F) (x : Fin n → F)
    (i j : Fin d) {M : Matrix (Fin d) (Fin d) (GuardedRational n)}
    (hM : GuardedMatrixValid coeff x M) :
    GuardedMatrixValid coeff x (guardedTransvectionCongruence i j M) := by
  apply symmetrizeGuardedMatrix_valid coeff x
  exact guardedMatrixCongruence_valid coeff x
    (guardedTransvection_valid coeff x i j) hM

theorem eval_guardedTransvectionCongruence {n d : ℕ}
    {F : Type*} [Field F] (coeff : ℝ →+* F) (x : Fin n → F)
    (i j : Fin d) {M : Matrix (Fin d) (Fin d) (GuardedRational n)}
    (hM : GuardedMatrixValid coeff x M)
    (hsymm : (evalGuardedMatrix coeff x M).IsSymm) :
    evalGuardedMatrix coeff x (guardedTransvectionCongruence i j M) =
      (Matrix.transvection i j (1 : F))ᵀ *
        evalGuardedMatrix coeff x M * Matrix.transvection i j (1 : F) := by
  rw [guardedTransvectionCongruence,
    eval_symmetrizeGuardedMatrix]
  · rw [eval_guardedMatrixCongruence coeff x
      (guardedTransvection_valid coeff x i j) hM,
      eval_guardedTransvection]
  · rw [eval_guardedMatrixCongruence coeff x
      (guardedTransvection_valid coeff x i j) hM,
      eval_guardedTransvection]
    exact matrixCongruence_isSymm _ hsymm

theorem matrixSignature_transvection_congruence {d : ℕ}
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (M : Matrix (Fin d) (Fin d) F) (i j : Fin d) (hij : i ≠ j) :
    matrixSignature ((Matrix.transvection i j (1 : F))ᵀ * M *
      Matrix.transvection i j (1 : F)) = matrixSignature M := by
  let P := Matrix.transvection i j (1 : F)
  have hdet : IsUnit P.det := by
    dsimp [P]
    rw [Matrix.det_transvection_of_ne i j hij]
    exact isUnit_one
  letI : Invertible P := Matrix.invertibleOfIsUnitDet P hdet
  rw [matrixSignature, matrixSignature]
  apply signature_congr (P.toLinearEquiv' inferInstance)
  intro v
  have he : (P.toLinearEquiv' inferInstance) v = P *ᵥ v := by
    change (Matrix.toLin' P) v = P *ᵥ v
    rfl
  rw [he]
  simp only [Matrix.toQuadraticForm', Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']
  change (P *ᵥ v) ⬝ᵥ (M *ᵥ (P *ᵥ v)) =
    v ⬝ᵥ ((Pᵀ * M * P) *ᵥ v)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec v Pᵀ (M *ᵥ (P *ᵥ v)), Matrix.vecMul_transpose]

end OptimalConvergenceRates.KrivineStengle

end
