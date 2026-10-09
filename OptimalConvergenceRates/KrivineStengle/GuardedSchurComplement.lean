/-
  OptimalConvergenceRates/KrivineStengle/GuardedSchurComplement.lean

  Guarded rational Schur complements and their specialization theorem.
-/
import OptimalConvergenceRates.KrivineStengle.GuardedHermiteMatrix
import OptimalConvergenceRates.KrivineStengle.MatrixSchurSignature

noncomputable section

open Matrix MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

namespace GuardedRational
theorem mul_comm {n : ℕ} (r s : GuardedRational n) : r.mul s = s.mul r := by
  cases r
  cases s
  simp only [mul]
  congr 1 <;> exact _root_.mul_comm _ _


theorem Valid.num_ne_zero_of_eval_ne {n : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F) {r : GuardedRational n}
    (hr : r.Valid coeff x) (heval : r.eval coeff x ≠ 0) :
    eval₂Hom coeff x r.num ≠ 0 := by
  intro hnum
  apply heval
  simp [eval, hnum]

end GuardedRational

/-- Delete the zeroth guarded row and column. -/
def guardedMatrixTail {n k : ℕ}
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) (GuardedRational n)) :
    Matrix (Fin k) (Fin k) (GuardedRational n) :=
  fun i j ↦ M i.succ j.succ

/-- Symbolic Schur complement, valid on the branch where the zeroth pivot
is nonzero. -/
def guardedMatrixSchurComplement {n k : ℕ}
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) (GuardedRational n)) :
    Matrix (Fin k) (Fin k) (GuardedRational n) :=
  fun i j ↦ (M i.succ j.succ).sub
    (((M i.succ 0).mul (M 0 j.succ)).mul (M 0 0).inv)
theorem guardedMatrixSchurComplement_isSymm {n k : ℕ}
    {M : Matrix (Fin (k + 1)) (Fin (k + 1)) (GuardedRational n)}
    (hM : M.IsSymm) : (guardedMatrixSchurComplement M).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [guardedMatrixSchurComplement]
  rw [hM.apply i.succ j.succ, hM.apply 0 j.succ,
    hM.apply i.succ 0]
  rw [GuardedRational.mul_comm (M 0 j.succ) (M i.succ 0)]


theorem guardedMatrixTail_valid {n k : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    {M : Matrix (Fin (k + 1)) (Fin (k + 1)) (GuardedRational n)}
    (hM : GuardedMatrixValid coeff x M) :
    GuardedMatrixValid coeff x (guardedMatrixTail M) := by
  intro i j
  exact hM i.succ j.succ

theorem guardedMatrixSchurComplement_valid {n k : ℕ} {F : Type*}
    [Field F] (coeff : ℝ →+* F) (x : Fin n → F)
    {M : Matrix (Fin (k + 1)) (Fin (k + 1)) (GuardedRational n)}
    (hM : GuardedMatrixValid coeff x M)
    (hpivot : (M 0 0).eval coeff x ≠ 0) :
    GuardedMatrixValid coeff x (guardedMatrixSchurComplement M) := by
  have hpinv : (M 0 0).inv.Valid coeff x :=
    GuardedRational.Valid.inv coeff x
      ((hM 0 0).num_ne_zero_of_eval_ne coeff x hpivot)
  intro i j
  exact (hM i.succ j.succ).sub coeff x
    (((hM i.succ 0).mul coeff x (hM 0 j.succ)).mul coeff x hpinv)

@[simp] theorem eval_guardedMatrixTail {n k : ℕ} {F : Type*}
    [Field F] (coeff : ℝ →+* F) (x : Fin n → F)
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) (GuardedRational n)) :
    evalGuardedMatrix coeff x (guardedMatrixTail M) =
      matrixTail (evalGuardedMatrix coeff x M) := by
  rfl

theorem eval_guardedMatrixSchurComplement {n k : ℕ} {F : Type*}
    [Field F] (coeff : ℝ →+* F) (x : Fin n → F)
    {M : Matrix (Fin (k + 1)) (Fin (k + 1)) (GuardedRational n)}
    (hM : GuardedMatrixValid coeff x M)
    (hpivot : (M 0 0).eval coeff x ≠ 0) :
    evalGuardedMatrix coeff x (guardedMatrixSchurComplement M) =
      matrixSchurComplement (evalGuardedMatrix coeff x M) := by
  have hnum : eval₂Hom coeff x (M 0 0).num ≠ 0 :=
    (hM 0 0).num_ne_zero_of_eval_ne coeff x hpivot
  have hpinv : (M 0 0).inv.Valid coeff x :=
    GuardedRational.Valid.inv coeff x hnum
  ext i j
  change ((M i.succ j.succ).sub
      (((M i.succ 0).mul (M 0 j.succ)).mul (M 0 0).inv)).eval coeff x =
    (M i.succ j.succ).eval coeff x -
      (M i.succ 0).eval coeff x * (M 0 j.succ).eval coeff x /
        (M 0 0).eval coeff x
  rw [GuardedRational.eval_sub coeff x (hM i.succ j.succ)
    (((hM i.succ 0).mul coeff x (hM 0 j.succ)).mul coeff x hpinv)]
  rw [GuardedRational.eval_mul coeff x
    ((hM i.succ 0).mul coeff x (hM 0 j.succ)) hpinv]
  rw [GuardedRational.eval_mul coeff x (hM i.succ 0) (hM 0 j.succ)]
  rw [GuardedRational.eval_inv coeff x (hM 0 0) hnum]
  ring

theorem eval_guardedMatrix_isSymm {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    {M : Matrix (Fin d) (Fin d) (GuardedRational n)} (hM : M.IsSymm) :
    (evalGuardedMatrix coeff x M).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  change (M j i).eval coeff x = (M i j).eval coeff x
  rw [hM.apply i j]

/-- Specialization of the Schur signature identity for guarded matrices. -/
theorem matrixSignature_eval_eq_orderedSign_add_guardedSchur
    {n k : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    {M : Matrix (Fin (k + 1)) (Fin (k + 1)) (GuardedRational n)}
    (hvalid : GuardedMatrixValid coeff x M) (hM : M.IsSymm)
    (hpivot : (M 0 0).eval coeff x ≠ 0) :
    matrixSignature (evalGuardedMatrix coeff x M) =
      orderedSign ((M 0 0).eval coeff x) +
        matrixSignature
          (evalGuardedMatrix coeff x (guardedMatrixSchurComplement M)) := by
  rw [eval_guardedMatrixSchurComplement coeff x hvalid hpivot]
  exact matrixSignature_eq_orderedSign_add_schur _
    (eval_guardedMatrix_isSymm coeff x hM) hpivot

end OptimalConvergenceRates.KrivineStengle

end
