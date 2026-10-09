/-
  OptimalConvergenceRates/KrivineStengle/GuardedMatrix.lean

  Fixed-size matrix arithmetic with guarded rational entries.
-/
import OptimalConvergenceRates.KrivineStengle.GuardedRationalOperations
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic

noncomputable section

open Matrix

namespace OptimalConvergenceRates.KrivineStengle

/-- Entrywise validity for a matrix of guarded rational expressions. -/
def GuardedMatrixValid {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (M : Matrix (Fin d) (Fin d) (GuardedRational n)) : Prop :=
  ∀ i j, (M i j).Valid coeff x

/-- Evaluate every guarded entry of a matrix. -/
def evalGuardedMatrix {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (M : Matrix (Fin d) (Fin d) (GuardedRational n)) :
    Matrix (Fin d) (Fin d) F :=
  fun i j ↦ (M i j).eval coeff x

def guardedMatrixZero {n d : ℕ} :
    Matrix (Fin d) (Fin d) (GuardedRational n) :=
  fun _ _ ↦ GuardedRational.zero

def guardedMatrixOne {n d : ℕ} :
    Matrix (Fin d) (Fin d) (GuardedRational n) :=
  fun i j ↦ if i = j then GuardedRational.one else GuardedRational.zero

def guardedMatrixAdd {n d : ℕ}
    (A B : Matrix (Fin d) (Fin d) (GuardedRational n)) :
    Matrix (Fin d) (Fin d) (GuardedRational n) :=
  fun i j ↦ (A i j).add (B i j)

def guardedMatrixMul {n d : ℕ}
    (A B : Matrix (Fin d) (Fin d) (GuardedRational n)) :
    Matrix (Fin d) (Fin d) (GuardedRational n) :=
  fun i j ↦ GuardedRational.listSum
    (List.ofFn fun k : Fin d ↦ (A i k).mul (B k j))

def guardedMatrixPow {n d : ℕ}
    (A : Matrix (Fin d) (Fin d) (GuardedRational n)) :
    ℕ → Matrix (Fin d) (Fin d) (GuardedRational n)
  | 0 => guardedMatrixOne
  | k + 1 => guardedMatrixMul (guardedMatrixPow A k) A

theorem guardedMatrixValid_zero {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F) :
    GuardedMatrixValid coeff x (guardedMatrixZero (n := n) (d := d)) := by
  intro i j
  exact GuardedRational.valid_ofPolynomial coeff x 0

theorem guardedMatrixValid_one {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F) :
    GuardedMatrixValid coeff x (guardedMatrixOne (n := n) (d := d)) := by
  intro i j
  by_cases hij : i = j
  · simp [guardedMatrixOne, hij, GuardedRational.one,
      GuardedRational.valid_ofPolynomial]
  · simp [guardedMatrixOne, hij, GuardedRational.zero,
      GuardedRational.valid_ofPolynomial]

theorem GuardedMatrixValid.add {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    {A B : Matrix (Fin d) (Fin d) (GuardedRational n)}
    (hA : GuardedMatrixValid coeff x A)
    (hB : GuardedMatrixValid coeff x B) :
    GuardedMatrixValid coeff x (guardedMatrixAdd A B) := by
  intro i j
  exact (hA i j).add coeff x (hB i j)

theorem GuardedMatrixValid.mul {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    {A B : Matrix (Fin d) (Fin d) (GuardedRational n)}
    (hA : GuardedMatrixValid coeff x A)
    (hB : GuardedMatrixValid coeff x B) :
    GuardedMatrixValid coeff x (guardedMatrixMul A B) := by
  intro i j
  apply GuardedRational.Valid.listSum coeff x
  intro r hr
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
  exact (hA i k).mul coeff x (hB k j)

theorem GuardedMatrixValid.pow {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    {A : Matrix (Fin d) (Fin d) (GuardedRational n)}
    (hA : GuardedMatrixValid coeff x A) :
    ∀ k, GuardedMatrixValid coeff x (guardedMatrixPow A k)
  | 0 => guardedMatrixValid_one coeff x
  | k + 1 =>
      (GuardedMatrixValid.pow coeff x hA k).mul coeff x hA

@[simp] theorem evalGuardedMatrix_zero {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F) :
    evalGuardedMatrix coeff x (guardedMatrixZero (n := n) (d := d)) = 0 := by
  ext i j
  change GuardedRational.zero.eval coeff x = 0
  simp [GuardedRational.zero]

@[simp] theorem evalGuardedMatrix_one {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F) :
    evalGuardedMatrix coeff x (guardedMatrixOne (n := n) (d := d)) = 1 := by
  ext i j
  by_cases hij : i = j <;>
    simp [evalGuardedMatrix, guardedMatrixOne, hij, GuardedRational.one,
      GuardedRational.zero, Matrix.one_apply]

theorem evalGuardedMatrix_add {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    {A B : Matrix (Fin d) (Fin d) (GuardedRational n)}
    (hA : GuardedMatrixValid coeff x A)
    (hB : GuardedMatrixValid coeff x B) :
    evalGuardedMatrix coeff x (guardedMatrixAdd A B) =
      evalGuardedMatrix coeff x A + evalGuardedMatrix coeff x B := by
  ext i j
  exact GuardedRational.eval_add coeff x (hA i j) (hB i j)

theorem evalGuardedMatrix_mul {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    {A B : Matrix (Fin d) (Fin d) (GuardedRational n)}
    (hA : GuardedMatrixValid coeff x A)
    (hB : GuardedMatrixValid coeff x B) :
    evalGuardedMatrix coeff x (guardedMatrixMul A B) =
      evalGuardedMatrix coeff x A * evalGuardedMatrix coeff x B := by
  ext i j
  rw [Matrix.mul_apply]
  change (GuardedRational.listSum
      (List.ofFn fun k : Fin d ↦ (A i k).mul (B k j))).eval coeff x = _
  rw [GuardedRational.eval_listSum coeff x]
  · simp only [List.map_ofFn, List.sum_ofFn, evalGuardedMatrix]
    apply Finset.sum_congr rfl
    intro k _
    exact GuardedRational.eval_mul coeff x (hA i k) (hB k j)
  · intro r hr
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
    exact (hA i k).mul coeff x (hB k j)

theorem evalGuardedMatrix_pow {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    {A : Matrix (Fin d) (Fin d) (GuardedRational n)}
    (hA : GuardedMatrixValid coeff x A) :
    ∀ k, evalGuardedMatrix coeff x (guardedMatrixPow A k) =
      (evalGuardedMatrix coeff x A) ^ k
  | 0 => evalGuardedMatrix_one coeff x
  | k + 1 => by
      rw [guardedMatrixPow, evalGuardedMatrix_mul coeff x (GuardedMatrixValid.pow coeff x hA k) hA,
        evalGuardedMatrix_pow coeff x hA k, pow_succ]

end OptimalConvergenceRates.KrivineStengle

end
