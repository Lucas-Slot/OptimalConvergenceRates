/-
  OptimalConvergenceRates/KrivineStengle/CompanionMatrix.lean

  Companion matrices with guarded rational coefficients, together with
  specialization correctness on an actual-degree branch.
-/
import OptimalConvergenceRates.KrivineStengle.GuardedMatrix
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Trace.Basic

noncomputable section

open Matrix MvPolynomial Polynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- The companion matrix of a monic polynomial whose degree is known to be
`d`. Columns record multiplication by `X` in the power basis. -/
def companionMatrixOfDegree {F : Type*} [Field F] (p : F[X]) (d : ℕ) :
    Matrix (Fin d) (Fin d) F :=
  fun i j ↦
    if _hj : (j : ℕ) + 1 < d then
      if (i : ℕ) = (j : ℕ) + 1 then 1 else 0
    else
      -p.coeff i

/-- The symbolic companion matrix on the branch where the parameterized
polynomial has actual degree `d`. -/
def guardedCompanionMatrix {n : ℕ}
    (f : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ) :
    Matrix (Fin d) (Fin d) (GuardedRational n) :=
  fun i j ↦
    if _hj : (j : ℕ) + 1 < d then
      if (i : ℕ) = (j : ℕ) + 1 then GuardedRational.one
      else GuardedRational.zero
    else
      (monicNormalizedCoefficient f d i).neg

/-- Every entry of the guarded companion matrix is valid on its selected
actual-degree branch. -/
theorem guardedCompanionMatrix_valid {n : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (f : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ)
    (hdegree : ActualDegreeCondition coeff x f d) :
    GuardedMatrixValid coeff x (guardedCompanionMatrix f d) := by
  intro i j
  by_cases hj : (j : ℕ) + 1 < d
  · by_cases hi : (i : ℕ) = (j : ℕ) + 1
    · simp [guardedCompanionMatrix, hj, hi, GuardedRational.one]
    · simp [guardedCompanionMatrix, hj, hi, GuardedRational.zero]
  · simp only [guardedCompanionMatrix, hj]
    exact (monicNormalizedCoefficient_valid coeff x f d i hdegree).neg coeff x

private theorem coeff_monicNormalizeSpecialization {n : ℕ} {F : Type*}
    [Field F] (coeff : ℝ →+* F) (x : Fin n → F)
    (f : (MvPolynomial (Fin n) ℝ)[X]) (d j : ℕ) :
    (monicNormalizeSpecialization coeff x f d).coeff j =
      (specializePolynomial coeff x f).coeff j /
        (specializePolynomial coeff x f).coeff d := by
  simp [monicNormalizeSpecialization, Polynomial.coeff_mul_C, div_eq_mul_inv]

/-- Evaluating the guarded companion matrix gives the ordinary companion
matrix of the monic normalization of the specialized polynomial. -/
theorem eval_guardedCompanionMatrix {n : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (f : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ) :
    evalGuardedMatrix coeff x (guardedCompanionMatrix f d) =
      companionMatrixOfDegree
        (monicNormalizeSpecialization coeff x f d) d := by
  ext i j
  by_cases hj : (j : ℕ) + 1 < d
  · by_cases hi : (i : ℕ) = (j : ℕ) + 1 <;>
      simp [evalGuardedMatrix, guardedCompanionMatrix,
        companionMatrixOfDegree, hj, hi, GuardedRational.one,
        GuardedRational.zero]
  · simp [evalGuardedMatrix, guardedCompanionMatrix,
      companionMatrixOfDegree, hj, GuardedRational.eval_neg,
      eval_monicNormalizedCoefficient,
      coeff_monicNormalizeSpecialization]

private theorem modByMonic_X_pow_natDegree {F : Type*} [Field F]
    (p : F[X]) (hp : p.Monic) :
    Polynomial.X ^ p.natDegree %ₘ p = -p.eraseLead := by
  calc
    Polynomial.X ^ p.natDegree %ₘ p = (-p.eraseLead) %ₘ p := by
      apply Polynomial.modByMonic_eq_of_dvd_sub hp
      refine ⟨1, ?_⟩
      rw [mul_one]
      calc
        Polynomial.X ^ p.natDegree - -p.eraseLead =
            p.eraseLead + Polynomial.X ^ p.natDegree := by ring
        _ = p := by
          simpa [hp.leadingCoeff] using
            Polynomial.eraseLead_add_C_mul_X_pow p
    _ = -p.eraseLead :=
      (Polynomial.modByMonic_eq_self_iff hp).2 (by
        simpa [Polynomial.degree_neg] using
          Polynomial.degree_eraseLead_lt hp.ne_zero)

/-- The ordinary companion matrix is the matrix of multiplication by the
quotient root in its power basis. -/
theorem companionMatrixOfDegree_eq_leftMulMatrix_root
    {F : Type*} [Field F] (p : F[X]) (hp : p.Monic) :
    companionMatrixOfDegree p p.natDegree =
      Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hp).basis
        (AdjoinRoot.root p) := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  rw [(AdjoinRoot.powerBasis' hp).basis_eq_pow j]
  change companionMatrixOfDegree p p.natDegree i j =
    ((AdjoinRoot.powerBasis' hp).basis.repr
      (AdjoinRoot.root p * AdjoinRoot.root p ^ (j : ℕ))) i
  rw [← pow_succ']
  by_cases hj : (j : ℕ) + 1 < p.natDegree
  · rw [companionMatrixOfDegree, dif_pos hj]
    change (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) =
      (AdjoinRoot.modByMonicHom hp
        (AdjoinRoot.root p ^ ((j : ℕ) + 1))).coeff i
    rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.modByMonicHom_mk]
    rw [(Polynomial.modByMonic_eq_self_iff hp).2]
    · simp [Polynomial.coeff_X_pow]
    · rw [Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hp.ne_zero]
      exact_mod_cast hj
  · have hlast : (j : ℕ) + 1 = p.natDegree := by
      exact Nat.le_antisymm (Nat.succ_le_of_lt j.isLt)
        (Nat.le_of_not_gt hj)
    rw [companionMatrixOfDegree, dif_neg hj]
    change -p.coeff i = (AdjoinRoot.modByMonicHom hp
      (AdjoinRoot.root p ^ ((j : ℕ) + 1))).coeff i
    rw [hlast]
    rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.modByMonicHom_mk]
    rw [modByMonic_X_pow_natDegree p hp, Polynomial.coeff_neg,
      Polynomial.eraseLead_coeff_of_ne]
    exact ne_of_lt i.isLt

end OptimalConvergenceRates.KrivineStengle

end
