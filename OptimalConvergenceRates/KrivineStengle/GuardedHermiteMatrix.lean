/-
  OptimalConvergenceRates/KrivineStengle/GuardedHermiteMatrix.lean

  Specialization-safe symbolic Hermite matrices.
-/
import OptimalConvergenceRates.KrivineStengle.CompanionMatrix
import OptimalConvergenceRates.KrivineStengle.HermiteTrace
import Mathlib.Algebra.Polynomial.Eval.Degree

noncomputable section

open Matrix MvPolynomial Polynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- Multiply a guarded matrix by a guarded scalar. -/
def guardedMatrixScale {n d : ℕ} (r : GuardedRational n)
    (A : Matrix (Fin d) (Fin d) (GuardedRational n)) :
    Matrix (Fin d) (Fin d) (GuardedRational n) :=
  fun i j ↦ r.mul (A i j)

theorem GuardedMatrixValid.scale {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F) {r : GuardedRational n}
    {A : Matrix (Fin d) (Fin d) (GuardedRational n)}
    (hr : r.Valid coeff x) (hA : GuardedMatrixValid coeff x A) :
    GuardedMatrixValid coeff x (guardedMatrixScale r A) := by
  intro i j
  exact hr.mul coeff x (hA i j)

theorem eval_guardedMatrixScale {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F) {r : GuardedRational n}
    {A : Matrix (Fin d) (Fin d) (GuardedRational n)}
    (hr : r.Valid coeff x) (hA : GuardedMatrixValid coeff x A) :
    evalGuardedMatrix coeff x (guardedMatrixScale r A) =
      r.eval coeff x • evalGuardedMatrix coeff x A := by
  ext i j
  exact GuardedRational.eval_mul coeff x hr (hA i j)

/-- Guarded trace of a square matrix. -/
def guardedMatrixTrace {n d : ℕ}
    (A : Matrix (Fin d) (Fin d) (GuardedRational n)) : GuardedRational n :=
  GuardedRational.listSum (List.ofFn fun i : Fin d ↦ A i i)

theorem guardedMatrixTrace_valid {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    {A : Matrix (Fin d) (Fin d) (GuardedRational n)}
    (hA : GuardedMatrixValid coeff x A) :
    (guardedMatrixTrace A).Valid coeff x := by
  apply GuardedRational.Valid.listSum coeff x
  intro r hr
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  exact hA i i

theorem eval_guardedMatrixTrace {n d : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    {A : Matrix (Fin d) (Fin d) (GuardedRational n)}
    (hA : GuardedMatrixValid coeff x A) :
    (guardedMatrixTrace A).eval coeff x =
      Matrix.trace (evalGuardedMatrix coeff x A) := by
  rw [guardedMatrixTrace, GuardedRational.eval_listSum coeff x]
  · simp [Matrix.trace, Matrix.diag, evalGuardedMatrix,
      List.map_ofFn, List.sum_ofFn]
  · intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact hA i i

/-- Evaluate a parameterized univariate polynomial at a guarded matrix.
The fixed range is chosen before specialization, so vanishing specialized
leading coefficients cause no problem. -/
def guardedPolynomialMatrixEval {n d : ℕ}
    (h : (MvPolynomial (Fin n) ℝ)[X])
    (A : Matrix (Fin d) (Fin d) (GuardedRational n)) :
    Matrix (Fin d) (Fin d) (GuardedRational n) :=
  fun i j ↦ GuardedRational.listSum
    (List.ofFn fun k : Fin (h.natDegree + 1) ↦
      (GuardedRational.ofPolynomial (h.coeff k)).mul
        ((guardedMatrixPow A k) i j))

theorem guardedPolynomialMatrixEval_valid {n d : ℕ} {F : Type*}
    [Field F] (coeff : ℝ →+* F) (x : Fin n → F)
    (h : (MvPolynomial (Fin n) ℝ)[X])
    {A : Matrix (Fin d) (Fin d) (GuardedRational n)}
    (hA : GuardedMatrixValid coeff x A) :
    GuardedMatrixValid coeff x (guardedPolynomialMatrixEval h A) := by
  intro i j
  apply GuardedRational.Valid.listSum coeff x
  intro r hr
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
  exact (GuardedRational.valid_ofPolynomial coeff x (h.coeff k)).mul
    coeff x (GuardedMatrixValid.pow coeff x hA k i j)

theorem eval_guardedPolynomialMatrixEval {n d : ℕ} {F : Type*}
    [Field F] (coeff : ℝ →+* F) (x : Fin n → F)
    (h : (MvPolynomial (Fin n) ℝ)[X])
    {A : Matrix (Fin d) (Fin d) (GuardedRational n)}
    (hA : GuardedMatrixValid coeff x A) :
    evalGuardedMatrix coeff x (guardedPolynomialMatrixEval h A) =
      aeval (evalGuardedMatrix coeff x A)
        (specializePolynomial coeff x h) := by
  ext i j
  change (GuardedRational.listSum
    (List.ofFn fun k : Fin (h.natDegree + 1) ↦
      (GuardedRational.ofPolynomial (h.coeff k)).mul
        ((guardedMatrixPow A k) i j))).eval coeff x = _
  rw [GuardedRational.eval_listSum coeff x]
  · simp only [List.map_ofFn, List.sum_ofFn]
    rw [Polynomial.aeval_eq_sum_range' (x := evalGuardedMatrix coeff x A)]
    · rw [← Fin.sum_univ_eq_sum_range]
      rw [Finset.sum_apply, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro k _
      simp only [Function.comp_apply]
      rw [GuardedRational.eval_mul coeff x
        (GuardedRational.valid_ofPolynomial coeff x (h.coeff k))
        (GuardedMatrixValid.pow coeff x hA k i j)]
      rw [GuardedRational.eval_ofPolynomial]
      change eval₂Hom coeff x (h.coeff k) *
        evalGuardedMatrix coeff x (guardedMatrixPow A k) i j = _
      rw [evalGuardedMatrix_pow coeff x hA]
      simp [specializePolynomial, Polynomial.coeff_map]
    · exact (Polynomial.natDegree_map_le.trans_lt (Nat.lt_succ_self _))
  · intro r hr
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
    exact (GuardedRational.valid_ofPolynomial coeff x (h.coeff k)).mul
      coeff x (GuardedMatrixValid.pow coeff x hA k i j)

/-- Hermite matrix computed from a companion matrix. -/
def companionHermiteMatrix {F : Type*} [Field F]
    (p h : F[X]) (d : ℕ) : Matrix (Fin d) (Fin d) F :=
  let C := companionMatrixOfDegree p d
  fun i j ↦ Matrix.trace (aeval C h * C ^ ((i : ℕ) + (j : ℕ)))

/-- Guarded symbolic Hermite matrix on the actual-degree branch `d`. -/
def guardedHermiteMatrix {n : ℕ}
    (f h : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ) :
    Matrix (Fin d) (Fin d) (GuardedRational n) :=
  let C := guardedCompanionMatrix f d
  fun i j ↦ guardedMatrixTrace
    (guardedMatrixMul (guardedPolynomialMatrixEval h C)
      (guardedMatrixPow C ((i : ℕ) + (j : ℕ))))

theorem guardedHermiteMatrix_valid {n : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (f h : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ)
    (hdegree : ActualDegreeCondition coeff x f d) :
    GuardedMatrixValid coeff x (guardedHermiteMatrix f h d) := by
  let C := guardedCompanionMatrix f d
  have hC : GuardedMatrixValid coeff x C :=
    guardedCompanionMatrix_valid coeff x f d hdegree
  intro i j
  exact guardedMatrixTrace_valid coeff x
    ((guardedPolynomialMatrixEval_valid coeff x h hC).mul coeff x
      (GuardedMatrixValid.pow coeff x hC ((i : ℕ) + (j : ℕ))))

theorem eval_guardedHermiteMatrix {n : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (f h : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ)
    (hdegree : ActualDegreeCondition coeff x f d) :
    evalGuardedMatrix coeff x (guardedHermiteMatrix f h d) =
      companionHermiteMatrix
        (monicNormalizeSpecialization coeff x f d)
        (specializePolynomial coeff x h) d := by
  let C := guardedCompanionMatrix f d
  have hC : GuardedMatrixValid coeff x C :=
    guardedCompanionMatrix_valid coeff x f d hdegree
  ext i j
  rw [guardedHermiteMatrix, evalGuardedMatrix]
  rw [eval_guardedMatrixTrace coeff x
    ((guardedPolynomialMatrixEval_valid coeff x h hC).mul coeff x
      (GuardedMatrixValid.pow coeff x hC ((i : ℕ) + (j : ℕ))))]
  rw [evalGuardedMatrix_mul coeff x
    (guardedPolynomialMatrixEval_valid coeff x h hC)
    (GuardedMatrixValid.pow coeff x hC ((i : ℕ) + (j : ℕ)))]
  rw [eval_guardedPolynomialMatrixEval coeff x h hC,
    evalGuardedMatrix_pow coeff x hC,
    eval_guardedCompanionMatrix]
  rfl

/-- The companion construction recovers the existing intrinsic Hermite
trace matrix. -/
theorem companionHermiteMatrix_eq_hermiteTraceMatrix
    {F : Type*} [Field F] (p h : F[X]) (hp : p.Monic) :
    companionHermiteMatrix p h p.natDegree =
      hermiteTraceMatrix p h hp := by
  let b := (AdjoinRoot.powerBasis' hp).basis
  ext i j
  rw [companionHermiteMatrix, hermiteTraceMatrix]
  rw [companionMatrixOfDegree_eq_leftMulMatrix_root p hp]
  rw [Algebra.trace_eq_matrix_trace b]
  change Matrix.trace
      (aeval (Algebra.leftMulMatrix b (AdjoinRoot.root p)) h *
        Algebra.leftMulMatrix b (AdjoinRoot.root p) ^
          ((i : ℕ) + (j : ℕ))) = _
  rw [Polynomial.aeval_algHom_apply]
  rw [← map_pow, ← map_mul]

theorem companionHermiteMatrix_reindex_hermiteTraceMatrix
    {F : Type*} [Field F] (p h : F[X]) (d : ℕ)
    (hp : p.Monic) (hdegree : p.natDegree = d) :
    companionHermiteMatrix p h d =
      Matrix.reindex (finCongr hdegree) (finCongr hdegree)
        (hermiteTraceMatrix p h hp) := by
  subst d
  simpa using companionHermiteMatrix_eq_hermiteTraceMatrix p h hp

/-- Main specialization theorem: every guarded Hermite matrix evaluates,
on its degree branch, to a reindexing of the repository's Hermite matrix. -/
theorem eval_guardedHermiteMatrix_eq_reindex_hermiteTraceMatrix
    {n : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (f h : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ)
    (hdegree : ActualDegreeCondition coeff x f d) :
    evalGuardedMatrix coeff x (guardedHermiteMatrix f h d) =
      Matrix.reindex
        (finCongr (natDegree_monicNormalizeSpecialization coeff x f d hdegree))
        (finCongr (natDegree_monicNormalizeSpecialization coeff x f d hdegree))
        (hermiteTraceMatrix (monicNormalizeSpecialization coeff x f d)
          (specializePolynomial coeff x h)
          (monic_monicNormalizeSpecialization coeff x f d hdegree)) := by
  rw [eval_guardedHermiteMatrix coeff x f h d hdegree]
  exact companionHermiteMatrix_reindex_hermiteTraceMatrix _ _ _
    (monic_monicNormalizeSpecialization coeff x f d hdegree)
    (natDegree_monicNormalizeSpecialization coeff x f d hdegree)

end OptimalConvergenceRates.KrivineStengle

end
