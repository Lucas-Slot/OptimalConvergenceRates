import OptimalConvergenceRates.KrivineStengle.HermiteLinearPower
import OptimalConvergenceRates.KrivineStengle.RankOneSignature
import OptimalConvergenceRates.KrivineStengle.StrictRootCounting

noncomputable section

open Matrix Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F]

/-- After reindexing by its degree, the Hermite matrix of a repeated linear
factor is an explicit rank-one matrix. -/
theorem hermiteTraceMatrix_reindex_X_sub_C_pow (a : F) (h : F[X])
    (n : ℕ) :
    let hf := (monic_X_sub_C a).pow n
    let hdegree : ((X - C a) ^ n : F[X]).natDegree = n := by
      rw [natDegree_pow, natDegree_X_sub_C, mul_one]
    Matrix.reindex (finCongr hdegree) (finCongr hdegree)
        (hermiteTraceMatrix ((X - C a) ^ n) h hf) =
      fun i j : Fin n ↦ (n : F) * h.eval a * a ^ (i : ℕ) * a ^ (j : ℕ) := by
  dsimp only
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, hermiteTraceMatrix]
  simp only [finCongr_symm_apply_coe]
  rw [show aeval (AdjoinRoot.root ((X - C a) ^ n : F[X])) h *
      AdjoinRoot.root ((X - C a) ^ n : F[X]) ^
          ((i : ℕ) + (j : ℕ)) =
        aeval (AdjoinRoot.root ((X - C a) ^ n : F[X]))
          (h * X ^ ((i : ℕ) + (j : ℕ))) by simp]
  rw [trace_aeval_adjoinRoot_X_sub_C_pow]
  simp [nsmul_eq_mul, pow_add]
  ring

variable [LinearOrder F] [IsStrictOrderedRing F]

/-- Repetition of a linear factor does not change its Hermite signature. -/
theorem hermiteSignature_X_sub_C_pow (a : F) (h : F[X])
    {n : ℕ} (hn : 0 < n) :
    hermiteSignature ((X - C a) ^ n) h ((monic_X_sub_C a).pow n) =
      orderedSign (h.eval a) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let hdegree : ((X - C a) ^ (k + 1) : F[X]).natDegree = k + 1 := by
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  rw [hermiteSignature]
  rw [← matrixSignature_reindex (finCongr hdegree)
    (hermiteTraceMatrix ((X - C a) ^ (k + 1)) h
      ((monic_X_sub_C a).pow (k + 1)))]
  rw [hermiteTraceMatrix_reindex_X_sub_C_pow]
  let c : F := ((k + 1 : ℕ) : F) * h.eval a
  let v : Fin (k + 1) → F := fun i ↦ a ^ (i : ℕ)
  have hv : v 0 = 1 := by simp [v]
  rw [show (fun i j : Fin (k + 1) ↦
      ((k + 1 : ℕ) : F) * h.eval a * a ^ (i : ℕ) * a ^ (j : ℕ)) =
        (fun i j ↦ c * v i * v j) by
    funext i j
    rfl]
  rw [matrixSignature_rankOne_succ c v hv]
  simp only [c, orderedSign_mul]
  rw [orderedSign_eq_one_iff.mpr (by positivity : (0 : F) < (k + 1 : ℕ))]
  simp

/-- The distinct-root sign sum of a positive power of a linear factor is the
sign of the weight at its unique root. -/
theorem rootSignSum_X_sub_C_pow (a : F) (h : F[X]) {n : ℕ} (hn : 0 < n) :
    rootSignSum ((X - C a) ^ n) h = orderedSign (h.eval a) := by
  rw [rootSignSum_pow _ _ (Nat.ne_of_gt hn), rootSignSum_X_sub_C]

/-- Hermite's root-sign identity for a positive power of a monic linear
polynomial. -/
theorem hermiteSignature_eq_rootSignSum_X_sub_C_pow (a : F) (h : F[X])
    {n : ℕ} (hn : 0 < n) :
    hermiteSignature ((X - C a) ^ n) h ((monic_X_sub_C a).pow n) =
      rootSignSum ((X - C a) ^ n) h := by
  rw [hermiteSignature_X_sub_C_pow a h hn, rootSignSum_X_sub_C_pow a h hn]

/-- Hermite's root-sign identity for a positive power of an arbitrary monic
linear polynomial. -/
theorem hermiteSignature_eq_rootSignSum_monic_linear_pow {p : F[X]}
    (hpMonic : p.Monic) (hpDegree : p.natDegree = 1)
    (h : F[X]) {n : ℕ} (hn : 0 < n) :
    hermiteSignature (p ^ n) h (hpMonic.pow n) = rootSignSum (p ^ n) h := by
  let a := -p.coeff 0
  have hp : p = X - C a := by
    simpa [a] using hpMonic.eq_X_add_C hpDegree
  simpa only [hp] using hermiteSignature_eq_rootSignSum_X_sub_C_pow a h hn

end OptimalConvergenceRates.KrivineStengle

end
