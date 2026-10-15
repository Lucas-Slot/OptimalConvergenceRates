import OptimalConvergenceRates.KrivineStengle.HermiteIrreducible

noncomputable section

open Matrix Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F]

private theorem coeff_modByMonic_X_pow_of_lt (p : F[X]) {n i : ℕ}
    (hi : i < n) : (p %ₘ (X ^ n)).coeff i = p.coeff i := by
  rw [modByMonic_eq_sub_mul_div p (X ^ n), coeff_sub,
    coeff_X_pow_mul']
  simp [not_le_of_gt hi]

/-- In the truncated polynomial algebra `F[X]/(X^n)`, the trace of
multiplication by `h(root)` is `n` times the constant coefficient of `h`. -/
theorem trace_aeval_adjoinRoot_X_pow (h : F[X]) (n : ℕ) :
    Algebra.trace F (AdjoinRoot (X ^ n : F[X]))
        (aeval (AdjoinRoot.root (X ^ n : F[X])) h) = n • h.coeff 0 := by
  let hf : (X ^ n : F[X]).Monic := by exact monic_X_pow n
  letI : Module.Free F (AdjoinRoot (X ^ n : F[X])) := hf.free_adjoinRoot
  letI : Module.Finite F (AdjoinRoot (X ^ n : F[X])) :=
    (AdjoinRoot.powerBasis' hf).finite
  let b := AdjoinRoot.powerBasisAux' hf
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  have hdiag (i : Fin (X ^ n : F[X]).natDegree) :
      Algebra.leftMulMatrix b (aeval (AdjoinRoot.root (X ^ n : F[X])) h) i i =
        h.coeff 0 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    rw [show b i = AdjoinRoot.root (X ^ n) ^ (i : ℕ) by
      exact (AdjoinRoot.powerBasis' hf).basis_eq_pow i]
    change ((AdjoinRoot.powerBasisAux' hf).repr
      (aeval (AdjoinRoot.root (X ^ n)) h *
        AdjoinRoot.root (X ^ n) ^ (i : ℕ))) i = h.coeff 0
    rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
    change (AdjoinRoot.modByMonicHom hf
      (aeval (AdjoinRoot.root (X ^ n : F[X])) h *
        AdjoinRoot.root (X ^ n) ^ (i : ℕ))).coeff (i : ℕ) = h.coeff 0
    rw [AdjoinRoot.aeval_eq, ← AdjoinRoot.mk_X, ← map_pow, ← map_mul,
      AdjoinRoot.modByMonicHom_mk]
    rw [coeff_modByMonic_X_pow_of_lt _ (by simpa using i.isLt)]
    simpa using coeff_mul_X_pow h (i : ℕ) 0
  simp_rw [Matrix.diag_apply, hdiag]
  simp [Finset.sum_const]

private theorem root_X_pow_nilpotent (n : ℕ) :
    AdjoinRoot.root (X ^ n : F[X]) ^ n = 0 := by
  rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]

private theorem root_sub_C_pow_nilpotent (a : F) (n : ℕ) :
    (AdjoinRoot.root ((X - C a) ^ n : F[X]) - algebraMap F _ a) ^ n = 0 := by
  rw [AdjoinRoot.algebraMap_eq]
  change (AdjoinRoot.mk ((X - C a) ^ n) X -
    AdjoinRoot.mk ((X - C a) ^ n) (C a)) ^ n = 0
  rw [← map_sub, ← map_pow, AdjoinRoot.mk_self]

/-- Translation by `a` identifies the local algebra at `a` with the truncated
polynomial algebra at zero. -/
def adjoinRootLinearPowerEquiv (a : F) (n : ℕ) :
    AdjoinRoot ((X - C a) ^ n : F[X]) ≃ₐ[F]
      AdjoinRoot (X ^ n : F[X]) :=
  AlgEquiv.ofAlgHom
    (AdjoinRoot.liftAlgHom ((X - C a) ^ n : F[X]) (Algebra.ofId F _)
      (AdjoinRoot.root (X ^ n : F[X]) + algebraMap F _ a) (by
        rw [eval₂_pow, eval₂_sub, eval₂_X, eval₂_C]
        change ((AdjoinRoot.root (X ^ n : F[X]) + algebraMap F _ a) -
          algebraMap F _ a) ^ n = 0
        rw [add_sub_cancel_right, root_X_pow_nilpotent]))
    (AdjoinRoot.liftAlgHom (X ^ n : F[X]) (Algebra.ofId F _)
      (AdjoinRoot.root ((X - C a) ^ n : F[X]) - algebraMap F _ a) (by
        rw [eval₂_X_pow]
        exact root_sub_C_pow_nilpotent (F := F) a n))
    (by ext; simp)
    (by ext; simp)

@[simp]
theorem adjoinRootLinearPowerEquiv_root (a : F) (n : ℕ) :
    adjoinRootLinearPowerEquiv a n
        (AdjoinRoot.root ((X - C a) ^ n : F[X])) =
      AdjoinRoot.root (X ^ n : F[X]) + algebraMap F _ a := by
  simp [adjoinRootLinearPowerEquiv]

/-- The trace in the local algebra of a repeated linear factor is its
multiplicity times evaluation at the root. -/
theorem trace_aeval_adjoinRoot_X_sub_C_pow (h : F[X]) (a : F) (n : ℕ) :
    Algebra.trace F (AdjoinRoot ((X - C a) ^ n : F[X]))
        (aeval (AdjoinRoot.root ((X - C a) ^ n : F[X])) h) =
      n • h.eval a := by
  let e := adjoinRootLinearPowerEquiv a n
  rw [← Algebra.trace_eq_of_algEquiv e
    (aeval (AdjoinRoot.root ((X - C a) ^ n : F[X])) h)]
  rw [← Polynomial.aeval_algHom_apply]
  rw [adjoinRootLinearPowerEquiv_root]
  let shifted := h.comp (X + C a)
  have heval :
      aeval (AdjoinRoot.root (X ^ n : F[X])) shifted =
        aeval (AdjoinRoot.root (X ^ n : F[X]) + algebraMap F _ a) h := by
    simp [shifted, aeval_comp]
  rw [← heval, trace_aeval_adjoinRoot_X_pow]
  congr 1
  simp [shifted, coeff_zero_eq_eval_zero, eval_comp]

end OptimalConvergenceRates.KrivineStengle

end
