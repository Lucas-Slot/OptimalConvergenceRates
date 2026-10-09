/-
  OptimalConvergenceRates/KrivineStengle/HermiteQuadratic.lean

  Hermite's root-sign identity for irreducible quadratic factors.
-/
import OptimalConvergenceRates.KrivineStengle.TraceZeroBlock
import OptimalConvergenceRates.KrivineStengle.StrictRootCounting
import OptimalConvergenceRates.KrivineStengle.RealFactorization

noncomputable section

open Matrix Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

theorem hermiteTraceMatrix_reindex_quadratic {p : R[X]}
    (hpMonic : p.Monic) (hpDegree : p.natDegree = 2) (h : R[X]) :
    let root := AdjoinRoot.root p
    let weight := aeval root h
    let t0 := Algebra.trace R (AdjoinRoot p) weight
    let t1 := Algebra.trace R (AdjoinRoot p) (weight * root)
    Matrix.reindex (finCongr hpDegree) (finCongr hpDegree)
        (hermiteTraceMatrix p h hpMonic) =
      !![t0, t1; t1, -p.coeff 1 * t1 - p.coeff 0 * t0] := by
  letI : Module.Free R (AdjoinRoot p) := hpMonic.free_adjoinRoot
  letI : Module.Finite R (AdjoinRoot p) :=
    (AdjoinRoot.powerBasis' hpMonic).finite
  let root := AdjoinRoot.root p
  let weight := aeval root h
  let t0 := Algebra.trace R (AdjoinRoot p) weight
  let t1 := Algebra.trace R (AdjoinRoot p) (weight * root)
  have hcoeffTwo : p.coeff 2 = 1 := by
    rw [← hpDegree, coeff_natDegree, hpMonic.leadingCoeff]
  have hpoly :
      p = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
    calc
      p = ∑ i ∈ Finset.range (p.natDegree + 1), C (p.coeff i) * X ^ i :=
        p.as_sum_range_C_mul_X_pow
      _ = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
        rw [hpDegree]
        norm_num [Finset.sum_range_succ, hcoeffTwo]
        ring
  have hroot :
      root ^ 2 + algebraMap R (AdjoinRoot p) (p.coeff 1) * root +
          algebraMap R (AdjoinRoot p) (p.coeff 0) = 0 := by
    calc
      root ^ 2 + algebraMap R (AdjoinRoot p) (p.coeff 1) * root +
          algebraMap R (AdjoinRoot p) (p.coeff 0) =
          (X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0)).eval₂
            (AdjoinRoot.of p) root := by simp
      _ = p.eval₂ (AdjoinRoot.of p) root :=
        congrArg (fun q ↦ q.eval₂ (AdjoinRoot.of p) root) hpoly.symm
      _ = 0 := AdjoinRoot.eval₂_root p
  have hroot_sq :
      root ^ 2 =
        -algebraMap R (AdjoinRoot p) (p.coeff 1) * root -
          algebraMap R (AdjoinRoot p) (p.coeff 0) := by
    linear_combination hroot
  have htrace_two :
      Algebra.trace R (AdjoinRoot p) (weight * root ^ 2) =
        -p.coeff 1 * t1 - p.coeff 0 * t0 := by
    have hmul :
        weight * root ^ 2 =
          -(p.coeff 1 • (weight * root)) - p.coeff 0 • weight := by
      rw [hroot_sq]
      simp only [Algebra.smul_def]
      ring
    rw [hmul]
    simp [t0, t1]
  dsimp only
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.reindex_apply, hermiteTraceMatrix]
  · simp [Matrix.reindex_apply, hermiteTraceMatrix]
  · simp [Matrix.reindex_apply, hermiteTraceMatrix,
      add_comm]
  · simpa [Matrix.reindex_apply, hermiteTraceMatrix, root, weight, t0, t1]
      using htrace_two


/-- An irreducible monic quadratic contributes no signature to a Hermite form. -/
theorem hermiteSignature_irreducible_quadratic {p : R[X]}
    (hpMonic : p.Monic) (hpIrr : Irreducible p)
    (hpDegree : p.natDegree = 2) (h : R[X]) :
    hermiteSignature p h hpMonic = 0 := by
  let root := AdjoinRoot.root p
  let weight := aeval root h
  let t0 := Algebra.trace R (AdjoinRoot p) weight
  let t1 := Algebra.trace R (AdjoinRoot p) (weight * root)
  rw [hermiteSignature]
  rw [← matrixSignature_reindex (finCongr hpDegree)
    (hermiteTraceMatrix p h hpMonic)]
  rw [hermiteTraceMatrix_reindex_quadratic hpMonic hpDegree h]
  change matrixSignature
    !![t0, t1; t1, -p.coeff 1 * t1 - p.coeff 0 * t0] = 0
  have hcoeffTwo : p.coeff 2 = 1 := by
    rw [← hpDegree, coeff_natDegree, hpMonic.leadingCoeff]
  have hpoly :
      p = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
    calc
      p = ∑ i ∈ Finset.range (p.natDegree + 1), C (p.coeff i) * X ^ i :=
        p.as_sum_range_C_mul_X_pow
      _ = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
        rw [hpDegree]
        norm_num [Finset.sum_range_succ, hcoeffTwo]
        ring
  have hcenter : 0 < p.coeff 0 - p.coeff 1 ^ 2 / 4 := by
    have hpos := monic_irreducible_quadratic_eval_pos
      hpMonic hpIrr hpDegree (-p.coeff 1 / 2)
    rw [hpoly] at hpos
    norm_num [eval_add, eval_mul, eval_pow, eval_C, eval_X] at hpos
    nlinarith
  by_cases ht0 : t0 = 0
  · by_cases ht1 : t1 = 0
    · simpa [ht0, ht1] using
        (matrixSignature_traceZero_two (F := R) (0 : R) 0)
    · apply matrixSignature_two_of_det_neg
      rw [ht0]
      nlinarith [sq_pos_of_ne_zero ht1]
  · apply matrixSignature_two_of_det_neg
    have ht0sq : 0 < t0 ^ 2 := sq_pos_of_ne_zero ht0
    have hprod : 0 < (p.coeff 0 - p.coeff 1 ^ 2 / 4) * t0 ^ 2 :=
      mul_pos hcenter ht0sq
    nlinarith [sq_nonneg (t1 + p.coeff 1 * t0 / 2)]

/-- The root-sign sum of an irreducible quadratic is empty. -/
theorem rootSignSum_irreducible_quadratic {p : R[X]}
    (hpIrr : Irreducible p) (hpDegree : p.natDegree = 2) (h : R[X]) :
    rootSignSum p h = 0 := by
  rw [rootSignSum,
    roots_eq_zero_of_irreducible_of_natDegree_ne_one hpIrr (by omega)]
  simp

/-- Hermite's root-sign identity for an irreducible monic quadratic. -/
theorem hermiteSignature_eq_rootSignSum_irreducible_quadratic {p : R[X]}
    (hpMonic : p.Monic) (hpIrr : Irreducible p)
    (hpDegree : p.natDegree = 2) (h : R[X]) :
    hermiteSignature p h hpMonic = rootSignSum p h := by
  rw [hermiteSignature_irreducible_quadratic hpMonic hpIrr hpDegree,
    rootSignSum_irreducible_quadratic hpIrr hpDegree]
end OptimalConvergenceRates.KrivineStengle

end
