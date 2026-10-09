/-
  OptimalConvergenceRates/KrivineStengle/HermiteSignatureFormula.lean

  Quantifier-free formulas computing specialized Hermite signatures.
-/
import OptimalConvergenceRates.KrivineStengle.GuardedHermiteMatrix
import OptimalConvergenceRates.KrivineStengle.TotalSignatureCorrectness
import OptimalConvergenceRates.KrivineStengle.HermiteSignature

noncomputable section

open Matrix MvPolynomial Polynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- On the actual-degree branch `d`, the formula saying that the Hermite
matrix of `f` and `h` has signature `s`. -/
def guardedHermiteSignatureFormula {n : ℕ}
    (f h : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ) (s : ℤ) :
    SignFormula n :=
  totalMatrixSignatureFormula d (guardedHermiteMatrix f h d) s

/-- Correctness of the specialization-safe Hermite-signature formula on an
actual-degree branch. -/
theorem realizes_guardedHermiteSignatureFormula_iff
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (f h : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ) (s : ℤ)
    (hdegree : ActualDegreeCondition coeff x f d) :
    (guardedHermiteSignatureFormula f h d s).Realizes coeff x ↔
      hermiteSignature
        (monicNormalizeSpecialization coeff x f d)
        (specializePolynomial coeff x h)
        (monic_monicNormalizeSpecialization coeff x f d hdegree) = s := by
  let p := monicNormalizeSpecialization coeff x f d
  let q := specializePolynomial coeff x h
  let hp := monic_monicNormalizeSpecialization coeff x f d hdegree
  let e := finCongr (natDegree_monicNormalizeSpecialization coeff x f d hdegree)
  have hvalid : GuardedMatrixValid coeff x (guardedHermiteMatrix f h d) :=
    guardedHermiteMatrix_valid coeff x f h d hdegree
  have heval :
      evalGuardedMatrix coeff x (guardedHermiteMatrix f h d) =
        Matrix.reindex e e (hermiteTraceMatrix p q hp) := by
    exact eval_guardedHermiteMatrix_eq_reindex_hermiteTraceMatrix
      coeff x f h d hdegree
  have hsymm :
      (evalGuardedMatrix coeff x (guardedHermiteMatrix f h d)).IsSymm := by
    rw [heval]
    exact (hermiteTraceMatrix_isSymm p q hp).submatrix e.symm
  rw [guardedHermiteSignatureFormula,
    realizes_totalMatrixSignatureFormula_iff coeff x _ s hvalid hsymm,
    heval, matrixSignature_reindex]
  rfl

end OptimalConvergenceRates.KrivineStengle

end
