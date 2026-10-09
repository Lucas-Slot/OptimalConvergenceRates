/-
  OptimalConvergenceRates/KrivineStengle/HermiteSignature.lean

  Basis-independent signature of a Hermite trace matrix.
-/

import OptimalConvergenceRates.KrivineStengle.MatrixSignature


noncomputable section

open Matrix Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F]

/-- The weighted trace pairing `(x,y) ↦ Tr(h(root) * x * y)` on the adjoined-root algebra. -/
def hermiteTraceForm (f h : F[X]) (hf : f.Monic) :
    LinearMap.BilinForm F (AdjoinRoot f) := by
  letI : Module.Free F (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite F (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  exact (Algebra.traceForm F (AdjoinRoot f)).compl₁₂
    (Algebra.lmul F (AdjoinRoot f) (aeval (AdjoinRoot.root f) h)) LinearMap.id

@[simp] theorem hermiteTraceForm_apply (f h : F[X]) (hf : f.Monic)
    (x y : AdjoinRoot f) :
    hermiteTraceForm f h hf x y =
      Algebra.trace F (AdjoinRoot f)
        (aeval (AdjoinRoot.root f) h * x * y) := by
  simp [hermiteTraceForm, Algebra.traceForm_apply]

/-- In the power basis, the weighted trace pairing has exactly the Hermite trace matrix. -/
theorem hermiteTraceForm_toMatrix (f h : F[X]) (hf : f.Monic) :
    (hermiteTraceForm f h hf).toMatrix (AdjoinRoot.powerBasis' hf).basis =
      hermiteTraceMatrix f h hf := by
  ext i j
  simp only [LinearMap.BilinForm.toMatrix_apply, hermiteTraceMatrix,
    hermiteTraceForm_apply]
  rw [(AdjoinRoot.powerBasis' hf).basis_eq_pow i,
    (AdjoinRoot.powerBasis' hf).basis_eq_pow j]
  simp [pow_add, mul_assoc]

end OptimalConvergenceRates.KrivineStengle

end

noncomputable section

open Polynomial QuadraticMap

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Signature of the Hermite matrix `H(f,h)`. -/
def hermiteSignature (f h : F[X]) (hf : f.Monic) : ℤ :=
  matrixSignature (hermiteTraceMatrix f h hf)

/-- A Hermite matrix has a diagonalization whose sign sum computes its intrinsic signature. -/
theorem exists_hermite_diagonalization_with_signature
    (f h : F[X]) (hf : f.Monic) :
    ∃ (diagonal :
        Fin (Module.finrank F (Fin f.natDegree → F)) → F)
      (e : (Fin f.natDegree → F) ≃ₗ[F]
        (Fin (Module.finrank F (Fin f.natDegree → F)) → F)),
      (∀ x, weightedSumSquares F diagonal (e x) =
        (hermiteTraceMatrix f h hf).toQuadraticMap' x) ∧
      diagonalSignature diagonal = hermiteSignature f h hf := by
  simpa [hermiteSignature] using
    exists_diagonalization_with_signature
      (hermiteTraceMatrix f h hf) (hermiteTraceMatrix_isSymm f h hf)

end OptimalConvergenceRates.KrivineStengle

end
