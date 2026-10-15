/-
  OptimalConvergenceRates/KrivineStengle/HermiteTraceIsometry.lean

  The Hermite matrix and the weighted trace quadratic form define the same
  quadratic space, via coordinates in the power basis.
-/
import OptimalConvergenceRates.KrivineStengle.HermiteSignature

noncomputable section

open Matrix Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F]

/-- Power-basis coordinates give an isometry from the weighted trace quadratic
form to the quadratic form represented by the Hermite matrix. -/
noncomputable def hermiteTraceIsometry (f h : F[X]) (hf : f.Monic) :
    (hermiteTraceForm f h hf).toQuadraticMap.IsometryEquiv
      (hermiteTraceMatrix f h hf).toQuadraticForm' where
  toLinearEquiv := (AdjoinRoot.powerBasis' hf).basis.equivFun
  map_app' x := by
    change Matrix.toLinearMap₂' F (hermiteTraceMatrix f h hf)
        ((AdjoinRoot.powerBasisAux' hf).equivFun x)
        ((AdjoinRoot.powerBasisAux' hf).equivFun x) =
      hermiteTraceForm f h hf x x
    rw [Matrix.toLinearMap₂'_apply']
    rw [← hermiteTraceForm_toMatrix]
    rw [Module.Basis.equivFun_apply]
    exact (LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec
      (b := AdjoinRoot.powerBasisAux' hf) (hermiteTraceForm f h hf) x x).symm

/-- Intrinsic signature of the weighted trace form.  The finite-dimensional
instances are obtained canonically from the power basis. -/
noncomputable def hermiteTraceFormSignature [LinearOrder F] [IsStrictOrderedRing F]
    (f h : F[X]) (hf : f.Monic) : ℤ := by
  letI : Module.Free F (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite F (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  exact signature (hermiteTraceForm f h hf).toQuadraticMap

/-- The intrinsic signature of the weighted trace form is the Hermite signature. -/
theorem hermiteTraceFormSignature_eq [LinearOrder F] [IsStrictOrderedRing F]
    (f h : F[X]) (hf : f.Monic) :
    hermiteTraceFormSignature f h hf = hermiteSignature f h hf := by
  letI : Module.Free F (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite F (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  change signature (hermiteTraceForm f h hf).toQuadraticMap =
    matrixSignature (hermiteTraceMatrix f h hf)
  rw [matrixSignature]
  exact signature_congr (hermiteTraceIsometry f h hf).toLinearEquiv
    (hermiteTraceIsometry f h hf).map_app

end OptimalConvergenceRates.KrivineStengle

end
