/-
  OptimalConvergenceRates/KrivineStengle/StrictRootExistenceFormula.lean

  A specialization-safe formula for a root satisfying finitely many
  strict polynomial inequalities.
-/
import OptimalConvergenceRates.KrivineStengle.PositiveHermiteSignatureFormula
import OptimalConvergenceRates.KrivineStengle.HermiteGeneral

noncomputable section

open MvPolynomial Polynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- The finite list of products with exponents in `{1,2}` used by the
Hermite strict-root counting identity. -/
def strictHermiteProducts {n s : ℕ}
    (g : Fin s → (MvPolynomial (Fin n) ℝ)[X]) :
    List ((MvPolynomial (Fin n) ℝ)[X]) :=
  Finset.univ.toList.map fun exponent : Fin s → Fin 2 ↦
    ∏ i, (g i) ^ (exponent i).1.succ

theorem specialize_strictHermiteProduct
    {n s : ℕ} {F : Type*} [CommRing F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (g : Fin s → (MvPolynomial (Fin n) ℝ)[X])
    (exponent : Fin s → Fin 2) :
    specializePolynomial coeff x (∏ i, (g i) ^ (exponent i).1.succ) =
      ∏ i, (specializePolynomial coeff x (g i)) ^ (exponent i).1.succ := by
  simpa only [specializePolynomial, Polynomial.map_pow] using
    Polynomial.map_prod (eval₂Hom coeff x)
      (fun i ↦ (g i) ^ (exponent i).1.succ) Finset.univ

/-- On the actual-degree branch `d`, this formula says that the
specialization of `f` has a root at which every specialization of `g i`
is strictly positive. -/
def strictRootExistenceFormula {n s : ℕ}
    (f : (MvPolynomial (Fin n) ℝ)[X])
    (g : Fin s → (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ) :
    SignFormula n :=
  positiveHermiteSignatureListFormula f d (strictHermiteProducts g)

/-- Correctness of the strict-root formula over every real-closed ordered
field, uniformly in all coefficient specializations. -/
theorem realizes_strictRootExistenceFormula_iff
    {n s : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] [IsRealClosed F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (f : (MvPolynomial (Fin n) ℝ)[X])
    (g : Fin s → (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ)
    (hdegree : ActualDegreeCondition coeff x f d) :
    (strictRootExistenceFormula f g d).Realizes coeff x ↔
      ∃ r ∈ (specializePolynomial coeff x f).roots.toFinset,
        ∀ i, 0 < (specializePolynomial coeff x (g i)).eval r := by
  let p := monicNormalizeSpecialization coeff x f d
  let hp := monic_monicNormalizeSpecialization coeff x f d hdegree
  let gs : Fin s → F[X] := fun i ↦ specializePolynomial coeff x (g i)
  rw [strictRootExistenceFormula,
    realizes_positiveHermiteSignatureListFormula_iff
      coeff x f d (strictHermiteProducts g) hdegree]
  have hsum :
      ((strictHermiteProducts g).map fun h ↦
        hermiteSignature p (specializePolynomial coeff x h) hp).sum =
        ∑ exponent : Fin s → Fin 2,
          hermiteSignature p
            (∏ i, (gs i) ^ (exponent i).1.succ) hp := by
    simp [strictHermiteProducts, specialize_strictHermiteProduct, gs]
  rw [hsum]
  rw [← exists_root_all_pos_iff_hermite_sum_pos_realClosed p hp gs]
  rw [roots_monicNormalizeSpecialization coeff x f d hdegree]

end OptimalConvergenceRates.KrivineStengle

end
