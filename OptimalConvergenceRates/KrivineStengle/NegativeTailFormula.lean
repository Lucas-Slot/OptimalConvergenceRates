/-
  OptimalConvergenceRates/KrivineStengle/NegativeTailFormula.lean

  Negative-infinity tail formulas obtained by the substitution `X ↦ -X`.
-/
import OptimalConvergenceRates.KrivineStengle.PositiveTailFormulaCorrectness

noncomputable section

open MvPolynomial Polynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- Reflect a univariate polynomial by substituting `-X`. -/
def reflectPolynomial {n : ℕ}
    (f : (MvPolynomial (Fin n) ℝ)[X]) :
    (MvPolynomial (Fin n) ℝ)[X] :=
  f.comp (-Polynomial.X)

theorem specialize_reflectPolynomial
    {n : ℕ} {F : Type*} [CommRing F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (f : (MvPolynomial (Fin n) ℝ)[X]) :
    specializePolynomial coeff x (reflectPolynomial f) =
      (specializePolynomial coeff x f).comp (-Polynomial.X) := by
  simp [reflectPolynomial, specializePolynomial, Polynomial.map_comp]

theorem eval_specialize_reflectPolynomial
    {n : ℕ} {F : Type*} [CommRing F]
    (coeff : ℝ →+* F) (x : Fin n → F) (y : F)
    (f : (MvPolynomial (Fin n) ℝ)[X]) :
    (specializePolynomial coeff x (reflectPolynomial f)).eval y =
      (specializePolynomial coeff x f).eval (-y) := by
  rw [specialize_reflectPolynomial]
  simp

/-- Formula saying that all specialized polynomials in `fs` are positive
on one common negative tail. -/
def allNegativeTailFormula {n : ℕ}
    (fs : List ((MvPolynomial (Fin n) ℝ)[X])) : SignFormula n :=
  allPositiveLeadingFormula (fs.map reflectPolynomial)

theorem realizes_allNegativeTailFormula_iff
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] [IsRealClosed F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (fs : List ((MvPolynomial (Fin n) ℝ)[X])) :
    (allNegativeTailFormula fs).Realizes coeff x ↔
      ∃ B : F, ∀ y, y < B → ∀ f ∈ fs,
        0 < (specializePolynomial coeff x f).eval y := by
  rw [allNegativeTailFormula,
    realizes_allPositiveLeadingFormula_iff_exists_tail]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨-C, ?_⟩
    intro y hy f hf
    have hneg : C < -y := by linarith
    have href := hC (-y) hneg (reflectPolynomial f)
      (List.mem_map.mpr ⟨f, hf, rfl⟩)
    rw [eval_specialize_reflectPolynomial] at href
    simpa using href
  · rintro ⟨B, hB⟩
    refine ⟨-B, ?_⟩
    intro y hy reflected hreflected
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hreflected
    rw [eval_specialize_reflectPolynomial]
    exact hB (-y) (by linarith) f hf

end OptimalConvergenceRates.KrivineStengle

end
