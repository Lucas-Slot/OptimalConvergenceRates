/-
  OptimalConvergenceRates/KrivineStengle/StrictSamplerFormula.lean

  The finite strict-sign sampler formula: positive tail, negative tail,
  or a root of the derivative of the product.
-/
import OptimalConvergenceRates.KrivineStengle.NegativeTailFormula
import OptimalConvergenceRates.KrivineStengle.BranchedRootExistenceFormula
import OptimalConvergenceRates.KrivineStengle.ClauseElimination

noncomputable section

open MvPolynomial Polynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- Product of a finite list of parameterized univariate polynomials. -/
def polynomialListProduct {n : ℕ}
    (fs : List ((MvPolynomial (Fin n) ℝ)[X])) :
    (MvPolynomial (Fin n) ℝ)[X] :=
  fs.prod

/-- Candidate sampler for a finite strict sign condition. The two tail
branches handle unbounded sign cells; the derivative-root branch handles
bounded cells. -/
def strictSamplerFormula {n : ℕ}
    (fs : List ((MvPolynomial (Fin n) ℝ)[X])) : SignFormula n :=
  .disj (allPositiveLeadingFormula fs)
    (.disj (allNegativeTailFormula fs)
      (branchedRootExistenceFormula (polynomialListProduct fs).derivative
        (listFamily fs)))

/-- Soundness of the strict sampler formula. Completeness is the algebraic
Rolle/sign-cell step developed separately. -/
theorem realizes_strictSamplerFormula_imp_exists
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] [IsRealClosed F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (fs : List ((MvPolynomial (Fin n) ℝ)[X]))
    (h : (strictSamplerFormula fs).Realizes coeff x) :
    ∃ y : F, ∀ f ∈ fs, 0 < (specializePolynomial coeff x f).eval y := by
  rw [strictSamplerFormula, SignFormula.realizes_disj,
    SignFormula.realizes_disj] at h
  rcases h with hposTail | hnegTail | hroot
  · obtain ⟨B, hB⟩ :=
      (realizes_allPositiveLeadingFormula_iff_exists_tail coeff x fs).1 hposTail
    exact ⟨B + 1, fun f hf ↦ hB (B + 1) (lt_add_one B) f hf⟩
  · obtain ⟨B, hB⟩ :=
      (realizes_allNegativeTailFormula_iff coeff x fs).1 hnegTail
    exact ⟨B - 1, fun f hf ↦ hB (B - 1) (sub_lt_self B zero_lt_one) f hf⟩
  · obtain ⟨y, _, hy⟩ :=
      (realizes_branchedRootExistenceFormula_iff coeff x
        (polynomialListProduct fs).derivative (listFamily fs)).1 hroot
    refine ⟨y, ?_⟩
    exact (forall_listFamily_iff fs
      (fun f ↦ 0 < (specializePolynomial coeff x f).eval y)).1 hy

end OptimalConvergenceRates.KrivineStengle

end
