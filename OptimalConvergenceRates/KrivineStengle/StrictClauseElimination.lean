/-
  OptimalConvergenceRates/KrivineStengle/StrictClauseElimination.lean

  Complete one-variable elimination for a conjunction of polynomial
  equations and strict positivity atoms.
-/
import OptimalConvergenceRates.KrivineStengle.ClauseElimination
import OptimalConvergenceRates.KrivineStengle.StrictSamplerCorrectness
import OptimalConvergenceRates.KrivineStengle.DegreeBranchPartition

noncomputable section

open MvPolynomial Polynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- The clause branch on which the combined sum-of-squares equation
specializes identically to zero. -/
def eliminateZeroEquationClause {n : ℕ}
    (equations positives : List (MvPolynomial (Fin (n + 1)) ℝ)) :
    SignFormula n :=
  .conj
    (zeroPolynomialBranch (asUnivariate (equationSumSquares equations)))
    (strictSamplerFormula (positives.map asUnivariate))

theorem realizes_eliminateZeroEquationClause_iff
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] [IsRealClosed F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (equations positives : List (MvPolynomial (Fin (n + 1)) ℝ)) :
    (eliminateZeroEquationClause equations positives).Realizes coeff x ↔
      specializePolynomial coeff x
        (asUnivariate (equationSumSquares equations)) = 0 ∧
      ∃ y : F, ∀ p ∈ positives,
        0 < eval₂Hom coeff (Fin.cons y x) p := by
  rw [eliminateZeroEquationClause, SignFormula.realizes_conj,
    realizes_zeroPolynomialBranch_iff,
    realizes_strictSamplerFormula_iff_exists]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    intro p hp
    have h := hy (asUnivariate p) (List.mem_map.mpr ⟨p, hp, rfl⟩)
    rwa [eval_specialize_asUnivariate] at h
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    rw [eval_specialize_asUnivariate]
    exact hy p hp

/-- Complete elimination formula for a conjunctive strict clause. -/
def eliminateStrictClause {n : ℕ}
    (equations positives : List (MvPolynomial (Fin (n + 1)) ℝ)) :
    SignFormula n :=
  .disj (eliminateNonzeroEquationClause equations positives)
    (eliminateZeroEquationClause equations positives)

/-- Exact one-variable elimination for finite conjunctions of equations
and strict inequalities, including an empty equation list. -/
theorem realizes_eliminateStrictClause_iff
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] [IsRealClosed F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (equations positives : List (MvPolynomial (Fin (n + 1)) ℝ)) :
    (eliminateStrictClause equations positives).Realizes coeff x ↔
      ∃ y : F,
        (∀ p ∈ equations, eval₂Hom coeff (Fin.cons y x) p = 0) ∧
        (∀ p ∈ positives, 0 < eval₂Hom coeff (Fin.cons y x) p) := by
  rw [eliminateStrictClause, SignFormula.realizes_disj,
    realizes_eliminateNonzeroEquationClause_iff,
    realizes_eliminateZeroEquationClause_iff]
  let combined := specializePolynomial coeff x
    (asUnivariate (equationSumSquares equations))
  constructor
  · rintro (⟨_, y, heq, hpos⟩ | ⟨hzero, y, hpos⟩)
    · exact ⟨y, heq, hpos⟩
    · refine ⟨y, ?_, hpos⟩
      apply (eval_equationSumSquares_eq_zero_iff
        coeff (Fin.cons y x) equations).1
      rw [← eval_specialize_asUnivariate coeff x y,
        show specializePolynomial coeff x
          (asUnivariate (equationSumSquares equations)) = 0 from hzero]
      simp
  · rintro ⟨y, heq, hpos⟩
    by_cases hzero : combined = 0
    · exact Or.inr ⟨hzero, y, hpos⟩
    · exact Or.inl ⟨hzero, y, heq, hpos⟩

end OptimalConvergenceRates.KrivineStengle

end
