/-
  OptimalConvergenceRates/KrivineStengle/EquationElimination.lean

  One-variable elimination for a nonzero polynomial equation together
  with finitely many strict inequalities.
-/
import OptimalConvergenceRates.KrivineStengle.BranchedRootExistenceFormula
import OptimalConvergenceRates.KrivineStengle.DegreeBranches

noncomputable section

open MvPolynomial Polynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- Eliminate variable zero from `f = 0 ∧ ∀ i, 0 < g i`, on the
branch where the univariate specialization of `f` is nonzero. -/
def eliminateEquationStrictFormula {n s : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℝ)
    (g : Fin s → MvPolynomial (Fin (n + 1)) ℝ) : SignFormula n :=
  branchedRootExistenceFormula (asUnivariate f) (fun i ↦ asUnivariate (g i))

/-- Correctness of elimination for the nonzero-equation branch. -/
theorem realizes_eliminateEquationStrictFormula_iff
    {n s : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] [IsRealClosed F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (f : MvPolynomial (Fin (n + 1)) ℝ)
    (g : Fin s → MvPolynomial (Fin (n + 1)) ℝ) :
    (eliminateEquationStrictFormula f g).Realizes coeff x ↔
      specializePolynomial coeff x (asUnivariate f) ≠ 0 ∧
        ∃ y : F, eval₂Hom coeff (Fin.cons y x) f = 0 ∧
          ∀ i, 0 < eval₂Hom coeff (Fin.cons y x) (g i) := by
  rw [eliminateEquationStrictFormula,
    realizes_branchedRootExistenceFormula_iff]
  constructor
  · rintro ⟨y, hy, hpos⟩
    have hy' : y ∈ (specializePolynomial coeff x (asUnivariate f)).roots :=
      Multiset.mem_toFinset.mp hy
    have hf0 : specializePolynomial coeff x (asUnivariate f) ≠ 0 :=
      ne_zero_of_mem_roots hy'
    refine ⟨hf0, y, ?_, ?_⟩
    · rw [← eval_specialize_asUnivariate coeff x y f]
      exact isRoot_of_mem_roots hy'
    · intro i
      rw [← eval_specialize_asUnivariate coeff x y (g i)]
      exact hpos i
  · rintro ⟨hf0, y, hfy, hpos⟩
    refine ⟨y, Multiset.mem_toFinset.mpr ?_, ?_⟩
    · apply (mem_roots hf0).2
      rw [IsRoot, eval_specialize_asUnivariate coeff x y f]
      exact hfy
    · intro i
      rw [eval_specialize_asUnivariate coeff x y (g i)]
      exact hpos i

end OptimalConvergenceRates.KrivineStengle

end

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- The sum of the squares of a finite list of polynomials. -/
def equationSumSquares {n : ℕ}
    (equations : List (MvPolynomial (Fin n) ℝ)) :
    MvPolynomial (Fin n) ℝ :=
  ∑ p ∈ equations.toFinset, p ^ 2

/-- A sum of squares vanishes exactly when every equation in the list
vanishes. -/
theorem eval_equationSumSquares_eq_zero_iff
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (equations : List (MvPolynomial (Fin n) ℝ)) :
    eval₂Hom coeff x (equationSumSquares equations) = 0 ↔
      ∀ p ∈ equations, eval₂Hom coeff x p = 0 := by
  classical
  simp only [equationSumSquares, map_sum, map_pow]
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · simp
  · intro p _
    positivity

end OptimalConvergenceRates.KrivineStengle

end
