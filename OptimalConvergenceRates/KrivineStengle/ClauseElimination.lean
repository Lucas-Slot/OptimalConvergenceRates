/-
  OptimalConvergenceRates/KrivineStengle/ClauseElimination.lean

  Elimination for a conjunctive clause on the branch where its combined
  equation is not the zero polynomial after specialization.
-/
import OptimalConvergenceRates.KrivineStengle.EquationElimination

noncomputable section

open MvPolynomial Polynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- Regard a list as a family indexed by its positions. -/
def listFamily {A : Type*} (xs : List A) : Fin xs.length → A :=
  xs.get

theorem forall_listFamily_iff {A : Type*} (xs : List A) (P : A → Prop) :
    (∀ i, P (listFamily xs i)) ↔ ∀ a ∈ xs, P a := by
  constructor
  · intro h a ha
    obtain ⟨i, rfl⟩ := List.get_of_mem ha
    exact h i
  · intro h i
    exact h _ (List.get_mem xs i)

/-- Eliminate one variable from a conjunction of equations and strict
positivity atoms on the nonzero combined-equation branch. -/
def eliminateNonzeroEquationClause {n : ℕ}
    (equations positives : List (MvPolynomial (Fin (n + 1)) ℝ)) :
    SignFormula n :=
  eliminateEquationStrictFormula (equationSumSquares equations)
    (listFamily positives)

theorem realizes_eliminateNonzeroEquationClause_iff
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] [IsRealClosed F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (equations positives : List (MvPolynomial (Fin (n + 1)) ℝ)) :
    (eliminateNonzeroEquationClause equations positives).Realizes coeff x ↔
      specializePolynomial coeff x
          (asUnivariate (equationSumSquares equations)) ≠ 0 ∧
        ∃ y : F,
          (∀ p ∈ equations, eval₂Hom coeff (Fin.cons y x) p = 0) ∧
          (∀ p ∈ positives, 0 < eval₂Hom coeff (Fin.cons y x) p) := by
  rw [eliminateNonzeroEquationClause,
    realizes_eliminateEquationStrictFormula_iff]
  constructor
  · rintro ⟨hne, y, heq, hpos⟩
    refine ⟨hne, y, ?_, ?_⟩
    · exact (eval_equationSumSquares_eq_zero_iff
        coeff (Fin.cons y x) equations).1 heq
    · exact (forall_listFamily_iff positives
        (fun p ↦ 0 < eval₂Hom coeff (Fin.cons y x) p)).1 hpos
  · rintro ⟨hne, y, heq, hpos⟩
    refine ⟨hne, y, ?_, ?_⟩
    · exact (eval_equationSumSquares_eq_zero_iff
        coeff (Fin.cons y x) equations).2 heq
    · exact (forall_listFamily_iff positives
        (fun p ↦ 0 < eval₂Hom coeff (Fin.cons y x) p)).2 hpos

end OptimalConvergenceRates.KrivineStengle

end
