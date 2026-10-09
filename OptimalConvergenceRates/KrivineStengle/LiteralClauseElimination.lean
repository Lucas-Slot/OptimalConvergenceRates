/-
  OptimalConvergenceRates/KrivineStengle/LiteralClauseElimination.lean

  One-variable elimination for a clause of arbitrary sign literals.
-/
import OptimalConvergenceRates.KrivineStengle.LiteralClauseNormalization
import OptimalConvergenceRates.KrivineStengle.StrictClauseElimination

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- Eliminate variable zero from a conjunction of arbitrary sign literals. -/
def eliminateLiteralClause {n : ℕ}
    (clause : List (SignLiteral (n + 1))) : SignFormula n :=
  SignFormula.any ((normalizeLiteralClause clause).map fun strictClause ↦
    eliminateStrictClause strictClause.equations strictClause.positives)

theorem realizes_eliminateLiteralClause_iff
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] [IsRealClosed F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (clause : List (SignLiteral (n + 1))) :
    (eliminateLiteralClause clause).Realizes coeff x ↔
      ∃ y : F, SignFormula.ClauseRealizes coeff (Fin.cons y x) clause := by
  rw [eliminateLiteralClause, SignFormula.realizes_any]
  constructor
  · rintro ⟨formula, hformula, hrealizes⟩
    obtain ⟨strictClause, hstrictClause, rfl⟩ := List.mem_map.mp hformula
    obtain ⟨y, hequations, hpositives⟩ :=
      (realizes_eliminateStrictClause_iff coeff x
        strictClause.equations strictClause.positives).1 hrealizes
    refine ⟨y, (strictDNFRealizes_normalizeLiteralClause
      coeff (Fin.cons y x) clause).1 ?_⟩
    exact ⟨strictClause, hstrictClause, hequations, hpositives⟩
  · rintro ⟨y, hclause⟩
    obtain ⟨strictClause, hstrictClause, hequations, hpositives⟩ :=
      (strictDNFRealizes_normalizeLiteralClause
        coeff (Fin.cons y x) clause).2 hclause
    refine ⟨eliminateStrictClause strictClause.equations strictClause.positives,
      List.mem_map.mpr ⟨strictClause, hstrictClause, rfl⟩, ?_⟩
    exact (realizes_eliminateStrictClause_iff coeff x
      strictClause.equations strictClause.positives).2
        ⟨y, hequations, hpositives⟩

end OptimalConvergenceRates.KrivineStengle

end
