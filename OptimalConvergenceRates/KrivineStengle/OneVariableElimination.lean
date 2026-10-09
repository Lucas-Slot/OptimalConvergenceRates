/-
  OptimalConvergenceRates/KrivineStengle/OneVariableElimination.lean

  Structural elimination of one existentially quantified variable from
  an arbitrary polynomial sign formula.
-/
import OptimalConvergenceRates.KrivineStengle.LiteralClauseElimination

noncomputable section

namespace OptimalConvergenceRates.KrivineStengle

/-- Eliminate variable zero from a DNF of sign-literal clauses. -/
def eliminateLiteralDNF {n : ℕ}
    (dnf : List (List (SignLiteral (n + 1)))) : SignFormula n :=
  SignFormula.any (dnf.map eliminateLiteralClause)

theorem realizes_eliminateLiteralDNF_iff
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] [IsRealClosed F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (dnf : List (List (SignLiteral (n + 1)))) :
    (eliminateLiteralDNF dnf).Realizes coeff x ↔
      ∃ y : F, SignFormula.DNFRealizes coeff (Fin.cons y x) dnf := by
  rw [eliminateLiteralDNF, SignFormula.realizes_any]
  constructor
  · rintro ⟨formula, hformula, hrealizes⟩
    obtain ⟨clause, hclause, rfl⟩ := List.mem_map.mp hformula
    obtain ⟨y, hy⟩ :=
      (realizes_eliminateLiteralClause_iff coeff x clause).1 hrealizes
    exact ⟨y, clause, hclause, hy⟩
  · rintro ⟨y, clause, hclause, hy⟩
    refine ⟨eliminateLiteralClause clause,
      List.mem_map.mpr ⟨clause, hclause, rfl⟩, ?_⟩
    exact (realizes_eliminateLiteralClause_iff coeff x clause).2 ⟨y, hy⟩

/-- Eliminate variable zero from an arbitrary sign formula. -/
def eliminateOne {n : ℕ} (formula : SignFormula (n + 1)) : SignFormula n :=
  eliminateLiteralDNF (SignFormula.toDNF true formula)

/-- Correctness of one-variable existential elimination over every
real-closed ordered field with an interpretation of the real coefficients. -/
theorem realizes_eliminateOne_iff
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] [IsRealClosed F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (formula : SignFormula (n + 1)) :
    (eliminateOne formula).Realizes coeff x ↔
      ∃ y : F, formula.Realizes coeff (Fin.cons y x) := by
  rw [eliminateOne, realizes_eliminateLiteralDNF_iff]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (SignFormula.dnfRealizes_toDNF_true
      coeff (Fin.cons y x) formula).1 hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, (SignFormula.dnfRealizes_toDNF_true
      coeff (Fin.cons y x) formula).2 hy⟩

end OptimalConvergenceRates.KrivineStengle

end
