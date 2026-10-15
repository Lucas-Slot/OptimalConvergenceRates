/-
  OptimalConvergenceRates/KrivineStengle/ExistentialTransfer.lean

  Iterate one-variable elimination and transfer existential sign formulas
  from real-closed fields with real coefficients back to the reals.
-/
import OptimalConvergenceRates.KrivineStengle.OneVariableElimination
import OptimalConvergenceRates.KrivineStengle.FormulaTransfer
import Mathlib.Algebra.Order.Archimedean.Real.Hom

noncomputable section

namespace OptimalConvergenceRates.KrivineStengle

/-- Eliminate all variables from a sign formula. -/
def eliminateAll : (n : ℕ) → SignFormula n → SignFormula 0
  | 0, formula => formula
  | n + 1, formula => eliminateAll n (eliminateOne formula)

/-- Iterated elimination is equivalent to existential satisfiability. -/
theorem realizes_eliminateAll_iff_satisfiable
    {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] [IsRealClosed F]
    (coeff : ℝ →+* F) :
    ∀ {n : ℕ} (formula : SignFormula n),
      (eliminateAll n formula).Realizes coeff (fun i ↦ Fin.elim0 i) ↔
        formula.Satisfiable coeff := by
  intro n
  induction n with
  | zero =>
      intro formula
      constructor
      · intro h
        exact ⟨fun i ↦ Fin.elim0 i, h⟩
      · rintro ⟨x, hx⟩
        simpa only [eliminateAll,
          show x = (fun i ↦ Fin.elim0 i) from Subsingleton.elim _ _] using hx
  | succ n ih =>
      intro formula
      rw [eliminateAll, ih]
      constructor
      · rintro ⟨x, hx⟩
        obtain ⟨y, hy⟩ := (realizes_eliminateOne_iff coeff x formula).1 hx
        exact ⟨Fin.cons y x, hy⟩
      · rintro ⟨z, hz⟩
        refine ⟨Fin.tail z, (realizes_eliminateOne_iff
          coeff (Fin.tail z) formula).2 ⟨z 0, ?_⟩⟩
        simpa only [Fin.cons_self_tail z] using hz

/-- Every ring homomorphism from the reals to an ordered field is monotone. -/
def realCoeffOrderRingHom
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) : ℝ →+*o F where
  toRingHom := coeff
  monotone' := ringHom_monotone
    (fun r hr ↦ ⟨Real.sqrt r, by simpa [pow_two] using (Real.sq_sqrt hr).symm⟩) coeff

/-- Proved existential transfer for the repository's sign-formula language. -/
theorem realClosedSignFormulaTransfer : RealClosedSignFormulaTransferStatement := by
  intro n formula F _ _ _ _ coeff hsat
  let closedFormula := eliminateAll n formula
  have hclosedF : closedFormula.Realizes coeff (fun i ↦ Fin.elim0 i) :=
    (realizes_eliminateAll_iff_satisfiable coeff formula).2 hsat
  let embedding : ℝ →+*o F := realCoeffOrderRingHom coeff
  have hmap := SignFormula.realizes_map_iff embedding (RingHom.id ℝ)
    (fun i : Fin 0 ↦ Fin.elim0 i) closedFormula
  have hclosedReal : closedFormula.Realizes (RingHom.id ℝ)
      (fun i ↦ Fin.elim0 i) := by
    apply hmap.mp
    convert hclosedF using 1
    ext x
    rfl
  exact (realizes_eliminateAll_iff_satisfiable
    (RingHom.id ℝ) formula).1 hclosedReal

end OptimalConvergenceRates.KrivineStengle

end
