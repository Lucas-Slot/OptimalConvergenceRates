/-
  OptimalConvergenceRates/KrivineStengle/FormulaTransfer.lean

  Reduction of finite sign realization to transfer for one explicit sign formula.
-/
import OptimalConvergenceRates.KrivineStengle.SignTransfer

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- Existential transfer for the small sign-formula language, from an arbitrary real-closed
ordered field carrying real coefficients back to the real numbers. -/
def RealClosedSignFormulaTransferStatement : Prop :=
  ∀ {n : ℕ} (formula : SignFormula n)
    (F : Type) [Field F] [LinearOrder F] [IsStrictOrderedRing F] [IsRealClosed F]
    (coeff : ℝ →+* F),
    formula.Satisfiable coeff → formula.Satisfiable (RingHom.id ℝ)

/-- Formula transfer gives exactly the real-closed finite sign-transfer theorem needed by the
Krivine--Stengle separation proof. -/
theorem realClosedFiniteSignTransfer_of_formulaTransfer
    (htransfer : RealClosedSignFormulaTransferStatement) :
    RealClosedFiniteSignTransferStatement := by
  intro n m g p F _ _ _ _ phi hg hp
  have hsatF : (SignFormula.counterexampleFormula g p).Satisfiable (phi.comp C) :=
    ⟨fun i ↦ phi (X i),
      SignFormula.counterexampleFormula_realizes_of_hom g p phi hg hp⟩
  obtain ⟨x, hx⟩ := htransfer (SignFormula.counterexampleFormula g p) F (phi.comp C) hsatF
  rw [SignFormula.realizes_counterexampleFormula] at hx
  refine ⟨x, ?_, ?_⟩
  · change ∀ i, 0 ≤ eval₂Hom (RingHom.id ℝ) x (g i)
    exact hx.1
  · change eval₂Hom (RingHom.id ℝ) x p < 0
    exact hx.2

/-- Ordered real-closure existence and formula transfer imply the precise finite realization
principle consumed by the certificate construction. -/
theorem finiteSignRealization_of_realClosure_and_formulaTransfer
    (hclosure : OrderedRealClosureExistenceStatement)
    (htransfer : RealClosedSignFormulaTransferStatement) :
    FiniteSignRealizationStatement :=
  finiteSignRealization_of_realClosure_and_transfer hclosure
    (realClosedFiniteSignTransfer_of_formulaTransfer htransfer)

/-- Formula-level assembly of the nonnegative Krivine--Stengle certificate theorem. -/
theorem nonnegative_krivine_stengle_of_realClosure_and_formulaTransfer
    (hclosure : OrderedRealClosureExistenceStatement)
    (htransfer : RealClosedSignFormulaTransferStatement)
    {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (hp : IsNonnegOn p (basicClosedSet g)) :
    Nonempty (KSWitness g p) :=
  nonnegative_krivine_stengle_of_realClosure_and_transfer hclosure
    (realClosedFiniteSignTransfer_of_formulaTransfer htransfer) g p hp

end OptimalConvergenceRates.KrivineStengle

end
