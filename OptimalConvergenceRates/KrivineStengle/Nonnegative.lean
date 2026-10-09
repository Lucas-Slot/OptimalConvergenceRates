/-
  OptimalConvergenceRates/KrivineStengle/Nonnegative.lean

  Unconditional nonnegative Krivine--Stengle theorem.
-/
import OptimalConvergenceRates.KrivineStengle.RealClosure
import OptimalConvergenceRates.KrivineStengle.ExistentialTransfer

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- Finite real sign realization, obtained from ordered real closures and
the proved elimination procedure. -/
theorem finiteSignRealization : FiniteSignRealizationStatement :=
  finiteSignRealization_of_realClosure_and_formulaTransfer
    orderedRealClosureExistence realClosedSignFormulaTransfer

/-- Nonnegative Krivine--Stengle over finite real multivariate polynomial rings. -/
theorem nonnegative_krivine_stengle
    {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (hp : IsNonnegOn p (basicClosedSet g)) :
    Nonempty (KSWitness g p) :=
  nonnegative_krivine_stengle_of_signRealization
    finiteSignRealization g p hp

/-- Equivalence between nonnegativity on a basic closed set and existence
of a Krivine--Stengle witness. -/
theorem nonnegative_krivine_stengle_iff
    {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) :
    IsNonnegOn p (basicClosedSet g) ↔ Nonempty (KSWitness g p) := by
  constructor
  · exact nonnegative_krivine_stengle g p
  · rintro ⟨w⟩
    exact w.nonnegOn

/-- The locked forward statement is now proved. -/
theorem nonnegativeKrivineStengleStatement : NonnegativeKrivineStengleStatement := by
  intro n m g p hp
  exact nonnegative_krivine_stengle g p hp

/-- The locked equivalence statement is now proved. -/
theorem nonnegativeKrivineStengleIffStatement : NonnegativeKrivineStengleIffStatement := by
  intro n m g p
  exact nonnegative_krivine_stengle_iff g p

end OptimalConvergenceRates.KrivineStengle

end
