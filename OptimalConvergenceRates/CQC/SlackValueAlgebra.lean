import OptimalConvergenceRates.CQC.SlackValueSquareAlgebra

/-! Elementary identities for substituting the generators as slack values. -/

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

@[simp]
theorem generatorSlackSubstitution_liftBasePolynomial
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (q : MvPolynomial (Fin n) ℝ) :
    generatorSlackSubstitution g (liftBasePolynomial q) = q := by
  unfold generatorSlackSubstitution liftBasePolynomial
  rw [MvPolynomial.aeval_rename]
  have hf : ((fun j : Fin (n + m) ↦ Fin.addCases X g j) ∘ Fin.castAdd m) =
      (fun i ↦ (X i : MvPolynomial (Fin n) ℝ)) := by
    funext i
    simp
  rw [hf]
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add q r hq hr => rw [map_add, hq, hr]
  | mul_X q i hq =>
      rw [map_mul, hq]
      simp

@[simp]
theorem generatorSlackSubstitution_X_slack
    (g : Fin m → MvPolynomial (Fin n) ℝ) (i : Fin m) :
    generatorSlackSubstitution g (X (Fin.natAdd n i)) = g i := by
  simp [generatorSlackSubstitution]

end CQCInternal
end OptimalConvergenceRates

end
