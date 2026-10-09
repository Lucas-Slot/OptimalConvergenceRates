import OptimalConvergenceRates.CQC.SlackValueRhsDescent

/-! Descent of the complete adjugate correction. -/

noncomputable section

open MvPolynomial Finset Matrix

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

@[simp]
theorem squareSlackSubstitution_slackValueCorrection
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (i : Fin m) :
    squareSlackSubstitution (slackValueCorrection g p i) =
      slackCorrection g p i := by
  change squareSlackSubstitution
      (((slackValueGramPolynomial g).adjugate *ᵥ
        slackValueCorrectionRhs g p) i) = _
  rw [Matrix.mulVec, dotProduct]
  simp only [map_sum, map_mul,
    squareSlackSubstitution_adjugate_slackValueGramPolynomial,
    squareSlackSubstitution_slackValueCorrectionRhs]
  rfl

@[simp]
theorem squareSlackSubstitution_slackValueEquation
    (g : Fin m → MvPolynomial (Fin n) ℝ) (i : Fin m) :
    squareSlackSubstitution
        (liftBasePolynomial (g i) - X (Fin.natAdd n i)) =
      slackPolynomial g i := by
  simp [slackPolynomial]

/-- The explicit slack-value polynomial descends exactly to the penalized
squared-slack lift. -/
theorem squareSlackSubstitution_descendedSlackObjective
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (M : ℝ) :
    squareSlackSubstitution (descendedSlackObjective g p M) =
      penalizedSlackObjective g p M := by
  simp [descendedSlackObjective, penalizedSlackObjective,
    correctedSlackObjective, equationSquareSum]

end CQCInternal
end OptimalConvergenceRates

end
