import OptimalConvergenceRates.CQC.SlackValueDefs

/-! Elementary identities for squaring the slack variables. -/

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

@[simp]
theorem squareSlackSubstitution_X_base (j : Fin n) :
    squareSlackSubstitution (n := n) (m := m) (X (Fin.castAdd m j)) =
      X (Fin.castAdd m j) := by
  simp [squareSlackSubstitution]

@[simp]
theorem squareSlackSubstitution_X_slack (i : Fin m) :
    squareSlackSubstitution (n := n) (m := m) (X (Fin.natAdd n i)) =
      (X (Fin.natAdd n i)) ^ 2 := by
  simp [squareSlackSubstitution]

@[simp]
theorem squareSlackSubstitution_liftBasePolynomial
    (q : MvPolynomial (Fin n) ℝ) :
    squareSlackSubstitution (m := m) (liftBasePolynomial q) =
      liftBasePolynomial q := by
  unfold squareSlackSubstitution liftBasePolynomial
  rw [MvPolynomial.aeval_rename]
  have hf :
      ((fun j : Fin (n + m) ↦ Fin.addCases
        (fun k ↦ X (Fin.castAdd m k))
        (fun i ↦ (X (Fin.natAdd n i)) ^ 2) j) ∘ Fin.castAdd m) =
      fun i ↦ (X (Fin.castAdd m i) : MvPolynomial (Fin (n + m)) ℝ) := by
    funext i
    simp
  rw [hf]
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add q r hq hr => rw [map_add, map_add, hq, hr]
  | mul_X q i hq =>
      rw [map_mul, map_mul, hq]
      simp

end CQCInternal
end OptimalConvergenceRates

end
