import OptimalConvergenceRates.CQC.SlackValueBaseChainRule

/-! Chain rule in the slack coordinates for square-slack substitution. -/

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

theorem pderiv_slack_squareSlackSubstitution
    (P : MvPolynomial (Fin (n + m)) ℝ) (i : Fin m) :
    MvPolynomial.pderiv (Fin.natAdd n i)
        (squareSlackSubstitution P) =
      (2 • X (Fin.natAdd n i)) *
        squareSlackSubstitution
          (MvPolynomial.pderiv (Fin.natAdd n i) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
      simp [hP, hQ]
      ring
  | mul_X P q hP =>
      refine Fin.addCases ?_ ?_ q
      · intro k
        have hne : Fin.castAdd m k ≠ Fin.natAdd n i := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
          omega
        simp [hP, hne]
        ring
      · intro k
        by_cases hki : k = i
        · subst k
          simp [hP]
          ring
        · have hne : Fin.natAdd n k ≠ Fin.natAdd n i := by
            intro h
            have hv := congrArg Fin.val h
            simp at hv
            exact hki (Fin.ext hv)
          simp [hP, hne]
          ring

end CQCInternal
end OptimalConvergenceRates

end
