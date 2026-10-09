import OptimalConvergenceRates.CQC.SlackValueSquareAlgebra

/-! Chain rule in the base coordinates for square-slack substitution. -/

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

theorem pderiv_base_squareSlackSubstitution
    (P : MvPolynomial (Fin (n + m)) ℝ) (j : Fin n) :
    MvPolynomial.pderiv (Fin.castAdd m j)
        (squareSlackSubstitution P) =
      squareSlackSubstitution (MvPolynomial.pderiv (Fin.castAdd m j) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P q hP =>
      refine Fin.addCases ?_ ?_ q
      · intro k
        by_cases hkj : k = j
        · subst k
          simp [hP]
        · have hne : Fin.castAdd m k ≠ Fin.castAdd m j := by
            exact fun h ↦ hkj (Fin.castAdd_injective n m h)
          simp [hP, hne]
      · intro k
        have hne : Fin.natAdd n k ≠ Fin.castAdd m j := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
          omega
        simp [hP, hne]

end CQCInternal
end OptimalConvergenceRates

end
