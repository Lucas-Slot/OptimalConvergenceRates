import OptimalConvergenceRates.CQC.SlackValueChainRule

/-! Coordinate derivatives of the squared-slack equations. -/

noncomputable section

open MvPolynomial Set

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

theorem pderiv_slackPolynomial_base
    (g : Fin m → MvPolynomial (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    MvPolynomial.pderiv (Fin.castAdd m j) (slackPolynomial g i) =
      liftBasePolynomial (MvPolynomial.pderiv j (g i)) := by
  have hdis : Fin.castAdd m j ≠ Fin.natAdd n i := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  simp [slackPolynomial, liftBasePolynomial,
    MvPolynomial.pderiv_rename (Fin.castAdd_injective n m), hdis]

theorem pderiv_slackPolynomial_slack
    (g : Fin m → MvPolynomial (Fin n) ℝ) (i k : Fin m) :
    MvPolynomial.pderiv (Fin.natAdd n k) (slackPolynomial g i) =
      if k = i then -(2 • X (Fin.natAdd n i)) else 0 := by
  have hout : Fin.natAdd n k ∉ Set.range (Fin.castAdd m) := by
    rintro ⟨l, hl⟩
    have hv := congrArg Fin.val hl
    simp at hv
    omega
  simp [slackPolynomial, liftBasePolynomial,
    pderiv_rename_eq_zero_of_not_mem_range _ _ _ hout]
  by_cases hki : k = i
  · subst k
    simp
  · have hne : Fin.natAdd n k ≠ Fin.natAdd n i := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      exact hki (Fin.ext hv)
    simp [hki, hne]

end CQCInternal
end OptimalConvergenceRates

end
