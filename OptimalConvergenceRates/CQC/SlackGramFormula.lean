import OptimalConvergenceRates.CQC.SlackDerivativeFormula

/-! Coordinate formula for the squared-slack polynomial Gram matrix. -/

noncomputable section

open MvPolynomial Finset Matrix

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

theorem slackGramPolynomial_apply
    (g : Fin m → MvPolynomial (Fin n) ℝ) (i k : Fin m) :
    slackGramPolynomial g i k =
      (∑ j : Fin n,
        liftBasePolynomial (MvPolynomial.pderiv j (g i)) *
          liftBasePolynomial (MvPolynomial.pderiv j (g k))) +
        if i = k then MvPolynomial.C 4 * (X (Fin.natAdd n i)) ^ 2 else 0 := by
  rw [slackGramPolynomial, Matrix.mul_apply, Fin.sum_univ_add]
  simp only [Matrix.transpose_apply, slackJacobianPolynomial,
    pderiv_slackPolynomial_base, pderiv_slackPolynomial_slack]
  congr 1
  by_cases hik : i = k
  · subst k
    rw [Finset.sum_eq_single i]
    · simp
      have htwo : (2 : MvPolynomial (Fin (n + m)) ℝ) =
          MvPolynomial.C 2 :=
        (map_natCast
          (MvPolynomial.C : ℝ →+* MvPolynomial (Fin (n + m)) ℝ) 2).symm
      have hfour :
          (MvPolynomial.C 2 : MvPolynomial (Fin (n + m)) ℝ) *
              MvPolynomial.C 2 = MvPolynomial.C 4 := by
        rw [← map_mul]
        norm_num
      rw [htwo]
      let x : MvPolynomial (Fin (n + m)) ℝ := X (Fin.natAdd n i)
      change (MvPolynomial.C 2 : MvPolynomial (Fin (n + m)) ℝ) * x *
          (MvPolynomial.C 2 * x) = MvPolynomial.C 4 * x ^ 2
      calc
        (MvPolynomial.C 2 : MvPolynomial (Fin (n + m)) ℝ) * x *
            (MvPolynomial.C 2 * x) =
            (MvPolynomial.C 2 * MvPolynomial.C 2) * (x * x) := by ring
        _ = MvPolynomial.C 4 * (x * x) := by rw [hfour]
        _ = MvPolynomial.C 4 * x ^ 2 := by rw [pow_two]
    · intro j _ hji
      simp [hji]
    · simp
  · simp only [ite_eq_right hik]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hji : j = i
    · subst j
      simp [hik]
    · simp [hji]

@[simp]
theorem squareSlackSubstitution_slackValueGramPolynomial
    (g : Fin m → MvPolynomial (Fin n) ℝ) (i k : Fin m) :
    squareSlackSubstitution (slackValueGramPolynomial g i k) =
      slackGramPolynomial g i k := by
  rw [slackGramPolynomial_apply]
  by_cases hik : i = k
  · subst k
    simp [slackValueGramPolynomial]
  · simp [slackValueGramPolynomial, hik]

end CQCInternal
end OptimalConvergenceRates

end
