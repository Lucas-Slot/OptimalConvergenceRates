import OptimalConvergenceRates.CQC.SlackValueDeterminantDescent

/-! Descent of the slack-coordinate part of the correction vector. -/

noncomputable section

open MvPolynomial Set

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

theorem pderiv_slack_liftBasePolynomial_eq_zero
    (p : MvPolynomial (Fin n) ℝ) (i : Fin m) :
    MvPolynomial.pderiv (Fin.natAdd n i) (liftBasePolynomial p) = 0 := by
  apply pderiv_rename_eq_zero_of_not_mem_range
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  simp at hv
  omega

/-- The coefficient `4` in the slack block of `W` after the substitution
`u_i = y_i^2`. -/
theorem slackW_slack_eq
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (i : Fin m) :
    slackW g p (Fin.natAdd n i) =
      MvPolynomial.C 4 * liftBasePolynomial p * X (Fin.natAdd n i) *
        squareSlackSubstitution
          (MvPolynomial.pderiv (Fin.natAdd n i)
            (slackValueDeterminant g)) := by
  have hd :
      MvPolynomial.pderiv (Fin.natAdd n i) (slackDeterminant g) =
        (2 • X (Fin.natAdd n i)) *
          squareSlackSubstitution
            (MvPolynomial.pderiv (Fin.natAdd n i)
              (slackValueDeterminant g)) := by
    calc
      MvPolynomial.pderiv (Fin.natAdd n i) (slackDeterminant g) =
          MvPolynomial.pderiv (Fin.natAdd n i)
            (squareSlackSubstitution (slackValueDeterminant g)) := by
              rw [squareSlackSubstitution_slackValueDeterminant]
      _ = _ := pderiv_slack_squareSlackSubstitution
        (slackValueDeterminant g) i
  rw [slackW, hd, pderiv_slack_liftBasePolynomial_eq_zero,
    mul_zero, add_zero]
  have htwo : (2 : MvPolynomial (Fin (n + m)) ℝ) =
      MvPolynomial.C 2 :=
    (map_natCast
      (MvPolynomial.C : ℝ →+* MvPolynomial (Fin (n + m)) ℝ) 2).symm
  have hfour :
      (MvPolynomial.C 2 : MvPolynomial (Fin (n + m)) ℝ) *
          MvPolynomial.C 2 = MvPolynomial.C 4 := by
    rw [← map_mul]
    norm_num
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  rw [htwo]
  calc
    MvPolynomial.C 2 * liftBasePolynomial p *
        (MvPolynomial.C 2 * X (Fin.natAdd n i) *
          squareSlackSubstitution
            (MvPolynomial.pderiv (Fin.natAdd n i)
              (slackValueDeterminant g))) =
      (MvPolynomial.C 2 * MvPolynomial.C 2) * liftBasePolynomial p *
        X (Fin.natAdd n i) *
          squareSlackSubstitution
            (MvPolynomial.pderiv (Fin.natAdd n i)
              (slackValueDeterminant g)) := by ring
    _ = _ := by rw [hfour]

end CQCInternal
end OptimalConvergenceRates

end
