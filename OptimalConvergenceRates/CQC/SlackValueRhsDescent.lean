import OptimalConvergenceRates.CQC.SlackValueSlackWDescent

/-! Descent of the vector inside the adjugate correction. -/

noncomputable section

open MvPolynomial Finset Matrix

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

theorem slackJacobian_mulVec_slackW_apply
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (i : Fin m) :
    ((slackJacobianPolynomial g) *ᵥ slackW g p) i =
      (∑ j : Fin n,
        liftBasePolynomial (MvPolynomial.pderiv j (g i)) *
          slackW g p (Fin.castAdd m j)) -
      MvPolynomial.C 8 * liftBasePolynomial p *
        (X (Fin.natAdd n i)) ^ 2 *
        squareSlackSubstitution
          (MvPolynomial.pderiv (Fin.natAdd n i)
            (slackValueDeterminant g)) := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_add]
  simp only [slackJacobianPolynomial, pderiv_slackPolynomial_base,
    pderiv_slackPolynomial_slack]
  have hslack :
      ∑ k : Fin m,
          (if k = i then -(2 • X (Fin.natAdd n i)) else 0) *
            slackW g p (Fin.natAdd n k) =
        -(MvPolynomial.C 8 * liftBasePolynomial p *
          (X (Fin.natAdd n i)) ^ 2 *
          squareSlackSubstitution
            (MvPolynomial.pderiv (Fin.natAdd n i)
              (slackValueDeterminant g))) := by
    rw [Finset.sum_eq_single i]
    · simp only [ite_eq_left, slackW_slack_eq, neg_mul]
      have htwo : (2 : MvPolynomial (Fin (n + m)) ℝ) =
          MvPolynomial.C 2 :=
        (map_natCast
          (MvPolynomial.C : ℝ →+* MvPolynomial (Fin (n + m)) ℝ) 2).symm
      have height :
          (MvPolynomial.C 2 : MvPolynomial (Fin (n + m)) ℝ) *
              MvPolynomial.C 4 = MvPolynomial.C 8 := by
        rw [← map_mul]
        norm_num
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      rw [htwo]
      calc
        -(MvPolynomial.C 2 * X (Fin.natAdd n i) *
            (MvPolynomial.C 4 * liftBasePolynomial p *
              X (Fin.natAdd n i) *
              squareSlackSubstitution
                (MvPolynomial.pderiv (Fin.natAdd n i)
                  (slackValueDeterminant g)))) =
          -((MvPolynomial.C 2 * MvPolynomial.C 4) *
            liftBasePolynomial p * (X (Fin.natAdd n i)) ^ 2 *
              squareSlackSubstitution
                (MvPolynomial.pderiv (Fin.natAdd n i)
                  (slackValueDeterminant g))) := by ring
        _ = _ := by rw [height]
    · intro k _ hki
      simp [hki]
    · simp
  rw [hslack]
  ring

@[simp]
theorem squareSlackSubstitution_slackValueCorrectionRhs
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (i : Fin m) :
    squareSlackSubstitution (slackValueCorrectionRhs g p i) =
      ((slackJacobianPolynomial g) *ᵥ slackW g p) i := by
  rw [slackJacobian_mulVec_slackW_apply]
  simp [slackValueCorrectionRhs]

end CQCInternal
end OptimalConvergenceRates

end
