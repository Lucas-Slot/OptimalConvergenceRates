/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/Motzkin/Algebra.lean

  Algebraic properties of the Motzkin sextic.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.Defs
import Mathlib.Analysis.MeanInequalities

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

namespace Motzkin

/-- The Motzkin sextic has total degree at most six. -/
theorem motzkinSextic_totalDegree_le_six : motzkinSextic.totalDegree ≤ 6 := by
  unfold motzkinSextic
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
      · calc
          ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 4 * X 1 ^ 2).totalDegree
              ≤ ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 4).totalDegree
                  + ((X 1 : MvPolynomial (Fin 3) ℝ) ^ 2).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
          _ = 6 := by simp [MvPolynomial.totalDegree_X_pow]
      · calc
          ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 * X 1 ^ 4).totalDegree
              ≤ ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2).totalDegree
                  + ((X 1 : MvPolynomial (Fin 3) ℝ) ^ 4).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
          _ = 6 := by simp [MvPolynomial.totalDegree_X_pow]
    · simp [MvPolynomial.totalDegree_X_pow]
  · calc
      (C 3 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 3) ℝ).totalDegree
          ≤ (C 3 * X 0 ^ 2 * X 1 ^ 2 : MvPolynomial (Fin 3) ℝ).totalDegree
              + ((X 2 : MvPolynomial (Fin 3) ℝ) ^ 2).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ (C 3 * X 0 ^ 2 : MvPolynomial (Fin 3) ℝ).totalDegree
              + ((X 1 : MvPolynomial (Fin 3) ℝ) ^ 2).totalDegree
              + ((X 2 : MvPolynomial (Fin 3) ℝ) ^ 2).totalDegree := by
        gcongr
        exact MvPolynomial.totalDegree_mul _ _
      _ ≤ (C 3 * X 0 ^ 2 : MvPolynomial (Fin 3) ℝ).totalDegree
              + 2 + 2 := by simp [MvPolynomial.totalDegree_X_pow]
      _ ≤ ((C 3 : MvPolynomial (Fin 3) ℝ).totalDegree
              + ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2).totalDegree) + 2 + 2 := by
        gcongr
        exact MvPolynomial.totalDegree_mul _ _
      _ = 6 := by simp [MvPolynomial.totalDegree_X_pow, MvPolynomial.totalDegree_C]

/-- Every square root in an SOS representation of the Motzkin sextic has
total degree at most three. -/
theorem motzkinSosSummand_totalDegree_le_three
    {N : ℕ} {Q : Fin N → MvPolynomial (Fin 3) ℝ}
    (hQ : motzkinSextic = ∑ i : Fin N, (Q i) ^ 2) :
    ∀ i, (Q i).totalDegree ≤ 3 := by
  exact sos_summand_totalDegree_le_of_sum_sq_totalDegree hQ
    (by simpa using motzkinSextic_totalDegree_le_six)


end Motzkin

end OptimalConvergenceRates

end
