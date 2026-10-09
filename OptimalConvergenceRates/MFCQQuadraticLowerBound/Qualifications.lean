/-
  Constraint qualifications for the fixed MFCQ example.
-/
import OptimalConvergenceRates.MFCQQuadraticLowerBound.GradientFormulas

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.MFCQQuadraticLowerBound

/-- Feasible points lie in the unit ball and have `0 ≤ t ≤ 1`. -/
theorem feasible_coordinate_bounds {z : Fin 3 → ℝ} (hz : z ∈ feasibleSet) :
    z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 ≤ 1 ∧ 0 ≤ z 2 ∧ z 2 ≤ 1 := by
  have hb := hz (4 : Fin 5)
  simp only [eval_generator_four] at hb
  have ht0 := feasible_t_nonneg hz
  have ht1 : z 2 ≤ 1 := by
    nlinarith [sq_nonneg (z 0), sq_nonneg (z 1), sq_nonneg (z 2 - 1)]
  exact ⟨by linarith, ht0, ht1⟩

/-- The explicit direction used in the note's MFCQ proof. -/
def mfcqDirection (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-z 0, -z 1, (1 : ℝ) / 2 - z 2]

private theorem active_direction_positive {z : Fin 3 → ℝ}
    (hz : z ∈ feasibleSet) (i : Fin 5)
    (hi : eval z (generators i) = 0) :
    0 < ∑ j : Fin 3,
      gradientAt (generators i) z j * mfcqDirection z j := by
  have ht := feasible_coordinate_bounds hz
  fin_cases i
  · change eval z (generators 0) = 0 at hi
    change 0 < ∑ j : Fin 3,
      gradientAt (generators 0) z j * mfcqDirection z j
    have hactive : z 2 - (z 0 ^ 2 - 3 * z 1 ^ 2) = 0 := by
      simpa only [eval_generator_zero] using hi
    rw [gradient_generator_zero]
    simp [mfcqDirection, Fin.sum_univ_succ]
    nlinarith
  · change eval z (generators 1) = 0 at hi
    change 0 < ∑ j : Fin 3,
      gradientAt (generators 1) z j * mfcqDirection z j
    have hactive : z 2 - (z 1 ^ 2 - 3 * z 0 ^ 2) = 0 := by
      simpa only [eval_generator_one] using hi
    rw [gradient_generator_one]
    simp [mfcqDirection, Fin.sum_univ_succ]
    nlinarith
  · change eval z (generators 2) = 0 at hi
    change 0 < ∑ j : Fin 3,
      gradientAt (generators 2) z j * mfcqDirection z j
    have hactive : z 2 - (4 * z 0 * z 1 - z 0 ^ 2 - z 1 ^ 2) = 0 := by
      simpa only [eval_generator_two] using hi
    rw [gradient_generator_two]
    simp [mfcqDirection, Fin.sum_univ_succ]
    nlinarith
  · change eval z (generators 3) = 0 at hi
    change 0 < ∑ j : Fin 3,
      gradientAt (generators 3) z j * mfcqDirection z j
    have hactive : z 2 - (-4 * z 0 * z 1 - z 0 ^ 2 - z 1 ^ 2) = 0 := by
      simpa only [eval_generator_three] using hi
    rw [gradient_generator_three]
    simp [mfcqDirection, Fin.sum_univ_succ]
    nlinarith
  · change eval z (generators 4) = 0 at hi
    change 0 < ∑ j : Fin 3,
      gradientAt (generators 4) z j * mfcqDirection z j
    have hball : 1 - z 0 ^ 2 - z 1 ^ 2 - z 2 ^ 2 = 0 := by
      simpa only [eval_generator_four] using hi
    rw [gradient_generator_four]
    simp [mfcqDirection, Fin.sum_univ_succ]
    nlinarith

/-- MFCQ holds at every feasible point. -/
theorem mfcq_everywhere : ∀ z ∈ feasibleSet, MFCQAt generators z := by
  intro z hz
  exact ⟨hz, mfcqDirection z, fun i hi ↦ active_direction_positive hz i hi⟩

/-- CQC/LICQ fails at the unique minimizer because its first four active
gradients are all `(0,0,1)`. -/
theorem cqc_fails_at_origin : ¬ CQCAt generators origin := by
  rintro ⟨_, hlin⟩
  let i₀ : {i : Fin 5 // eval origin (generators i) = 0} :=
    ⟨0, by simp [origin, generators]⟩
  let i₁ : {i : Fin 5 // eval origin (generators i) = 0} :=
    ⟨1, by simp [origin, generators]⟩
  have hne : i₀ ≠ i₁ := by
    intro h
    have hval := congrArg Subtype.val h
    norm_num [i₀, i₁] at hval
  apply hne
  apply hlin.injective
  simp [i₀, i₁, origin]

end OptimalConvergenceRates.MFCQQuadraticLowerBound

end
