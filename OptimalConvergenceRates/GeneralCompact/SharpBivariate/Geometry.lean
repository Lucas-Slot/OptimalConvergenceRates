/- Geometry of the fixed bivariate sharp Schmüdgen example. -/
import OptimalConvergenceRates.GeneralCompact.Hierarchy

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralCompact

/-- The displayed quadratic module is Archimedean because the ball is a
generator. -/
theorem sharp_isArchimedean :
    GeneralArchimedean.IsArchimedean sharpGenerators := by
  refine ⟨1, sharpBall.totalDegree, by norm_num, ?_⟩
  have hgen := genQuadraticModule_generator sharpGenerators (1 : Fin 2)
  have heq :
      C (1 : ℝ) - ∑ i : Fin 2, (X i : MvPolynomial (Fin 2) ℝ) ^ 2 =
        sharpGenerators (1 : Fin 2) := by
    simp [sharpGenerators, sharpBall, sharpA, sharpZ, Fin.sum_univ_succ]
    ring
  rw [heq]
  exact hgen

/-- Concrete description of the bivariate feasible set. -/
theorem mem_sharpSet_iff (x : Fin 2 → ℝ) :
    x ∈ KrivineStengle.basicClosedSet sharpGenerators ↔
      0 ≤ x 1 ∧ x 0 ^ 2 + x 1 ^ 2 ≤ 1 := by
  constructor
  · intro hx
    have hh : 0 ≤ x 1 * (x 0 ^ 2 + x 1 ^ 2) := by
      simpa [sharpGenerators, sharpH, sharpA, sharpZ] using hx (0 : Fin 2)
    have hz : 0 ≤ x 1 := by
      by_contra hnz
      have hzneg : x 1 < 0 := lt_of_not_ge hnz
      have hfactor : 0 < x 0 ^ 2 + x 1 ^ 2 :=
        add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_neg hzneg)
      exact (not_lt_of_ge hh) (mul_neg_of_neg_of_pos hzneg hfactor)
    have hball := hx (1 : Fin 2)
    simp [sharpGenerators, sharpBall, sharpA, sharpZ] at hball
    exact ⟨hz, by linarith⟩
  · rintro ⟨hz, hball⟩ i
    fin_cases i
    · simp [sharpGenerators, sharpH, sharpA, sharpZ]
      exact mul_nonneg hz (add_nonneg (sq_nonneg _) (sq_nonneg _))
    · simp [sharpGenerators, sharpBall, sharpA, sharpZ]
      linarith

/-- The origin is feasible. -/
theorem sharp_origin_mem :
    (fun _ : Fin 2 ↦ (0 : ℝ)) ∈
      KrivineStengle.basicClosedSet sharpGenerators := by
  rw [mem_sharpSet_iff]
  norm_num

theorem sharp_set_nonempty :
    (KrivineStengle.basicClosedSet sharpGenerators).Nonempty :=
  ⟨fun _ ↦ 0, sharp_origin_mem⟩

theorem sharp_set_compact :
    IsCompact (KrivineStengle.basicClosedSet sharpGenerators) :=
  sharp_isArchimedean.isCompact_basicClosedSet

/-- The linear objective is nonnegative on the feasible upper half-ball. -/
theorem sharpObjective_nonnegOn :
    IsNonnegOn sharpObjective
      (KrivineStengle.basicClosedSet sharpGenerators) := by
  intro x hx
  simpa [sharpObjective, sharpZ] using (mem_sharpSet_iff x).mp hx |>.1

/-- The minimum of the sharp objective is zero. -/
theorem sharpObjective_minimum :
    GeneralArchimedean.polynomialMinimum sharpGenerators sharpObjective = 0 := by
  apply le_antisymm
  · have h := polynomialMinimum_le_eval_of_compact sharp_set_compact
      sharpObjective sharp_origin_mem
    simpa [sharpObjective, sharpZ] using h
  · obtain ⟨x, hx, heq⟩ := polynomialMinimum_mem_of_compact
      sharp_set_nonempty sharp_set_compact sharpObjective
    rw [← heq]
    exact sharpObjective_nonnegOn x hx

end OptimalConvergenceRates.GeneralCompact

end
