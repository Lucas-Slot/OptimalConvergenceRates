/-
  Geometry of the fixed three-variable sharp Archimedean example.
-/
import OptimalConvergenceRates.GeneralArchimedean.ArchimedeanGeometry
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.Defs

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

/-- Concrete description of the sharp example's feasible set. -/
theorem mem_sharpArchimedeanSet_iff (x : Fin 3 → ℝ) :
    x ∈ KrivineStengle.basicClosedSet sharpArchimedeanGenerators ↔
      0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 ∧
        x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 ≤ 1 := by
  constructor
  · intro hx
    have ha : 0 ≤ x 0 := by
      simpa [sharpArchimedeanGenerators, KrivineStengle.sharpSeedGenerators,
        KrivineStengle.sharpSeedA] using hx (0 : Fin 4)
    have hb : 0 ≤ x 1 := by
      simpa [sharpArchimedeanGenerators, KrivineStengle.sharpSeedGenerators,
        KrivineStengle.sharpSeedB] using hx (1 : Fin 4)
    have hw : 0 ≤ x 2 * x 0 * x 1 + x 2 ^ 5 := by
      simpa [sharpArchimedeanGenerators, KrivineStengle.sharpSeedGenerators,
        KrivineStengle.sharpSeedW, KrivineStengle.sharpSeedA,
        KrivineStengle.sharpSeedB, KrivineStengle.sharpSeedZ] using hx (2 : Fin 4)
    have hz : 0 ≤ x 2 := by
      by_contra hnz
      have hzneg : x 2 < 0 := lt_of_not_ge hnz
      have hz2 : 0 < x 2 ^ 2 := sq_pos_of_neg hzneg
      have hz4 : 0 < x 2 ^ 4 := by
        rw [show x 2 ^ 4 = (x 2 ^ 2) * (x 2 ^ 2) by ring]
        exact mul_pos hz2 hz2
      have hab : 0 ≤ x 0 * x 1 := mul_nonneg ha hb
      have hfactor : x 2 * x 0 * x 1 + x 2 ^ 5 =
          x 2 * (x 0 * x 1 + x 2 ^ 4) := by ring
      rw [hfactor] at hw
      exact (not_lt_of_ge hw)
        (mul_neg_of_neg_of_pos hzneg (add_pos_of_nonneg_of_pos hab hz4))
    have hball : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 ≤ 1 := by
      have h := hx (3 : Fin 4)
      simp [sharpArchimedeanGenerators, KrivineStengle.sharpSeedGenerators,
        KrivineStengle.sharpSeedA, KrivineStengle.sharpSeedB,
        KrivineStengle.sharpSeedZ] at h
      linarith
    exact ⟨ha, hb, hz, hball⟩
  · rintro ⟨ha, hb, hz, hball⟩ i
    fin_cases i
    · simpa [sharpArchimedeanGenerators, KrivineStengle.sharpSeedGenerators,
        KrivineStengle.sharpSeedA] using ha
    · simpa [sharpArchimedeanGenerators, KrivineStengle.sharpSeedGenerators,
        KrivineStengle.sharpSeedB] using hb
    · simpa [sharpArchimedeanGenerators, KrivineStengle.sharpSeedGenerators,
        KrivineStengle.sharpSeedW, KrivineStengle.sharpSeedZ,
        KrivineStengle.sharpSeedA, KrivineStengle.sharpSeedB] using
          add_nonneg (mul_nonneg (mul_nonneg hz ha) hb) (pow_nonneg hz 5)
    · simp [sharpArchimedeanGenerators, KrivineStengle.sharpSeedGenerators,
        KrivineStengle.sharpSeedA, KrivineStengle.sharpSeedB,
        KrivineStengle.sharpSeedZ]
      linarith

/-- The sharp example is Archimedean, witnessed by its fourth generator. -/
theorem sharpArchimedean_isArchimedean :
    IsArchimedean sharpArchimedeanGenerators := by
  refine ⟨1, (sharpArchimedeanGenerators (3 : Fin 4)).totalDegree, by norm_num, ?_⟩
  have hgen := genQuadraticModule_generator sharpArchimedeanGenerators (3 : Fin 4)
  have heq :
      C (1 : ℝ) - ∑ i : Fin 3, (X i : MvPolynomial (Fin 3) ℝ) ^ 2 =
        sharpArchimedeanGenerators (3 : Fin 4) := by
    simp [sharpArchimedeanGenerators, KrivineStengle.sharpSeedGenerators,
      KrivineStengle.sharpSeedA, KrivineStengle.sharpSeedB,
      KrivineStengle.sharpSeedZ, Fin.sum_univ_succ]
    ring
  rw [heq]
  exact hgen

/-- The origin is feasible for the sharp example. -/
theorem sharpArchimedean_origin_mem :
    (fun _ : Fin 3 ↦ (0 : ℝ)) ∈
      KrivineStengle.basicClosedSet sharpArchimedeanGenerators := by
  rw [mem_sharpArchimedeanSet_iff]
  norm_num

theorem sharpArchimedean_set_nonempty :
    (KrivineStengle.basicClosedSet sharpArchimedeanGenerators).Nonempty :=
  ⟨fun _ ↦ 0, sharpArchimedean_origin_mem⟩

/-- The objective is nonnegative on the sharp feasible set. -/
theorem sharpArchimedeanObjective_nonnegOn :
    IsNonnegOn sharpArchimedeanObjective
      (KrivineStengle.basicClosedSet sharpArchimedeanGenerators) := by
  intro x hx
  have hz := (mem_sharpArchimedeanSet_iff x).mp hx |>.2.2.1
  simpa [sharpArchimedeanObjective, sharpArchimedeanZ,
    KrivineStengle.sharpSeedZ] using hz

/-- The minimum of the sharp objective is exactly zero. -/
theorem sharpArchimedeanObjective_minimum :
    polynomialMinimum sharpArchimedeanGenerators sharpArchimedeanObjective = 0 := by
  apply le_antisymm
  · have h := polynomialMinimum_le_eval sharpArchimedean_isArchimedean
      sharpArchimedeanObjective sharpArchimedean_origin_mem
    simpa [sharpArchimedeanObjective, sharpArchimedeanZ,
      KrivineStengle.sharpSeedZ] using h
  · obtain ⟨x, hx, heq⟩ := polynomialMinimum_mem sharpArchimedean_set_nonempty
      sharpArchimedean_isArchimedean sharpArchimedeanObjective
    rw [← heq]
    exact sharpArchimedeanObjective_nonnegOn x hx

end OptimalConvergenceRates.GeneralArchimedean

end
