/-
  Feasible geometry and Archimedeanity of the fixed MFCQ example.
-/
import OptimalConvergenceRates.MFCQQuadraticLowerBound.Defs
import OptimalConvergenceRates.GeneralArchimedean.ArchimedeanGeometry

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.MFCQQuadraticLowerBound

@[simp] theorem eval_q₁ (z : Fin 3 → ℝ) :
    eval z q₁ = z 0 ^ 2 - 3 * z 1 ^ 2 := by simp [q₁, u, v]

@[simp] theorem eval_q₂ (z : Fin 3 → ℝ) :
    eval z q₂ = z 1 ^ 2 - 3 * z 0 ^ 2 := by simp [q₂, u, v]

@[simp] theorem eval_q₃ (z : Fin 3 → ℝ) :
    eval z q₃ = 4 * z 0 * z 1 - z 0 ^ 2 - z 1 ^ 2 := by
  simp [q₃, u, v]

@[simp] theorem eval_q₄ (z : Fin 3 → ℝ) :
    eval z q₄ = -4 * z 0 * z 1 - z 0 ^ 2 - z 1 ^ 2 := by
  simp [q₄, u, v]

@[simp] theorem eval_ball (z : Fin 3 → ℝ) :
    eval z ball = 1 - z 0 ^ 2 - z 1 ^ 2 - z 2 ^ 2 := by
  simp [ball, u, v, t]

@[simp] theorem eval_objective (z : Fin 3 → ℝ) :
    eval z objective = z 2 := by simp [objective, t]

@[simp] theorem eval_generator_zero (z : Fin 3 → ℝ) :
    eval z (generators 0) = z 2 - (z 0 ^ 2 - 3 * z 1 ^ 2) := by
  simp [generators]

@[simp] theorem eval_generator_one (z : Fin 3 → ℝ) :
    eval z (generators 1) = z 2 - (z 1 ^ 2 - 3 * z 0 ^ 2) := by
  simp [generators]

@[simp] theorem eval_generator_two (z : Fin 3 → ℝ) :
    eval z (generators 2) =
      z 2 - (4 * z 0 * z 1 - z 0 ^ 2 - z 1 ^ 2) := by
  simp [generators]

@[simp] theorem eval_generator_three (z : Fin 3 → ℝ) :
    eval z (generators 3) =
      z 2 - (-4 * z 0 * z 1 - z 0 ^ 2 - z 1 ^ 2) := by
  simp [generators]

@[simp] theorem eval_generator_four (z : Fin 3 → ℝ) :
    eval z (generators 4) = 1 - z 0 ^ 2 - z 1 ^ 2 - z 2 ^ 2 := by
  simp [generators]

/-- Every feasible point has nonnegative objective value. -/
theorem feasible_t_nonneg {z : Fin 3 → ℝ} (hz : z ∈ feasibleSet) :
    0 ≤ z 2 := by
  have h₁ := hz (0 : Fin 5)
  have h₂ := hz (1 : Fin 5)
  have h₃ := hz (2 : Fin 5)
  have h₄ := hz (3 : Fin 5)
  simp only [eval_generator_zero] at h₁
  simp only [eval_generator_one] at h₂
  simp only [eval_generator_two] at h₃
  simp only [eval_generator_three] at h₄
  let R : ℝ := z 0 ^ 2 + z 1 ^ 2
  let Xc : ℝ := z 0 ^ 2 - z 1 ^ 2
  let Yc : ℝ := 2 * z 0 * z 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hs : 0 ≤ z 2 + R := by
    dsimp [R]
    nlinarith
  have hXp : 2 * Xc ≤ z 2 + R := by dsimp [Xc, R]; nlinarith
  have hXm : -(2 * Xc) ≤ z 2 + R := by dsimp [Xc, R]; nlinarith
  have hYp : 2 * Yc ≤ z 2 + R := by dsimp [Yc, R]; nlinarith
  have hYm : -(2 * Yc) ≤ z 2 + R := by dsimp [Yc, R]; nlinarith
  have hXsq : (2 * Xc) ^ 2 ≤ (z 2 + R) ^ 2 := by
    have hp : 0 ≤ (z 2 + R) - 2 * Xc := sub_nonneg.mpr hXp
    have hm : 0 ≤ (z 2 + R) + 2 * Xc := by linarith
    nlinarith [mul_nonneg hp hm]
  have hYsq : (2 * Yc) ^ 2 ≤ (z 2 + R) ^ 2 := by
    have hp : 0 ≤ (z 2 + R) - 2 * Yc := sub_nonneg.mpr hYp
    have hm : 0 ≤ (z 2 + R) + 2 * Yc := by linarith
    nlinarith [mul_nonneg hp hm]
  have hidentity : Xc ^ 2 + Yc ^ 2 = R ^ 2 := by
    dsimp [Xc, Yc, R]
    ring
  by_contra ht
  have htneg : z 2 < 0 := lt_of_not_ge ht
  have hRpos : 0 < R := by
    by_contra h
    have hRzero : R = 0 := le_antisymm (le_of_not_gt h) hR
    dsimp [R] at hRzero
    have hu : z 0 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (z 1)])
    have hv : z 1 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (z 0)])
    rw [hu, hv] at h₁
    norm_num at h₁
    exact (not_lt_of_ge h₁) htneg
  nlinarith

/-- The origin is feasible. -/
theorem origin_mem : origin ∈ feasibleSet := by
  intro i
  fin_cases i <;> simp [origin, generators]

/-- A feasible point with objective zero is the origin. -/
theorem eq_origin_of_feasible_of_t_eq_zero {z : Fin 3 → ℝ}
    (hz : z ∈ feasibleSet) (ht : z 2 = 0) : z = origin := by
  have h₁ := hz (0 : Fin 5)
  have h₂ := hz (1 : Fin 5)
  have h₃ := hz (2 : Fin 5)
  have h₄ := hz (3 : Fin 5)
  simp only [eval_generator_zero, ht, zero_sub, neg_nonneg] at h₁
  simp only [eval_generator_one, ht, zero_sub, neg_nonneg] at h₂
  simp only [eval_generator_two, ht, zero_sub, neg_nonneg] at h₃
  simp only [eval_generator_three, ht, zero_sub, neg_nonneg] at h₄
  let R : ℝ := z 0 ^ 2 + z 1 ^ 2
  let Xc : ℝ := z 0 ^ 2 - z 1 ^ 2
  let Yc : ℝ := 2 * z 0 * z 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hXp : 2 * Xc ≤ R := by dsimp [Xc, R]; nlinarith
  have hXm : -(2 * Xc) ≤ R := by dsimp [Xc, R]; nlinarith
  have hYp : 2 * Yc ≤ R := by dsimp [Yc, R]; nlinarith
  have hYm : -(2 * Yc) ≤ R := by dsimp [Yc, R]; nlinarith
  have hXsq : (2 * Xc) ^ 2 ≤ R ^ 2 := by
    have hp : 0 ≤ R - 2 * Xc := sub_nonneg.mpr hXp
    have hm : 0 ≤ R + 2 * Xc := by linarith
    nlinarith [mul_nonneg hp hm]
  have hYsq : (2 * Yc) ^ 2 ≤ R ^ 2 := by
    have hp : 0 ≤ R - 2 * Yc := sub_nonneg.mpr hYp
    have hm : 0 ≤ R + 2 * Yc := by linarith
    nlinarith [mul_nonneg hp hm]
  have hidentity : Xc ^ 2 + Yc ^ 2 = R ^ 2 := by
    dsimp [Xc, Yc, R]
    ring
  have hRzero : R = 0 := by nlinarith
  have hu : z 0 = 0 := by
    dsimp [R] at hRzero
    nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
  have hv : z 1 = 0 := by
    dsimp [R] at hRzero
    nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
  funext i
  fin_cases i <;> simp [origin, hu, hv, ht]

/-- The fifth generator directly supplies the Archimedean ball certificate. -/
theorem isArchimedean : GeneralArchimedean.IsArchimedean generators := by
  refine ⟨1, (generators 4).totalDegree, by norm_num, ?_⟩
  have hgen := genQuadraticModule_generator generators (4 : Fin 5)
  have heq :
      C (1 : ℝ) - ∑ i : Fin 3, (X i : MvPolynomial (Fin 3) ℝ) ^ 2 =
        generators 4 := by
    simp [generators, ball, u, v, t, Fin.sum_univ_succ]
    ring
  rw [heq]
  exact hgen

/-- Bundled geometry theorem used by the public statement file. -/
theorem archimedean_and_unique_minimum_proof :
    GeneralArchimedean.IsArchimedean generators ∧
      origin ∈ feasibleSet ∧
      eval origin objective = 0 ∧
      ∀ z ∈ feasibleSet, 0 ≤ eval z objective ∧
        (eval z objective = 0 → z = origin) := by
  refine ⟨isArchimedean, origin_mem, by simp [origin], ?_⟩
  intro z hz
  rw [eval_objective]
  exact ⟨feasible_t_nonneg hz, eq_origin_of_feasible_of_t_eq_zero hz⟩

end OptimalConvergenceRates.MFCQQuadraticLowerBound

end
