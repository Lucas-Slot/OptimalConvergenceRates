/-
  The explicit global linear feasibility error bound.
-/
import OptimalConvergenceRates.MFCQQuadraticLowerBound.Qualifications

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.MFCQQuadraticLowerBound

theorem violation_nonneg (z : Fin 3 → ℝ) : 0 ≤ violation z := by
  simp [violation]

theorem generator_ge_neg_violation (z : Fin 3 → ℝ) (i : Fin 5) :
    -violation z ≤ eval z (generators i) := by
  fin_cases i
  · change -violation z ≤ eval z (generators 0)
    have h : -eval z (generators 0) ≤ violation z := by
      unfold violation
      exact (le_max_left _ _).trans (le_max_right _ _)
    linarith
  · change -violation z ≤ eval z (generators 1)
    have h : -eval z (generators 1) ≤ violation z := by
      unfold violation
      exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
    linarith
  · change -violation z ≤ eval z (generators 2)
    have h : -eval z (generators 2) ≤ violation z := by
      unfold violation
      exact (((le_max_left _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)
    linarith
  · change -violation z ≤ eval z (generators 3)
    have h : -eval z (generators 3) ≤ violation z := by
      unfold violation
      exact ((((le_max_left _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
    linarith
  · change -violation z ≤ eval z (generators 4)
    have h : -eval z (generators 4) ≤ violation z := by
      unfold violation
      exact ((((le_max_right _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
    linarith

/-- The first four almost-feasible inequalities already imply `t ≥ -ν`. -/
theorem t_ge_neg_violation (z : Fin 3 → ℝ) : -violation z ≤ z 2 := by
  let η := violation z
  have hη : 0 ≤ η := violation_nonneg z
  have h₁ := generator_ge_neg_violation z (0 : Fin 5)
  have h₂ := generator_ge_neg_violation z (1 : Fin 5)
  have h₃ := generator_ge_neg_violation z (2 : Fin 5)
  have h₄ := generator_ge_neg_violation z (3 : Fin 5)
  change -η ≤ eval z (generators 0) at h₁
  change -η ≤ eval z (generators 1) at h₂
  change -η ≤ eval z (generators 2) at h₃
  change -η ≤ eval z (generators 3) at h₄
  simp only [eval_generator_zero] at h₁
  simp only [eval_generator_one] at h₂
  simp only [eval_generator_two] at h₃
  simp only [eval_generator_three] at h₄
  let R : ℝ := z 0 ^ 2 + z 1 ^ 2
  let Xc : ℝ := z 0 ^ 2 - z 1 ^ 2
  let Yc : ℝ := 2 * z 0 * z 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hs : 0 ≤ z 2 + η + R := by dsimp [R]; nlinarith
  have hXp : 2 * Xc ≤ z 2 + η + R := by dsimp [Xc, R]; nlinarith
  have hXm : -(2 * Xc) ≤ z 2 + η + R := by dsimp [Xc, R]; nlinarith
  have hYp : 2 * Yc ≤ z 2 + η + R := by dsimp [Yc, R]; nlinarith
  have hYm : -(2 * Yc) ≤ z 2 + η + R := by dsimp [Yc, R]; nlinarith
  have hXsq : (2 * Xc) ^ 2 ≤ (z 2 + η + R) ^ 2 := by
    have hp : 0 ≤ (z 2 + η + R) - 2 * Xc := sub_nonneg.mpr hXp
    have hm : 0 ≤ (z 2 + η + R) + 2 * Xc := by linarith
    nlinarith [mul_nonneg hp hm]
  have hYsq : (2 * Yc) ^ 2 ≤ (z 2 + η + R) ^ 2 := by
    have hp : 0 ≤ (z 2 + η + R) - 2 * Yc := sub_nonneg.mpr hYp
    have hm : 0 ≤ (z 2 + η + R) + 2 * Yc := by linarith
    nlinarith [mul_nonneg hp hm]
  have hidentity : Xc ^ 2 + Yc ^ 2 = R ^ 2 := by
    dsimp [Xc, Yc, R]
    ring
  by_contra h
  have htneg : z 2 + η < 0 := by linarith
  have hRpos : 0 < R := by
    by_contra hzero
    have hRzero : R = 0 := le_antisymm (le_of_not_gt hzero) hR
    dsimp [R] at hRzero
    have hu : z 0 = 0 := by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
    have hv : z 1 = 0 := by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
    rw [hu, hv] at h₁
    norm_num at h₁
    linarith
  nlinarith

/-- The correction point used in the global error-bound proof. -/
def correctedPoint (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let η := violation z
  ![z 0 / (1 + 2 * η), z 1 / (1 + 2 * η),
    (z 2 + η) / (1 + 2 * η)]

/-- The correction map always lands in the feasible set. -/
theorem correctedPoint_mem (z : Fin 3 → ℝ) : correctedPoint z ∈ feasibleSet := by
  let η := violation z
  let d : ℝ := 1 + 2 * η
  have hη : 0 ≤ η := violation_nonneg z
  have hd : 0 < d := by dsimp [d]; positivity
  have ht : 0 ≤ z 2 + η := by
    have := t_ge_neg_violation z
    change -η ≤ z 2 at this
    linarith
  have hgi (i : Fin 5) : -η ≤ eval z (generators i) := by
    simpa [η] using generator_ge_neg_violation z i
  intro i
  fin_cases i
  · change 0 ≤ eval (correctedPoint z) (generators 0)
    have hbase := hgi (0 : Fin 5)
    simp only [eval_generator_zero] at hbase
    have hnum : 0 ≤ (z 2 + η) * d - (z 0 ^ 2 - 3 * z 1 ^ 2) := by
      dsimp [d]
      nlinarith [mul_nonneg hη ht]
    rw [eval_generator_zero]
    dsimp [correctedPoint, η, d]
    rw [show (z 2 + η) / d - ((z 0 / d) ^ 2 - 3 * (z 1 / d) ^ 2) =
        ((z 2 + η) * d - (z 0 ^ 2 - 3 * z 1 ^ 2)) / d ^ 2 by
      field_simp <;> ring]
    exact div_nonneg hnum (sq_nonneg d)
  · change 0 ≤ eval (correctedPoint z) (generators 1)
    have hbase := hgi (1 : Fin 5)
    simp only [eval_generator_one] at hbase
    have hnum : 0 ≤ (z 2 + η) * d - (z 1 ^ 2 - 3 * z 0 ^ 2) := by
      dsimp [d]
      nlinarith [mul_nonneg hη ht]
    rw [eval_generator_one]
    dsimp [correctedPoint, η, d]
    rw [show (z 2 + η) / d - ((z 1 / d) ^ 2 - 3 * (z 0 / d) ^ 2) =
        ((z 2 + η) * d - (z 1 ^ 2 - 3 * z 0 ^ 2)) / d ^ 2 by
      field_simp <;> ring]
    exact div_nonneg hnum (sq_nonneg d)
  · change 0 ≤ eval (correctedPoint z) (generators 2)
    have hbase := hgi (2 : Fin 5)
    simp only [eval_generator_two] at hbase
    have hnum : 0 ≤ (z 2 + η) * d -
        (4 * z 0 * z 1 - z 0 ^ 2 - z 1 ^ 2) := by
      dsimp [d]
      nlinarith [mul_nonneg hη ht]
    rw [eval_generator_two]
    dsimp [correctedPoint, η, d]
    rw [show (z 2 + η) / d -
        (4 * (z 0 / d) * (z 1 / d) - (z 0 / d) ^ 2 - (z 1 / d) ^ 2) =
        ((z 2 + η) * d -
          (4 * z 0 * z 1 - z 0 ^ 2 - z 1 ^ 2)) / d ^ 2 by
      field_simp <;> ring]
    exact div_nonneg hnum (sq_nonneg d)
  · change 0 ≤ eval (correctedPoint z) (generators 3)
    have hbase := hgi (3 : Fin 5)
    simp only [eval_generator_three] at hbase
    have hnum : 0 ≤ (z 2 + η) * d -
        (-4 * z 0 * z 1 - z 0 ^ 2 - z 1 ^ 2) := by
      dsimp [d]
      nlinarith [mul_nonneg hη ht]
    rw [eval_generator_three]
    dsimp [correctedPoint, η, d]
    rw [show (z 2 + η) / d -
        (-4 * (z 0 / d) * (z 1 / d) - (z 0 / d) ^ 2 - (z 1 / d) ^ 2) =
        ((z 2 + η) * d -
          (-4 * z 0 * z 1 - z 0 ^ 2 - z 1 ^ 2)) / d ^ 2 by
      field_simp <;> ring]
    exact div_nonneg hnum (sq_nonneg d)
  · change 0 ≤ eval (correctedPoint z) (generators 4)
    have hbase := hgi (4 : Fin 5)
    simp only [eval_generator_four] at hbase
    have hnorm : z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 ≤ 1 + η := by linarith
    have htupper : z 2 ≤ 1 + η := by
      nlinarith [sq_nonneg (z 0), sq_nonneg (z 1), sq_nonneg (z 2 - (1 + η))]
    have hnum : z 0 ^ 2 + z 1 ^ 2 + (z 2 + η) ^ 2 ≤ d ^ 2 := by
      dsimp [d]
      nlinarith [mul_nonneg hη (sub_nonneg.mpr htupper)]
    rw [eval_generator_four]
    dsimp [correctedPoint, η, d]
    rw [show 1 - (z 0 / d) ^ 2 - (z 1 / d) ^ 2 - ((z 2 + η) / d) ^ 2 =
        (d ^ 2 - (z 0 ^ 2 + z 1 ^ 2 + (z 2 + η) ^ 2)) / d ^ 2 by
      field_simp <;> ring]
    exact div_nonneg (sub_nonneg.mpr hnum) (sq_nonneg d)

/-- The correction point is within `3ν(z)` in Euclidean distance. -/
theorem dist_correctedPoint_le (z : Fin 3 → ℝ) :
    dist (WithLp.toLp 2 z) (WithLp.toLp 2 (correctedPoint z)) ≤
      3 * violation z := by
  let η := violation z
  let d : ℝ := 1 + 2 * η
  have hη : 0 ≤ η := violation_nonneg z
  have hd : 0 < d := by dsimp [d]; positivity
  have ht := t_ge_neg_violation z
  change -η ≤ z 2 at ht
  have hb := generator_ge_neg_violation z (4 : Fin 5)
  change -η ≤ eval z (generators 4) at hb
  simp only [eval_generator_four] at hb
  have hnorm : z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 ≤ 1 + η := by linarith
  have hbracket :
      4 * z 0 ^ 2 + 4 * z 1 ^ 2 + (2 * z 2 - 1) ^ 2 ≤ 9 * d ^ 2 := by
    dsimp [d]
    nlinarith [mul_nonneg hη hη]
  have hsq :
      dist (WithLp.toLp 2 z) (WithLp.toLp 2 (correctedPoint z)) ^ 2 ≤
        (3 * η) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    simp [Fin.sum_univ_succ, Real.dist_eq, correctedPoint]
    change (z 0 - z 0 / d) ^ 2 +
      ((z 1 - z 1 / d) ^ 2 + (z 2 - (z 2 + η) / d) ^ 2) ≤ (3 * η) ^ 2
    rw [show (z 0 - z 0 / d) ^ 2 +
          ((z 1 - z 1 / d) ^ 2 + (z 2 - (z 2 + η) / d) ^ 2) =
        η ^ 2 * (4 * z 0 ^ 2 + 4 * z 1 ^ 2 + (2 * z 2 - 1) ^ 2) / d ^ 2 by
      field_simp
      ring]
    have hscaled := mul_le_mul_of_nonneg_left hbracket (sq_nonneg η)
    have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
    apply (div_le_iff₀ hd2).2
    nlinarith
  have hdist0 : 0 ≤ dist (WithLp.toLp 2 z)
      (WithLp.toLp 2 (correctedPoint z)) := dist_nonneg
  change _ ≤ 3 * η
  nlinarith

/-- The public global linear feasibility bound. -/
theorem global_linear_error_bound_proof (z : Fin 3 → ℝ) :
    euclideanDistanceToSet z feasibleSet ≤ 3 * violation z := by
  have hmem : WithLp.toLp 2 (correctedPoint z) ∈
      WithLp.toLp 2 '' feasibleSet :=
    ⟨correctedPoint z, correctedPoint_mem z, rfl⟩
  exact (Metric.infDist_le_dist_of_mem hmem).trans (dist_correctedPoint_le z)

end OptimalConvergenceRates.MFCQQuadraticLowerBound

end
