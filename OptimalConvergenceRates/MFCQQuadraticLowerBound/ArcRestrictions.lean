/-
  The three scaled parabolic arcs used by the SOS obstruction.
-/
import OptimalConvergenceRates.MFCQQuadraticLowerBound.CertificateExtraction

noncomputable section

open Finset MvPolynomial Polynomial

namespace OptimalConvergenceRates.MFCQQuadraticLowerBound

/-- Polynomial substitutions for `gamma_j(tau / 2)`. -/
def scaledArcSubstitution (j : Fin 3) : Fin 3 → Polynomial ℝ :=
  match j with
  | 0 => ![0, 0, Polynomial.C (1 / 4) * Polynomial.X ^ 2]
  | 1 => ![Polynomial.C (1 / 2) * Polynomial.X, 0, Polynomial.C (1 / 4) * Polynomial.X ^ 2]
  | 2 => ![0, Polynomial.C (1 / 2) * Polynomial.X, Polynomial.C (1 / 4) * Polynomial.X ^ 2]

/-- Restriction of a multivariate polynomial to a scaled parabolic arc. -/
def restrictScaledArc (j : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    Polynomial ℝ :=
  MvPolynomial.aeval (scaledArcSubstitution j) p

/-- The corresponding point on a scaled arc. -/
def scaledArcPoint (j : Fin 3) (s : ℝ) : Fin 3 → ℝ :=
  fun i ↦ (scaledArcSubstitution j i).eval s

@[simp] theorem restrictScaledArc_eval (j : Fin 3) (s : ℝ)
    (p : MvPolynomial (Fin 3) ℝ) :
    (restrictScaledArc j p).eval s = MvPolynomial.eval (scaledArcPoint j s) p := by
  rw [restrictScaledArc]
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X,
        Polynomial.eval_mul]
      rw [hp]
      rfl

theorem scaledArcPoint_zero (j : Fin 3) : scaledArcPoint j 0 = origin := by
  funext i
  fin_cases j <;> fin_cases i <;>
    simp [scaledArcPoint, scaledArcSubstitution, origin, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]

@[simp] theorem restrictScaledArc_coeff_zero (j : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) :
    (restrictScaledArc j p).coeff 0 = MvPolynomial.eval origin p := by
  rw [Polynomial.coeff_zero_eq_eval_zero, restrictScaledArc_eval,
    scaledArcPoint_zero]

theorem restrictScaledArc_natDegree_le (j : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) :
    (restrictScaledArc j p).natDegree ≤ 2 * p.totalDegree := by
  have h := MvPolynomial.aeval_natDegree_le p (le_refl p.totalDegree)
    (scaledArcSubstitution j) (n := 2) (by
      intro i
      fin_cases j <;> fin_cases i <;>
        simp [scaledArcSubstitution, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two])
  simpa [Nat.mul_comm] using h

/-- The coefficient of `tau^2` in each restricted generator. -/
def arcGeneratorCoeffTwo (j : Fin 3) : Fin 5 → ℝ :=
  match j with
  | 0 => ![1 / 4, 1 / 4, 1 / 4, 1 / 4, 0]
  | 1 => ![0, 1, 1 / 2, 1 / 2, -1 / 4]
  | 2 => ![1, 0, 1 / 2, 1 / 2, -1 / 4]

@[simp] theorem restrictScaledArc_generator_coeff_zero (j : Fin 3)
    (i : Fin 5) :
    (restrictScaledArc j (generators i)).coeff 0 = if i = 4 then 1 else 0 := by
  fin_cases j <;> fin_cases i <;>
    norm_num [restrictScaledArc, scaledArcSubstitution, generators,
      ball, q₁, q₂, q₃, q₄, u, v, t, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, pow_two, Polynomial.coeff_mul, Finset.antidiagonal]
    <;> simp [Fin.ext_iff]

@[simp] theorem restrictScaledArc_generator_coeff_one (j : Fin 3)
    (i : Fin 5) :
    (restrictScaledArc j (generators i)).coeff 1 = 0 := by
  fin_cases j <;> fin_cases i <;>
    norm_num [restrictScaledArc, scaledArcSubstitution, generators,
      ball, q₁, q₂, q₃, q₄, u, v, t, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, pow_two, Polynomial.coeff_mul, Finset.antidiagonal]
  all_goals
    rw [Polynomial.coeff_one]
    norm_num

@[simp] theorem restrictScaledArc_generator_coeff_two (j : Fin 3)
    (i : Fin 5) :
    (restrictScaledArc j (generators i)).coeff 2 =
      arcGeneratorCoeffTwo j i := by
  fin_cases j <;> fin_cases i <;>
    norm_num [restrictScaledArc, scaledArcSubstitution, arcGeneratorCoeffTwo,
      generators, ball, q₁, q₂, q₃, q₄, u, v, t, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, pow_two, Polynomial.coeff_mul, Finset.antidiagonal]
  all_goals
    rw [Polynomial.coeff_one]
    norm_num

@[simp] theorem restrictScaledArc_objective (j : Fin 3) :
    restrictScaledArc j objective = Polynomial.C (1 / 4) * Polynomial.X ^ 2 := by
  fin_cases j <;>
    simp [restrictScaledArc, scaledArcSubstitution, objective, t, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two]

theorem scaledArc_generators_nonneg (j : Fin 3) (i : Fin 5)
    {s : ℝ} (hs : |s| ≤ 1) :
    0 ≤ MvPolynomial.eval (scaledArcPoint j s) (generators i) := by
  rw [← restrictScaledArc_eval]
  have hs' := abs_le.mp hs
  have hsSq : s ^ 2 ≤ 1 := by nlinarith
  have hsFour : s ^ 4 ≤ s ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsSq (sq_nonneg s)]
  fin_cases j <;> fin_cases i <;>
    norm_num [restrictScaledArc, scaledArcSubstitution, generators,
      ball, q₁, q₂, q₃, q₄, u, v, t, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, pow_two, Polynomial.coeff_mul, Finset.antidiagonal] <;>
    nlinarith [sq_nonneg s, sq_nonneg (s ^ 2 - 2)]

theorem scaledArc_ball_ge_half (j : Fin 3) {s : ℝ} (hs : |s| ≤ 1) :
    (1 / 2 : ℝ) ≤ MvPolynomial.eval (scaledArcPoint j s) ball := by
  have hs' := abs_le.mp hs
  have hsSq : s ^ 2 ≤ 1 := by nlinarith
  have hsFour : s ^ 4 ≤ s ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsSq (sq_nonneg s)]
  fin_cases j <;>
    norm_num [scaledArcPoint, scaledArcSubstitution, ball, u, v, t, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two] <;>
    nlinarith [sq_nonneg s, sq_nonneg (s ^ 2 - 2)]

/-- The central arc is even, so every restricted polynomial has zero
linear coefficient. -/
theorem restrictScaledArc_zero_coeff_one
    (p : MvPolynomial (Fin 3) ℝ) :
    (restrictScaledArc 0 p).coeff 1 = 0 := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [restrictScaledArc]
  | add p q hp hq =>
      rw [restrictScaledArc, map_add, Polynomial.coeff_add]
      change (restrictScaledArc 0 p).coeff 1 +
        (restrictScaledArc 0 q).coeff 1 = 0
      rw [hp, hq, add_zero]
  | mul_X p i hp =>
      fin_cases i
      · simp [restrictScaledArc, scaledArcSubstitution, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two]
      · simp [restrictScaledArc, scaledArcSubstitution, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two]
      · rw [restrictScaledArc]
        simp only [map_mul, MvPolynomial.aeval_X]
        rw [Polynomial.coeff_mul]
        norm_num [Finset.antidiagonal, scaledArcSubstitution, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two]

/-- The low coefficient formula used repeatedly in the jet calculation. -/
theorem coeff_two_mul (P Q : Polynomial ℝ) :
    (P * Q).coeff 2 =
      P.coeff 0 * Q.coeff 2 + P.coeff 1 * Q.coeff 1 +
        P.coeff 2 * Q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  norm_num [Finset.antidiagonal]
  ring

end OptimalConvergenceRates.MFCQQuadraticLowerBound

end
