/-
  Coefficient-size bookkeeping for real univariate polynomials and their
  substitution into multivariate polynomials.
-/
import OptimalConvergenceRates.BasicNotions.CoefficientNorm

noncomputable section

open Finset MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

/-- The coefficient `ℓ¹` norm of a real univariate polynomial.  The range
presentation is convenient for estimates involving `Polynomial.aeval`. -/
def polynomialCoeffL1Norm (P : Polynomial ℝ) : ℝ :=
  ∑ k ∈ Finset.range (P.natDegree + 1), |P.coeff k|

theorem polynomialCoeffL1Norm_nonneg (P : Polynomial ℝ) :
    0 ≤ polynomialCoeffL1Norm P := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

@[simp]
theorem polynomialCoeffL1Norm_zero :
    polynomialCoeffL1Norm (0 : Polynomial ℝ) = 0 := by
  simp [polynomialCoeffL1Norm]

/-- Every coefficient is bounded by the univariate coefficient norm. -/
theorem abs_polynomial_coeff_le_polynomialCoeffL1Norm
    (P : Polynomial ℝ) (k : ℕ) :
    |P.coeff k| ≤ polynomialCoeffL1Norm P := by
  by_cases hk : k ≤ P.natDegree
  · unfold polynomialCoeffL1Norm
    exact Finset.single_le_sum
      (fun j _ => abs_nonneg (P.coeff j)) (Finset.mem_range.mpr (by omega))
  · have hzero : P.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hzero, abs_zero]
    exact polynomialCoeffL1Norm_nonneg P

/-- Coefficient norm of a univariate substitution. -/
theorem coeffL1Norm_polynomial_aeval_le
    {n : ℕ} (a : MvPolynomial (Fin n) ℝ) (P : Polynomial ℝ)
    {G : ℝ} (hG : 1 ≤ G) (ha : coeffL1Norm a ≤ G) :
    coeffL1Norm (Polynomial.aeval a P) ≤
      polynomialCoeffL1Norm P * G ^ P.natDegree := by
  rw [Polynomial.aeval_eq_sum_range]
  calc
    coeffL1Norm
        (∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k • a ^ k) ≤
        ∑ k ∈ Finset.range (P.natDegree + 1),
          coeffL1Norm (P.coeff k • a ^ k) :=
      coeffL1Norm_sum_le (Finset.range (P.natDegree + 1))
        (fun k => P.coeff k • a ^ k)
    _ ≤ ∑ k ∈ Finset.range (P.natDegree + 1),
          |P.coeff k| * G ^ P.natDegree := by
      apply Finset.sum_le_sum
      intro k hk
      rw [MvPolynomial.smul_eq_C_mul]
      calc
        coeffL1Norm (C (P.coeff k) * a ^ k) ≤
            |P.coeff k| * coeffL1Norm (a ^ k) :=
          coeffL1Norm_C_mul_le (P.coeff k) (a ^ k)
        _ ≤ |P.coeff k| * coeffL1Norm a ^ k := by
          exact mul_le_mul_of_nonneg_left (coeffL1Norm_pow_le a k) (abs_nonneg _)
        _ ≤ |P.coeff k| * G ^ k := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (coeffL1Norm_nonneg a) ha k)
            (abs_nonneg _)
        _ ≤ |P.coeff k| * G ^ P.natDegree := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hG
              (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
            (abs_nonneg _)
    _ = polynomialCoeffL1Norm P * G ^ P.natDegree := by
      rw [polynomialCoeffL1Norm, Finset.sum_mul]


/-- A coefficient norm presented through the canonical embedding into a
one-variable multivariate polynomial.  This presentation makes its algebra
laws immediate consequences of the shared multivariate norm API. -/
def embeddedPolynomialCoeffL1Norm (P : Polynomial ℝ) : ℝ :=
  coeffL1Norm (P.toMvPolynomial (0 : Fin 1))

theorem embeddedPolynomialCoeffL1Norm_nonneg (P : Polynomial ℝ) :
    0 ≤ embeddedPolynomialCoeffL1Norm P :=
  coeffL1Norm_nonneg _

@[simp]
theorem embeddedPolynomialCoeffL1Norm_zero :
    embeddedPolynomialCoeffL1Norm (0 : Polynomial ℝ) = 0 := by
  simp [embeddedPolynomialCoeffL1Norm]

theorem embeddedPolynomialCoeffL1Norm_add_le (P Q : Polynomial ℝ) :
    embeddedPolynomialCoeffL1Norm (P + Q) ≤
      embeddedPolynomialCoeffL1Norm P + embeddedPolynomialCoeffL1Norm Q := by
  simpa [embeddedPolynomialCoeffL1Norm] using
    coeffL1Norm_add_le
      (P.toMvPolynomial (0 : Fin 1)) (Q.toMvPolynomial (0 : Fin 1))

theorem embeddedPolynomialCoeffL1Norm_mul_le (P Q : Polynomial ℝ) :
    embeddedPolynomialCoeffL1Norm (P * Q) ≤
      embeddedPolynomialCoeffL1Norm P * embeddedPolynomialCoeffL1Norm Q := by
  simpa [embeddedPolynomialCoeffL1Norm] using
    coeffL1Norm_mul_le
      (P.toMvPolynomial (0 : Fin 1)) (Q.toMvPolynomial (0 : Fin 1))

theorem embeddedPolynomialCoeffL1Norm_pow_le (P : Polynomial ℝ) (k : ℕ) :
    embeddedPolynomialCoeffL1Norm (P ^ k) ≤
      embeddedPolynomialCoeffL1Norm P ^ k := by
  simpa [embeddedPolynomialCoeffL1Norm] using
    coeffL1Norm_pow_le (P.toMvPolynomial (0 : Fin 1)) k

/-- The canonical one-variable embedding preserves the expected degree
upper bound. -/
theorem totalDegree_toMvPolynomial_le_natDegree (P : Polynomial ℝ) :
    (P.toMvPolynomial (0 : Fin 1)).totalDegree ≤ P.natDegree := by
  change (Polynomial.aeval (X (0 : Fin 1)) P).totalDegree ≤ P.natDegree
  rw [Polynomial.aeval_eq_sum_range]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  rw [MvPolynomial.smul_eq_C_mul]
  calc
    (C (P.coeff k) * (X (0 : Fin 1)) ^ k).totalDegree ≤
        (C (P.coeff k) : MvPolynomial (Fin 1) ℝ).totalDegree +
          ((X (0 : Fin 1) : MvPolynomial (Fin 1) ℝ) ^ k).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ k := by
      calc
        _ ≤ 0 + k * (X (0 : Fin 1) : MvPolynomial (Fin 1) ℝ).totalDegree :=
          Nat.add_le_add (MvPolynomial.totalDegree_C _).le
            (MvPolynomial.totalDegree_pow _ _)
        _ = k := by simp
    _ ≤ P.natDegree :=
      Nat.le_of_lt_succ (Finset.mem_range.mp hk)

/-- Substitution estimate in the algebra-compatible norm.  This is the form
used to propagate rational-package coefficient bounds through multivariate
substitution. -/
theorem coeffL1Norm_polynomial_aeval_le_embedded
    {n : ℕ} (a : MvPolynomial (Fin n) ℝ) (P : Polynomial ℝ)
    {G : ℝ} (hG : 1 ≤ G) (ha : coeffL1Norm a ≤ G) :
    coeffL1Norm (Polynomial.aeval a P) ≤
      embeddedPolynomialCoeffL1Norm P * G ^ P.natDegree := by
  let f : Fin 1 → MvPolynomial (Fin n) ℝ := fun _ => a
  have hraw := coeffL1Norm_aeval_le f
    (P.toMvPolynomial (0 : Fin 1)) hG (fun _ => ha)
  rw [MvPolynomial.aeval_toMvPolynomial] at hraw
  calc
    coeffL1Norm (Polynomial.aeval a P) ≤
        embeddedPolynomialCoeffL1Norm P *
          G ^ (P.toMvPolynomial (0 : Fin 1)).totalDegree := by
      simpa [f, embeddedPolynomialCoeffL1Norm] using hraw
    _ ≤ embeddedPolynomialCoeffL1Norm P * G ^ P.natDegree := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hG (totalDegree_toMvPolynomial_le_natDegree P))
        (embeddedPolynomialCoeffL1Norm_nonneg P)

/-- Coefficients are preserved by the canonical embedding into the chosen
variable of a multivariate polynomial ring. -/
theorem coeff_toMvPolynomial_single
    {σ : Type*} [DecidableEq σ] (P : Polynomial ℝ) (i : σ) (k : ℕ) :
    MvPolynomial.coeff (Finsupp.single i k) (P.toMvPolynomial i) =
      P.coeff k := by
  induction P using Polynomial.induction_on' with
  | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [map_mul, map_pow, Polynomial.toMvPolynomial_X]
      have hs : Finsupp.single i k = Finsupp.single i n ↔ k = n := by
        constructor
        · intro h
          rcases (Finsupp.single_eq_single_iff i i k n).mp h with h | h
          · exact h.2
          · omega
        · rintro rfl
          rfl
      simp [MvPolynomial.coeff_X_pow, hs, eq_comm]
  | add P Q hP hQ =>
      simp only [map_add, MvPolynomial.coeff_add, Polynomial.coeff_add]
      rw [hP, hQ]

/-- The direct univariate coefficient norm is controlled by the embedded
norm, up to the number of possible coefficients. -/
theorem polynomialCoeffL1Norm_le_natDegree_succ_mul_embedded
    (P : Polynomial ℝ) :
    polynomialCoeffL1Norm P ≤
      (P.natDegree + 1 : ℕ) * embeddedPolynomialCoeffL1Norm P := by
  unfold polynomialCoeffL1Norm
  calc
    ∑ k ∈ Finset.range (P.natDegree + 1), |P.coeff k| ≤
        ∑ _k ∈ Finset.range (P.natDegree + 1),
          embeddedPolynomialCoeffL1Norm P := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← coeff_toMvPolynomial_single P (0 : Fin 1) k]
      exact abs_coeff_le_coeffL1Norm
        (P.toMvPolynomial (0 : Fin 1)) (Finsupp.single 0 k)
    _ = (P.natDegree + 1 : ℕ) * embeddedPolynomialCoeffL1Norm P := by
      simp
/-- The algebra-compatible norm is bounded by the direct sum of absolute
univariate coefficients. -/
theorem embeddedPolynomialCoeffL1Norm_le_polynomialCoeffL1Norm
    (P : Polynomial ℝ) :
    embeddedPolynomialCoeffL1Norm P ≤ polynomialCoeffL1Norm P := by
  have hX : coeffL1Norm (X (0 : Fin 1) : MvPolynomial (Fin 1) ℝ) ≤ 1 := by
    simpa using coeffL1Norm_monomial_le
      (n := 1) (Finsupp.single (0 : Fin 1) 1) (1 : ℝ)
  simpa [embeddedPolynomialCoeffL1Norm] using
    coeffL1Norm_polynomial_aeval_le
      (X (0 : Fin 1) : MvPolynomial (Fin 1) ℝ) P le_rfl hX

theorem embeddedPolynomialCoeffL1Norm_C_le (c : ℝ) :
    embeddedPolynomialCoeffL1Norm (Polynomial.C c) ≤ |c| := by
  simpa [embeddedPolynomialCoeffL1Norm] using
    coeffL1Norm_C_le (n := 1) c

theorem embeddedPolynomialCoeffL1Norm_X_le :
    embeddedPolynomialCoeffL1Norm (Polynomial.X : Polynomial ℝ) ≤ 1 := by
  simpa [embeddedPolynomialCoeffL1Norm] using
    coeffL1Norm_monomial_le
      (n := 1) (Finsupp.single (0 : Fin 1) 1) (1 : ℝ)

theorem embeddedPolynomialCoeffL1Norm_sub_le
    (P Q : Polynomial ℝ) :
    embeddedPolynomialCoeffL1Norm (P - Q) ≤
      embeddedPolynomialCoeffL1Norm P +
        embeddedPolynomialCoeffL1Norm Q := by
  simpa [embeddedPolynomialCoeffL1Norm] using
    coeffL1Norm_sub_le
      (P.toMvPolynomial (0 : Fin 1)) (Q.toMvPolynomial (0 : Fin 1))

/-- Composition grows the algebra-compatible coefficient norm by at most a
power of any common upper bound for the inner polynomial's norm. -/
theorem embeddedPolynomialCoeffL1Norm_comp_le
    (P Q : Polynomial ℝ) {G : ℝ}
    (hG : 1 ≤ G) (hQ : embeddedPolynomialCoeffL1Norm Q ≤ G) :
    embeddedPolynomialCoeffL1Norm (P.comp Q) ≤
      embeddedPolynomialCoeffL1Norm P * G ^ P.natDegree := by
  have hraw := coeffL1Norm_polynomial_aeval_le_embedded
    (Q.toMvPolynomial (0 : Fin 1)) P hG hQ
  have hhom :
      Polynomial.aeval (Q.toMvPolynomial (0 : Fin 1)) =
        (Polynomial.toMvPolynomial (0 : Fin 1)).comp
          (Polynomial.aeval Q) := by
    apply Polynomial.algHom_ext
    simp
  have heval := DFunLike.congr_fun hhom P
  change
    coeffL1Norm ((P.comp Q).toMvPolynomial (0 : Fin 1)) ≤
      embeddedPolynomialCoeffL1Norm P * G ^ P.natDegree
  rw [Polynomial.comp_eq_aeval]
  simpa only [AlgHom.comp_apply] using heval ▸ hraw

/-- A convenient bound for the affine polynomial c*X+d. -/
theorem embeddedPolynomialCoeffL1Norm_C_mul_X_add_C_le
    (c d : ℝ) :
    embeddedPolynomialCoeffL1Norm
        (Polynomial.C c * Polynomial.X + Polynomial.C d) ≤
      |c| + |d| := by
  calc
    embeddedPolynomialCoeffL1Norm
        (Polynomial.C c * Polynomial.X + Polynomial.C d) ≤
      embeddedPolynomialCoeffL1Norm (Polynomial.C c * Polynomial.X) +
        embeddedPolynomialCoeffL1Norm (Polynomial.C d) :=
      embeddedPolynomialCoeffL1Norm_add_le _ _
    _ ≤ |c| + |d| := by
      apply add_le_add
      · calc
          embeddedPolynomialCoeffL1Norm (Polynomial.C c * Polynomial.X) ≤
              embeddedPolynomialCoeffL1Norm (Polynomial.C c) *
                embeddedPolynomialCoeffL1Norm Polynomial.X :=
            embeddedPolynomialCoeffL1Norm_mul_le _ _
          _ ≤ |c| * 1 := by
            exact mul_le_mul
              (embeddedPolynomialCoeffL1Norm_C_le c)
              embeddedPolynomialCoeffL1Norm_X_le
              (embeddedPolynomialCoeffL1Norm_nonneg Polynomial.X)
              (abs_nonneg c)
          _ = |c| := mul_one _
      · exact embeddedPolynomialCoeffL1Norm_C_le d

end OptimalConvergenceRates.GeneralArchimedean

end
