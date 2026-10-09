/-
  Coarse coefficient bounds for univariate polynomials from their sup norm
  on an interval.  These estimates are designed for quantitative
  Markov--Lukacs certificates, where exponential-in-degree losses suffice.
-/
import OptimalConvergenceRates.GeneralArchimedean.UnivariateCoefficientNorm
import OptimalConvergenceRates.MarkovInequality.MarkovInequalityClassical

noncomputable section

open Polynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

/-- Iterated analytic differentiation of a polynomial evaluation agrees
with iterated algebraic differentiation. -/
theorem iteratedDeriv_polynomial_eval_eq
    (k : ℕ) (P : Polynomial ℝ) :
    iteratedDeriv k P.eval = (Polynomial.derivative^[k] P).eval := by
  induction k generalizing P with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ']
      have hderiv : deriv P.eval = (Polynomial.derivative P).eval := by
        funext x
        have h := Polynomial.deriv_aeval (𝕜 := ℝ) P (x := x)
        simpa only [Polynomial.coe_aeval_eq_eval] using h
      rw [hderiv]
      simpa [Function.iterate_succ'] using ih (Polynomial.derivative P)

/-- Evaluation at zero of the k-th algebraic derivative extracts the
k-th coefficient, up to the factorial. -/
theorem iterate_derivative_eval_zero
    (P : Polynomial ℝ) (k : ℕ) :
    ((Polynomial.derivative^[k]) P).eval 0 =
      (Nat.factorial k : ℝ) * P.coeff k := by
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  rw [Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self]

/-- Each monomial coefficient is bounded by the corresponding weak Markov
factor times the sup norm on [-1,1]. -/
theorem abs_coeff_le_markov_sup
    (P : Polynomial ℝ) (d k : ℕ) (hdegree : P.natDegree ≤ d) :
    |P.coeff k| ≤
      (d : ℝ) ^ (2 * k) * polySupNormUni P := by
  have hmarkov :=
    univariate_markov_general_inside P d k hdegree 0
      (by norm_num : |(0 : ℝ)| ≤ 1)
  rw [iteratedDeriv_polynomial_eval_eq] at hmarkov
  have hmarkov' :
      |((Polynomial.derivative^[k]) P).eval 0| ≤
        (d : ℝ) ^ (2 * k) * polySupNormUni P := by simpa using hmarkov
  rw [iterate_derivative_eval_zero] at hmarkov'
  have hfactorial : (1 : ℝ) ≤ Nat.factorial k := by
    exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos k)
  calc
    |P.coeff k| ≤ |(Nat.factorial k : ℝ) * P.coeff k| := by
      rw [abs_mul, abs_of_nonneg
        (show 0 ≤ (Nat.factorial k : ℝ) by positivity)]
      exact le_mul_of_one_le_left (abs_nonneg _) hfactorial
    _ ≤ (d : ℝ) ^ (2 * k) * polySupNormUni P := hmarkov'

/-- A coarse but explicit coefficient norm bound from a uniform bound on
[-1,1].  Its growth is at most exponential in a quadratic function of the
degree, which is more than sufficient for the conversion theorem. -/
theorem polynomialCoeffL1Norm_le_of_unit_interval_bound
    (P : Polynomial ℝ) (d : ℕ) {M : ℝ}
    (hd : 1 ≤ d) (hdegree : P.natDegree ≤ d)
    (hbound : ∀ x : ℝ, |x| ≤ 1 → |P.eval x| ≤ M) :
    polynomialCoeffL1Norm P ≤
      (d + 1 : ℕ) * (d : ℝ) ^ (2 * d) * M := by
  have hsup : polySupNormUni P ≤ M := by
    apply polySupNormUni_le_of_bound
    intro x hxleft hxright
    exact hbound x (abs_le.mpr ⟨hxleft, hxright⟩)
  have hM : 0 ≤ M := (polySupNormUni_nonneg P).trans hsup
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  unfold polynomialCoeffL1Norm
  calc
    (∑ k ∈ range (P.natDegree + 1), |P.coeff k|) ≤
        ∑ _k ∈ range (P.natDegree + 1),
          (d : ℝ) ^ (2 * d) * M := by
      apply Finset.sum_le_sum
      intro k hk
      have hkdegree : k ≤ d := by
        exact (Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans hdegree
      calc
        |P.coeff k| ≤
            (d : ℝ) ^ (2 * k) * polySupNormUni P :=
          abs_coeff_le_markov_sup P d k hdegree
        _ ≤ (d : ℝ) ^ (2 * k) * M :=
          mul_le_mul_of_nonneg_left hsup (by positivity)
        _ ≤ (d : ℝ) ^ (2 * d) * M := by
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ hdreal (Nat.mul_le_mul_left 2 hkdegree)) hM
    _ = (P.natDegree + 1 : ℕ) * (d : ℝ) ^ (2 * d) * M := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      ring
    _ ≤ (d + 1 : ℕ) * (d : ℝ) ^ (2 * d) * M := by
      have hcard : (P.natDegree + 1 : ℝ) ≤ (d + 1 : ℝ) := by
        exact_mod_cast Nat.add_le_add_right hdegree 1
      gcongr

/-- On the unit interval, evaluation is bounded by the coefficient l1 norm. -/
theorem abs_eval_le_polynomialCoeffL1Norm
    (P : Polynomial ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    |P.eval x| ≤ polynomialCoeffL1Norm P := by
  rw [Polynomial.eval_eq_sum_range]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  unfold polynomialCoeffL1Norm
  apply Finset.sum_le_sum
  intro k hk
  rw [abs_mul]
  have hxpow : |x ^ k| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg x) hx
  simpa using mul_le_mul_of_nonneg_left hxpow (abs_nonneg (P.coeff k))

/-- Evaluation in a radius at least one is bounded by the coefficient norm
times the corresponding degree power. -/
theorem abs_eval_le_polynomialCoeffL1Norm_mul_pow
    (P : Polynomial ℝ) {x R : ℝ} (hR : 1 ≤ R) (hx : |x| ≤ R) :
    |P.eval x| ≤ polynomialCoeffL1Norm P * R ^ P.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  calc
    |∑ k ∈ range (P.natDegree + 1), P.coeff k * x ^ k| ≤
        ∑ k ∈ range (P.natDegree + 1), |P.coeff k * x ^ k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range (P.natDegree + 1),
        |P.coeff k| * R ^ P.natDegree := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul, abs_pow]
      have hkdegree : k ≤ P.natDegree :=
        Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      calc
        |P.coeff k| * |x| ^ k ≤ |P.coeff k| * R ^ k := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (abs_nonneg x) hx k) (abs_nonneg (P.coeff k))
        _ ≤ |P.coeff k| * R ^ P.natDegree := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hR hkdegree) (abs_nonneg (P.coeff k))
    _ = polynomialCoeffL1Norm P * R ^ P.natDegree := by
      unfold polynomialCoeffL1Norm
      rw [Finset.sum_mul]

end OptimalConvergenceRates.GeneralArchimedean

end
