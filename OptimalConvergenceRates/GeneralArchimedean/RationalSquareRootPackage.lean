/-
  A packaged form of the dyadic rational-square-root construction.
-/
import OptimalConvergenceRates.GeneralArchimedean.DyadicReflection
import OptimalConvergenceRates.GeneralArchimedean.UnivariateCoefficientNorm

noncomputable section

namespace OptimalConvergenceRates
namespace GeneralArchimedean
namespace RationalSquareRoot

/-- The two integer parameters of the dyadic rational-square-root
construction, together with the facts shared by the conversion results. -/
structure Package (δ B theta : ℝ) where
  ell : ℕ
  J : ℕ
  ell_pos : 0 < ell
  cover : CoversInterval δ B J
  attenuation : 4 * (1 / 3 : ℝ) ^ (2 * ell) ≤ theta

/-- Positive shift, nonnegative interval length, and positive target error
suffice to choose the finite dyadic construction. -/
theorem package_nonempty
    {δ B theta : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) (htheta : 0 < theta) :
    Nonempty (Package δ B theta) := by
  obtain ⟨ell, hell, hatt⟩ := exists_positive_ell_for_theta htheta
  obtain ⟨J, hcover⟩ := exists_coversInterval hδ hB
  exact ⟨⟨ell, J, hell, hcover, hatt⟩⟩


/-- A package can be chosen whose dyadic index is explicitly logarithmic in
the interval-to-shift ratio. -/
theorem package_nonempty_with_log_bound
    {δ B theta : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) (htheta : 0 < theta) :
    ∃ pkg : Package δ B theta,
      (pkg.J : ℝ) ≤
        Real.log (Real.sqrt (B + δ) / Real.sqrt δ) /
          Real.log 2 := by
  obtain ⟨ell, hell, hatt⟩ := exists_positive_ell_for_theta htheta
  obtain ⟨J, hcover, hJ⟩ :=
    exists_coversInterval_with_log_bound hδ hB
  exact ⟨⟨ell, J, hell, hcover, hatt⟩, hJ⟩

/-- Both integer parameters can be chosen with their explicit logarithmic
bounds. -/
theorem package_nonempty_with_parameter_log_bounds
    {δ B theta : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1) :
    ∃ pkg : Package δ B theta,
      (pkg.ell : ℝ) ≤
          Real.log (theta / 4) / Real.log (1 / 9) + 1 ∧
        (pkg.J : ℝ) ≤
          Real.log (Real.sqrt (B + δ) / Real.sqrt δ) /
            Real.log 2 := by
  obtain ⟨ell, hell, hatt, hellLog⟩ :=
    exists_positive_ell_for_theta_with_log_bound htheta htheta1
  obtain ⟨J, hcover, hJLog⟩ :=
    exists_coversInterval_with_log_bound hδ hB
  exact ⟨⟨ell, J, hell, hcover, hatt⟩, hellLog, hJLog⟩
namespace Package

abbrev P {δ B theta : ℝ} (pkg : Package δ B theta) : Polynomial ℝ :=
  normalizedNumerator δ pkg.ell pkg.J

abbrev V {δ B theta : ℝ} (pkg : Package δ B theta) : Polynomial ℝ :=
  normalizedDenominator δ pkg.ell pkg.J

abbrev E {δ B theta : ℝ} (pkg : Package δ B theta) : Polynomial ℝ :=
  normalizedError δ pkg.ell pkg.J

theorem denominator_value_pos
    {δ B theta : ℝ} (pkg : Package δ B theta) (hδ : 0 < δ) :
    0 < (denominator δ pkg.ell pkg.J).eval δ :=
  denominator_eval_self_pos hδ pkg.ell_pos pkg.J

theorem V_coeffNonneg
    {δ B theta : ℝ} (pkg : Package δ B theta) (hδ : 0 < δ) :
    CoeffNonneg pkg.V :=
  normalizedDenominator_coeffNonneg hδ.le pkg.ell pkg.J
    (pkg.denominator_value_pos hδ)

theorem V_coeff_zero
    {δ B theta : ℝ} (pkg : Package δ B theta) (hδ : 0 < δ) :
    pkg.V.coeff 0 = 1 :=
  normalizedDenominator_coeff_zero pkg.ell pkg.J
    (pkg.denominator_value_pos hδ)

theorem polynomial_identity
    {δ B theta : ℝ} (pkg : Package δ B theta) (hδ : 0 < δ) :
    pkg.P ^ 2 - Polynomial.X * pkg.V ^ 2 = pkg.E :=
  normalizedNumerator_sq_sub_X_mul_denominator_sq
    hδ pkg.ell_pos pkg.J

theorem error_isSOS
    {δ B theta : ℝ} (pkg : Package δ B theta) (hδ : 0 < δ) :
    IsSOSUni pkg.E :=
  normalizedError_isSOSUni hδ.le pkg.ell pkg.J

theorem error_le
    {δ B theta : ℝ} (pkg : Package δ B theta) (hδ : 0 < δ)
    {u : ℝ} (hu0 : 0 ≤ u) (huB : u ≤ B) :
    pkg.E.eval u ≤ theta * pkg.P.eval u ^ 2 +
      δ * pkg.V.eval u ^ 2 :=
  normalizedError_le hδ pkg.ell_pos pkg.cover pkg.attenuation hu0 huB

theorem numerator_sq_le
    {δ B theta B' : ℝ} (pkg : Package δ B theta) (hδ : 0 < δ)
    (htheta1 : theta < 1)
    (hB' : B + δ ≤ (1 - theta) * B')
    {u : ℝ} (hu0 : 0 ≤ u) (huB : u ≤ B) :
    pkg.P.eval u ^ 2 ≤ B' * pkg.V.eval u ^ 2 :=
  normalizedNumerator_sq_le hδ pkg.ell_pos pkg.cover pkg.attenuation
    htheta1 hB' hu0 huB

/-- A convenient fixed bound for the numerator when the small parameters are
at most one and one half, respectively. -/
theorem numerator_sq_le_two_mul
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B)
    (htheta : theta ≤ 1 / 2)
    {u : ℝ} (hu0 : 0 ≤ u) (huB : u ≤ B) :
    pkg.P.eval u ^ 2 ≤ (2 * (B + 1)) * pkg.V.eval u ^ 2 := by
  have htheta1 : theta < 1 := lt_of_le_of_lt htheta (by norm_num)
  have hfactor : 1 ≤ 2 * (1 - theta) := by linarith
  have hB1 : 0 ≤ B + 1 := by linarith
  have hB' : B + δ ≤ (1 - theta) * (2 * (B + 1)) := by
    calc
      B + δ ≤ B + 1 := by linarith
      _ = 1 * (B + 1) := by ring
      _ ≤ (2 * (1 - theta)) * (B + 1) :=
        mul_le_mul_of_nonneg_right hfactor hB1
      _ = (1 - theta) * (2 * (B + 1)) := by ring
  exact pkg.numerator_sq_le hδ htheta1 hB' hu0 huB

theorem P_degree_le
    {δ B theta : ℝ} (pkg : Package δ B theta) :
    pkg.P.natDegree ≤ 2 * pkg.ell * (pkg.J + 1) :=
  normalizedNumerator_degree_bound δ pkg.ell pkg.J

theorem V_degree_le
    {δ B theta : ℝ} (pkg : Package δ B theta) :
    pkg.V.natDegree ≤ 2 * pkg.ell * (pkg.J + 1) :=
  normalizedDenominator_degree_bound δ pkg.ell pkg.J



/-- A single coefficient envelope for all three univariate polynomials in a
rational-square-root package. -/
def coefficientBound {δ B theta : ℝ} (pkg : Package δ B theta) : ℝ :=
  1 + embeddedPolynomialCoeffL1Norm pkg.P +
    embeddedPolynomialCoeffL1Norm pkg.V +
      embeddedPolynomialCoeffL1Norm pkg.E

theorem one_le_coefficientBound
    {δ B theta : ℝ} (pkg : Package δ B theta) :
    1 ≤ pkg.coefficientBound := by
  unfold coefficientBound
  have hP := embeddedPolynomialCoeffL1Norm_nonneg pkg.P
  have hV := embeddedPolynomialCoeffL1Norm_nonneg pkg.V
  have hE := embeddedPolynomialCoeffL1Norm_nonneg pkg.E
  linarith

theorem P_coeffL1Norm_le_coefficientBound
    {δ B theta : ℝ} (pkg : Package δ B theta) :
    embeddedPolynomialCoeffL1Norm pkg.P ≤ pkg.coefficientBound := by
  unfold coefficientBound
  have hV := embeddedPolynomialCoeffL1Norm_nonneg pkg.V
  have hE := embeddedPolynomialCoeffL1Norm_nonneg pkg.E
  linarith

theorem V_coeffL1Norm_le_coefficientBound
    {δ B theta : ℝ} (pkg : Package δ B theta) :
    embeddedPolynomialCoeffL1Norm pkg.V ≤ pkg.coefficientBound := by
  unfold coefficientBound
  have hP := embeddedPolynomialCoeffL1Norm_nonneg pkg.P
  have hE := embeddedPolynomialCoeffL1Norm_nonneg pkg.E
  linarith

theorem E_coeffL1Norm_le_coefficientBound
    {δ B theta : ℝ} (pkg : Package δ B theta) :
    embeddedPolynomialCoeffL1Norm pkg.E ≤ pkg.coefficientBound := by
  unfold coefficientBound
  have hP := embeddedPolynomialCoeffL1Norm_nonneg pkg.P
  have hV := embeddedPolynomialCoeffL1Norm_nonneg pkg.V
  linarith
/-- Common degree envelope for the squared numerator, squared denominator,
and error polynomials in a package. -/
def degreeBound {δ B theta : ℝ} (pkg : Package δ B theta) : ℕ :=
  4 * pkg.ell * (pkg.J + 1)

theorem P_sq_degree_le
    {δ B theta : ℝ} (pkg : Package δ B theta) :
    (pkg.P ^ 2).natDegree ≤ pkg.degreeBound := by
  calc
    (pkg.P ^ 2).natDegree ≤ 2 * pkg.P.natDegree :=
      Polynomial.natDegree_pow_le
    _ ≤ 2 * (2 * pkg.ell * (pkg.J + 1)) :=
      Nat.mul_le_mul_left 2 pkg.P_degree_le
    _ = pkg.degreeBound := by simp [degreeBound]; ring

theorem V_sq_degree_le
    {δ B theta : ℝ} (pkg : Package δ B theta) :
    (pkg.V ^ 2).natDegree ≤ pkg.degreeBound := by
  calc
    (pkg.V ^ 2).natDegree ≤ 2 * pkg.V.natDegree :=
      Polynomial.natDegree_pow_le
    _ ≤ 2 * (2 * pkg.ell * (pkg.J + 1)) :=
      Nat.mul_le_mul_left 2 pkg.V_degree_le
    _ = pkg.degreeBound := by simp [degreeBound]; ring

theorem E_degree_le
    {δ B theta : ℝ} (pkg : Package δ B theta) :
    pkg.E.natDegree ≤ pkg.degreeBound := by
  exact normalizedError_degree_bound δ pkg.ell pkg.J

end Package
end RationalSquareRoot
end GeneralArchimedean
end OptimalConvergenceRates

end
