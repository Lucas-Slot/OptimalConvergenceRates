import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.AngularFrequencies
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.TaylorPolynomials
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Quantitative Cauchy truncation of the actual angular certificate vector. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Foundation

open scoped BigOperators NNReal ENNReal

theorem weighted_bound_on_circle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {H : ℂ → E} {a r R : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a)
    (hweighted : ∀ z : ℂ, ‖H z‖ ≤
      (a + r⁻¹ ^ 2) * (1 + r * ‖z‖) ^ 2 * Real.exp (r * |z.im|)) :
    ∀ z ∈ Metric.sphere (0 : ℂ) R,
      ‖H z‖ ≤ (a + r⁻¹ ^ 2) * (1 + r * R) ^ 2 * Real.exp (r * R) := by
  intro z hz
  have hzR : ‖z‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
  have him : |z.im| ≤ R := hzR ▸ Complex.abs_im_le_norm z
  calc
    ‖H z‖ ≤ (a + r⁻¹ ^ 2) * (1 + r * ‖z‖) ^ 2 * Real.exp (r * |z.im|) := hweighted z
    _ ≤ (a + r⁻¹ ^ 2) * (1 + r * R) ^ 2 * Real.exp (r * R) := by
      rw [hzR]
      gcongr

theorem cauchy_tail_le_of_circle_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {H : ℂ → E} (hH : Differentiable ℂ H) (R : ℝ≥0) (hR : 0 < R)
    {B ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcircle : ∀ z ∈ Metric.sphere (0 : ℂ) (R : ℝ), ‖H z‖ ≤ B)
    (τ : ℂ) (hτ : ‖τ‖ ≤ ρ * (R : ℝ)) (K : ℕ) :
    ‖H τ - (cauchyPowerSeries H 0 R).partialSum (K + 1) τ‖ ≤
      B * ρ ^ (K + 1) / (1 - ρ) := by
  have hRreal : (0 : ℝ) < (R : ℝ) := hR
  have hB : 0 ≤ B := by
    have hpoint : ((R : ℝ) : ℂ) ∈ Metric.sphere (0 : ℂ) (R : ℝ) := by
      simp [Metric.mem_sphere, Complex.norm_real, abs_of_nonneg R.property]
    exact (norm_nonneg _).trans (hcircle _ hpoint)
  have hcoef (n : ℕ) :
      ‖cauchyPowerSeries H 0 R n‖ * ‖τ‖ ^ n ≤ B * ρ ^ n := by
    calc
      ‖cauchyPowerSeries H 0 R n‖ * ‖τ‖ ^ n ≤ (B / (R : ℝ) ^ n) * ‖τ‖ ^ n :=
        mul_le_mul_of_nonneg_right
          (norm_cauchyPowerSeries_le_of_bound H 0 hRreal hcircle n) (by positivity)
      _ ≤ (B / (R : ℝ) ^ n) * (ρ * (R : ℝ)) ^ n := by gcongr
      _ = B * ρ ^ n := by
        rw [mul_pow]
        field_simp <;> ring
  apply norm_powerSeries_tail_le_geometric (hH.hasFPowerSeriesOnBall 0 hR) ?_
    hρ0 hρ1 hcoef K
  simp

/-- The exact vector Cauchy tail, for the polynomial truncation constructed
in `TaylorPolynomials`. Its constants do not count the certificate squares. -/
theorem angularTaylorVector_tail_le
    {σ J : Type*} [Fintype J] (p : J → MvPolynomial (Option σ) ℝ)
    (y : σ → ℝ) {r K : ℕ} (hr : 0 < r) (hK : 0 < K)
    (hdegree : ∀ j, (p j).totalDegree ≤ r) {a ρ : ℝ}
    (hreal : ∀ t : ℝ, ‖angularVector p y (t : ℂ)‖ ≤ a + t ^ 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (τ : ℂ)
    (hτ : ‖τ‖ ≤ ρ * ((K : ℝ) / (r : ℝ))) :
    ‖angularVector p y τ - angularTaylorVector p τ K y‖ ≤
      ((a + (r : ℝ)⁻¹ ^ 2) * ((K : ℝ) + 1) ^ 2 * Real.exp (K : ℝ)) *
        ρ ^ (K + 1) / (1 - ρ) := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  let R : ℝ≥0 := ⟨(K : ℝ) / (r : ℝ), (div_pos hKR hrR).le⟩
  have hR : 0 < R := div_pos hKR hrR
  have ha : 0 ≤ a := by
    have hz := (norm_nonneg (angularVector p y 0)).trans (hreal 0)
    simpa using hz
  have hweighted := angularVector_weighted_complex_bound p y hr hdegree hreal
  have hcircle : ∀ z ∈ Metric.sphere (0 : ℂ) (R : ℝ),
      ‖angularVector p y z‖ ≤
        (a + (r : ℝ)⁻¹ ^ 2) * ((K : ℝ) + 1) ^ 2 * Real.exp (K : ℝ) := by
    have hcancel : (r : ℝ) * (R : ℝ) = (K : ℝ) := by
      change (r : ℝ) * ((K : ℝ) / (r : ℝ)) = (K : ℝ)
      field_simp
    simpa only [hcancel, add_comm] using
      weighted_bound_on_circle (R := (R : ℝ)) hrR.le ha hweighted
  rw [angularTaylorVector_eq_cauchyPartialSum p τ K y hR]
  exact cauchy_tail_le_of_circle_bound (angularVector_differentiable p y) R hR
    hρ0 hρ1 hcircle τ hτ K

theorem norm_sq_sub_le_of_approximation
    {E : Type*} [NormedAddCommGroup E] (u v : E) {D M : ℝ}
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hu : ‖u‖ ≤ M) (huv : ‖u - v‖ ≤ D * M) :
    |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ D * (2 + D) * M ^ 2 := by
  have hv : ‖v‖ ≤ (1 + D) * M := by
    have htri := norm_sub_norm_le v u
    rw [norm_sub_rev] at htri
    nlinarith
  calc
    |‖u‖ ^ 2 - ‖v‖ ^ 2| = |‖u‖ - ‖v‖| * (‖u‖ + ‖v‖) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖u‖ + ‖v‖)]
      ring
    _ ≤ (D * M) * ((2 + D) * M) := by
      apply mul_le_mul ((abs_norm_sub_norm_le u v).trans huv) ?_ (by positivity) (by positivity)
      nlinarith
    _ = D * (2 + D) * M ^ 2 := by ring

theorem norm_sq_sub_le_six
    {E : Type*} [NormedAddCommGroup E] (u v : E) {D a t : ℝ}
    (hD0 : 0 ≤ D) (hD1 : D ≤ 1) (ha : 0 ≤ a)
    (hu : ‖u‖ ≤ a + t ^ 2) (huv : ‖u - v‖ ≤ D * (a + t ^ 2)) :
    |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ 6 * D * (a ^ 2 + t ^ 4) := by
  have hM : 0 ≤ a + t ^ 2 := by positivity
  have hpoly : (a + t ^ 2) ^ 2 ≤ 2 * (a ^ 2 + t ^ 4) := by
    nlinarith [sq_nonneg (a - t ^ 2)]
  have hfactor : D * (2 + D) ≤ 3 * D := by nlinarith
  calc
    |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ D * (2 + D) * (a + t ^ 2) ^ 2 :=
      norm_sq_sub_le_of_approximation u v hD0 hM hu huv
    _ ≤ (3 * D) * (2 * (a ^ 2 + t ^ 4)) := by gcongr
    _ = 6 * D * (a ^ 2 + t ^ 4) := by ring

theorem real_exp_nat_le_four_pow (K : ℕ) : Real.exp (K : ℝ) ≤ (4 : ℝ) ^ K := by
  have he : Real.exp (1 : ℝ) ≤ 4 := (Real.exp_one_lt_d9.trans (by norm_num)).le
  calc
    Real.exp (K : ℝ) = Real.exp ((K : ℝ) * 1) := by rw [mul_one]
    _ = Real.exp 1 ^ K := Real.exp_nat_mul 1 K
    _ ≤ (4 : ℝ) ^ K := pow_le_pow_left₀ (Real.exp_nonneg 1) he K

def angularTruncationFactor (K : ℕ) (ρ : ℝ) : ℝ :=
  ((K : ℝ) + 1) ^ 2 * (4 * ρ) ^ K

theorem cauchy_tail_factor_bound (a r ρ : ℝ) (K : ℕ)
    (ha : 0 ≤ a) (hr : 0 < r) (hρ0 : 0 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (hscale : 1 ≤ ρ * (K : ℝ)) :
    ((a + r⁻¹ ^ 2) * ((K : ℝ) + 1) ^ 2 * Real.exp (K : ℝ)) *
        ρ ^ (K + 1) / (1 - ρ) ≤
      angularTruncationFactor K ρ * (a + (ρ * (K : ℝ) / r) ^ 2) := by
  have hden : 0 < 1 - ρ := by linarith
  have hfrac : ρ / (1 - ρ) ≤ 1 := by
    apply (div_le_iff₀ hden).2
    linarith
  have hquad : r⁻¹ ^ 2 ≤ (ρ * (K : ℝ) / r) ^ 2 := by
    have hlin : r⁻¹ ≤ ρ * (K : ℝ) / r := by
      simpa only [one_div] using (div_le_div_of_nonneg_right hscale hr.le)
    exact pow_le_pow_left₀ (inv_nonneg.mpr hr.le) hlin 2
  have hexp : Real.exp (K : ℝ) * ρ ^ K ≤ (4 * ρ) ^ K := by
    calc
      Real.exp (K : ℝ) * ρ ^ K ≤ (4 : ℝ) ^ K * ρ ^ K :=
        mul_le_mul_of_nonneg_right (real_exp_nat_le_four_pow K) (pow_nonneg hρ0 K)
      _ = (4 * ρ) ^ K := (mul_pow _ _ _).symm
  calc
    ((a + r⁻¹ ^ 2) * ((K : ℝ) + 1) ^ 2 * Real.exp (K : ℝ)) *
        ρ ^ (K + 1) / (1 - ρ) =
      (a + r⁻¹ ^ 2) * ((K : ℝ) + 1) ^ 2 *
        (Real.exp (K : ℝ) * ρ ^ K) * (ρ / (1 - ρ)) := by rw [pow_succ]; ring
    _ ≤ (a + (ρ * (K : ℝ) / r) ^ 2) * ((K : ℝ) + 1) ^ 2 *
        (4 * ρ) ^ K * 1 := by gcongr
    _ = angularTruncationFactor K ρ * (a + (ρ * (K : ℝ) / r) ^ 2) := by
      unfold angularTruncationFactor
      ring

theorem angularTaylorVector_relative_tail_le
    {σ J : Type*} [Fintype J] (p : J → MvPolynomial (Option σ) ℝ)
    (y : σ → ℝ) {r K : ℕ} (hr : 0 < r) (hK : 0 < K)
    (hdegree : ∀ j, (p j).totalDegree ≤ r) {a ρ : ℝ}
    (hreal : ∀ t : ℝ, ‖angularVector p y (t : ℂ)‖ ≤ a + t ^ 2)
    (hρ0 : 0 ≤ ρ) (hρhalf : ρ ≤ 1 / 2) (hscale : 1 ≤ ρ * (K : ℝ)) :
    let τ : ℝ := ρ * (K : ℝ) / (r : ℝ)
    ‖angularVector p y (τ : ℂ) - angularTaylorVector p (τ : ℂ) K y‖ ≤
      angularTruncationFactor K ρ * (a + τ ^ 2) := by
  dsimp only
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have ha : 0 ≤ a := by
    have hz := (norm_nonneg (angularVector p y 0)).trans (hreal 0)
    simpa using hz
  have hτ0 : 0 ≤ ρ * (K : ℝ) / (r : ℝ) := by positivity
  have hτ : ‖((ρ * (K : ℝ) / (r : ℝ) : ℝ) : ℂ)‖ ≤
      ρ * ((K : ℝ) / (r : ℝ)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ0]
    exact le_of_eq (by ring)
  exact (angularTaylorVector_tail_le p y hr hK hdegree hreal hρ0
    (by linarith : ρ < 1) _ hτ).trans
      (cauchy_tail_factor_bound a (r : ℝ) ρ K ha hrR hρ0 hρhalf hscale)

/-- The dimension-free squared-norm error used in the uniform transfer.
The truncation is a vector of actual degree-`K` polynomials. -/
theorem angularTaylorVector_norm_square_error
    {σ J : Type*} [Fintype J] (p : J → MvPolynomial (Option σ) ℝ)
    (y : σ → ℝ) {r K : ℕ} (hr : 0 < r) (hK : 0 < K)
    (hdegree : ∀ j, (p j).totalDegree ≤ r) {a ρ : ℝ}
    (hreal : ∀ t : ℝ, ‖angularVector p y (t : ℂ)‖ ≤ a + t ^ 2)
    (hρ0 : 0 ≤ ρ) (hρhalf : ρ ≤ 1 / 2) (hscale : 1 ≤ ρ * (K : ℝ))
    (hD : angularTruncationFactor K ρ ≤ 1) :
    let τ : ℝ := ρ * (K : ℝ) / (r : ℝ)
    |‖angularVector p y (τ : ℂ)‖ ^ 2 -
        ‖angularTaylorVector p (τ : ℂ) K y‖ ^ 2| ≤
      6 * angularTruncationFactor K ρ * (a ^ 2 + τ ^ 4) := by
  dsimp only
  have ha : 0 ≤ a := by
    have hz := (norm_nonneg (angularVector p y 0)).trans (hreal 0)
    simpa using hz
  apply norm_sq_sub_le_six _ _ (by unfold angularTruncationFactor; positivity)
    hD ha (hreal _)
  exact angularTaylorVector_relative_tail_le p y hr hK hdegree hreal hρ0 hρhalf hscale

end Foundation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
