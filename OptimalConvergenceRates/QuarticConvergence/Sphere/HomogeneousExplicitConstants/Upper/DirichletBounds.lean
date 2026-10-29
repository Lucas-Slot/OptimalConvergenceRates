import Mathlib.Analysis.Real.Pi.Bounds
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.KernelConstants
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Pointwise and integrability bounds for the actual quotient Dirichlet kernel. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants

open MeasureTheory Set
open scoped Interval

def quotientDirichlet (k : ℕ) (θ : ℝ) : ℝ :=
  Real.sin (((2 * k + 1 : ℕ) : ℝ) * (θ / 2)) / Real.sin (θ / 2)

def angularDirichletWeight (n k : ℕ) (θ : ℝ) : ℝ :=
  |quotientDirichlet k θ| ^ (2 * (n + 3)) * Real.sin θ ^ (n - 2)

theorem abs_sin_nat_mul_le (m : ℕ) (x : ℝ) :
    |Real.sin ((m : ℝ) * x)| ≤ (m : ℝ) * |Real.sin x| := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.cast_succ, add_mul, one_mul, Real.sin_add]
      calc
        _ ≤ |Real.sin ((m : ℝ) * x) * Real.cos x| +
            |Real.cos ((m : ℝ) * x) * Real.sin x| := abs_add_le _ _
        _ ≤ |Real.sin ((m : ℝ) * x)| + |Real.sin x| := by
          simp only [abs_mul]
          exact add_le_add
            (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
            (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _))
        _ ≤ (m : ℝ) * |Real.sin x| + |Real.sin x| := add_le_add ih le_rfl
        _ = ((m : ℝ) + 1) * |Real.sin x| := by ring

theorem quotientDirichlet_abs_le (k : ℕ) (θ : ℝ) :
    |quotientDirichlet k θ| ≤ (2 * k + 1 : ℕ) := by
  by_cases hden : Real.sin (θ / 2) = 0
  · simp only [quotientDirichlet, hden, div_zero, abs_zero]
    positivity
  · unfold quotientDirichlet
    rw [abs_div]
    calc
      _ ≤ (((2 * k + 1 : ℕ) : ℝ) * |Real.sin (θ / 2)|) / |Real.sin (θ / 2)| :=
        div_le_div_of_nonneg_right (abs_sin_nat_mul_le _ _) (abs_nonneg _)
      _ = ((2 * k + 1 : ℕ) : ℝ) := mul_div_cancel_right₀ _ (abs_ne_zero.mpr hden)

theorem quotientDirichlet_measurable (k : ℕ) : Measurable (quotientDirichlet k) := by
  unfold quotientDirichlet
  fun_prop

theorem angularDirichletWeight_measurable (n k : ℕ) : Measurable (angularDirichletWeight n k) := by
  convert ((quotientDirichlet_measurable k).norm.pow_const (2 * (n + 3))).mul
    (Real.measurable_sin.pow_const (n - 2)) using 1
  ext θ
  simp only [angularDirichletWeight, Pi.mul_apply, Real.norm_eq_abs]

theorem angularDirichletWeight_abs_le (n k : ℕ) (θ : ℝ) :
    |angularDirichletWeight n k θ| ≤ (((2 * k + 1 : ℕ) : ℝ)) ^ (2 * (n + 3)) := by
  unfold angularDirichletWeight
  rw [abs_mul, abs_pow, abs_abs, abs_pow]
  calc
    _ ≤ (((2 * k + 1 : ℕ) : ℝ)) ^ (2 * (n + 3)) * (1 : ℝ) ^ (n - 2) :=
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (quotientDirichlet_abs_le k θ) _)
        (pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sin_le_one _) _) (by positivity) (by positivity)
    _ = _ := by simp

theorem angularDirichletMoment_intervalIntegrable (n k j : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun θ ↦ θ ^ j * angularDirichletWeight n k θ) volume a b := by
  let C : ℝ := (((2 * k + 1 : ℕ) : ℝ)) ^ (2 * (n + 3))
  have hdom : IntervalIntegrable (fun θ : ℝ ↦ C * |θ| ^ j) volume a b :=
    (continuous_const.mul (continuous_abs.pow j)).intervalIntegrable _ _
  apply hdom.mono_fun
  · exact ((measurable_id.pow_const j).mul
      (angularDirichletWeight_measurable n k)).aestronglyMeasurable
  · filter_upwards [] with θ
    rw [Real.norm_eq_abs, abs_mul, abs_pow, Real.norm_eq_abs]
    have hC : 0 ≤ C := by positivity
    rw [abs_of_nonneg (mul_nonneg hC (pow_nonneg (abs_nonneg θ) j))]
    simpa only [C, mul_comm] using mul_le_mul_of_nonneg_left
      (angularDirichletWeight_abs_le n k θ) (pow_nonneg (abs_nonneg θ) j)

theorem angularDirichletWeight_intervalIntegrable (n k : ℕ) (a b : ℝ) :
    IntervalIntegrable (angularDirichletWeight n k) volume a b := by
  simpa only [pow_zero, one_mul] using angularDirichletMoment_intervalIntegrable n k 0 a b

theorem angularDirichletWeight_nonneg (n k : ℕ) {θ : ℝ} (hθ : θ ∈ Icc 0 Real.pi) :
    0 ≤ angularDirichletWeight n k θ := by
  exact mul_nonneg (pow_nonneg (abs_nonneg _) _)
    (pow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2) _)

theorem quotientDirichlet_lower (k : ℕ) (hk : 1 ≤ k) {θ : ℝ}
    (hθ0 : 0 < θ) (hθk : θ ≤ 1 / (k : ℝ)) : (k : ℝ) ≤ quotientDirichlet k θ := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hθ1 : θ ≤ 1 := hθk.trans ((div_le_one hkpos).2 hkR)
  have hprod : (k : ℝ) * θ ≤ 1 := by
    have h := (le_div_iff₀ hkpos).1 hθk
    nlinarith
  let u : ℝ := (((2 * k + 1 : ℕ) : ℝ)) * (θ / 2)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ Real.pi / 2 := by
    dsimp [u]
    push_cast
    nlinarith [Real.pi_gt_three]
  have hden : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_gt_three])
  have hhalf : (1 : ℝ) / 2 ≤ 2 / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    linarith [Real.pi_lt_four]
  have hsin : u / 2 ≤ Real.sin u := by
    calc
      u / 2 = (1 / 2) * u := by ring
      _ ≤ (2 / Real.pi) * u := mul_le_mul_of_nonneg_right hhalf hu0
      _ ≤ Real.sin u := Real.mul_le_sin hu0 hu1
  unfold quotientDirichlet
  apply (le_div_iff₀ hden).2
  calc
    (k : ℝ) * Real.sin (θ / 2) ≤ (k : ℝ) * (θ / 2) :=
      mul_le_mul_of_nonneg_left (Real.sin_le (by linarith)) hkpos.le
    _ ≤ Real.sin u := by
      have hu : (k : ℝ) * (θ / 2) ≤ u / 2 := by
        dsimp [u]
        push_cast
        nlinarith
      exact hu.trans hsin

theorem quotientDirichlet_abs_upper (k : ℕ) {θ : ℝ}
    (hθ0 : 0 < θ) (hθpi : θ ≤ Real.pi) :
    |quotientDirichlet k θ| ≤ Real.pi / θ := by
  have hden : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hJordan : θ / Real.pi ≤ Real.sin (θ / 2) := by
    have h := Real.mul_le_sin (x := θ / 2) (by linarith) (by linarith)
    convert h using 1
    ring
  unfold quotientDirichlet
  rw [abs_div, abs_of_pos hden]
  calc
    _ ≤ 1 / Real.sin (θ / 2) := div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hden.le
    _ ≤ 1 / (θ / Real.pi) := one_div_le_one_div_of_le (by positivity) hJordan
    _ = Real.pi / θ := by field_simp

theorem angularDirichletWeight_lower (n k : ℕ) (hk : 1 ≤ k) {θ : ℝ}
    (hθ0 : 0 < θ) (hθk : θ ≤ 1 / (k : ℝ)) :
    (k : ℝ) ^ (2 * (n + 3)) * (2 / Real.pi) ^ (n - 2) * θ ^ (n - 2) ≤
      angularDirichletWeight n k θ := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hθ1 : θ ≤ 1 := hθk.trans ((div_le_one hkpos).2 hkR)
  have hsin : (2 / Real.pi) * θ ≤ Real.sin θ :=
    Real.mul_le_sin hθ0.le (by linarith [Real.pi_gt_three])
  have hD := (quotientDirichlet_lower k hk hθ0 hθk).trans
    (le_abs_self (quotientDirichlet k θ))
  unfold angularDirichletWeight
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg k) hD _)
    (pow_le_pow_left₀ (by positivity) hsin _) (by positivity) (by positivity)

end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
