import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.DirichletMoments

/-!
# Weighted cosine moments and finite polynomial matching

These statements concern interval integrals and abstract polynomial functionals.
No identification of an external spherical measure is assumed or asserted.
-/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants

open MeasureTheory Set
open scoped Interval

def weightedCosineIntegral (s m : ℕ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ m * Real.sin θ ^ s

def normalizedCosineMoment (s m : ℕ) : ℝ :=
  weightedCosineIntegral s m / weightedCosineIntegral s 0

theorem weightedCosineIntegral_intervalIntegrable (s m : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun θ ↦ Real.cos θ ^ m * Real.sin θ ^ s) volume a b :=
  ((Real.continuous_cos.pow m).mul (Real.continuous_sin.pow s)).intervalIntegrable _ _

theorem weightedCosineIntegral_mass_pos (s : ℕ) : 0 < weightedCosineIntegral s 0 := by
  unfold weightedCosineIntegral
  apply intervalIntegral.integral_pos Real.pi_pos
    (((Real.continuous_cos.pow 0).mul (Real.continuous_sin.pow s)).continuousOn)
  · intro θ hθ
    exact mul_nonneg (by simp) (pow_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2) _)
  · refine ⟨Real.pi / 2, ⟨by positivity, by linarith [Real.pi_pos]⟩, ?_⟩
    simp

theorem hasDerivAt_cosine_moment_primitive (s m : ℕ) (θ : ℝ) :
    HasDerivAt (fun u ↦ Real.cos u ^ (m + 1) * Real.sin u ^ (s + 1))
      ((((m + s + 2 : ℕ) : ℝ) * (Real.cos θ ^ (m + 2) * Real.sin θ ^ s)) -
        ((m + 1 : ℕ) : ℝ) * (Real.cos θ ^ m * Real.sin θ ^ s)) θ := by
  have h := ((Real.hasDerivAt_cos θ).pow (m + 1)).mul
    ((Real.hasDerivAt_sin θ).pow (s + 1))
  simp only [Nat.add_sub_cancel] at h
  convert h using 1
  push_cast
  simp only [pow_add, pow_one, Pi.pow_apply]
  linear_combination (((m : ℝ) + 1) * Real.cos θ ^ m * Real.sin θ ^ s) *
    (Real.sin_sq_add_cos_sq θ)

/-- The recurrence for all weighted cosine moments, without parity restrictions. -/
theorem weightedCosineIntegral_recurrence (s m : ℕ) :
    (((m + s + 2 : ℕ) : ℝ)) * weightedCosineIntegral s (m + 2) =
      (((m + 1 : ℕ) : ℝ)) * weightedCosineIntegral s m := by
  have hi1 := (weightedCosineIntegral_intervalIntegrable s (m + 2) 0 Real.pi).const_mul
    (((m + s + 2 : ℕ) : ℝ))
  have hi2 := (weightedCosineIntegral_intervalIntegrable s m 0 Real.pi).const_mul
    (((m + 1 : ℕ) : ℝ))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := Real.pi)
    (fun θ _ ↦ hasDerivAt_cosine_moment_primitive s m θ) (hi1.sub hi2)
  rw [intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hFTC
  simp only [Real.sin_pi, Real.sin_zero, zero_pow (Nat.succ_ne_zero _), mul_zero,
    sub_self] at hFTC
  exact sub_eq_zero.mp hFTC

theorem weightedCosineIntegral_odd (s q : ℕ) :
    weightedCosineIntegral s (2 * q + 1) = 0 := by
  have hreflect := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := Real.pi)
    (fun θ ↦ Real.cos θ ^ (2 * q + 1) * Real.sin θ ^ s) Real.pi
  have hnegative : (fun θ : ℝ ↦ Real.cos (Real.pi - θ) ^ (2 * q + 1) *
      Real.sin (Real.pi - θ) ^ s) =
      fun θ ↦ -(Real.cos θ ^ (2 * q + 1) * Real.sin θ ^ s) := by
    funext θ
    simp [Real.cos_pi_sub, Real.sin_pi_sub, pow_add, pow_mul]
  rw [hnegative, intervalIntegral.integral_neg] at hreflect
  simp only [sub_self, sub_zero] at hreflect
  change -weightedCosineIntegral s (2 * q + 1) = weightedCosineIntegral s (2 * q + 1) at hreflect
  linarith

@[simp] theorem normalizedCosineMoment_zero (s : ℕ) : normalizedCosineMoment s 0 = 1 := by
  exact div_self (weightedCosineIntegral_mass_pos s).ne'

@[simp] theorem normalizedCosineMoment_odd (s q : ℕ) :
    normalizedCosineMoment s (2 * q + 1) = 0 := by
  simp only [normalizedCosineMoment, weightedCosineIntegral_odd, zero_div]

theorem normalizedCosineMoment_recurrence (s m : ℕ) :
    (((m + s + 2 : ℕ) : ℝ)) * normalizedCosineMoment s (m + 2) =
      (((m + 1 : ℕ) : ℝ)) * normalizedCosineMoment s m := by
  unfold normalizedCosineMoment
  rw [← mul_div_assoc, ← mul_div_assoc, weightedCosineIntegral_recurrence]

/-- Ambient-dimension form, with angular weight `sin θ^(n-2)`. -/
theorem normalizedCosineMoment_ambient_recurrence (n m : ℕ) (hn : 2 ≤ n) :
    (((m + n : ℕ) : ℝ)) * normalizedCosineMoment (n - 2) (m + 2) =
      (((m + 1 : ℕ) : ℝ)) * normalizedCosineMoment (n - 2) m := by
  simpa only [show m + (n - 2) + 2 = m + n by omega] using
    normalizedCosineMoment_recurrence (n - 2) m

theorem polynomialCosine_intervalIntegrable (s : ℕ) (p : Polynomial ℝ) (a b : ℝ) :
    IntervalIntegrable (fun θ ↦ p.eval (Real.cos θ) * Real.sin θ ^ s) volume a b := by
  have hc : Continuous (fun θ ↦ p.eval (Real.cos θ) * Real.sin θ ^ s) := by fun_prop
  exact hc.intervalIntegrable _ _

/-- The normalized weighted-cosine integral is an actual real-linear functional
on univariate polynomials. -/
def normalizedZonalFunctional (s : ℕ) : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun p := (∫ θ in (0 : ℝ)..Real.pi, p.eval (Real.cos θ) * Real.sin θ ^ s) /
    weightedCosineIntegral s 0
  map_add' p q := by
    simp only [Polynomial.eval_add, add_mul]
    rw [intervalIntegral.integral_add
      (polynomialCosine_intervalIntegrable s p _ _)
      (polynomialCosine_intervalIntegrable s q _ _)]
    ring
  map_smul' c p := by
    simp only [Polynomial.smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C,
      mul_assoc]
    rw [intervalIntegral.integral_const_mul]
    simp only [RingHom.id_apply, smul_eq_mul]
    ring

@[simp] theorem normalizedZonalFunctional_X_pow (s m : ℕ) :
    normalizedZonalFunctional s (Polynomial.X ^ m) = normalizedCosineMoment s m := by
  simp only [normalizedZonalFunctional, LinearMap.coe_mk, AddHom.coe_mk,
    Polynomial.eval_pow, Polynomial.eval_X, normalizedCosineMoment, weightedCosineIntegral]

/-- A two-step moment recurrence and its first two values determine every moment. -/
theorem zonal_moment_sequence_unique (s : ℕ) (u v : ℕ → ℝ)
    (h0 : u 0 = v 0) (h1 : u 1 = v 1)
    (hu : ∀ m, (((m + s + 2 : ℕ) : ℝ)) * u (m + 2) =
      (((m + 1 : ℕ) : ℝ)) * u m)
    (hv : ∀ m, (((m + s + 2 : ℕ) : ℝ)) * v (m + 2) =
      (((m + 1 : ℕ) : ℝ)) * v m) : ∀ m, u m = v m := by
  intro m
  induction m using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more m hm hm1 =>
      have hc : (((m + s + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
      apply mul_left_cancel₀ hc
      rw [hu, hv, hm]

/-- Equality on monomial moments determines a polynomial linear functional. -/
theorem polynomial_functional_eq_of_moments (L T : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hmom : ∀ m, L (Polynomial.X ^ m) = T (Polynomial.X ^ m)) : L = T := by
  apply LinearMap.ext
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial m a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.smul_eq_C_mul]
      simp only [map_smul, hmom]

/-- A spherical polynomial functional can be matched with the actual angular
integral by proving this finite moment recurrence and its first two values.
No such recurrence for an external sphere measure is assumed by the module. -/
theorem polynomial_functional_eq_zonal_of_recurrence (s : ℕ)
    (L : Polynomial ℝ →ₗ[ℝ] ℝ) (h0 : L 1 = 1) (h1 : L Polynomial.X = 0)
    (hrec : ∀ m, (((m + s + 2 : ℕ) : ℝ)) * L (Polynomial.X ^ (m + 2)) =
      (((m + 1 : ℕ) : ℝ)) * L (Polynomial.X ^ m)) :
    L = normalizedZonalFunctional s := by
  have hfirst : normalizedCosineMoment s 1 = 0 := normalizedCosineMoment_odd s 0
  have hmom := zonal_moment_sequence_unique s
    (fun m ↦ L (Polynomial.X ^ m)) (normalizedCosineMoment s)
    (by simpa only [pow_zero, normalizedCosineMoment_zero] using h0)
    (by simpa only [pow_one, hfirst] using h1)
    hrec (normalizedCosineMoment_recurrence s)
  apply polynomial_functional_eq_of_moments
  intro m
  rw [normalizedZonalFunctional_X_pow]
  exact hmom m

end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
