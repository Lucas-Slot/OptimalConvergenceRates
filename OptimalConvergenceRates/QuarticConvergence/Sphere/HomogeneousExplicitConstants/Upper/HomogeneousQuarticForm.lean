import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.QuarticPolarization
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.Compactness
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.SphereCurve
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Polynomial

/-! Actual homogeneous quartics represented by a symmetric continuous
four-linear form on the Euclidean model. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem iteratedDeriv_fourth_power (c : ℝ) :
    iteratedDeriv 4 (fun t : ℝ ↦ t ^ 4 * c) 0 = 24 * c := by
  have hlin : deriv (fun t : ℝ ↦ 2 * t) 0 = 2 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).deriv
  norm_num [iteratedDeriv_succ', iteratedDeriv_zero,
    deriv_mul_const_field', deriv_const_mul_field', deriv_pow', hlin]

theorem homogeneousFourthDerivative_diagonal (f : E → ℝ)
    (hf : ContDiff ℝ 4 f)
    (hscale : ∀ (t : ℝ) (x : E), f (t • x) = t ^ 4 * f x) (x : E) :
    iteratedFDeriv ℝ 4 f 0 (fun _ ↦ x) = 24 * f x := by
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ x
  have hcomp : f ∘ L = fun t : ℝ ↦ t ^ 4 * f x := by
    ext t
    exact hscale t x
  have h := congrArg (fun B : ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ ℝ) ℝ =>
      B (fun _ ↦ 1)) (L.iteratedFDeriv_comp_right hf 0 (i := 4) le_rfl)
  rw [hcomp] at h
  change iteratedDeriv 4 (fun t : ℝ ↦ t ^ 4 * f x) 0 = _ at h
  rw [iteratedDeriv_fourth_power] at h
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    L, ContinuousLinearMap.toSpanSingleton_apply, one_smul, map_zero] using h.symm

def euclideanPolynomialEval {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  MvPolynomial.eval (fun i ↦ x i) p

theorem euclideanPolynomialEval_analytic {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    AnalyticOnNhd ℝ (euclideanPolynomialEval p) Set.univ := by
  exact AnalyticOnNhd.eval_continuousLinearMap
    (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap p

theorem euclideanPolynomialEval_contDiff {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    ContDiff ℝ 4 (euclideanPolynomialEval p) :=
  (euclideanPolynomialEval_analytic p).contDiff

theorem euclideanPolynomialEval_scale {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous 4) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    euclideanPolynomialEval p (t • x) = t ^ 4 * euclideanPolynomialEval p x := by
  simpa only [euclideanPolynomialEval, PiLp.smul_apply, smul_eq_mul] using
    Foundation.homogeneous_eval_scale p 4 hp t (fun i ↦ x i)

def homogeneousQuarticForm {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ EuclideanSpace ℝ (Fin n)) ℝ :=
  (1 / 24 : ℝ) • iteratedFDeriv ℝ 4 (euclideanPolynomialEval p) 0

theorem homogeneousQuarticForm_symmetric {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    SymmetricQuarticForm (homogeneousQuarticForm p) := by
  intro σ v
  simp only [homogeneousQuarticForm, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  exact (euclideanPolynomialEval_analytic p).analyticOn.iteratedFDeriv_comp_perm v σ

theorem homogeneousQuarticForm_diagonal {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous 4) (x : EuclideanSpace ℝ (Fin n)) :
    homogeneousQuarticForm p (fun _ ↦ x) = euclideanPolynomialEval p x := by
  simp only [homogeneousQuarticForm, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [homogeneousFourthDerivative_diagonal (euclideanPolynomialEval p)
    (euclideanPolynomialEval_contDiff p) (euclideanPolynomialEval_scale p hp)]
  ring

theorem euclideanPolynomialEval_zero {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous 4) : euclideanPolynomialEval p 0 = 0 := by
  simpa using euclideanPolynomialEval_scale p hp (0 : ℝ) (0 : EuclideanSpace ℝ (Fin n))

theorem polynomial_sphereSupNorm_nonneg {n : ℕ} (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) : 0 ≤ Foundation.sphereSupNorm p := by
  obtain ⟨x, _, hx⟩ := Foundation.sphereSupNorm_attained hn p
  exact hx ▸ abs_nonneg _

theorem euclideanPolynomialEval_homogeneous_bound {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous 4) (x : EuclideanSpace ℝ (Fin n)) :
    |euclideanPolynomialEval p x| ≤ Foundation.sphereSupNorm p * ‖x‖ ^ 4 := by
  by_cases hx : x = 0
  · simp only [hx, euclideanPolynomialEval_zero p hp, abs_zero, norm_zero, zero_pow
      (by norm_num : (4 : ℕ) ≠ 0), mul_zero, le_refl]
  · let y : EuclideanSpace ℝ (Fin n) := ‖x‖⁻¹ • x
    have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hynorm : ‖y‖ = 1 := by
      dsimp [y]
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxnorm]
    have hySphere : (fun i ↦ y i) ∈ Foundation.unitSphere n := by
      have hy : y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
        simpa only [mem_sphere_zero_iff_norm] using hynorm
      rw [EuclideanSpace.sphere_zero_eq 1 zero_le_one] at hy
      simpa only [Foundation.unitSphere, one_pow] using! hy
    have hyeval : |euclideanPolynomialEval p y| ≤ Foundation.sphereSupNorm p :=
      Foundation.abs_eval_le_sphereSupNorm p (fun i ↦ y i) hySphere
    have hxscale : x = ‖x‖ • y := by
      dsimp [y]
      rw [smul_smul, mul_inv_cancel₀ hxnorm, one_smul]
    calc
      |euclideanPolynomialEval p x| = |‖x‖ ^ 4 * euclideanPolynomialEval p y| := by
        conv_lhs => rw [hxscale, euclideanPolynomialEval_scale p hp]
      _ = ‖x‖ ^ 4 * |euclideanPolynomialEval p y| := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
      _ ≤ ‖x‖ ^ 4 * Foundation.sphereSupNorm p :=
        mul_le_mul_of_nonneg_left hyeval (pow_nonneg (norm_nonneg _) _)
      _ = _ := mul_comm _ _

/-- The actual Euclidean quartic tensor has a dimension-free norm bound by
its actual polynomial sphere sup norm. -/
theorem homogeneousQuarticForm_opNorm_bound {n : ℕ} (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous 4) :
    ‖homogeneousQuarticForm p‖ ≤ (32 / 3 : ℝ) * Foundation.sphereSupNorm p := by
  apply symmetricQuarticForm_opNorm_bound (homogeneousQuarticForm p)
    (homogeneousQuarticForm_symmetric p) (Foundation.sphereSupNorm p)
    (polynomial_sphereSupNorm_nonneg hn p)
  intro x
  rw [homogeneousQuarticForm_diagonal p hp]
  exact euclideanPolynomialEval_homogeneous_bound p hp x

/-- Every actual finite homogeneous real quartic admits this representation;
no representation premise is imposed on the polynomial. -/
theorem exists_homogeneousQuarticForm {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous 4) :
    ∃ A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ EuclideanSpace ℝ (Fin n)) ℝ,
      SymmetricQuarticForm A ∧ ∀ x, A (fun _ ↦ x) = euclideanPolynomialEval p x :=
  ⟨homogeneousQuarticForm p, homogeneousQuarticForm_symmetric p,
    homogeneousQuarticForm_diagonal p hp⟩

theorem exists_homogeneousQuarticForm_bounded {n : ℕ} (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous 4) :
    ∃ A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ EuclideanSpace ℝ (Fin n)) ℝ,
      SymmetricQuarticForm A ∧
      (∀ x, A (fun _ ↦ x) = euclideanPolynomialEval p x) ∧
      ‖A‖ ≤ (32 / 3 : ℝ) * Foundation.sphereSupNorm p :=
  ⟨homogeneousQuarticForm p, homogeneousQuarticForm_symmetric p,
    homogeneousQuarticForm_diagonal p hp, homogeneousQuarticForm_opNorm_bound hn p hp⟩

end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
