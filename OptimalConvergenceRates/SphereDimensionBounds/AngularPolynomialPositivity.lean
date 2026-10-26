import OptimalConvergenceRates.SphereDimensionBounds.ZonalMoments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Strict positivity of actual angular polynomial square integrals. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.AngularPolynomialPositivity

open Polynomial Set MeasureTheory

theorem exists_nonzero_in_interval (p : Polynomial ℝ) (hp : p ≠ 0)
    (a b : ℝ) (hab : a < b) : ∃ x ∈ Set.Ioo a b,p.eval x ≠ 0 := by
  by_contra h
  have hs : Set.Ioo a b ⊆ {x | p.IsRoot x} := by
    intro x hx
    change p.eval x=0
    by_contra hp0
    exact h ⟨x,hx,hp0⟩
  exact (Set.Ioo_infinite hab) ((Polynomial.finite_setOfPred_isRoot hp).subset hs)

theorem zonal_pos (s : ℕ) (p : Polynomial ℝ)
    (hpos : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ p.eval x)
    (hex : ∃ x ∈ Set.Ioo (-1 : ℝ) 1, 0 < p.eval x) :
    0 < normalizedZonalFunctional s p := by
  change 0 < (∫ theta in (0:ℝ)..Real.pi,p.eval (Real.cos theta)*Real.sin theta^s)/
    weightedCosineIntegral s 0
  apply div_pos _ (weightedCosineIntegral_mass_pos s)
  apply intervalIntegral.integral_pos Real.pi_pos
    (show Continuous (fun theta : ℝ => p.eval (Real.cos theta)*Real.sin theta^s) by fun_prop).continuousOn
  · intro theta htheta
    exact mul_nonneg (hpos _ ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩)
      (pow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi htheta.1.le htheta.2) _)
  · obtain ⟨x,hx,hpx⟩ := hex
    let theta := Real.arccos x
    have htheta0 : 0 < theta := Real.arccos_pos.mpr hx.2
    have hthetaPi : theta < Real.pi := by
      apply lt_of_le_of_ne (Real.arccos_le_pi x)
      intro heq
      have hh := Real.arccos_eq_pi.mp heq
      linarith [hx.1]
    refine ⟨theta,⟨htheta0.le,hthetaPi.le⟩,?_⟩
    rw [Real.cos_arccos hx.1.le hx.2.le]
    exact mul_pos hpx (pow_pos (Real.sin_pos_of_pos_of_lt_pi htheta0 hthetaPi) _)

theorem zonal_square_pos (s : ℕ) (p : Polynomial ℝ) (hp : p ≠ 0) :
    0 < normalizedZonalFunctional s (p^2) := by
  apply zonal_pos
  · intro x _
    rw [Polynomial.eval_pow]
    exact sq_nonneg _
  · obtain ⟨x,hx,hpx⟩ := exists_nonzero_in_interval p hp (-1) 1 (by norm_num)
    refine ⟨x,hx,?_⟩
    rw [Polynomial.eval_pow]
    exact sq_pos_of_ne_zero hpx

theorem zonal_left_weight_square_pos (s : ℕ) (p : Polynomial ℝ) (hp : p ≠ 0) :
    0 < normalizedZonalFunctional s ((1+X)*p^2) := by
  apply zonal_pos
  · intro x hx
    simp only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_one,
      Polynomial.eval_X,Polynomial.eval_pow]
    exact mul_nonneg (by linarith [hx.1]) (sq_nonneg _)
  · obtain ⟨x,hx,hpx⟩ := exists_nonzero_in_interval p hp (-1) 1 (by norm_num)
    refine ⟨x,hx,?_⟩
    simp only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_one,
      Polynomial.eval_X,Polynomial.eval_pow]
    exact mul_pos (by linarith [hx.1]) (sq_pos_of_ne_zero hpx)

theorem zonal_right_weight_square_pos (s : ℕ) (p : Polynomial ℝ) (hp : p ≠ 0) :
    0 < normalizedZonalFunctional s ((1-X)*p^2) := by
  apply zonal_pos
  · intro x hx
    simp only [Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_one,
      Polynomial.eval_X,Polynomial.eval_pow]
    exact mul_nonneg (by linarith [hx.2]) (sq_nonneg _)
  · obtain ⟨x,hx,hpx⟩ := exists_nonzero_in_interval p hp (-1) 1 (by norm_num)
    refine ⟨x,hx,?_⟩
    simp only [Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_one,
      Polynomial.eval_X,Polynomial.eval_pow]
    exact mul_pos (by linarith [hx.2]) (sq_pos_of_ne_zero hpx)

end OptimalConvergenceRates.SphereDimensionBounds.AngularPolynomialPositivity
