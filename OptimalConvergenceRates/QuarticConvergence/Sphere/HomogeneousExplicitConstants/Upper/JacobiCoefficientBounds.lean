import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.GegenbauerJacobi

/-! Quantitative bounds for the actual positive Jacobi coefficients.
The later two-dimensional spectral and quadrature arguments are separate. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace JacobiCoefficientBounds

open GegenbauerJacobi

theorem sqrt_one_sub_lower {u : ℝ} (hu : 0 ≤ u) (huq : u ≤ 1 / 4) :
    1-(3/5:ℝ)*u ≤ Real.sqrt (1-u) := by
  have hr : 0 ≤ 1-u := by linarith
  apply (sq_le_sq₀ (by linarith : 0 ≤ 1-(3/5:ℝ)*u) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hr]
  nlinarith [mul_nonneg hu (by linarith : 0 ≤ 5-9*u)]

theorem delta_bounds (N J L : ℝ) (hN : 4 ≤ N) (hL : 3 * N ≤ L) (hJ : L ≤ 3 * J) :
    0 ≤ ((N-2)*(N-4))/((2*J+N-4)*(2*J+N-2)) ∧
    ((N-2)*(N-4))/((2*J+N-4)*(2*J+N-2)) ≤ 9*N^2/(4*L^2) ∧
    9*N^2/(4*L^2) ≤ 1/4 := by
  have hLp : 0 < L := by linarith
  have hJp : 0 < J := by linarith
  have hden : 0 < (2*J+N-4)*(2*J+N-2) := mul_pos (by linarith) (by linarith)
  have hJden : 0 < 4*J^2 := by positivity
  have hLden : 0 < 4*L^2 := by positivity
  have hdenBound : 4*J^2 ≤ (2*J+N-4)*(2*J+N-2) := by
    have hh := mul_le_mul (by linarith : 2*J ≤ 2*J+N-4)
      (by linarith : 2*J ≤ 2*J+N-2) (by positivity : 0 ≤ 2*J)
      (by linarith : 0 ≤ 2*J+N-4)
    nlinarith
  have hnum : (N-2)*(N-4) ≤ N^2 := by nlinarith
  have hfirst : ((N-2)*(N-4))/((2*J+N-4)*(2*J+N-2)) ≤ N^2/(4*J^2) := by
    exact (div_le_div_of_nonneg_right hnum hden.le).trans
      (div_le_div_of_nonneg_left (sq_nonneg N) hJden hdenBound)
  have hsq : L^2 ≤ 9*J^2 := by
    have hh := (sq_le_sq₀ hLp.le (by positivity : 0 ≤ 3*J)).mpr hJ
    nlinarith
  have hsecond : N^2/(4*J^2) ≤ 9*N^2/(4*L^2) := by
    apply (div_le_div_iff₀ hJden hLden).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg N)]
  refine ⟨div_nonneg (mul_nonneg (by linarith) (by linarith)) hden.le,
    hfirst.trans hsecond,?_⟩
  apply (div_le_iff₀ hLden).mpr
  have hh := (sq_le_sq₀ (by linarith : 0 ≤ 3*N) hLp.le).mpr hL
  nlinarith

theorem coefficient_lower {N ell j : ℕ} (hN : 15 ≤ N) (hL : 3 * N ≤ ell)
    (hJ : ell ≤ 3 * (j + 1)) :
    1-(27/20:ℝ)*(N:ℝ)^2/(ell:ℝ)^2 ≤ 2*coefficient N j := by
  have hNR : (4:ℝ) ≤ N := by exact_mod_cast (show 4 ≤ N by omega)
  have hLR : 3*(N:ℝ) ≤ ell := by exact_mod_cast hL
  have hJR : (ell:ℝ) ≤ 3*((j:ℝ)+1) := by exact_mod_cast hJ
  have hb := delta_bounds (N:ℝ) ((j:ℝ)+1) (ell:ℝ) hNR hLR hJR
  have ha : 2*((j:ℝ)+1)+(N:ℝ)-4=2*(j:ℝ)+(N:ℝ)-2 := by ring
  have hc : 2*((j:ℝ)+1)+(N:ℝ)-2=2*(j:ℝ)+(N:ℝ) := by ring
  rw [ha,hc] at hb
  have hs := sqrt_one_sub_lower hb.1 (hb.2.1.trans hb.2.2)
  rw [←two_coefficient_sqrt (by omega : 3 ≤ N) j] at hs
  have hid : (27/20:ℝ)*(N:ℝ)^2/(ell:ℝ)^2=
      (3/5:ℝ)*(9*(N:ℝ)^2/(4*(ell:ℝ)^2)) := by ring
  rw [hid]
  linarith [hb.2.1]

end JacobiCoefficientBounds
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
