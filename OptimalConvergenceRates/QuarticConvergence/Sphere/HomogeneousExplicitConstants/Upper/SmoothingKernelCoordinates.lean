import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.PolynomialSmoothingKernel

/-! Actual coordinate-block moments and numerical eigenvalue bounds for
the polynomial smoothing kernel. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace SmoothingKernelCoordinates

open scoped BigOperators InnerProductSpace
open MeasureTheory SphereMeasure SphereMoments PolynomialSmoothingKernel

theorem kernel_even_square {n : ℕ} (s : ℕ) (x : E n) (y : Sphere n) :
    kernel (2*s) x y=((1+⟪x,y.1⟫_ℝ)^s/Real.sqrt (normalization n (2*s)))^2 := by
  rw [kernel_eval,div_pow,Real.sq_sqrt (normalization_pos n (2*s)).le]
  rw [show 2*s=s*2 by omega,pow_mul]

theorem kernel_coordinate {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (x : Sphere n) (i : Fin n) :
    (∫ y : Sphere n,kernel k x.1 y*y.1 i ∂surface n)=lambda1 n k*x.1 i := by
  simpa [axis,EuclideanSpace.inner_single_left,EuclideanSpace.inner_single_right]
    using kernel_linear hn k x (axis i)

theorem kernel_coordinate_sq {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (x : Sphere n) (i : Fin n) :
    (∫ y : Sphere n,kernel k x.1 y*y.1 i^2 ∂surface n)=
      lambda2 n k*x.1 i^2+(1-lambda2 n k)/(n:ℝ) := by
  simpa [axis,EuclideanSpace.inner_single_left,EuclideanSpace.inner_single_right,PiLp.norm_single]
    using
    kernel_quadratic hn k x (axis i)

def blockRadius {n : ℕ} (U : Finset (Fin n)) (x : E n) : ℝ := ∑ i ∈ U,x i^2

theorem kernel_blockRadius {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (x : Sphere n)
    (U : Finset (Fin n)) :
    (∫ y : Sphere n,kernel k x.1 y*blockRadius U y.1 ∂surface n)=
      lambda2 n k*blockRadius U x.1+(1-lambda2 n k)*(U.card:ℝ)/(n:ℝ) := by
  unfold blockRadius
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · simp_rw [kernel_coordinate_sq hn k x]
    rw [Finset.sum_add_distrib,←Finset.mul_sum]
    simp only [Finset.sum_const,nsmul_eq_mul]
    ring
  · intro i _
    have hi := (ZonalSmoothingAction.integrable_weighted (by omega : 0 < n)
      x.1 (axis i) 2 (SmoothingMoments.kernelPower k)).div_const (normalization n k)
    simpa [kernel,axis,EuclideanSpace.inner_single_left,div_mul_eq_mul_div] using hi

theorem lambda1_pos {n k : ℕ} (hn : 2 ≤ n) (hk : 0 < k) : 0 < lambda1 n k := by
  have hnreal : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hkreal : (0:ℝ) < k := by exact_mod_cast hk
  unfold lambda1
  exact div_pos hkreal (by linarith)

theorem lambda1_gt_half {n k : ℕ} (hn : 2 ≤ n) (hk : n ≤ k) :
    (1/2:ℝ) < lambda1 n k := by
  have hnreal : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hkreal : (n:ℝ) ≤ k := by exact_mod_cast hk
  unfold lambda1
  apply (lt_div_iff₀ (by linarith : (0:ℝ) < (k:ℝ)+(n:ℝ)-1)).mpr
  linarith

theorem lambda2_nonnegative {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) : 0 ≤ lambda2 n k := by
  rw [lambda2_explicit hn]
  have hnreal : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hkreal : (1:ℝ) ≤ k := by exact_mod_cast hk
  apply div_nonneg
  · exact mul_nonneg (by positivity) (by linarith)
  · apply mul_nonneg <;> linarith

theorem lambda2_le_one {n k : ℕ} (hn : 2 ≤ n) : lambda2 n k ≤ 1 := by
  rw [lambda2_explicit hn]
  have hnreal : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hkreal : (0:ℝ) ≤ k := by positivity
  have hden1 : (0:ℝ) < (k:ℝ)+(n:ℝ)-1 := by linarith
  have hden2 : (0:ℝ) < (k:ℝ)+(n:ℝ) := by linarith
  apply (div_le_one (mul_pos hden1 hden2)).mpr
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ n)
    (by linarith : (0:ℝ) ≤ 2*(k:ℝ)+(n:ℝ)-1)]

theorem smoothing_order_ge_dimension (n : ℕ) : n ≤ 4*((n+3)/4) := by omega

theorem smoothing_lambda1_gt_half {n : ℕ} (hn : 2 ≤ n) :
    (1/2:ℝ) < lambda1 n (4*((n+3)/4)) :=
  lambda1_gt_half hn (smoothing_order_ge_dimension n)

end SmoothingKernelCoordinates
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
