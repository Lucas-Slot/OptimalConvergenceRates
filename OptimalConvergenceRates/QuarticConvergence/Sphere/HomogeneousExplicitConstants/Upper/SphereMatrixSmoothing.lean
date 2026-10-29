import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.PolynomialKernelFeatures
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.WeightedMatrixKernelSmoothing
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.SmoothingKernelCoordinates

/-! Actual normalized sphere smoothing with the coordinate-block radius
retained in the matrix-SOS top term. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace SphereMatrixSmoothing

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
open MeasureTheory Matrix MvPolynomial SphereMeasure PolynomialSmoothingKernel
  SmoothingKernelCoordinates PolynomialKernelFeatures

abbrev P (n : ℕ) := Foundation.Polynomial n

def blockBound {n : ℕ} (b0 : ℝ) (U : Finset (Fin n)) (y : Sphere n) : ℝ :=
  b0*Real.sqrt (blockRadius U y.1)

theorem blockRadius_nonnegative {n : ℕ} (U : Finset (Fin n)) (y : E n) :
    0≤blockRadius U y := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem blockRadius_le_one {n : ℕ} (U : Finset (Fin n)) (y : Sphere n) :
    blockRadius U y.1≤1 := by
  have hy := SphereMeasure.coordinates_unitSphere y
  change (∑i, y.1 i^2)=1 at hy
  rw [←hy]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
  intro i _ _
  exact sq_nonneg _

theorem blockBound_nonnegative {n : ℕ} {b0 : ℝ} (hb0 : 0 ≤ b0) (U : Finset (Fin n)) (y : Sphere n) :
    0≤blockBound b0 U y := mul_nonneg hb0 (Real.sqrt_nonneg _)

theorem blockBound_le {n : ℕ} {b0 : ℝ} (hb0 : 0 ≤ b0) (U : Finset (Fin n)) (y : Sphere n) :
    blockBound b0 U y≤b0 := by
  exact mul_le_of_le_one_right hb0 (Real.sqrt_le_one.mpr (blockRadius_le_one U y))

theorem blockBound_sq {n : ℕ} (b0 : ℝ) (U : Finset (Fin n)) (y : Sphere n) :
    blockBound b0 U y^2=b0^2*blockRadius U y.1 := by
  rw [blockBound,mul_pow,Real.sq_sqrt (blockRadius_nonnegative U y.1)]

theorem blockBound_continuous {n : ℕ} (b0 : ℝ) (U : Finset (Fin n)) :
    Continuous (blockBound b0 U) := by
  apply continuous_const.mul
  apply Real.continuous_sqrt.comp
  unfold blockRadius
  apply continuous_finsetSum
  intro i _
  exact ((EuclideanSpace.proj i).continuous.comp continuous_subtype_val).pow 2

theorem block_coefficient_products_integrable {n s : ℕ} (hn : 0 < n) (b0 : ℝ)
    (U : Finset (Fin n)) (α β : Feature n s) :
    Integrable (fun y : Sphere n ↦ coefficient y α*coefficient y β*blockBound b0 U y^2) (surface
      n) :=
  SphereMeasure.integrable_continuous hn _
    (((coefficient_continuous α).mul (coefficient_continuous β)).mul
      ((blockBound_continuous b0 U).pow 2))

theorem topPolynomial_block_eval {n s : ℕ} (hn : 2 ≤ n) (b0 : ℝ)
    (U : Finset (Fin n)) (x : Sphere n) :
    eval (fun i ↦ x.1 i) (WeightedMatrixKernelSmoothing.topPolynomial (surface n)
      (coefficient (s:=s)) (featurePolynomial (s:=s)) (blockBound b0 U))=
      b0^2*(lambda2 n (2*s)*blockRadius U x.1+
        (1-lambda2 n (2*s))*(U.card:ℝ)/(n:ℝ)) := by
  rw [WeightedMatrixKernelSmoothing.topPolynomial,
    MatrixKernelSmoothing.weightedPolynomial_eval (surface n) coefficient featurePolynomial _
      (block_coefficient_products_integrable (by omega) b0 U) (fun i ↦ x.1 i)]
  simp_rw [normalized_root_square,blockBound_sq]
  have heq : (fun y : Sphere n ↦ kernel (2*s) x.1 y*(b0^2*blockRadius U y.1))=
      (fun y : Sphere n ↦ b0^2*(kernel (2*s) x.1 y*blockRadius U y.1)) := by
    funext y
    ring
  rw [heq,integral_const_mul,kernel_blockRadius hn]

/-- The actual even-power sphere kernel produces a finite matrix SOS of
root degree3s with top b0²[λ2 R_U+(1−λ2)|U|/n], preserving the block radius. -/
theorem block_field_kernel_sphereSOS {n s d e : ℕ} (hn : 2 ≤ n) {b0 : ℝ} (hb0 : 0 ≤ b0)
    (U : Finset (Fin n)) (F : Sphere n → Matrix (Fin d) (Fin e) ℝ)
    (hFmeas : ∀ u v, Measurable (fun y ↦ F y u v))
    (hFnorm : ∀ y, ‖F y‖ ≤ blockBound b0 U y) :
    ∃ N : Matrix (Fin d) (Fin d) (P n), FiniteMatrixVariance.BoundedMatrixSOS (3*s) N ∧
      ∀x : Sphere n,∀u v,eval (fun i ↦ x.1 i) (N u v)=
        (b0^2*(lambda2 n (2*s)*blockRadius U x.1+
          (1-lambda2 n (2*s))*(U.card:ℝ)/(n:ℝ)))*(if u=v then 1 else 0)-
        ∑k,eval (fun i ↦ x.1 i) (MatrixKernelSmoothing.meanMatrix (surface n)
          (coefficient (s:=s)) (featurePolynomial (s:=s)) F u k)*
          eval (fun i ↦ x.1 i) (MatrixKernelSmoothing.meanMatrix (surface n)
          (coefficient (s:=s)) (featurePolynomial (s:=s)) F v k) := by
  have hFprod (α β : Feature n s) (u : Fin d) (v : Fin e) :
      Integrable (fun y : Sphere n ↦ coefficient y α*coefficient y β*F y u v) (surface n) := by
    apply weighted_coefficient_products_integrable (by omega) α β _ (hFmeas u v)
    exact ⟨b0,fun y ↦ (matrix_entry_le_operatorNorm (F y) u v).trans
      ((hFnorm y).trans (blockBound_le hb0 U y))⟩
  obtain ⟨N,hN,hNeval⟩ := WeightedMatrixKernelSmoothing.exists_weighted_matrix_sphereSOS
    (surface n) (coefficient (s:=s)) (featurePolynomial (s:=s)) featurePolynomial_degree F
    (blockBound b0 U) (blockBound_nonnegative hb0 U) hFnorm
    (coefficient_products_integrable (by omega))
    (block_coefficient_products_integrable (by omega) b0 U) hFprod
    (normalized_root_mass_algebraic hn)
  refine ⟨N,hN,?_⟩
  intro x u v
  have he := hNeval (fun i ↦ x.1 i) (SphereMeasure.coordinates_unitSphere x) u v
  rw [topPolynomial_block_eval hn b0 U x] at he
  exact he

end SphereMatrixSmoothing
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
