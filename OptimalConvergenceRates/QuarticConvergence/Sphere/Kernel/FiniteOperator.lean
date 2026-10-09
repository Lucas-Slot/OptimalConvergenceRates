/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Kernel/FiniteOperator.lean

  Finite positive quadrature operators built from zonal Dirichlet kernel sections.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.PolynomialRange

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

/-- The finite zonal-kernel transform as a linear map from sampled values to
ambient polynomials. -/
noncomputable def finiteZonalKernelOperator {n N : ℕ}
    (p k : ℕ) (w : Fin N → ℝ) (y : Fin N → Fin n → ℝ) :
    (Fin N → ℝ) →ₗ[ℝ] MvPolynomial (Fin n) ℝ where
  toFun a := finiteZonalKernelSum p k (fun i ↦ w i * a i) y
  map_add' := by
    intro a b
    unfold finiteZonalKernelSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply, mul_add, map_add]
    ring
  map_smul' := by
    intro c a
    unfold finiteZonalKernelSum
    rw [MvPolynomial.smul_eq_C_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [show w i * (c * a i) = c * (w i * a i) by ring, map_mul]
    ring

@[simp] theorem finiteZonalKernelOperator_apply {n N : ℕ}
    (p k : ℕ) (w : Fin N → ℝ) (y : Fin N → Fin n → ℝ)
    (a : Fin N → ℝ) :
    finiteZonalKernelOperator p k w y a =
      finiteZonalKernelSum p k (fun i ↦ w i * a i) y := rfl

theorem eval_finiteZonalKernelOperator {n N : ℕ}
    (p k : ℕ) (w : Fin N → ℝ) (y : Fin N → Fin n → ℝ)
    (a : Fin N → ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval x (finiteZonalKernelOperator p k w y a) =
      ∑ i, (w i * a i) *
        ((sphereDirichletPolynomial k).eval (∑ j, y i j * x j)) ^ (2 * p) := by
  exact eval_finiteZonalKernelSum p k (fun i ↦ w i * a i) y x
/-- The ambient degree bound does not require positivity of either the weights
or the sampled values. -/
theorem finiteZonalKernelOperator_totalDegree_le' {n N : ℕ}
    (p k : ℕ) (w : Fin N → ℝ) (y : Fin N → Fin n → ℝ)
    (a : Fin N → ℝ) :
    (finiteZonalKernelOperator p k w y a).totalDegree ≤ 2 * (p * k) := by
  change (finiteZonalKernelSum p k (fun i ↦ w i * a i) y).totalDegree ≤ _
  unfold finiteZonalKernelSum
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  calc
    (MvPolynomial.C (w i * a i) *
        sphereDirichletZonalKernel p k (y i)).totalDegree ≤
      (MvPolynomial.C (w i * a i)).totalDegree +
        (sphereDirichletZonalKernel p k (y i)).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + 2 * (p * k) := by
      simpa only [MvPolynomial.totalDegree_C, zero_add] using
        sphereDirichletZonalKernel_totalDegree_le p k (y i)
    _ = 2 * (p * k) := by simp

/-- The finite operator sends the nonnegative orthant to ordinary SOS
polynomials of root degree at most `p*k`. -/
noncomputable def finiteZonalKernelOperator_degreeBoundedSOS {n N : ℕ}
    (p k : ℕ) (w : Fin N → ℝ) (y : Fin N → Fin n → ℝ)
    (a : Fin N → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, 0 ≤ a i) :
    DegreeBoundedSOS (finiteZonalKernelOperator p k w y a) (p * k) :=
  finiteZonalKernelSum_degreeBoundedSOS p k (fun i ↦ w i * a i) y
    (fun i ↦ mul_nonneg (hw i) (ha i))

/-- The comparison-facing form of positivity uses the same `SphereSOSMod`
hierarchy predicate as the Choi--Lam development. -/
theorem finiteZonalKernelOperator_sphereSOSMod {n N : ℕ}
    (p k : ℕ) (w : Fin N → ℝ) (y : Fin N → Fin n → ℝ)
    (a : Fin N → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, 0 ≤ a i) :
    SphereSOSMod (finiteZonalKernelOperator p k w y a) (p * k) :=
  SphereBallTransfers.DegreeBoundedSOS.toSphereSOSMod
    (finiteZonalKernelOperator_degreeBoundedSOS p k w y a hw ha)

/-- Every output produced from nonnegative weights and data has ambient degree
at most twice the kernel root degree. -/
theorem finiteZonalKernelOperator_totalDegree_le {n N : ℕ}
    (p k : ℕ) (w : Fin N → ℝ) (y : Fin N → Fin n → ℝ)
    (a : Fin N → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, 0 ≤ a i) :
    (finiteZonalKernelOperator p k w y a).totalDegree ≤ 2 * (p * k) :=
  (finiteZonalKernelOperator_degreeBoundedSOS p k w y a hw ha).totalDegree_le_two_mul

/-- A sampled function is transformed by applying the linear operator to its
vector of values at the quadrature nodes. -/
theorem finiteZonalKernelImage_eq_operator {n N : ℕ}
    (p k : ℕ) (w : Fin N → ℝ) (y : Fin N → Fin n → ℝ)
    (v : (Fin n → ℝ) → ℝ) :
    finiteZonalKernelImage p k w y v =
      finiteZonalKernelOperator p k w y (fun i ↦ v (y i)) := rfl

end QuarticConvergence
end OptimalConvergenceRates

end
