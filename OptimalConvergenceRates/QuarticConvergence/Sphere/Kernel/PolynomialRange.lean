/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Kernel/PolynomialRange.lean

  Polynomial sections of the positive Chebyshev--Dirichlet zonal kernel.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Dirichlet
import OptimalConvergenceRates.QuarticConvergence.Sphere.Defs

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers
/-- Substituting a multivariate polynomial of degree d into a univariate
polynomial of degree m has total degree at most m*d. -/
theorem totalDegree_polynomial_eval₂_le {n : ℕ}
    (P : Polynomial ℝ) (q : MvPolynomial (Fin n) ℝ) :
    (Polynomial.eval₂ MvPolynomial.C q P).totalDegree ≤
      P.natDegree * q.totalDegree := by
  rw [Polynomial.eval₂_eq_sum_range]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  simp only [Finset.mem_range] at hi
  calc
    (MvPolynomial.C (P.coeff i) * q ^ i).totalDegree ≤
        (MvPolynomial.C (P.coeff i)).totalDegree + (q ^ i).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + i * q.totalDegree := by
      rw [MvPolynomial.totalDegree_C]
      exact Nat.add_le_add_left (MvPolynomial.totalDegree_pow q i) 0
    _ ≤ P.natDegree * q.totalDegree := by
      simp only [zero_add]
      exact Nat.mul_le_mul_right q.totalDegree (by omega)

/-- The polynomial function x ↦ sum_i y_i*x_i. -/
def sphereDotPolynomial {n : ℕ} (y : Fin n → ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ i, MvPolynomial.C (y i) * MvPolynomial.X i

@[simp] theorem eval_sphereDotPolynomial {n : ℕ}
    (x y : Fin n → ℝ) :
    MvPolynomial.eval x (sphereDotPolynomial y) = ∑ i, y i * x i := by
  simp [sphereDotPolynomial]

theorem sphereDotPolynomial_totalDegree_le_one {n : ℕ} (y : Fin n → ℝ) :
    (sphereDotPolynomial y).totalDegree ≤ 1 := by
  unfold sphereDotPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  calc
    (MvPolynomial.C (y i) * MvPolynomial.X i).totalDegree ≤
        (MvPolynomial.C (y i)).totalDegree + (MvPolynomial.X i).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = 1 := by simp

/-- The degree-p*k polynomial square root whose square is the unnormalized
positive kernel section based at y. -/
noncomputable def sphereDirichletZonalRoot {n : ℕ}
    (p k : ℕ) (y : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  (Polynomial.eval₂ MvPolynomial.C (sphereDotPolynomial y)
    (sphereDirichletPolynomial k)) ^ p

theorem eval_sphereDirichletZonalRoot {n : ℕ}
    (p k : ℕ) (x y : Fin n → ℝ) :
    MvPolynomial.eval x (sphereDirichletZonalRoot p k y) =
      ((sphereDirichletPolynomial k).eval (∑ i, y i * x i)) ^ p := by
  unfold sphereDirichletZonalRoot
  rw [map_pow, Polynomial.hom_eval₂]
  have hcomp : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℝ := by
    ext c
    simp
  rw [hcomp]
  simp [Polynomial.eval₂_eq_eval_map]

theorem sphereDirichletZonalRoot_totalDegree_le {n : ℕ}
    (p k : ℕ) (y : Fin n → ℝ) :
    (sphereDirichletZonalRoot p k y).totalDegree ≤ p * k := by
  unfold sphereDirichletZonalRoot
  calc
    (Polynomial.eval₂ MvPolynomial.C (sphereDotPolynomial y)
      (sphereDirichletPolynomial k) ^ p).totalDegree ≤
        p * (Polynomial.eval₂ MvPolynomial.C (sphereDotPolynomial y)
          (sphereDirichletPolynomial k)).totalDegree :=
      MvPolynomial.totalDegree_pow _ p
    _ ≤ p * ((sphereDirichletPolynomial k).natDegree *
        (sphereDotPolynomial y).totalDegree) :=
      Nat.mul_le_mul_left p
        (totalDegree_polynomial_eval₂_le (sphereDirichletPolynomial k)
          (sphereDotPolynomial y))
    _ ≤ p * (k * 1) := by
      gcongr
      · exact sphereDirichletPolynomial_natDegree_le k
      · exact sphereDotPolynomial_totalDegree_le_one y
    _ = p * k := by simp

/-- An unnormalized positive zonal kernel section, displayed as one polynomial
square to expose its root-degree bound. -/
noncomputable def sphereDirichletZonalKernel {n : ℕ}
    (p k : ℕ) (y : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  (sphereDirichletZonalRoot p k y) ^ 2

theorem eval_sphereDirichletZonalKernel {n : ℕ}
    (p k : ℕ) (x y : Fin n → ℝ) :
    MvPolynomial.eval x (sphereDirichletZonalKernel p k y) =
      ((sphereDirichletPolynomial k).eval (∑ i, y i * x i)) ^ (2 * p) := by
  rw [sphereDirichletZonalKernel, map_pow, eval_sphereDirichletZonalRoot]
  rw [show 2 * p = p * 2 by omega, pow_mul]

/-- A zonal-kernel section attains the Dirichlet peak at its center. -/
theorem eval_sphereDirichletZonalKernel_self {n : ℕ}
    (p k : ℕ) {x : Fin n → ℝ} (hx : x ∈ sphereSet n) :
    MvPolynomial.eval x (sphereDirichletZonalKernel p k x) =
      (2 * (k : ℝ) + 1) ^ (2 * p) := by
  rw [eval_sphereDirichletZonalKernel]
  have hdot : ∑ i, x i * x i = 1 := by
    simpa [sphereSet, sphereQuadratic, pow_two] using hx
  rw [hdot, sphereDirichletPolynomial_eval_one]

theorem eval_sphereDirichletZonalKernel_nonneg {n : ℕ}
    (p k : ℕ) (x y : Fin n → ℝ) :
    0 ≤ MvPolynomial.eval x (sphereDirichletZonalKernel p k y) := by
  rw [sphereDirichletZonalKernel, map_pow]
  exact sq_nonneg _

/-- The zonal kernel is symmetric in its two sphere arguments. -/
theorem eval_sphereDirichletZonalKernel_comm {n : ℕ}
    (p k : ℕ) (x y : Fin n → ℝ) :
    MvPolynomial.eval x (sphereDirichletZonalKernel p k y) =
      MvPolynomial.eval y (sphereDirichletZonalKernel p k x) := by
  rw [eval_sphereDirichletZonalKernel, eval_sphereDirichletZonalKernel]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Each kernel section is already an ordinary SOS with root degree p*k;
the remaining Gram argument integrates these rank-one sections. -/
def sphereDirichletZonalKernel_degreeBoundedSOS {n : ℕ}
    (p k : ℕ) (y : Fin n → ℝ) :
    DegreeBoundedSOS (sphereDirichletZonalKernel p k y) (p * k) where
  N := 1
  P := fun _ ↦ sphereDirichletZonalRoot p k y
  decomp := by simp [sphereDirichletZonalKernel]
  degree := fun _ ↦ sphereDirichletZonalRoot_totalDegree_le p k y

/-- Consequently, the kernel section itself has degree at most twice
its square-root degree. -/
theorem sphereDirichletZonalKernel_totalDegree_le {n : ℕ}
    (p k : ℕ) (y : Fin n → ℝ) :
    (sphereDirichletZonalKernel p k y).totalDegree ≤ 2 * (p * k) :=
  (sphereDirichletZonalKernel_degreeBoundedSOS p k y).totalDegree_le_two_mul

/-- A finite positive quadrature of zonal kernel sections. -/
noncomputable def finiteZonalKernelSum {n N : ℕ}
    (p k : ℕ) (w : Fin N → ℝ) (y : Fin N → Fin n → ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ i, MvPolynomial.C (w i) * sphereDirichletZonalKernel p k (y i)

theorem eval_finiteZonalKernelSum {n N : ℕ}
    (p k : ℕ) (w : Fin N → ℝ) (y : Fin N → Fin n → ℝ)
    (x : Fin n → ℝ) :
    MvPolynomial.eval x (finiteZonalKernelSum p k w y) =
      ∑ i, w i *
        ((sphereDirichletPolynomial k).eval (∑ j, y i j * x j)) ^ (2 * p) := by
  simp [finiteZonalKernelSum, eval_sphereDirichletZonalKernel]

/-- A finite positive quadrature has an explicit SOS witness with the same
root-degree bound as each individual kernel section. -/
noncomputable def finiteZonalKernelSum_degreeBoundedSOS {n N : ℕ}
    (p k : ℕ) (w : Fin N → ℝ) (y : Fin N → Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    DegreeBoundedSOS (finiteZonalKernelSum p k w y) (p * k) where
  N := N
  P := fun i ↦
    MvPolynomial.C (Real.sqrt (w i)) * sphereDirichletZonalRoot p k (y i)
  decomp := by
    unfold finiteZonalKernelSum sphereDirichletZonalKernel
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, ← MvPolynomial.C_pow, Real.sq_sqrt (hw i)]
  degree := by
    intro i
    calc
      (MvPolynomial.C (Real.sqrt (w i)) *
        sphereDirichletZonalRoot p k (y i)).totalDegree ≤
          (MvPolynomial.C (Real.sqrt (w i))).totalDegree +
            (sphereDirichletZonalRoot p k (y i)).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ p * k := by
        simpa using sphereDirichletZonalRoot_totalDegree_le p k (y i)

/-- Applying the finite zonal kernel to sampled values amounts to absorbing the
sampled values into the quadrature weights. -/
noncomputable def finiteZonalKernelImage {n N : ℕ}
    (p k : ℕ) (w : Fin N → ℝ) (y : Fin N → Fin n → ℝ)
    (v : (Fin n → ℝ) → ℝ) : MvPolynomial (Fin n) ℝ :=
  finiteZonalKernelSum p k (fun i ↦ w i * v (y i)) y

theorem eval_finiteZonalKernelImage {n N : ℕ}
    (p k : ℕ) (w : Fin N → ℝ) (y : Fin N → Fin n → ℝ)
    (v : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval x (finiteZonalKernelImage p k w y v) =
      ∑ i, (w i * v (y i)) *
        ((sphereDirichletPolynomial k).eval (∑ j, y i j * x j)) ^ (2 * p) := by
  simp [finiteZonalKernelImage, eval_finiteZonalKernelSum]

/-- Nonnegative quadrature weights and nonnegative sampled data become an
ordinary SOS without increasing the kernel's square-root degree. -/
noncomputable def finiteZonalKernelImage_degreeBoundedSOS {n N : ℕ}
    (p k : ℕ) (w : Fin N → ℝ) (y : Fin N → Fin n → ℝ)
    (v : (Fin n → ℝ) → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hv : ∀ i, 0 ≤ v (y i)) :
    DegreeBoundedSOS (finiteZonalKernelImage p k w y v) (p * k) :=
  finiteZonalKernelSum_degreeBoundedSOS p k (fun i ↦ w i * v (y i)) y
    (fun i ↦ mul_nonneg (hw i) (hv i))

/-- This is stated with the repository's shared spherical SOS predicate, also
used by the Choi--Lam results, so the hierarchy levels compare directly. -/
theorem finiteZonalKernelImage_sphereSOSMod {n N : ℕ}
    (p k : ℕ) (w : Fin N → ℝ) (y : Fin N → Fin n → ℝ)
    (v : (Fin n → ℝ) → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hv : ∀ i, 0 ≤ v (y i)) :
    SphereSOSMod (finiteZonalKernelImage p k w y v) (p * k) :=
  SphereBallTransfers.DegreeBoundedSOS.toSphereSOSMod
    (finiteZonalKernelImage_degreeBoundedSOS p k w y v hw hv)

/-- In particular, the finite positive kernel image is nonnegative on the
repository's algebraic unit sphere. -/
theorem finiteZonalKernelImage_sphereNonnegative {n N : ℕ}
    (p k : ℕ) (w : Fin N → ℝ) (y : Fin N → Fin n → ℝ)
    (v : (Fin n → ℝ) → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hv : ∀ i, 0 ≤ v (y i)) :
    SphereNonnegative (finiteZonalKernelImage p k w y v) := by
  intro x hx
  exact (finiteZonalKernelImage_sphereSOSMod p k w y v hw hv).nonnegOnSphere hx
end QuarticConvergence
end OptimalConvergenceRates

end
