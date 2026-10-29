import OptimalConvergenceRates.QuarticConvergence.Sphere.Hierarchy
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Degree bounds forced by the canonical sphere certificate identity. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence
open MvPolynomial SphereBallTransfers
open scoped BigOperators

/-- The sphere equation has degree two in every positive ambient dimension. -/
theorem sphereRelation_degree (n : ℕ) (hn : 0 < n) :
    (sphereRelation n).totalDegree = 2 := by
  classical
  let i : Fin n := ⟨0, hn⟩
  have hi : (Finsupp.single i 2 : Fin n →₀ ℕ) ≠ 0 := by simp
  have hcoeff : (sphereRelation n).coeff (Finsupp.single i 2) = 1 := by
    simp [sphereRelation, sphereQuadratic, coeff_one, coeff_X_pow,
      Finsupp.single_left_inj (by decide : (2 : ℕ) ≠ 0), Ne.symm hi]
  apply le_antisymm
  · apply (totalDegree_sub _ _).trans
    apply max_le _ (by simp)
    apply totalDegree_finsetSum_le
    intro j _
    simp
  · have hm := le_totalDegree (Finsupp.mem_support_iff.mpr (by rw [hcoeff]; norm_num))
    simpa using hm

/-- The multiplier bound is forced by the objective and square-root degrees. -/
theorem sphere_multiplier_degree {n r m : ℕ} (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) (q : Fin m → MvPolynomial (Fin n) ℝ)
    (g : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ 2 * r) (hq : ∀ j, (q j).totalDegree ≤ r)
    (hid : p = (∑ j, q j ^ 2) + sphereRelation n * g) :
    g.totalDegree ≤ 2 * r - 2 := by
  classical
  by_cases hg : g = 0
  · simp [hg]
  have hrel : sphereRelation n ≠ 0 := by
    intro hzero
    have h := sphereRelation_degree n hn
    simp [hzero] at h
  have hsum : (∑ j, q j ^ 2).totalDegree ≤ 2 * r := by
    apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (hq j))
  have hprod : (sphereRelation n * g).totalDegree ≤ 2 * r := by
    have heq : sphereRelation n * g = p - ∑ j, q j ^ 2 := by rw [hid]; ring
    rw [heq]
    exact (totalDegree_sub _ _).trans (max_le hp hsum)
  rw [totalDegree_mul_of_isDomain hrel hg, sphereRelation_degree n hn] at hprod
  omega

end OptimalConvergenceRates.QuarticConvergence
