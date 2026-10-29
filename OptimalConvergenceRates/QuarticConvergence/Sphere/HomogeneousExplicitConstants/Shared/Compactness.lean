import Mathlib.Topology.Algebra.MvPolynomial
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.Hierarchy

/-! Attainment of the sphere extrema used by the hierarchy. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Foundation

open scoped BigOperators

theorem unitSphere_nonempty {n : ℕ} (hn : 0 < n) : (unitSphere n).Nonempty := by
  rw [unitSphere_eq_sphereSet]
  exact sphereSet_nonempty hn

theorem unitSphere_isClosed (n : ℕ) : IsClosed (unitSphere n) := by
  rw [unitSphere_eq_sphereSet]
  exact sphereSet_isClosed

theorem unitSphere_subset_cube (n : ℕ) :
    unitSphere n ⊆ Set.Icc (fun _ : Fin n ↦ (-1 : ℝ)) (fun _ ↦ 1) := by
  intro x hx
  have h := sphereSet_subset_hypercube ((unitSphere_eq_sphereSet n) ▸ hx)
  constructor
  · intro i
    exact (h i (Set.mem_univ i)).1
  · intro i
    exact (h i (Set.mem_univ i)).2

theorem unitSphere_isCompact (n : ℕ) : IsCompact (unitSphere n) := by
  rw [unitSphere_eq_sphereSet]
  exact sphereSet_compact

theorem sphereMinimum_exists {n : ℕ} (hn : 0 < n) (p : Polynomial n) :
    ∃ μ : ℝ, IsSphereMinimum p μ := by
  refine ⟨spherePolyMin p, ?_, ?_⟩
  · intro x hx
    exact spherePolyMin_le_eval p x ((unitSphere_eq_sphereSet n) ▸ hx)
  · simpa only [unitSphere_eq_sphereSet] using spherePolyMin_mem hn p

theorem sphereMinimum_attained {n : ℕ} (hn : 0 < n) (p : Polynomial n) :
    ∃ x ∈ unitSphere n, MvPolynomial.eval x p = sphereMinimum p := by
  simpa only [unitSphere_eq_sphereSet] using spherePolyMin_mem hn p

theorem sphereNormValues_bddAbove {n : ℕ} (p : Polynomial n) :
    BddAbove {v : ℝ | ∃ x ∈ unitSphere n, |MvPolynomial.eval x p| = v} := by
  have hc := (unitSphere_isCompact n).image (MvPolynomial.continuous_eval p).abs
  have heq : (fun x ↦ |MvPolynomial.eval x p|) '' unitSphere n =
      {v : ℝ | ∃ x ∈ unitSphere n, |MvPolynomial.eval x p| = v} := by
    ext v
    rfl
  rw [heq] at hc
  exact hc.bddAbove

theorem sphereSupNorm_attained {n : ℕ} (hn : 0 < n) (p : Polynomial n) :
    ∃ x ∈ unitSphere n, |MvPolynomial.eval x p| = sphereSupNorm p := by
  simpa only [unitSphere_eq_sphereSet] using sphereSupNorm_mem hn p

theorem abs_eval_le_sphereSupNorm {n : ℕ} (p : Polynomial n) (x : Fin n → ℝ)
    (hx : x ∈ unitSphere n) : |MvPolynomial.eval x p| ≤ sphereSupNorm p :=
  sphereSupNorm_eval_le p x ((unitSphere_eq_sphereSet n) ▸ hx)

theorem sphereSupNorm_pos_of_nonzero_value {n : ℕ} {p : Polynomial n}
    {x : Fin n → ℝ} (hx : x ∈ unitSphere n) (hvalue : MvPolynomial.eval x p ≠ 0) :
    0 < sphereSupNorm p := by
  exact (abs_pos.mpr hvalue).trans_le
    (sphereSupNorm_eval_le p x ((unitSphere_eq_sphereSet n) ▸ hx))

end Foundation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
