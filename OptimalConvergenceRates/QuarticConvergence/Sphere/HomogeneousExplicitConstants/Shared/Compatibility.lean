import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.Hierarchy
import OptimalConvergenceRates.QuarticConvergence.Sphere.Hierarchy
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
Public bridges from the local homogeneous notation to the repository's sphere API.
The certificate and extrema bridges are aliases. Nonemptiness explicitly justifies
identifying the real feasible supremum with the canonical `WithBot` hierarchy value.
-/

noncomputable section
set_option autoImplicit false

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Compatibility

open MvPolynomial SphereBallTransfers QuarticConvergence
open scoped BigOperators

theorem radiusPolynomial_eq_sphereQuadratic (n : ℕ) :
    Foundation.radiusPolynomial n = sphereQuadratic n := rfl

theorem unitSphere_eq_sphereSet (n : ℕ) :
    Foundation.unitSphere n = sphereSet n := Foundation.unitSphere_eq_sphereSet n

theorem sphereValues_eq_sphereValueSet {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Foundation.sphereValues p = sphereValueSet p := rfl

theorem sphereMinimum_eq_spherePolyMin {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Foundation.sphereMinimum p = spherePolyMin p := rfl

theorem sphereSupNorm_eq {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Foundation.sphereSupNorm p = QuarticConvergence.sphereSupNorm p := rfl

theorem sphereSupNorm_eq_spherePolyMax {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hpos : ∀ x : Fin n → ℝ, 0 ≤ eval x p) :
    Foundation.sphereSupNorm p = spherePolyMax p := by
  rw [Foundation.sphereSupNorm_eq_sSup]
  unfold spherePolyMax
  congr 1
  ext v
  simp only [Foundation.unitSphere, sphereValueSet, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨x, hx, hvalue⟩
    exact ⟨x, by simpa [sphereSet, sphereQuadratic] using hx,
      (abs_of_nonneg (hpos x)).symm.trans hvalue⟩
  · rintro ⟨x, hx, hvalue⟩
    exact ⟨x, by simpa [sphereSet, sphereQuadratic] using hx,
      (abs_of_nonneg (hpos x)).trans hvalue⟩

theorem isSphereMinimum_spherePolyMin {n : ℕ} (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) : Foundation.IsSphereMinimum p (spherePolyMin p) := by
  constructor
  · intro x hx
    exact spherePolyMin_le_eval p x (by rwa [← unitSphere_eq_sphereSet])
  · simpa only [unitSphere_eq_sphereSet] using spherePolyMin_mem hn p

theorem spherePolyMin_eq_of_isSphereMinimum {n : ℕ} {p : MvPolynomial (Fin n) ℝ}
    {mu : ℝ} (hmin : Foundation.IsSphereMinimum p mu) : spherePolyMin p = mu := by
  rw [← sphereMinimum_eq_spherePolyMin]
  exact Foundation.sphereMinimum_eq hmin

/-- Feasibility already uses the repository's sphere certificate. -/
theorem feasible_to_sphereSOSMod {n r : ℕ} {p : MvPolynomial (Fin n) ℝ} {lam : ℝ}
    (h : Foundation.Feasible r p lam) : SphereSOSMod (p - C lam) r := h

theorem feasible_iff_sphereSOSMod {n r : ℕ} (_hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) (_hp : p.totalDegree ≤ 2 * r) (lam : ℝ) :
    Foundation.Feasible r p lam ↔ SphereSOSMod (p - C lam) r := Iff.rfl

theorem feasibleValues_eq_sphereSOSFeasible {n r : ℕ} (_hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) (_hp : p.totalDegree ≤ 2 * r) :
    Foundation.feasibleValues r p = sphereSOSFeasible p r := rfl

/-- Nonemptiness identifies the canonical `WithBot` bound with its real supremum. -/
theorem sphereSOSBound_eq_coe_sos {n r : ℕ} (_hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) (_hp : p.totalDegree ≤ 2 * r)
    (hne : (Foundation.feasibleValues r p).Nonempty) :
    sphereSOSBound p r = (Foundation.sos r p : WithBot ℝ) := by
  simp only [sphereSOSBound, dif_pos hne, Foundation.sos, Foundation.feasibleValues]

theorem gap_eq_spherePolyMin_sub_sos {n r : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Foundation.gap r p = spherePolyMin p - Foundation.sos r p := by
  rw [Foundation.gap, sphereMinimum_eq_spherePolyMin]

end Compatibility
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
