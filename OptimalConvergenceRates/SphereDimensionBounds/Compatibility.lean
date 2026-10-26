import OptimalConvergenceRates.SphereDimensionBounds.Foundation.Hierarchy
import OptimalConvergenceRates.QuarticConvergence.Sphere.Hierarchy
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
The dimension-dependent bounds use the repository's existing sphere hierarchy.
The auxiliary proofs bound the equality multiplier by `2 * r - 2`; for an
objective of degree at most `2 * r`, this bound follows from the certificate
identity itself. The two feasible sets therefore agree at the same root degree.
-/

noncomputable section
set_option autoImplicit false

namespace OptimalConvergenceRates.SphereDimensionBounds.Compatibility

open MvPolynomial SphereBallTransfers QuarticConvergence
open scoped BigOperators

theorem radiusPolynomial_eq_sphereQuadratic (n : ℕ) :
    Foundation.radiusPolynomial n = sphereQuadratic n := rfl

theorem unitSphere_eq_sphereSet (n : ℕ) :
    Foundation.unitSphere n = sphereSet n := by
  ext x
  simp [Foundation.unitSphere, sphereSet, sphereQuadratic]

theorem sphereValues_eq_sphereValueSet {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Foundation.sphereValues p = sphereValueSet p := by
  ext v
  simp only [Foundation.sphereValues, sphereValueSet, Set.mem_ofPred_eq,
    Set.mem_image, unitSphere_eq_sphereSet]

theorem sphereMinimum_eq_spherePolyMin {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Foundation.sphereMinimum p = spherePolyMin p := by
  rw [Foundation.sphereMinimum, spherePolyMin, sphereValues_eq_sphereValueSet]

theorem sphereSupNorm_eq {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Foundation.sphereSupNorm p = QuarticConvergence.sphereSupNorm p := by
  unfold Foundation.sphereSupNorm QuarticConvergence.sphereSupNorm
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_image, unitSphere_eq_sphereSet]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨eval x p, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem sphereSupNorm_eq_spherePolyMax {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hpos : ∀ x : Fin n → ℝ, 0 ≤ eval x p) :
    Foundation.sphereSupNorm p = spherePolyMax p := by
  unfold Foundation.sphereSupNorm spherePolyMax
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

/-- Negating the equality multiplier reconciles the two sphere-relation signs. -/
theorem feasible_to_sphereSOSMod {n r : ℕ} {p : MvPolynomial (Fin n) ℝ} {lam : ℝ}
    (h : Foundation.Feasible r p lam) : SphereSOSMod (p - C lam) r := by
  obtain ⟨m, q, g, hq, _, hid⟩ := h
  refine ⟨m, q, -g, ?_, hq⟩
  rw [hid, radiusPolynomial_eq_sphereQuadratic]
  simp only [sphereRelation]
  ring

/-- The two degree conventions give exactly the same feasible lower values. -/
theorem feasible_iff_sphereSOSMod {n r : ℕ} (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ 2 * r) (lam : ℝ) :
    Foundation.Feasible r p lam ↔ SphereSOSMod (p - C lam) r := by
  constructor
  · exact feasible_to_sphereSOSMod
  · rintro ⟨m, q, g, hid, hq⟩
    refine ⟨m, q, -g, hq, ?_, ?_⟩
    · have hshift : (p - C lam).totalDegree ≤ 2 * r :=
        (totalDegree_sub _ _).trans (max_le hp (by simp))
      simpa using sphere_multiplier_degree hn (p - C lam) q g hshift hq hid
    · rw [hid, radiusPolynomial_eq_sphereQuadratic]
      simp only [sphereRelation]
      ring

theorem feasibleValues_eq_sphereSOSFeasible {n r : ℕ} (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ 2 * r) :
    Foundation.feasibleValues r p = sphereSOSFeasible p r := by
  ext lam
  exact feasible_iff_sphereSOSMod hn p hp lam

/-- A nonempty feasible set identifies the real supremum with the existing
`WithBot` hierarchy value. Nonemptiness is an explicit hypothesis. -/
theorem sphereSOSBound_eq_coe_sos {n r : ℕ} (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ 2 * r)
    (hne : (Foundation.feasibleValues r p).Nonempty) :
    sphereSOSBound p r = (Foundation.sos r p : WithBot ℝ) := by
  have hsets := feasibleValues_eq_sphereSOSFeasible hn p hp
  have hnew : (sphereSOSFeasible p r).Nonempty := hsets ▸ hne
  rw [sphereSOSBound, dite_eq_left hnew, Foundation.sos, hsets]

theorem gap_eq_spherePolyMin_sub_sos {n r : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Foundation.gap r p = spherePolyMin p - Foundation.sos r p := by
  rw [Foundation.gap, sphereMinimum_eq_spherePolyMin]

end OptimalConvergenceRates.SphereDimensionBounds.Compatibility
