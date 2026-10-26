import OptimalConvergenceRates.SphereDimensionBounds.Foundation.ObjectiveNormalization
import OptimalConvergenceRates.SphereDimensionBounds.Foundation.Compactness
import OptimalConvergenceRates.SphereDimensionBounds.Foundation.CertificateScaling
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Positive sphere-norm normalization for actual forms of every degree.
The full unit sphere and original Feasible/root-degree convention are unchanged. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.GeneralDegreeNormalization

open OptimalConvergenceRates.SphereDimensionBounds.Foundation

/-- A normalized globally nonnegative form, in the original hierarchy. -/
def NormalizedForm (d : ℕ) {n : ℕ} (p : Polynomial n) : Prop :=
  p.IsHomogeneous d ∧
  (∀ x : Fin n → ℝ, 0 ≤ MvPolynomial.eval x p) ∧
  IsSphereMinimum p 0 ∧ sphereSupNorm p = 1

/-- The new all-degree lower target; this definition is not a proof. -/
def UniformDegreeLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ d : ℕ, 4 ≤ d → Even d →
      ∃ p : Polynomial n, NormalizedForm d p ∧
        ∀ r : ℕ, d / 2 ≤ r →
          (feasibleValues r p).Nonempty ∧
          c * min (1 / (n : ℝ))
            ((d : ℝ)^4 * (n : ℝ)^3 / (r : ℝ)^4) ≤ gap r p

theorem normalizedObjective_form {n d : ℕ} (hn : 0 < n) (p : Polynomial n)
    (hhom : p.IsHomogeneous d) (hpos : ∀ x, 0 ≤ MvPolynomial.eval x p)
    (hmin : IsSphereMinimum p 0) (hβ : 0 < sphereSupNorm p) :
    NormalizedForm d (normalizeObjective p) := by
  have hscale : 0 ≤ (sphereSupNorm p)⁻¹ := (inv_pos.mpr hβ).le
  have heval (x : Fin n → ℝ) : MvPolynomial.eval x (normalizeObjective p) =
      (sphereSupNorm p)⁻¹ * MvPolynomial.eval x p := by
    simp only [normalizeObjective, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  have hnonneg (x : Fin n → ℝ) : 0 ≤ MvPolynomial.eval x (normalizeObjective p) := by
    rw [heval]
    exact mul_nonneg hscale (hpos x)
  refine ⟨?_, hnonneg, ?_, ?_⟩
  · simpa only [normalizeObjective, zero_add] using
      (MvPolynomial.isHomogeneous_C (σ := Fin n) (sphereSupNorm p)⁻¹).mul hhom
  · refine ⟨fun x hx => hnonneg x, ?_⟩
    obtain ⟨x, hx, hzero⟩ := hmin.2
    exact ⟨x, hx, by rw [heval, hzero, mul_zero]⟩
  · obtain ⟨x, hx, hxmax⟩ := sphereSupNorm_attained hn p
    have habs (y : Fin n → ℝ) :
        |MvPolynomial.eval y (normalizeObjective p)| =
          (sphereSupNorm p)⁻¹ * |MvPolynomial.eval y p| := by
      rw [heval, abs_mul, abs_of_nonneg hscale]
    have hxnorm : |MvPolynomial.eval x (normalizeObjective p)| = 1 := by
      rw [habs, hxmax, inv_mul_cancel₀ hβ.ne']
    apply le_antisymm
    · apply csSup_le (s := {v : ℝ | ∃ y ∈ unitSphere n,
        |MvPolynomial.eval y (normalizeObjective p)| = v}) ⟨1, x, hx, hxnorm⟩
      rintro v ⟨y, hy, rfl⟩
      rw [habs]
      calc
        (sphereSupNorm p)⁻¹ * |MvPolynomial.eval y p| ≤
            (sphereSupNorm p)⁻¹ * sphereSupNorm p :=
          mul_le_mul_of_nonneg_left
            (le_csSup (sphereNormValues_bddAbove p) ⟨y, hy, rfl⟩) hscale
        _ = 1 := inv_mul_cancel₀ hβ.ne'
    · exact le_csSup (sphereNormValues_bddAbove _) ⟨x, hx, hxnorm⟩

/-- Normalization by a sphere norm at most one cannot reduce a nonnegative
lower bound on the hierarchy gap. Nonempty feasible sets are transported. -/
theorem normalizeObjective_gap_lower {n r d : ℕ} {p : Polynomial n} {η : ℝ}
    (hn : 0 < n) (hhom : p.IsHomogeneous d)
    (hpos : ∀ x, 0 ≤ MvPolynomial.eval x p) (hmin : IsSphereMinimum p 0)
    (hβ : 0 < sphereSupNorm p) (hβone : sphereSupNorm p ≤ 1)
    (hne : (feasibleValues r p).Nonempty) (hη : 0 ≤ η)
    (hcert : ∀ lam, Feasible r p lam → lam ≤ -η) :
    η ≤ gap r (normalizeObjective p) := by
  have hnormalized := normalizedObjective_form hn p hhom hpos hmin hβ
  apply gap_lower_of_certificates hnormalized.2.2.1
    (normalizeObjective_feasible_nonempty hβ hne)
  intro lam hlam
  have hbound := normalized_certificate_obstruction hβ hcert lam hlam
  have hηβ : η ≤ η / sphereSupNorm p := by
    apply (le_div_iff₀ hβ).2
    exact mul_le_of_le_one_right hη hβone
  have hneg : -η / sphereSupNorm p ≤ -η := by
    rw [neg_div]
    exact neg_le_neg hηβ
  exact hbound.trans hneg

theorem normalizeObjective_gap_of_gap {n r d : ℕ} {p : Polynomial n} {η : ℝ}
    (hn : 0 < n) (hhom : p.IsHomogeneous d)
    (hpos : ∀ x, 0 ≤ MvPolynomial.eval x p) (hmin : IsSphereMinimum p 0)
    (hβ : 0 < sphereSupNorm p) (hβone : sphereSupNorm p ≤ 1)
    (hne : (feasibleValues r p).Nonempty) (hη : 0 ≤ η) (hgap : η ≤ gap r p) :
    η ≤ gap r (normalizeObjective p) := by
  apply normalizeObjective_gap_lower hn hhom hpos hmin hβ hβone hne hη
  obtain ⟨x, hx, hzero⟩ := hmin.2
  have hsos : sos r p ≤ -η := by
    rw [gap, sphereMinimum_eq hmin] at hgap
    linarith
  intro lam hlam
  exact (le_csSup (feasibleValues_bddAbove hx) hlam).trans hsos

end OptimalConvergenceRates.SphereDimensionBounds.GeneralDegreeNormalization
