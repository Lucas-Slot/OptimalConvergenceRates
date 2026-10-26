import OptimalConvergenceRates.SphereDimensionBounds.Compatibility
import OptimalConvergenceRates.SphereDimensionBounds.DegreeUpperBound
import OptimalConvergenceRates.SphereDimensionBounds.DegreeAmplificationLower

/-!
# Dimension-dependent sphere SOS bounds

For every even degree `d ≥ 4`, the upper certificate applies in dimension
`n ≥ 3` at every root degree `r ≥ 8 * n * d`. Its absolute constant is
`192 * pi^4 * 5476140000`; the error scales with the sphere oscillation.

The lower bound uses one normalized, globally nonnegative homogeneous form
for each sufficiently large dimension and each even degree. That same form
has the claimed gap at every root degree `r ≥ d / 2`.

Both results use the repository's existing `SphereSOSMod`, sphere extrema,
and `WithBot` sphere SOS lower bound.
-/

noncomputable section
set_option autoImplicit false

namespace OptimalConvergenceRates.SphereDimensionBounds

open MvPolynomial SphereBallTransfers QuarticConvergence

/-- An explicit absolute-constant upper certificate for all even degrees,
at the original sphere SOS root degree and with the actual oscillation. -/
theorem sphereDimensionUpperRate_membership {n d r : ℕ}
    (hn : 3 ≤ n) (hd : 4 ≤ d) (heven : Even d) (hr : 8 * n * d ≤ r)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous d) :
    SphereSOSMod
      (p - C (spherePolyMin p) +
        C ((192 * Real.pi ^ 4 * 5476140000) *
          ((d : ℝ) ^ 4 * (n : ℝ) ^ 4 * (1 + (Nat.clog 2 n : ℝ)) ^ 3 /
            (r : ℝ) ^ 4) * (spherePolyMax p - spherePolyMin p))) r := by
  have hnpos : 0 < n := by omega
  have hmin := Compatibility.isSphereMinimum_spherePolyMin hnpos p
  have hosc : 0 ≤ spherePolyMax p - spherePolyMin p :=
    sub_nonneg.mpr (spherePolyMin_le_spherePolyMax hnpos p)
  have hupper : ∀ x ∈ Foundation.unitSphere n,
      eval x p ≤ spherePolyMin p + (spherePolyMax p - spherePolyMin p) := by
    intro x hx
    have hmax := eval_le_spherePolyMax p x
      (by rwa [← Compatibility.unitSphere_eq_sphereSet])
    linarith
  have hcert := Compatibility.feasible_to_sphereSOSMod
    (DegreeUpperBound.upper_certificate hn hd heven hr p hp (spherePolyMin p)
      (spherePolyMax p - spherePolyMin p) hmin hosc hupper)
  convert hcert using 1
  simp only [DegreeUpperBound.errorBound, DimensionUpperConstants.absoluteUpperConstant,
    DimensionUpperConstants.L, map_sub]
  ring

/-- The upper certificate bounds the gap of the existing `WithBot` hierarchy;
the displayed real value also records nonemptiness of its feasible set. -/
theorem sphereDimensionUpperRate_gap {n d r : ℕ}
    (hn : 3 ≤ n) (hd : 4 ≤ d) (heven : Even d) (hr : 8 * n * d ≤ r)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous d) :
    ∃ b : ℝ, sphereSOSBound p r = (b : WithBot ℝ) ∧
      0 ≤ spherePolyMin p - b ∧
      spherePolyMin p - b ≤
        (192 * Real.pi ^ 4 * 5476140000) *
          ((d : ℝ) ^ 4 * (n : ℝ) ^ 4 * (1 + (Nat.clog 2 n : ℝ)) ^ 3 /
            (r : ℝ) ^ 4) * (spherePolyMax p - spherePolyMin p) := by
  exact sphereSOSBound_error_of_certificate (sphereSet_nonempty (by omega)) p r _
    (sphereDimensionUpperRate_membership hn hd heven hr p hp)

/-- One normalized globally nonnegative form has the lower gap at every
admissible order. The hierarchy value is explicitly a real number at each order. -/
theorem sphereDimensionLowerRate :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ d : ℕ, 4 ≤ d → Even d →
        ∃ p : MvPolynomial (Fin n) ℝ,
          p.IsHomogeneous d ∧
          (∀ x : Fin n → ℝ, 0 ≤ eval x p) ∧
          spherePolyMin p = 0 ∧ spherePolyMax p = 1 ∧
          ∀ r : ℕ, d / 2 ≤ r →
            ∃ b : ℝ, sphereSOSBound p r = (b : WithBot ℝ) ∧
              c * min (1 / (n : ℝ))
                ((d : ℝ) ^ 4 * (n : ℝ) ^ 3 / (r : ℝ) ^ 4) ≤
                  spherePolyMin p - b := by
  obtain ⟨c, hc, n₀, hbound⟩ := DegreeAmplification.uniform_degree_lower_bound
  refine ⟨c, hc, max n₀ 1, ?_⟩
  intro n hn d hd heven
  have hnpos : 0 < n := by omega
  obtain ⟨p, hp, hgap⟩ := hbound n ((le_max_left n₀ 1).trans hn) d hd heven
  refine ⟨p, hp.1, hp.2.1,
    Compatibility.spherePolyMin_eq_of_isSphereMinimum hp.2.2.1, ?_, ?_⟩
  · rw [← Compatibility.sphereSupNorm_eq_spherePolyMax p hp.2.1]
    exact hp.2.2.2
  · intro r hr
    have hdegree : p.totalDegree ≤ 2 * r := by
      apply hp.1.totalDegree_le.trans
      obtain ⟨k, hk⟩ := heven
      omega
    obtain ⟨hne, hlower⟩ := hgap r hr
    refine ⟨Foundation.sos r p,
      Compatibility.sphereSOSBound_eq_coe_sos hnpos p hdegree hne, ?_⟩
    simpa only [Compatibility.gap_eq_spherePolyMin_sub_sos] using hlower

end OptimalConvergenceRates.SphereDimensionBounds
