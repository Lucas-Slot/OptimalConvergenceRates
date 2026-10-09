/-
  Fixed-degree quartic certificate for lifted cube objectives.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.FiniteDegree

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers


/-- For fixed cube dimension and degree, the lifted centered objective has a
quartic sphere certificate whose perturbation is controlled by the cube
oscillation. -/
theorem quarticCubeLiftFixedDegree {n d : ℕ} (hn : 0 < n) :
    ∃ (C : ℝ) (r₀ : ℕ),
      0 < C ∧ 0 < r₀ ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (r : ℕ),
        p.totalDegree ≤ d → r₀ ≤ r →
          SphereSOSMod
            (cubeSphereLift n (p - MvPolynomial.C (polyMin p)) +
              MvPolynomial.C
                (C * (polyMax p - polyMin p) / (r : ℝ) ^ 4)) r := by
  obtain ⟨A, c, hA, hc, hcert⟩ := quarticCubeLiftCertificate hn
  obtain ⟨B, hB, hcompare⟩ := fixedDegreeCubeSphereC6Comparison (n := n) (d := d) hn
  let r₀ := c * max ((2 * n + 1) * d) 1
  refine ⟨A * B, r₀, mul_pos hA hB, ?_, ?_⟩
  · exact Nat.mul_pos hc (by omega)
  intro p r hpdeg hr
  have hrpos : 0 < r := (show 0 < r₀ by exact Nat.mul_pos hc (by omega)).trans_le hr
  have hsmall := hcert p d r hpdeg hr
  have hnorm := hcompare p hpdeg
  have hden : (0 : ℝ) < (r : ℝ) ^ 4 := pow_pos (Nat.cast_pos.mpr hrpos) _
  have hpert :
      A * cubeSphereC6Norm n (p - MvPolynomial.C (polyMin p)) / (r : ℝ) ^ 4 ≤
        (A * B) * (polyMax p - polyMin p) / (r : ℝ) ^ 4 := by
    apply div_le_div_of_nonneg_right _ hden.le
    calc
      A * cubeSphereC6Norm n (p - MvPolynomial.C (polyMin p)) ≤
          A * (B * (polyMax p - polyMin p)) :=
        mul_le_mul_of_nonneg_left hnorm hA.le
      _ = (A * B) * (polyMax p - polyMin p) := by ring
  let delta : ℝ :=
    (A * B) * (polyMax p - polyMin p) / (r : ℝ) ^ 4 -
      A * cubeSphereC6Norm n (p - MvPolynomial.C (polyMin p)) / (r : ℝ) ^ 4
  have hdelta : 0 ≤ delta := sub_nonneg.mpr hpert
  have hconst :
      SphereSOSMod (MvPolynomial.C delta : MvPolynomial (Fin (2 * n + 1)) ℝ) r :=
    sphereSOSMod_const hdelta
  have heq :
      cubeSphereLift n (p - MvPolynomial.C (polyMin p)) +
          MvPolynomial.C ((A * B) * (polyMax p - polyMin p) / (r : ℝ) ^ 4) =
        (cubeSphereLift n (p - MvPolynomial.C (polyMin p)) +
            MvPolynomial.C
              (A * cubeSphereC6Norm n (p - MvPolynomial.C (polyMin p)) /
                (r : ℝ) ^ 4)) +
          MvPolynomial.C delta := by
    rw [add_assoc, ← MvPolynomial.C_add]
    congr 1
    dsimp [delta]
    ring
  rw [heq]
  exact hsmall.add hconst

end QuarticConvergence
end OptimalConvergenceRates

end
