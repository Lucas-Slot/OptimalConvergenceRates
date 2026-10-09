/-
  Fixed-degree regularity comparison for lifted cube polynomials.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.FixedDegree
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.LiftCertificate

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence


/-- On cube polynomials of fixed degree, the inherited sphere `C6` size of
the centered lift is controlled by the cube oscillation. -/
theorem fixedDegreeCubeSphereC6Comparison {n d : ℕ} (hn : 0 < n) :
    ∃ B : ℝ, 0 < B ∧
      ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d →
        cubeSphereC6Norm n (p - MvPolynomial.C (polyMin p)) ≤
          B * (polyMax p - polyMin p) := by
  obtain ⟨B, hB, hbound⟩ :=
    fixedDegreeC6Comparison
      (n := 2 * n + 1) (d := (2 * n + 1) * d) (by omega : 3 ≤ 2 * n + 1)
  refine ⟨B, hB, ?_⟩
  intro p hpdeg
  have hliftdeg : (cubeSphereLift n p).totalDegree ≤ (2 * n + 1) * d :=
    (cubeSphereLift_totalDegree_le n p).trans
      (Nat.mul_le_mul_left (2 * n + 1) hpdeg)
  have h := hbound (cubeSphereLift n p) hliftdeg
  have hcenter :
      cubeSphereLift n (p - MvPolynomial.C (polyMin p)) =
        cubeSphereLift n p -
          MvPolynomial.C (spherePolyMin (cubeSphereLift n p)) := by
    rw [map_sub, cubeSphereLift_C, spherePolyMin_cubeSphereLift hn p]
  rw [← hcenter, spherePolyOscillation_cubeSphereLift hn p] at h
  exact h

end QuarticConvergence
end OptimalConvergenceRates

end
