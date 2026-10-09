/-
  Normalization of cube approximations by the lifted sphere C6 norm.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.LiftCertificate
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarApproximationHomogeneity

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- The lifted sphere `C^6` norm dominates the cube sup norm. -/
theorem polySupNorm_le_cubeSphereC6Norm {n : ℕ} (hn : 0 < n)
    (h : MvPolynomial (Fin n) ℝ) :
    polySupNorm h ≤ cubeSphereC6Norm n h := by
  rw [← sphereSupNorm_cubeSphereLift hn h]
  exact sphereSupNorm_le_sphereRotNorm (by omega : 0 < 2 * n + 1)
    6 (cubeSphereLift n h)

/-- It is enough to construct the quartic Putinar approximant after dividing
by the lifted sphere `C^6` norm.  The output error is homogeneous in that
norm, with no extra order cost. -/
theorem hasQuarticBoxQMApproximationAt_of_cubeSphereC6Norm_normalized
    {n B m : ℕ} {h : MvPolynomial (Fin n) ℝ} {L : ℝ}
    (hn : 0 < n) (hnonnegative : IsNonnegOn h (Hypercube n))
    (hnormalized : cubeSphereC6Norm n h ≠ 0 →
      HasQuarticBoxQMApproximationAt
        ((cubeSphereC6Norm n h)⁻¹ • h) B m L) :
    HasQuarticBoxQMApproximationAt h B m
      (cubeSphereC6Norm n h * L) := by
  apply hasQuarticBoxQMApproximationAt_of_normalized hnonnegative
    (sphereC6Norm_nonneg (by omega : 0 < 2 * n + 1)
      (cubeSphereLift n h))
    (polySupNorm_le_cubeSphereC6Norm hn h)
  exact hnormalized

end QuarticConvergence
end OptimalConvergenceRates

end
