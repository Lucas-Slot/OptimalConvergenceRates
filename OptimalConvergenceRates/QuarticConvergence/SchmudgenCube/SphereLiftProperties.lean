/-
  Order and norm consequences of the cube-valued polynomial lift.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.SphereLiftGeometry

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers


/-- Evaluating the lifted polynomial on the sphere is evaluating the original
polynomial at `cubeSphereMap`. -/
theorem eval_cubeSphereLift_eq_map (n : ℕ) (z : Fin (2 * n + 1) → ℝ)
    (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.eval z (cubeSphereLift n p) =
      MvPolynomial.eval (cubeSphereMap n z) p := by
  rw [eval_cubeSphereLift]
  rfl

/-- Cube nonnegativity pulls back to sphere nonnegativity. -/
theorem cubeSphereLift_nonnegative {n : ℕ} (hn : 0 < n)
    {p : MvPolynomial (Fin n) ℝ} (hp : IsNonnegOn p (Hypercube n)) :
    SphereNonnegative (cubeSphereLift n p) := by
  intro z hz
  rw [eval_cubeSphereLift_eq_map]
  exact hp (cubeSphereMap n z) (cubeSphereMap_mem_hypercube hn z hz)

/-- Pullback along the sphere-to-cube map does not increase the sup norm. -/
theorem sphereSupNorm_cubeSphereLift_le {n : ℕ} (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) :
    sphereSupNorm (cubeSphereLift n p) ≤ polySupNorm p := by
  apply sphereSupNorm_le_of_bound (by omega : 0 < 2 * n + 1)
  intro z hz
  rw [eval_cubeSphereLift_eq_map]
  exact polySupNorm_eval_le p (polySupNorm p) le_rfl
    (cubeSphereMap n z) (cubeSphereMap_mem_hypercube hn z hz)

/-- The minimum over the cube is a lower bound for the minimum of the
pullback over the sphere.  The reverse inequality is supplied by the
explicit section of the map. -/
theorem polyMin_le_spherePolyMin_cubeSphereLift {n : ℕ} (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) :
    polyMin p ≤ spherePolyMin (cubeSphereLift n p) := by
  obtain ⟨z, hz, hmin⟩ :=
    spherePolyMin_mem (by omega : 0 < 2 * n + 1) (cubeSphereLift n p)
  rw [← hmin, eval_cubeSphereLift_eq_map]
  exact polyMin_le_eval p (cubeSphereMap n z) (cubeSphereMap_mem_hypercube hn z hz)

end QuarticConvergence
end OptimalConvergenceRates

end
