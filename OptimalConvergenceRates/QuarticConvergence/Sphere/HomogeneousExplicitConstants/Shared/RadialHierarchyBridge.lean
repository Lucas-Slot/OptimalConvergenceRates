import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.ChebyshevSOSKernel
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.ExplicitFeasibility

/-! Exact bounded-degree bridges to the original equality-constrained
sphere hierarchy. No change of radius or relaxation order occurs. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace RadialHierarchyBridge

open scoped BigOperators
open Foundation ChebyshevSOSKernel

def radialGeometricSum (n r : ℕ) : Foundation.Polynomial n :=
  ∑ i ∈ Finset.range r, (radiusPolynomial n)^i

theorem radialGeometricSum_identity (n r : ℕ) :
    (1-radiusPolynomial n)*radialGeometricSum n r = 1-(radiusPolynomial n)^r := by
  have h := geom_sum_mul_neg (radiusPolynomial n) r
  simpa only [radialGeometricSum, mul_comm] using h

theorem radialGeometricSum_degree (n r : ℕ) :
    (radialGeometricSum n r).totalDegree ≤ 2*r-2 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  have hil : i<r := Finset.mem_range.mp hi
  calc
    ((radiusPolynomial n)^i).totalDegree ≤ i*(radiusPolynomial n).totalDegree :=
      MvPolynomial.totalDegree_pow _ _
    _ ≤ i*2 := Nat.mul_le_mul_left i (radiusPolynomial_totalDegree_le n)
    _ ≤ 2*r-2 := by omega

/-- A homogeneous radial shift with an actual bounded SOS proves a literal
`Feasible` value at the SAME root degree, with the full ideal budget. -/
theorem bounded_sos_radial_shift_feasible {n r : ℕ} (p : Foundation.Polynomial n)
    (c : ℝ) (hp : BoundedSOS r (p + MvPolynomial.C c * (radiusPolynomial n) ^ r)) :
    Feasible r p (-c) := by
  rcases hp.exists_squares with ⟨m,h,hh,hid⟩
  let g : Foundation.Polynomial n := MvPolynomial.C c*radialGeometricSum n r
  apply feasible_of_squares h g hh
  · calc
      g.totalDegree ≤ (MvPolynomial.C c : Foundation.Polynomial n).totalDegree+
          (radialGeometricSum n r).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ = (radialGeometricSum n r).totalDegree := by simp
      _ ≤ 2*r-2 := radialGeometricSum_degree n r
  · rw [← hid, MvPolynomial.C_neg]
    dsimp [g]
    have hgeom := radialGeometricSum_identity n r
    linear_combination -(MvPolynomial.C c)*hgeom

end RadialHierarchyBridge
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
