import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.RadialHierarchyBridge

/-! A homogeneous SOS certificate gives the exact original sphere level,
including the bounded-degree free equality multiplier. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace HomogeneousHierarchyBridge

open Foundation ChebyshevSOSKernel RadialHierarchyBridge

theorem polynomial_radialGeometricSum_degree {n r l : ℕ}
    (p : Foundation.Polynomial n) (hp : p.totalDegree ≤ 2 * l) (hlr : l ≤ r) :
    (p*radialGeometricSum n (r-l)).totalDegree≤2*r-2 := by
  by_cases hrl : r=l
  · simp [hrl,radialGeometricSum]
  · have hj : 1≤r-l := by omega
    calc
      (p*radialGeometricSum n (r-l)).totalDegree ≤
          p.totalDegree+(radialGeometricSum n (r-l)).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 2*l+(2*(r-l)-2) := Nat.add_le_add hp (radialGeometricSum_degree n (r-l))
      _ ≤ 2*r-2 := by omega

theorem bounded_sos_homogeneous_certificate_feasible {n r l : ℕ}
    (p : Foundation.Polynomial n) (hp : p.totalDegree ≤ 2 * l) (hlr : l ≤ r)
    (lam : ℝ)
    (hsos : BoundedSOS r ((radiusPolynomial n) ^ (r - l) *
      (p - MvPolynomial.C lam * (radiusPolynomial n) ^ l))) :
    Feasible r p lam := by
  rcases hsos.exists_squares with ⟨m,h,hh,hid⟩
  let g : Foundation.Polynomial n :=
    p*radialGeometricSum n (r-l)-MvPolynomial.C lam*radialGeometricSum n r
  apply feasible_of_squares h g hh
  · apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · exact polynomial_radialGeometricSum_degree p hp hlr
    · calc
        (MvPolynomial.C lam*radialGeometricSum n r).totalDegree ≤
            (MvPolynomial.C lam : Foundation.Polynomial n).totalDegree+
              (radialGeometricSum n r).totalDegree := MvPolynomial.totalDegree_mul _ _
        _ = (radialGeometricSum n r).totalDegree := by simp
        _ ≤ 2*r-2 := radialGeometricSum_degree n r
  · rw [←hid]
    dsimp [g]
    have hgeo1 := radialGeometricSum_identity n (r-l)
    have hgeo2 := radialGeometricSum_identity n r
    have hpow : (radiusPolynomial n)^(r-l)*(radiusPolynomial n)^l =
        (radiusPolynomial n)^r := by rw [←pow_add,Nat.sub_add_cancel hlr]
    linear_combination -p*hgeo1+MvPolynomial.C lam*hgeo2+MvPolynomial.C lam*hpow

end HomogeneousHierarchyBridge
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
