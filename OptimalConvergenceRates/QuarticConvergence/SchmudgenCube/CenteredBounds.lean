/-
  Public cube-centering lemmas for fixed-degree hierarchy estimates.

  These statements use the repository's existing `Hypercube`, `polyMin`,
  `polyMax`, `polySupNorm`, and `IsNonnegOn` APIs directly.
-/
import OptimalConvergenceRates.BasicNotions.SOS

open MvPolynomial

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

variable {n : ℕ}

/-- The oscillation `polyMax p - polyMin p` is nonnegative. -/
theorem polyMax_sub_polyMin_nonneg (p : MvPolynomial (Fin n) ℝ) :
    0 ≤ polyMax p - polyMin p :=
  sub_nonneg.mpr (polyMin_le_polyMax p)

/-- Centering a polynomial at its cube minimum makes it nonnegative on the cube. -/
theorem centerAtPolyMin_nonnegative (p : MvPolynomial (Fin n) ℝ) :
    IsNonnegOn (p - MvPolynomial.C (polyMin p)) (Hypercube n) := by
  intro x hx
  simp only [map_sub, MvPolynomial.eval_C]
  exact sub_nonneg.mpr (polyMin_le_eval p x hx)

/-- Centering at the cube minimum makes the new minimum exactly zero. -/
@[simp] theorem polyMin_centerAtPolyMin (p : MvPolynomial (Fin n) ℝ) :
    polyMin (p - MvPolynomial.C (polyMin p)) = 0 := by
  rw [polyMin_sub_C, sub_self]

/-- Centering at the cube minimum makes the new maximum the original oscillation. -/
@[simp] theorem polyMax_centerAtPolyMin (p : MvPolynomial (Fin n) ℝ) :
    polyMax (p - MvPolynomial.C (polyMin p)) = polyMax p - polyMin p := by
  exact polyMax_sub_C p (polyMin p)

/-- The cube sup norm after centering at the minimum is exactly the oscillation.

This is the cube analogue of `sphereSupNorm_center_eq_oscillation` and is the
normalization identity needed to turn nonnegative-polynomial estimates into
estimates for arbitrary objectives.
-/
theorem polySupNorm_centerAtPolyMin_eq (p : MvPolynomial (Fin n) ℝ) :
    polySupNorm (p - MvPolynomial.C (polyMin p)) = polyMax p - polyMin p := by
  let q := p - MvPolynomial.C (polyMin p)
  apply le_antisymm
  · calc
      polySupNorm q ≤ polyMax q :=
        polySupNorm_le_polyMax_of_nonneg q (centerAtPolyMin_nonnegative p)
      _ = polyMax p - polyMin p := polyMax_centerAtPolyMin p
  · obtain ⟨x, hx, hmax⟩ := polyMax_mem p
    have hnorm := polySupNorm_eval_le q (polySupNorm q) le_rfl x hx
    simp only [q, map_sub, MvPolynomial.eval_C, hmax] at hnorm
    rw [abs_of_nonneg (polyMax_sub_polyMin_nonneg p)] at hnorm
    exact hnorm

/-- Subtracting the cube minimum never increases total degree. -/
theorem centerAtPolyMin_totalDegree_le (p : MvPolynomial (Fin n) ℝ) :
    (p - MvPolynomial.C (polyMin p)).totalDegree ≤ p.totalDegree :=
  MvPolynomial.totalDegree_sub_C_le p (polyMin p)

/-- A convenient bounded-degree form of `centerAtPolyMin_totalDegree_le`. -/
theorem centerAtPolyMin_totalDegree_le_of_le {p : MvPolynomial (Fin n) ℝ} {d : ℕ}
    (hp : p.totalDegree ≤ d) :
    (p - MvPolynomial.C (polyMin p)).totalDegree ≤ d :=
  (centerAtPolyMin_totalDegree_le p).trans hp

end QuarticConvergence
end OptimalConvergenceRates

end
