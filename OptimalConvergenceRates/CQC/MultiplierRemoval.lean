import Mathlib.Algebra.Order.Field.GeomSum
import OptimalConvergenceRates.GeneralArchimedean.IntervalCertificateSubstitution
import OptimalConvergenceRates.GeneralArchimedean.QualitativePutinar

/-!
# Removing a fixed positive polynomial multiplier

This file contains the qualitative entry point and the degree-controlled
interval machinery used to remove the determinant multiplier produced by the
CQC lift.
-/

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates
namespace CQCInternal

open GeneralArchimedean

variable {n m : ℕ}

/-- A fixed polynomial that is strictly positive on a nonempty Archimedean
basic closed set belongs to the untruncated quadratic module without an added
perturbation. -/
theorem quadraticModuleMem_of_posOn
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (q : MvPolynomial (Fin n) ℝ)
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hq : ∀ x ∈ KrivineStengle.basicClosedSet g, 0 < MvPolynomial.eval x q) :
    QuadraticModuleMem g q := by
  obtain ⟨x, hx, hxmin⟩ := polynomialMinimum_mem hne harch q
  have hmin : 0 < polynomialMinimum g q := by
    rw [← hxmin]
    exact hq x hx
  have hcert := qualitative_putinar g
    (q - C (polynomialMinimum g q)) harch (centered_nonnegOn harch q) hmin
  convert hcert using 1
  ring

/-- Finite-order form of `quadraticModuleMem_of_posOn`. -/
theorem exists_order_of_posOn
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (q : MvPolynomial (Fin n) ℝ)
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hq : ∀ x ∈ KrivineStengle.basicClosedSet g, 0 < MvPolynomial.eval x q) :
    ∃ r, q ∈ GenQuadraticModule g r :=
  quadraticModuleMem_of_posOn g q hne harch hq

/-- The shifted geometric-series variable
`1 - (u + alpha) / beta`. -/
def inverseSeriesVariable (α β : ℝ) : Polynomial ℝ :=
  Polynomial.C (1 - α / β) - Polynomial.C (1 / β) * Polynomial.X

/-- The degree-`ell` finite geometric approximation to `1 / (u + alpha)` on
`0 <= u <= beta - alpha`. -/
def inverseSeriesApprox (α β : ℝ) (ell : ℕ) : Polynomial ℝ :=
  Polynomial.C (1 / β) *
    ∑ j ∈ Finset.range (ell + 1), inverseSeriesVariable α β ^ j

/-- The multiplicative residual of `inverseSeriesApprox`. -/
def inverseSeriesResidual (α β : ℝ) (ell : ℕ) : Polynomial ℝ :=
  1 - (Polynomial.X + Polynomial.C α) ^ 2 * inverseSeriesApprox α β ell ^ 2

@[simp]
theorem inverseSeriesVariable_eval (α β u : ℝ) :
    (inverseSeriesVariable α β).eval u = 1 - (u + α) / β := by
  simp [inverseSeriesVariable]
  ring

@[simp]
theorem inverseSeriesApprox_eval (α β u : ℝ) (ell : ℕ) :
    (inverseSeriesApprox α β ell).eval u =
      (1 / β) * ∑ j ∈ Finset.range (ell + 1), (1 - (u + α) / β) ^ j := by
  rw [inverseSeriesApprox, Polynomial.eval_mul, Polynomial.eval_C]
  congr 1
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.eval_pow, inverseSeriesVariable_eval]

@[simp]
theorem inverseSeriesResidual_eval (α β u : ℝ) (ell : ℕ) :
    (inverseSeriesResidual α β ell).eval u =
      1 - (u + α) ^ 2 * (inverseSeriesApprox α β ell).eval u ^ 2 := by
  simp [inverseSeriesResidual]

/-- Exact finite-geometric-series identity underlying multiplier removal. -/
theorem add_mul_inverseSeriesApprox_eval
    {α β : ℝ} (hβ : β ≠ 0) (u : ℝ) (ell : ℕ) :
    (u + α) * (inverseSeriesApprox α β ell).eval u =
      1 - (1 - (u + α) / β) ^ (ell + 1) := by
  let z : ℝ := 1 - (u + α) / β
  have hfactor : (u + α) * (1 / β) = 1 - z := by
    dsimp [z]
    field_simp
    ring
  rw [inverseSeriesApprox_eval]
  rw [← mul_assoc, hfactor]
  simpa [z, mul_comm] using geom_sum_mul_neg z (ell + 1)

/-- The residual is `2 z^L - z^(2L)`, where `L = ell + 1`. -/
theorem inverseSeriesResidual_eval_eq
    {α β : ℝ} (hβ : β ≠ 0) (u : ℝ) (ell : ℕ) :
    (inverseSeriesResidual α β ell).eval u =
      2 * (1 - (u + α) / β) ^ (ell + 1) -
        (1 - (u + α) / β) ^ (2 * (ell + 1)) := by
  have hgeom := add_mul_inverseSeriesApprox_eval (α := α) hβ u ell
  rw [inverseSeriesResidual_eval]
  have hsquare := congrArg (fun t : ℝ ↦ t ^ 2) hgeom
  change ((u + α) * (inverseSeriesApprox α β ell).eval u) ^ 2 =
    (1 - (1 - (u + α) / β) ^ (ell + 1)) ^ 2 at hsquare
  rw [mul_pow] at hsquare
  rw [hsquare]
  have hpow :
      (1 - (u + α) / β) ^ (2 * (ell + 1)) =
        ((1 - (u + α) / β) ^ (ell + 1)) ^ 2 := by
    rw [show 2 * (ell + 1) = (ell + 1) * 2 by omega, pow_mul]
  rw [hpow]
  ring

end CQCInternal
end OptimalConvergenceRates

end
