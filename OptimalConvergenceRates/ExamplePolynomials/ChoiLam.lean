/-
  OptimalConvergenceRates/ExamplePolynomials/ChoiLam.lean

  Shared definition and evaluation formula for the perturbed Choi-Lam quartic.
-/
import OptimalConvergenceRates.BasicNotions.Defs

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

/-! ## The quartic obstruction -/

/-- The Choi-Lam type quaternary quartic
`w^4 + x^2*y^2 + y^2*z^2 + z^2*x^2 - 4*w*x*y*z`. -/
def choiLamQuartic : MvPolynomial (Fin 4) ℝ :=
  (MvPolynomial.X (0 : Fin 4)) ^ 4
    + (MvPolynomial.X (1 : Fin 4)) ^ 2 * (MvPolynomial.X (2 : Fin 4)) ^ 2
    + (MvPolynomial.X (2 : Fin 4)) ^ 2 * (MvPolynomial.X (3 : Fin 4)) ^ 2
    + (MvPolynomial.X (3 : Fin 4)) ^ 2 * (MvPolynomial.X (1 : Fin 4)) ^ 2
    - 4 * MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (1 : Fin 4)
        * MvPolynomial.X (2 : Fin 4) * MvPolynomial.X (3 : Fin 4)

theorem choiLamQuartic_eval (v : Fin 4 → ℝ) :
    MvPolynomial.eval v choiLamQuartic =
      v 0 ^ 4 + v 1 ^ 2 * v 2 ^ 2 + v 2 ^ 2 * v 3 ^ 2
        + v 3 ^ 2 * v 1 ^ 2 - 4 * v 0 * v 1 * v 2 * v 3 := by
  simp [choiLamQuartic, map_add, map_sub, map_mul, map_pow, eval_X]


/-- Perturbation of the Choi-Lam quartic by a constant. -/
def choiLamPerturbed (epsilon : ℝ) : MvPolynomial (Fin 4) ℝ :=
  choiLamQuartic + MvPolynomial.C epsilon

theorem choiLamPerturbed_eq (epsilon : ℝ) :
    choiLamPerturbed epsilon = choiLamQuartic + MvPolynomial.C epsilon := rfl

end OptimalConvergenceRates

end
