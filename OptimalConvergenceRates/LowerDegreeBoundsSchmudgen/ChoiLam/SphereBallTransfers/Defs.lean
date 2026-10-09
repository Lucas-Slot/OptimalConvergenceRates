/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/ChoiLam/SphereBallTransfers/Defs.lean

  Polynomial data and SOS-modulo-sphere certificate predicates for the sphere transfer.
-/
import OptimalConvergenceRates.BasicNotions.BoxCones
import OptimalConvergenceRates.BasicNotions.SphereSOS
import OptimalConvergenceRates.ExamplePolynomials.ChoiLam
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MvPolynomial Finset
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace SphereBallTransfers


/-! ## The four-dimensional Choi-Lam sphere instance -/

/-- Embed one of the four Choi-Lam `x` variables into the five sphere variables
`(x_0,x_1,x_2,x_3,u)`. -/
abbrev xIndexInSphere (i : Fin 4) : Fin 5 :=
  Fin.castSucc i

/-- The fifth sphere variable `u`. -/
abbrev uIndexInSphere : Fin 5 :=
  4

/-- The existing Choi-Lam quartic, embedded into the first four variables of
`R[x_0,x_1,x_2,x_3,u]`. -/
def choiLamSphereQuartic : MvPolynomial (Fin 5) ℝ :=
  MvPolynomial.rename xIndexInSphere choiLamQuartic

/-- The ball quadratic `s(x) = x_0^2 + ... + x_3^2`, embedded in the sphere ring. -/
def ballQuadraticInSphere : MvPolynomial (Fin 5) ℝ :=
  ∑ i : Fin 4, (X (xIndexInSphere i)) ^ 2

/-- The ball generator `g(x) = 1 - s(x)`, embedded in the sphere ring. -/
def ballGeneratorInSphere : MvPolynomial (Fin 5) ℝ :=
  1 - ballQuadraticInSphere

/-- The sphere quadratic `rho(x,u) = s(x) + u^2`. -/
def sphereRho : MvPolynomial (Fin 5) ℝ :=
  ballQuadraticInSphere + (X uIndexInSphere) ^ 2

/-- The sphere relation in the `(x,u)` presentation: `rho - 1`. -/
def sphereRhoRelation : MvPolynomial (Fin 5) ℝ :=
  sphereRho - 1

@[simp] theorem sphereRhoRelation_eq_sphereRelation :
    sphereRhoRelation = sphereRelation 5 := by
  unfold sphereRhoRelation sphereRelation sphereRho sphereQuadratic ballQuadraticInSphere
    uIndexInSphere xIndexInSphere
  simp [Fin.sum_univ_five, Fin.sum_univ_four]

/-- The sphere equation `rho - 1 = u^2 - g`. -/
theorem sphereRhoRelation_eq_u_sq_sub_ballGenerator :
    sphereRhoRelation = (X uIndexInSphere) ^ 2 - ballGeneratorInSphere := by
  unfold sphereRhoRelation sphereRho ballGeneratorInSphere
  ring

@[simp] theorem eval_sphereRho (x : Fin 5 → ℝ) :
    MvPolynomial.eval x sphereRho =
      (∑ i : Fin 4, x (xIndexInSphere i) ^ 2) + x uIndexInSphere ^ 2 := by
  unfold sphereRho ballQuadraticInSphere
  simp [map_sum, map_add, map_pow, eval_X]

/-- The quartic perturbation `F_epsilon = C_x + epsilon * rho^2`. -/
def sphereChoiLamPerturbed (epsilon : ℝ) : MvPolynomial (Fin 5) ℝ :=
  choiLamSphereQuartic + MvPolynomial.C epsilon * sphereRho ^ 2

/-- The sphere SOS certificate with square-root degree `k`. -/
def ChoiLamHasSphereCert (k : ℕ) (epsilon : ℝ) : Prop :=
  SphereSOSMod (sphereChoiLamPerturbed epsilon) k

/-- The same sphere certificate, with explicit witness data. -/
abbrev ChoiLamSphereCertWitness (k : ℕ) (epsilon : ℝ) :=
  SphereSOSWitness (sphereChoiLamPerturbed epsilon) k

/-! ## Box-side notation used by the transfer theorem -/

/-- The degree-`2k` Schmudgen cone on the four-dimensional box.

The cone `BoxPreordering 4 r` uses a total degree bound `r`, so `Tbox k` is
`BoxPreordering 4 (2 * k)`. -/
def Tbox (k : ℕ) : Set (MvPolynomial (Fin 4) ℝ) :=
  BoxPreordering 4 (2 * k)

/-- Box certificate predicate for the perturbed Choi-Lam quartic. -/
def BoxCert (k : ℕ) (delta : ℝ) : Prop :=
  choiLamPerturbed delta ∈ Tbox k

/-- Fourth-power lower-bound hypothesis for the box theorem. -/
def BoxLB4 (beta delta0 : ℝ) : Prop :=
  ∀ ⦃k : ℕ⦄ ⦃delta : ℝ⦄,
    0 < delta → delta ≤ delta0 → BoxCert k delta → beta ≤ delta * (k : ℝ) ^ 4

/-- Root-form lower-bound hypothesis for the box theorem. This is useful for
stating the human-facing theorem, while `BoxLB4` is expected to be easier for
Lean arithmetic. -/
def BoxLBRoot (c delta0 : ℝ) : Prop :=
  ∀ ⦃k : ℕ⦄ ⦃delta : ℝ⦄,
    0 < delta → delta ≤ delta0 → BoxCert k delta → c * delta ^ (-(1 : ℝ) / 4) ≤ (k : ℝ)

/-- Feasible root-degree levels for the sphere certificate. -/
def sphereFeasibleLevels (epsilon : ℝ) : Set ℕ :=
  {k | 2 ≤ k ∧ ChoiLamHasSphereCert k epsilon}

/-- Feasible root-degree levels for the box certificate. -/
def boxFeasibleLevels (delta : ℝ) : Set ℕ :=
  {k | BoxCert k delta}

end SphereBallTransfers
end OptimalConvergenceRates

end
