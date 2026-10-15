/-
  OptimalConvergenceRates/ScaledRobinson/Defs.lean

  Definitions for the scaled Robinson polynomial and the one-generator quadratic
  modules of Euclidean balls used in the scaled Robinson lower-bound theorem.
-/
import OptimalConvergenceRates.BasicNotions.SOS
import OptimalConvergenceRates.ExamplePolynomials.Robinson
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace ScaledRobinson

/-- The squared radius form `x^2 + y^2 + z^2`. -/
def sphereSq : MvPolynomial (Fin 3) ℝ :=
  (X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 + (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2 +
    (X 2 : MvPolynomial (Fin 3) ℝ) ^ 2

/-- The homogeneous threshold form `P_{m,lambda}`. -/
def Pmlambda (m : ℕ) (lambda : ℝ) : MvPolynomial (Fin 3) ℝ :=
  sphereSq ^ m * Phi (MvPolynomial.C lambda * (X 0 : MvPolynomial (Fin 3) ℝ) ^ 2)
    (MvPolynomial.C lambda * (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2) sphereSq

/-- The critical threshold value `4*m*(m+1)` for `P_{m,lambda}`. -/
def criticalLambda (m : ℕ) : ℝ :=
  4 * (m : ℝ) * ((m : ℝ) + 1)

/-- The unit-ball generator `1 - x^2 - y^2`. -/
def UnitBallGenerator : MvPolynomial (Fin 2) ℝ :=
  1 - (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2 - (X 1 : MvPolynomial (Fin 2) ℝ) ^ 2

/-- The radius-`sqrt(lambda)` ball generator `lambda - x^2 - y^2`. -/
def BallGenerator (lambda : ℝ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C lambda - (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2 -
    (X 1 : MvPolynomial (Fin 2) ℝ) ^ 2

/-- The homogeneous radius-`sqrt(lambda)` ball generator `lambda*w^2 - x^2 - y^2`. -/
def HomBallGenerator (lambda : ℝ) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.C lambda * (X 2 : MvPolynomial (Fin 3) ℝ) ^ 2 -
    (X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 - (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2

/-- Dehomogenization map `w = 1` from ternary forms to bivariate polynomials. -/
def dehomogenize3To2 : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.aeval ![(X 0 : MvPolynomial (Fin 2) ℝ), X 1, 1]

/-- Prop-valued degree-bounded SOS witness. -/
def HasDegreeBoundedSOS (σ : MvPolynomial (Fin 2) ℝ) (r : ℕ) : Prop :=
  ∃ N : ℕ, ∃ Q : Fin N → MvPolynomial (Fin 2) ℝ,
    σ = ∑ i : Fin N, (Q i) ^ 2 ∧ ∀ i : Fin N, (Q i).totalDegree ≤ r

/-- Root-degree-bounded membership in the unit-ball quadratic module at order `r`. -/
def UnitBallQuadraticModule (r : ℕ) : Set (MvPolynomial (Fin 2) ℝ) :=
  {p | ∃ σ0 σ1 : MvPolynomial (Fin 2) ℝ,
    HasDegreeBoundedSOS σ0 r ∧ HasDegreeBoundedSOS σ1 (r - 1) ∧
      p = σ0 + UnitBallGenerator * σ1}

/-- Root-degree-bounded membership in the `lambda - x^2 - y^2` quadratic module. -/
def BallQuadraticModule (lambda : ℝ) (r : ℕ) : Set (MvPolynomial (Fin 2) ℝ) :=
  {p | ∃ σ0 σ1 : MvPolynomial (Fin 2) ℝ,
    HasDegreeBoundedSOS σ0 r ∧ HasDegreeBoundedSOS σ1 (r - 1) ∧
      p = σ0 + BallGenerator lambda * σ1}

/-- Degree-bounded SOS witnesses are monotone in the degree bound. -/
theorem HasDegreeBoundedSOS.mono {σ : MvPolynomial (Fin 2) ℝ} {r s : ℕ}
    (hσ : HasDegreeBoundedSOS σ r) (hrs : r ≤ s) :
    HasDegreeBoundedSOS σ s := by
  obtain ⟨N, Q, hQ, hdeg⟩ := hσ
  exact ⟨N, Q, hQ, fun i => (hdeg i).trans hrs⟩

/-- Unit-ball quadratic-module membership is monotone in the order. -/
theorem UnitBallQuadraticModule_mono {r s : ℕ} (hrs : r ≤ s) :
    UnitBallQuadraticModule r ⊆ UnitBallQuadraticModule s := by
  intro p hp
  obtain ⟨σ0, σ1, hσ0, hσ1, hp_eq⟩ := hp
  refine ⟨σ0, σ1, hσ0.mono hrs, ?_, hp_eq⟩
  exact hσ1.mono (Nat.sub_le_sub_right hrs 1)

/-- Scaled-ball quadratic-module membership is monotone in the order. -/
theorem BallQuadraticModule_mono (lambda : ℝ) {r s : ℕ} (hrs : r ≤ s) :
    BallQuadraticModule lambda r ⊆ BallQuadraticModule lambda s := by
  intro p hp
  obtain ⟨σ0, σ1, hσ0, hσ1, hp_eq⟩ := hp
  refine ⟨σ0, σ1, hσ0.mono hrs, ?_, hp_eq⟩
  exact hσ1.mono (Nat.sub_le_sub_right hrs 1)

/-- The expected exact order for `robinson` in the scaled-ball module. -/
def ballTargetOrder (lambda : ℝ) : ℕ :=
  if lambda ≤ 2 then 3 else 3 + Nat.ceil ((Real.sqrt (1 + lambda) - 1) / 2)

/-- The expected exact unit-ball relaxation order for `scaledRobinson eps`. -/
def scaledRobinsonOrder (eps : ℝ) : ℕ :=
  ballTargetOrder (eps⁻¹ ^ 2)

/-- Relational form of exactness for the unit-ball relaxation order. -/
def IsLeastUnitBallOrder (eps : ℝ) (r : ℕ) : Prop :=
  scaledRobinson eps ∈ UnitBallQuadraticModule r ∧
    ∀ s : ℕ, scaledRobinson eps ∈ UnitBallQuadraticModule s → r ≤ s

end ScaledRobinson
end OptimalConvergenceRates

end
