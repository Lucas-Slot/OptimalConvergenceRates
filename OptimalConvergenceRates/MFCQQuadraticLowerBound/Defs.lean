/-
# The MFCQ quadratic lower-bound example

This module formalizes the fixed three-variable example used for the MFCQ quadratic lower
bound. The variables, in order, are `u`, `v`, and `t`. The repository's generalized
quadratic module is truncated by *total certificate degree*, so paper order `r` is
represented by degree bound `2 * r`.
-/
import OptimalConvergenceRates.CQC.MainResults
import OptimalConvergenceRates.GeneralArchimedean.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.MFCQQuadraticLowerBound

/-- The coordinate `u`. -/
abbrev u : MvPolynomial (Fin 3) ℝ := X 0

/-- The coordinate `v`. -/
abbrev v : MvPolynomial (Fin 3) ℝ := X 1

/-- The coordinate `t`, which is also the objective. -/
abbrev t : MvPolynomial (Fin 3) ℝ := X 2

abbrev q₁ : MvPolynomial (Fin 3) ℝ := u ^ 2 - C 3 * v ^ 2
abbrev q₂ : MvPolynomial (Fin 3) ℝ := v ^ 2 - C 3 * u ^ 2
abbrev q₃ : MvPolynomial (Fin 3) ℝ := C 4 * u * v - u ^ 2 - v ^ 2
abbrev q₄ : MvPolynomial (Fin 3) ℝ := -C 4 * u * v - u ^ 2 - v ^ 2

/-- The redundant ball constraint that makes the module Archimedean. -/
abbrev ball : MvPolynomial (Fin 3) ℝ :=
  C 1 - u ^ 2 - v ^ 2 - t ^ 2

/-- The five generators `t-q₁`, ..., `t-q₄`, and the unit-ball generator. -/
def generators : Fin 5 → MvPolynomial (Fin 3) ℝ :=
  ![t - q₁, t - q₂, t - q₃, t - q₄, ball]

/-- The objective in the example. -/
abbrev objective : MvPolynomial (Fin 3) ℝ := t

/-- The basic closed feasible set of the example. -/
abbrev feasibleSet : Set (Fin 3 → ℝ) :=
  KrivineStengle.basicClosedSet generators

/-- The origin, which will be the unique minimizer. -/
def origin : Fin 3 → ℝ := fun _ ↦ 0

/-- The unnormalised maximum constraint violation from the note. -/
def violation (z : Fin 3 → ℝ) : ℝ :=
  max 0 <| max (-eval z (generators 0)) <|
    max (-eval z (generators 1)) <|
      max (-eval z (generators 2)) <|
        max (-eval z (generators 3)) (-eval z (generators 4))

/-- The Euclidean distance from `z` to a set of coordinate vectors. -/
def euclideanDistanceToSet (z : Fin 3 → ℝ) (S : Set (Fin 3 → ℝ)) : ℝ :=
  Metric.infDist (WithLp.toLp 2 z) (WithLp.toLp 2 '' S)

/-- The active-gradient vector of a polynomial at a point. -/
def gradientAt (p : MvPolynomial (Fin 3) ℝ) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun j ↦ eval z (pderiv j p)

/-- Mangasarian--Fromovitz constraint qualification at one feasible point. -/
def MFCQAt (g : Fin 5 → MvPolynomial (Fin 3) ℝ) (z : Fin 3 → ℝ) : Prop :=
  z ∈ KrivineStengle.basicClosedSet g ∧
    ∃ w : Fin 3 → ℝ, ∀ i, eval z (g i) = 0 →
      0 < ∑ j : Fin 3, gradientAt (g i) z j * w j

/-- Linear independence of the active gradients at one feasible point (CQC/LICQ). -/
def CQCAt (g : Fin 5 → MvPolynomial (Fin 3) ℝ) (z : Fin 3 → ℝ) : Prop :=
  z ∈ KrivineStengle.basicClosedSet g ∧
    LinearIndependent ℝ
      (fun i : {i : Fin 5 // eval z (g i) = 0} ↦ gradientAt (g i) z)

/-- Best nonnegative perturbation admitting a paper-order `r` certificate. -/
def hierarchyError (r : ℕ) : ℝ :=
  sInf {ε : ℝ | 0 ≤ ε ∧
    objective + C ε ∈ GenQuadraticModule generators (2 * r)}

end OptimalConvergenceRates.MFCQQuadraticLowerBound

end
