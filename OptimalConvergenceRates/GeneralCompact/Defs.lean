/-
  Shared definitions for the compact-domain Schmüdgen hierarchy.
-/
import OptimalConvergenceRates.GeneralArchimedean.Defs
import OptimalConvergenceRates.KrivineStengle.BoundedRefutation
import Mathlib.Data.Fin.VecNotation

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.GeneralCompact

variable {n m : ℕ}

/-- Archimedeanity of the generated preordering, in the ball-certificate form. -/
def IsPreorderingArchimedean
    (g : Fin m → MvPolynomial (Fin n) ℝ) : Prop :=
  ∃ R r, 0 < R ∧
    C R - ∑ i : Fin n, X i ^ 2 ∈ GenPreordering g r

open Classical in
/-- The generalized Schmüdgen lower bound at complete-term degree `r`. -/
noncomputable def genLasserreBoundPO
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (f : MvPolynomial (Fin n) ℝ) (r : ℕ) : WithBot ℝ :=
  if _h : {l : ℝ | f - C l ∈ GenPreordering g r}.Nonempty then
    ↑(sSup {l : ℝ | f - C l ∈ GenPreordering g r})
  else
    ⊥

/-- Internal abbreviation for the sharp compact-domain scale. -/
def logTwoOverSq (r : ℕ) : ℝ :=
  Real.log ((max r 2 : ℕ) : ℝ) ^ 2 / (r : ℝ) ^ 2

section SharpBivariate

/-- First coordinate in the fixed bivariate example. -/
def sharpA : MvPolynomial (Fin 2) ℝ := X 0

/-- Objective coordinate in the fixed bivariate example. -/
def sharpZ : MvPolynomial (Fin 2) ℝ := X 1

/-- Cubic generator of the fixed bivariate example. -/
def sharpH : MvPolynomial (Fin 2) ℝ :=
  sharpZ * (sharpA ^ 2 + sharpZ ^ 2)

/-- Unit-ball generator of the fixed bivariate example. -/
def sharpBall : MvPolynomial (Fin 2) ℝ :=
  1 - sharpA ^ 2 - sharpZ ^ 2

/-- The two generators of the fixed bivariate example. -/
def sharpGenerators : Fin 2 → MvPolynomial (Fin 2) ℝ :=
  ![sharpH, sharpBall]

/-- The linear objective of the fixed bivariate example. -/
def sharpObjective : MvPolynomial (Fin 2) ℝ := sharpZ

end SharpBivariate

end OptimalConvergenceRates.GeneralCompact

end
