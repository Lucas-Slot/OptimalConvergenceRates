import OptimalConvergenceRates.CQC.BoxLiftPenalty

/-! Polynomial definitions for the corrected lift in slack-value variables. -/

noncomputable section

open MvPolynomial Finset Matrix

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

/-- Substitute the square of every slack coordinate while fixing the base
coordinates. -/
def squareSlackSubstitution :
    MvPolynomial (Fin (n + m)) ℝ →ₐ[ℝ] MvPolynomial (Fin (n + m)) ℝ :=
  MvPolynomial.aeval fun j ↦ Fin.addCases
    (fun k ↦ X (Fin.castAdd m k))
    (fun i ↦ (X (Fin.natAdd n i)) ^ 2) j

/-- Row Gram matrix written in the independent slack-value variables `u`. -/
def slackValueGramPolynomial (g : Fin m → MvPolynomial (Fin n) ℝ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin (n + m)) ℝ) :=
  fun i k ↦
    (∑ j : Fin n,
      liftBasePolynomial (MvPolynomial.pderiv j (g i)) *
        liftBasePolynomial (MvPolynomial.pderiv j (g k))) +
      if i = k then MvPolynomial.C 4 * X (Fin.natAdd n i) else 0

/-- Gram determinant in independent slack-value variables. -/
def slackValueDeterminant (g : Fin m → MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin (n + m)) ℝ :=
  Matrix.det (slackValueGramPolynomial g)

/-- Base-coordinate part of `2 p grad d + d grad p`. -/
def slackValueBaseW (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (j : Fin n) :
    MvPolynomial (Fin (n + m)) ℝ :=
  MvPolynomial.C 2 * liftBasePolynomial p *
      MvPolynomial.pderiv (Fin.castAdd m j) (slackValueDeterminant g) +
    slackValueDeterminant g *
      liftBasePolynomial (MvPolynomial.pderiv j p)

/-- The vector inside the adjugate in the direct slack-value formula. -/
def slackValueCorrectionRhs (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (i : Fin m) :
    MvPolynomial (Fin (n + m)) ℝ :=
  (∑ j : Fin n,
      liftBasePolynomial (MvPolynomial.pderiv j (g i)) *
        slackValueBaseW g p j) -
    MvPolynomial.C 8 * liftBasePolynomial p * X (Fin.natAdd n i) *
      MvPolynomial.pderiv (Fin.natAdd n i) (slackValueDeterminant g)

/-- Adjugate correction coefficients in independent slack-value variables. -/
def slackValueCorrection (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) :
    Fin m → MvPolynomial (Fin (n + m)) ℝ :=
  (slackValueGramPolynomial g).adjugate *ᵥ slackValueCorrectionRhs g p

/-- The descended fixed polynomial `P(x,u)` from the CQC construction. -/
def descendedSlackObjective (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (M : ℝ) :
    MvPolynomial (Fin (n + m)) ℝ :=
  (slackValueDeterminant g) ^ 2 * liftBasePolynomial p -
    ∑ i, (liftBasePolynomial (g i) - X (Fin.natAdd n i)) *
      slackValueCorrection g p i +
    MvPolynomial.C M *
      ∑ i, (liftBasePolynomial (g i) - X (Fin.natAdd n i)) ^ 2

/-- Substitute the original generators for the independent slack values. -/
def generatorSlackSubstitution
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin (n + m)) ℝ →ₐ[ℝ] MvPolynomial (Fin n) ℝ :=
  MvPolynomial.aeval fun j ↦ Fin.addCases X g j

end CQCInternal
end OptimalConvergenceRates

end
