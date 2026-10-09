import OptimalConvergenceRates.CQC.RegularPenaltyNearest
import OptimalConvergenceRates.CQC.RegularPenaltyTaylor

/-!
# Quadratic penalties for regular polynomial equations

This file isolates the short final step of the regular-zero-set argument.  The
geometric input is a nearest normal point together with a uniform quadratic
equation-to-distance estimate.
-/

noncomputable section

open MvPolynomial Finset Set

namespace OptimalConvergenceRates
namespace CQCInternal

variable {N m : ℕ}

/-- The polynomial sum of squares of a finite equation family. -/
def equationSquareSum (h : Fin m → MvPolynomial (Fin N) ℝ) :
    MvPolynomial (Fin N) ℝ :=
  ∑ i, (h i) ^ 2

@[simp]
theorem eval_equationSquareSum
    (h : Fin m → MvPolynomial (Fin N) ℝ) (z : Fin N → ℝ) :
    MvPolynomial.eval z (equationSquareSum h) =
      ∑ i, (MvPolynomial.eval z (h i)) ^ 2 := by
  simp [equationSquareSum]

theorem eval_equationSquareSum_nonneg
    (h : Fin m → MvPolynomial (Fin N) ℝ) (z : Fin N → ℝ) :
    0 ≤ MvPolynomial.eval z (equationSquareSum h) := by
  rw [eval_equationSquareSum]
  exact Finset.sum_nonneg fun i _ ↦ sq_nonneg (MvPolynomial.eval z (h i))

/-- If the first derivative of `G` kills every constraint gradient, it kills
every normal linear combination of those gradients. -/
theorem evalFDeriv_eq_zero_of_normalCombination
    (h : Fin m → MvPolynomial (Fin N) ℝ)
    (G : MvPolynomial (Fin N) ℝ) (v w : Fin N → ℝ)
    (hnormal : ∀ i,
      QuarticConvergence.mvPolynomialEvalFDeriv G v
        (polynomialGradientAt (h i) v) = 0)
    (hw : ∃ coeff : Fin m → ℝ,
      w = ∑ i, coeff i • polynomialGradientAt (h i) v) :
    QuarticConvergence.mvPolynomialEvalFDeriv G v w = 0 := by
  obtain ⟨coeff, rfl⟩ := hw
  simp [hnormal]

/-- A uniform quadratic equation-to-distance estimate and normal derivative
cancellation give one fixed nonnegative quadratic penalty. -/
theorem exists_regularPolynomialPenalty_of_errorBound
    (h : Fin m → MvPolynomial (Fin N) ℝ)
    (G : MvPolynomial (Fin N) ℝ)
    (A : Set (Fin N → ℝ))
    (hAcompact : IsCompact A) (hAconvex : Convex ℝ A)
    (hVsub : polynomialZeroSet h ⊆ A)
    (hGnonneg : ∀ v ∈ polynomialZeroSet h, 0 ≤ MvPolynomial.eval v G)
    (hnormal : ∀ v ∈ polynomialZeroSet h, ∀ i,
      QuarticConvergence.mvPolynomialEvalFDeriv G v
        (polynomialGradientAt (h i) v) = 0)
    {Cdist : ℝ} (hCdist : 0 ≤ Cdist)
    (hnearest : ∀ z ∈ A,
      ∃ v ∈ polynomialZeroSet h, ∃ coeff : Fin m → ℝ,
        z - v = ∑ i, coeff i • polynomialGradientAt (h i) v ∧
        ‖z - v‖ ^ 2 ≤
          Cdist * MvPolynomial.eval z (equationSquareSum h)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ A,
      0 ≤ MvPolynomial.eval z
        (G + MvPolynomial.C M * equationSquareSum h) := by
  obtain ⟨L, hL, hTaylor⟩ :=
    exists_eval_taylor_bound G A hAcompact hAconvex
  let M := L * Cdist + 1
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  refine ⟨M, hM, ?_⟩
  intro z hz
  obtain ⟨v, hv, coeff, hw, hdist⟩ := hnearest z hz
  have hvA : v ∈ A := hVsub hv
  have hderiv :
      QuarticConvergence.mvPolynomialEvalFDeriv G v (z - v) = 0 :=
    evalFDeriv_eq_zero_of_normalCombination h G v (z - v)
      (hnormal v hv) ⟨coeff, hw⟩
  have hrem := hTaylor v hvA z hz
  rw [hderiv, sub_zero] at hrem
  have hdiff :
      -(L * ‖z - v‖ ^ 2) ≤
        MvPolynomial.eval z G - MvPolynomial.eval v G := by
    exact (neg_le_neg hrem).trans (neg_abs_le _)
  have hscaled :
      L * ‖z - v‖ ^ 2 ≤
        L * (Cdist * MvPolynomial.eval z (equationSquareSum h)) :=
    mul_le_mul_of_nonneg_left hdist hL
  have hsum : 0 ≤ MvPolynomial.eval z (equationSquareSum h) :=
    eval_equationSquareSum_nonneg h z
  rw [map_add, map_mul, eval_C]
  dsimp [M]
  nlinarith [hGnonneg v hv]

end CQCInternal
end OptimalConvergenceRates

end
