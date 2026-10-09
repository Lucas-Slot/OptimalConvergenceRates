import OptimalConvergenceRates.CQC.SlackValueCorrectionDescent
import OptimalConvergenceRates.CQC.SlackValueAlgebra

/-! Pullback of the descended polynomial to the original generators. -/

noncomputable section

open MvPolynomial Matrix

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

@[simp]
theorem generatorSlackSubstitution_slackValueGramPolynomial
    (g : Fin m → MvPolynomial (Fin n) ℝ) (i k : Fin m) :
    generatorSlackSubstitution g (slackValueGramPolynomial g i k) =
      cqcGramPolynomial g i k := by
  by_cases hik : i = k <;>
    simp [slackValueGramPolynomial, cqcGramPolynomial, hik]

@[simp]
theorem generatorSlackSubstitution_slackValueDeterminant
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    generatorSlackSubstitution g (slackValueDeterminant g) =
      determinantMultiplier g := by
  let φ := (generatorSlackSubstitution g).toRingHom
  have hm : φ.mapMatrix (slackValueGramPolynomial g) =
      cqcGramPolynomial g := by
    apply Matrix.ext
    intro i k
    exact generatorSlackSubstitution_slackValueGramPolynomial g i k
  calc
    generatorSlackSubstitution g (slackValueDeterminant g) =
        φ (Matrix.det (slackValueGramPolynomial g)) := rfl
    _ = Matrix.det (φ.mapMatrix (slackValueGramPolynomial g)) :=
      RingHom.map_det φ (slackValueGramPolynomial g)
    _ = Matrix.det (cqcGramPolynomial g) := by rw [hm]
    _ = determinantMultiplier g := rfl

/-- Algebraic pullback identity `P(x,g(x)) = a(x)^2 p(x)`. -/
theorem generatorSlackSubstitution_descendedSlackObjective
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (M : ℝ) :
    generatorSlackSubstitution g (descendedSlackObjective g p M) =
      (determinantMultiplier g) ^ 2 * p := by
  simp [descendedSlackObjective]

end CQCInternal
end OptimalConvergenceRates

end
