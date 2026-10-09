/-
  Explicit gradients of the five quadratic constraints.
-/
import OptimalConvergenceRates.MFCQQuadraticLowerBound.Geometry

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.MFCQQuadraticLowerBound

@[simp] theorem gradient_generator_zero (z : Fin 3 → ℝ) :
    gradientAt (generators 0) z = ![-2 * z 0, 6 * z 1, 1] := by
  change gradientAt (t - q₁) z = _
  funext j
  fin_cases j <;>
    simp [gradientAt, q₁, u, v, t, Pi.single_apply] <;> ring

@[simp] theorem gradient_generator_one (z : Fin 3 → ℝ) :
    gradientAt (generators 1) z = ![6 * z 0, -2 * z 1, 1] := by
  change gradientAt (t - q₂) z = _
  funext j
  fin_cases j <;>
    simp [gradientAt, q₂, u, v, t, Pi.single_apply] <;> ring

@[simp] theorem gradient_generator_two (z : Fin 3 → ℝ) :
    gradientAt (generators 2) z =
      ![2 * z 0 - 4 * z 1, 2 * z 1 - 4 * z 0, 1] := by
  change gradientAt (t - q₃) z = _
  funext j
  fin_cases j <;>
    simp [gradientAt, q₃, u, v, t, Pi.single_apply] <;> ring

@[simp] theorem gradient_generator_three (z : Fin 3 → ℝ) :
    gradientAt (generators 3) z =
      ![2 * z 0 + 4 * z 1, 2 * z 1 + 4 * z 0, 1] := by
  change gradientAt (t - q₄) z = _
  funext j
  fin_cases j <;>
    simp [gradientAt, q₄, u, v, t, Pi.single_apply] <;> ring

@[simp] theorem gradient_generator_four (z : Fin 3 → ℝ) :
    gradientAt (generators 4) z = ![-2 * z 0, -2 * z 1, -2 * z 2] := by
  change gradientAt ball z = _
  funext j
  fin_cases j <;>
    simp [gradientAt, ball, u, v, t, Pi.single_apply] <;> ring

end OptimalConvergenceRates.MFCQQuadraticLowerBound

end
