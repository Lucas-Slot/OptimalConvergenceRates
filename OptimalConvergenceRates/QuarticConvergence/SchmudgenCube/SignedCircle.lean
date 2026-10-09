/-
  Signed square-root parametrizations of the product of circles.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.SignOrthogonality
import OptimalConvergenceRates.BasicNotions.BoxCones

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

variable {n : ℕ}

/-- Complete a cube point to the product of circles, with independently chosen
signs on the square-root coordinates. -/
def signedCirclePoint (x : Fin n → ℝ) (eps : Fin n → Bool) :
    CubeCircleVar n → ℝ
  | (i, false) => x i
  | (i, true) => boolSign (eps i) * Real.sqrt (1 - x i ^ 2)

@[simp] theorem signedCirclePoint_first (x : Fin n → ℝ) (eps : Fin n → Bool)
    (i : Fin n) : signedCirclePoint x eps (i, false) = x i := rfl

@[simp] theorem signedCirclePoint_second (x : Fin n → ℝ) (eps : Fin n → Bool)
    (i : Fin n) :
    signedCirclePoint x eps (i, true) =
      boolSign (eps i) * Real.sqrt (1 - x i ^ 2) := rfl

/-- The signed square-root completion lies on every circle whenever the first
coordinates lie in the closed cube. -/
theorem signedCirclePoint_mem_productCircle (x : Fin n → ℝ)
    (eps : Fin n → Bool) (hx : ∀ i, |x i| ≤ 1) :
    signedCirclePoint x eps ∈ ProductCircle n := by
  intro i
  have hsq : x i ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one (x i)).2 (hx i)
  rw [signedCirclePoint_first, signedCirclePoint_second, mul_pow,
    boolSign_sq, one_mul, Real.sq_sqrt (sub_nonneg.mpr hsq)]
  ring

/-- A Walsh character is equivalently the product over its indexing set. -/
theorem cubeSignCharacter_eq_prod (eps : Fin n → Bool) (J : Finset (Fin n)) :
    cubeSignCharacter eps J = ∏ i ∈ J, boolSign (eps i) := by
  classical
  simp [cubeSignCharacter]

/-- The product of selected second coordinates splits into its sign character
and its nonnegative square-root part. -/
theorem signedCirclePoint_second_prod (x : Fin n → ℝ) (eps : Fin n → Bool)
    (J : Finset (Fin n)) :
    ∏ i ∈ J, signedCirclePoint x eps (i, true) =
      cubeSignCharacter eps J * ∏ i ∈ J, Real.sqrt (1 - x i ^ 2) := by
  classical
  rw [cubeSignCharacter_eq_prod]
  simp only [signedCirclePoint_second, Finset.prod_mul_distrib]

/-- The square of the unsigned radius product is the corresponding box-generator product. -/
theorem circleRadius_prod_sq (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ 1)
    (J : Finset (Fin n)) :
    (∏ i ∈ J, Real.sqrt (1 - x i ^ 2)) ^ 2 =
      MvPolynomial.eval x (BoxSemialgebraicGeneratorProd J) := by
  classical
  unfold BoxSemialgebraicGeneratorProd
  rw [map_prod, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  have hsq : x i ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one (x i)).2 (hx i)
  rw [Real.sq_sqrt (sub_nonneg.mpr hsq), BoxSemialgebraicGenerator_eval]

/-- Squaring the selected second-coordinate product gives the evaluation of
the corresponding box generator product. -/
theorem signedCirclePoint_second_prod_sq (x : Fin n → ℝ)
    (eps : Fin n → Bool) (hx : ∀ i, |x i| ≤ 1)
    (J : Finset (Fin n)) :
    (∏ i ∈ J, signedCirclePoint x eps (i, true)) ^ 2 =
      MvPolynomial.eval x (BoxSemialgebraicGeneratorProd J) := by
  classical
  unfold BoxSemialgebraicGeneratorProd
  rw [map_prod, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  have hsq : x i ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one (x i)).2 (hx i)
  rw [signedCirclePoint_second, mul_pow, boolSign_sq, one_mul,
    Real.sq_sqrt (sub_nonneg.mpr hsq), BoxSemialgebraicGenerator_eval]

end QuarticConvergence
end OptimalConvergenceRates

end
