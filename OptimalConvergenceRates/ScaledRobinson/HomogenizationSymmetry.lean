/-
  OptimalConvergenceRates/ScaledRobinson/HomogenizationSymmetry.lean

  First-order finite-vector identities used by the signed/swap symmetrization in the
  necessity proof.
-/
import OptimalConvergenceRates.ScaledRobinson.HomogenizationRestrictions
import OptimalConvergenceRates.ScaledRobinson.HomogenizationSpectralIteration
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Logic.Equiv.Fin.Basic

open MvPolynomial Finset


noncomputable section

namespace OptimalConvergenceRates
namespace ScaledRobinson

/-- Restriction to the affine line `(x,y,z) = (a t, b t, 1)`. -/
def lineRestrict3To1 (a b : ℝ) : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] Polynomial ℝ :=
  MvPolynomial.aeval ![Polynomial.C a * Polynomial.X, Polynomial.C b * Polynomial.X, 1]

/-- The value at `t = 0` of any affine line restriction is the value at `(0,0,1)`. -/
theorem lineRestrict3To1_eval_zero (a b : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    (lineRestrict3To1 a b p).eval 0 = MvPolynomial.eval ![0, 0, 1] p := by
  have h : (Polynomial.aeval (0 : ℝ)).comp (lineRestrict3To1 a b) =
      (MvPolynomial.aeval ![(0 : ℝ), 0, 1] : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] ℝ) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [lineRestrict3To1]
  simpa [MvPolynomial.aeval_eq_eval] using AlgHom.congr_fun h p

/-- Restriction to the `y`-axis line `(0,t,1)`. -/
def yAxisRestrict3To1 : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] Polynomial ℝ :=
  lineRestrict3To1 0 1

/-- First derivative at zero along the axis line `(t,0,1)`. -/
def axisFirstDeriv (p : MvPolynomial (Fin 3) ℝ) : ℝ :=
  (Polynomial.derivative (axisRestrict3To1 p)).eval 0

/-- First derivative at zero along the `y`-axis line `(0,t,1)`. -/
def yAxisFirstDeriv (p : MvPolynomial (Fin 3) ℝ) : ℝ :=
  (Polynomial.derivative (yAxisRestrict3To1 p)).eval 0

/-- The existing axis restriction is the generic line restriction with direction `(1,0)`. -/
theorem lineRestrict3To1_one_zero : lineRestrict3To1 1 0 = axisRestrict3To1 := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [lineRestrict3To1, axisRestrict3To1]

/-- The diagonal restriction is the generic line restriction with direction
`(1 / sqrt 2, 1 / sqrt 2)`. -/
theorem lineRestrict3To1_diagonal :
    lineRestrict3To1 (Real.sqrt 2)⁻¹ (Real.sqrt 2)⁻¹ = diagonalRestrict3To1 := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [lineRestrict3To1, diagonalRestrict3To1]

/-- Chain rule at zero for affine line restrictions through `(0,0,1)`. -/
theorem lineRestrict3To1_derivative_eval_zero (a b : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    (Polynomial.derivative (lineRestrict3To1 a b p)).eval 0 =
      a * MvPolynomial.eval ![0, 0, 1] (MvPolynomial.pderiv 0 p) +
        b * MvPolynomial.eval ![0, 0, 1] (MvPolynomial.pderiv 1 p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [lineRestrict3To1]
  | add p q hp hq =>
      simp [map_add, hp, hq]
      ring
  | mul_X p j hp =>
      fin_cases j
      · suffices (lineRestrict3To1 a b p).eval 0 * a =
            a * MvPolynomial.eval ![0, 0, 1] p by
          simpa [lineRestrict3To1, Polynomial.derivative_mul, Polynomial.derivative_C,
            Polynomial.derivative_X] using this
        rw [lineRestrict3To1_eval_zero]
        ring
      · suffices (lineRestrict3To1 a b p).eval 0 * b =
            b * MvPolynomial.eval ![0, 0, 1] p by
          simpa [lineRestrict3To1, Polynomial.derivative_mul, Polynomial.derivative_C,
            Polynomial.derivative_X] using this
        rw [lineRestrict3To1_eval_zero]
        ring
      · simpa [lineRestrict3To1, MvPolynomial.pderiv_mul, Polynomial.derivative_mul,
          Polynomial.derivative_C, Polynomial.derivative_X] using hp

/-- Axis first derivative as the `x` partial derivative at `(0,0,1)`. -/
theorem axisFirstDeriv_eq_pderiv_zero (p : MvPolynomial (Fin 3) ℝ) :
    axisFirstDeriv p = MvPolynomial.eval ![0, 0, 1] (MvPolynomial.pderiv 0 p) := by
  unfold axisFirstDeriv
  rw [← lineRestrict3To1_one_zero]
  rw [lineRestrict3To1_derivative_eval_zero]
  simp

/-- `y`-axis first derivative as the `y` partial derivative at `(0,0,1)`. -/
theorem yAxisFirstDeriv_eq_pderiv_one (p : MvPolynomial (Fin 3) ℝ) :
    yAxisFirstDeriv p = MvPolynomial.eval ![0, 0, 1] (MvPolynomial.pderiv 1 p) := by
  unfold yAxisFirstDeriv yAxisRestrict3To1
  rw [lineRestrict3To1_derivative_eval_zero]
  simp

/-- Diagonal first derivative is the normalized sum of the two coordinate derivatives. -/
theorem diagonalFirstDeriv_eq_axis_yAxis (p : MvPolynomial (Fin 3) ℝ) :
    (Polynomial.derivative (diagonalRestrict3To1 p)).eval 0 =
      (axisFirstDeriv p + yAxisFirstDeriv p) / Real.sqrt 2 := by
  rw [← lineRestrict3To1_diagonal]
  rw [lineRestrict3To1_derivative_eval_zero, axisFirstDeriv_eq_pderiv_zero,
    yAxisFirstDeriv_eq_pderiv_one]
  ring

/-- Reflection `x ↦ -x` on ternary forms. -/
def xReflect3 : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.aeval ![-(X 0 : MvPolynomial (Fin 3) ℝ), X 1, X 2]

/-- Reflection `y ↦ -y` on ternary forms. -/
def yReflect3 : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.aeval ![(X 0 : MvPolynomial (Fin 3) ℝ), -X 1, X 2]

/-- Swap of the two Robinson variables `x` and `y` on ternary forms. -/
def xySwap3 : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.aeval ![(X 1 : MvPolynomial (Fin 3) ℝ), X 0, X 2]

@[simp]
theorem xReflect3_C (a : ℝ) :
    xReflect3 (MvPolynomial.C a : MvPolynomial (Fin 3) ℝ) = MvPolynomial.C a := by
  simp [xReflect3]

@[simp]
theorem yReflect3_C (a : ℝ) :
    yReflect3 (MvPolynomial.C a : MvPolynomial (Fin 3) ℝ) = MvPolynomial.C a := by
  simp [yReflect3]

@[simp]
theorem xySwap3_C (a : ℝ) :
    xySwap3 (MvPolynomial.C a : MvPolynomial (Fin 3) ℝ) = MvPolynomial.C a := by
  simp [xySwap3]

@[simp]
theorem xReflect3_X_zero : xReflect3 (X 0 : MvPolynomial (Fin 3) ℝ) = -X 0 := by
  simp [xReflect3]

@[simp]
theorem xReflect3_X_one : xReflect3 (X 1 : MvPolynomial (Fin 3) ℝ) = X 1 := by
  simp [xReflect3]

@[simp]
theorem xReflect3_X_two : xReflect3 (X 2 : MvPolynomial (Fin 3) ℝ) = X 2 := by
  simp [xReflect3]

@[simp]
theorem yReflect3_X_zero : yReflect3 (X 0 : MvPolynomial (Fin 3) ℝ) = X 0 := by
  simp [yReflect3]

@[simp]
theorem yReflect3_X_one : yReflect3 (X 1 : MvPolynomial (Fin 3) ℝ) = -X 1 := by
  simp [yReflect3]

@[simp]
theorem yReflect3_X_two : yReflect3 (X 2 : MvPolynomial (Fin 3) ℝ) = X 2 := by
  simp [yReflect3]

@[simp]
theorem xySwap3_X_zero : xySwap3 (X 0 : MvPolynomial (Fin 3) ℝ) = X 1 := by
  simp [xySwap3]

@[simp]
theorem xySwap3_X_one : xySwap3 (X 1 : MvPolynomial (Fin 3) ℝ) = X 0 := by
  simp [xySwap3]

@[simp]
theorem xySwap3_X_two : xySwap3 (X 2 : MvPolynomial (Fin 3) ℝ) = X 2 := by
  simp [xySwap3]

/-- Restricting after `x ↦ -x` is restriction in the reflected direction. -/
theorem lineRestrict3To1_xReflect3 (a b : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    lineRestrict3To1 a b (xReflect3 p) = lineRestrict3To1 (-a) b p := by
  have h : (lineRestrict3To1 a b).comp xReflect3 = lineRestrict3To1 (-a) b := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [lineRestrict3To1, xReflect3]
  exact AlgHom.congr_fun h p

/-- Restricting after `y ↦ -y` is restriction in the reflected direction. -/
theorem lineRestrict3To1_yReflect3 (a b : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    lineRestrict3To1 a b (yReflect3 p) = lineRestrict3To1 a (-b) p := by
  have h : (lineRestrict3To1 a b).comp yReflect3 = lineRestrict3To1 a (-b) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [lineRestrict3To1, yReflect3]
  exact AlgHom.congr_fun h p

/-- Restricting after swapping `x,y` swaps the line direction. -/
theorem lineRestrict3To1_xySwap3 (a b : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    lineRestrict3To1 a b (xySwap3 p) = lineRestrict3To1 b a p := by
  have h : (lineRestrict3To1 a b).comp xySwap3 = lineRestrict3To1 b a := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [lineRestrict3To1, xySwap3]
  exact AlgHom.congr_fun h p

/-- First derivative of a line restriction in terms of the named axis derivatives. -/
theorem lineRestrict3To1_derivative_eval_zero_axis_yAxis
    (a b : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    (Polynomial.derivative (lineRestrict3To1 a b p)).eval 0 =
      a * axisFirstDeriv p + b * yAxisFirstDeriv p := by
  rw [lineRestrict3To1_derivative_eval_zero, axisFirstDeriv_eq_pderiv_zero,
    yAxisFirstDeriv_eq_pderiv_one]

/-- Axis first derivative of a scalar multiple. -/
theorem axisFirstDeriv_C_mul (c : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    axisFirstDeriv (MvPolynomial.C c * p) = c * axisFirstDeriv p := by
  unfold axisFirstDeriv
  simp [Polynomial.derivative_mul]

/-- Axis derivative after reflecting `x`. -/
theorem axisFirstDeriv_xReflect3 (p : MvPolynomial (Fin 3) ℝ) :
    axisFirstDeriv (xReflect3 p) = -axisFirstDeriv p := by
  change (Polynomial.derivative (axisRestrict3To1 (xReflect3 p))).eval 0 = -axisFirstDeriv p
  rw [← lineRestrict3To1_one_zero, lineRestrict3To1_xReflect3]
  rw [lineRestrict3To1_derivative_eval_zero_axis_yAxis]
  ring

/-- Axis derivative after reflecting `y`. -/
theorem axisFirstDeriv_yReflect3 (p : MvPolynomial (Fin 3) ℝ) :
    axisFirstDeriv (yReflect3 p) = axisFirstDeriv p := by
  change (Polynomial.derivative (axisRestrict3To1 (yReflect3 p))).eval 0 = axisFirstDeriv p
  rw [← lineRestrict3To1_one_zero, lineRestrict3To1_yReflect3]
  rw [lineRestrict3To1_derivative_eval_zero_axis_yAxis]
  ring

/-- Axis derivative after swapping `x` and `y`. -/
theorem axisFirstDeriv_xySwap3 (p : MvPolynomial (Fin 3) ℝ) :
    axisFirstDeriv (xySwap3 p) = yAxisFirstDeriv p := by
  change (Polynomial.derivative (axisRestrict3To1 (xySwap3 p))).eval 0 = yAxisFirstDeriv p
  rw [← lineRestrict3To1_one_zero, lineRestrict3To1_xySwap3]
  rw [lineRestrict3To1_derivative_eval_zero_axis_yAxis]
  ring

/-- `y`-axis derivative after reflecting `x`. -/
theorem yAxisFirstDeriv_xReflect3 (p : MvPolynomial (Fin 3) ℝ) :
    yAxisFirstDeriv (xReflect3 p) = yAxisFirstDeriv p := by
  change (Polynomial.derivative (yAxisRestrict3To1 (xReflect3 p))).eval 0 = yAxisFirstDeriv p
  rw [yAxisRestrict3To1, lineRestrict3To1_xReflect3]
  rw [lineRestrict3To1_derivative_eval_zero_axis_yAxis]
  ring

/-- `y`-axis derivative after reflecting `y`. -/
theorem yAxisFirstDeriv_yReflect3 (p : MvPolynomial (Fin 3) ℝ) :
    yAxisFirstDeriv (yReflect3 p) = -yAxisFirstDeriv p := by
  change (Polynomial.derivative (yAxisRestrict3To1 (yReflect3 p))).eval 0 = -yAxisFirstDeriv p
  rw [yAxisRestrict3To1, lineRestrict3To1_yReflect3]
  rw [lineRestrict3To1_derivative_eval_zero_axis_yAxis]
  ring

/-- `y`-axis derivative after swapping `x` and `y`. -/
theorem yAxisFirstDeriv_xySwap3 (p : MvPolynomial (Fin 3) ℝ) :
    yAxisFirstDeriv (xySwap3 p) = axisFirstDeriv p := by
  change (Polynomial.derivative (yAxisRestrict3To1 (xySwap3 p))).eval 0 = axisFirstDeriv p
  rw [yAxisRestrict3To1, lineRestrict3To1_xySwap3]
  rw [lineRestrict3To1_derivative_eval_zero_axis_yAxis]
  ring

/-- Raw axis derivative notation folds to `axisFirstDeriv`. -/
theorem axisRestrict3To1_derivative_eval_zero_eq_axisFirstDeriv
    (p : MvPolynomial (Fin 3) ℝ) :
    (Polynomial.derivative (axisRestrict3To1 p)).eval 0 = axisFirstDeriv p := rfl

/-- Raw axis derivative after reflecting `x`. -/
theorem axisRestrict3To1_derivative_xReflect3 (p : MvPolynomial (Fin 3) ℝ) :
    (Polynomial.derivative (axisRestrict3To1 (xReflect3 p))).eval 0 = -axisFirstDeriv p := by
  simpa [axisFirstDeriv] using axisFirstDeriv_xReflect3 p

/-- Raw axis derivative after reflecting `y`. -/
theorem axisRestrict3To1_derivative_yReflect3 (p : MvPolynomial (Fin 3) ℝ) :
    (Polynomial.derivative (axisRestrict3To1 (yReflect3 p))).eval 0 = axisFirstDeriv p := by
  simpa [axisFirstDeriv] using axisFirstDeriv_yReflect3 p

/-- Raw axis derivative after swapping `x` and `y`. -/
theorem axisRestrict3To1_derivative_xySwap3 (p : MvPolynomial (Fin 3) ℝ) :
    (Polynomial.derivative (axisRestrict3To1 (xySwap3 p))).eval 0 = yAxisFirstDeriv p := by
  simpa [axisFirstDeriv] using axisFirstDeriv_xySwap3 p

/-- Diagonal first derivative of a scalar multiple. -/
theorem diagonalFirstDeriv_C_mul (c : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    (Polynomial.derivative (diagonalRestrict3To1 (MvPolynomial.C c * p))).eval 0 =
      c * (Polynomial.derivative (diagonalRestrict3To1 p)).eval 0 := by
  simp [Polynomial.derivative_mul]

/-- Diagonal derivative after reflecting `x`. -/
theorem diagonalFirstDeriv_xReflect3 (p : MvPolynomial (Fin 3) ℝ) :
    (Polynomial.derivative (diagonalRestrict3To1 (xReflect3 p))).eval 0 =
      (-axisFirstDeriv p + yAxisFirstDeriv p) / Real.sqrt 2 := by
  rw [← lineRestrict3To1_diagonal, lineRestrict3To1_xReflect3]
  rw [lineRestrict3To1_derivative_eval_zero_axis_yAxis]
  ring

/-- Diagonal derivative after reflecting `y`. -/
theorem diagonalFirstDeriv_yReflect3 (p : MvPolynomial (Fin 3) ℝ) :
    (Polynomial.derivative (diagonalRestrict3To1 (yReflect3 p))).eval 0 =
      (axisFirstDeriv p - yAxisFirstDeriv p) / Real.sqrt 2 := by
  rw [← lineRestrict3To1_diagonal, lineRestrict3To1_yReflect3]
  rw [lineRestrict3To1_derivative_eval_zero_axis_yAxis]
  ring

/-- Diagonal derivative after swapping `x` and `y`. -/
theorem diagonalFirstDeriv_xySwap3 (p : MvPolynomial (Fin 3) ℝ) :
    (Polynomial.derivative (diagonalRestrict3To1 (xySwap3 p))).eval 0 =
      (yAxisFirstDeriv p + axisFirstDeriv p) / Real.sqrt 2 := by
  rw [← lineRestrict3To1_diagonal, lineRestrict3To1_xySwap3]
  rw [lineRestrict3To1_derivative_eval_zero_axis_yAxis]
  ring

/-- The threshold form is invariant under `x ↦ -x`. -/
theorem xReflect3_Pmlambda (m : ℕ) (lambda : ℝ) :
    xReflect3 (Pmlambda m lambda) = Pmlambda m lambda := by
  unfold Pmlambda Phi sphereSq
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, xReflect3_C,
    xReflect3_X_zero, xReflect3_X_one, xReflect3_X_two]
  ring_nf

/-- The threshold form is invariant under `y ↦ -y`. -/
theorem yReflect3_Pmlambda (m : ℕ) (lambda : ℝ) :
    yReflect3 (Pmlambda m lambda) = Pmlambda m lambda := by
  unfold Pmlambda Phi sphereSq
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, yReflect3_C,
    yReflect3_X_zero, yReflect3_X_one, yReflect3_X_two]
  ring_nf

/-- The threshold form is invariant under swapping `x` and `y`. -/
theorem xySwap3_Pmlambda (m : ℕ) (lambda : ℝ) :
    xySwap3 (Pmlambda m lambda) = Pmlambda m lambda := by
  unfold Pmlambda Phi sphereSq
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, xySwap3_C,
    xySwap3_X_zero, xySwap3_X_one, xySwap3_X_two]
  ring_nf

/-- The eight polynomial transforms generated by sign changes in `x,y` and the swap
`x ↔ y`, ordered to match the first-derivative vectors below. -/
def signedSwapOrbit (j : Fin 8) (p : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  match j with
  | 0 => p
  | 1 => xReflect3 p
  | 2 => yReflect3 p
  | 3 => xReflect3 (yReflect3 p)
  | 4 => xySwap3 p
  | 5 => xReflect3 (xySwap3 p)
  | 6 => yReflect3 (xySwap3 p)
  | 7 => xReflect3 (yReflect3 (xySwap3 p))

/-- Every signed/swap orbit transform fixes `P_{m,lambda}`. -/
theorem signedSwapOrbit_Pmlambda (j : Fin 8) (m : ℕ) (lambda : ℝ) :
    signedSwapOrbit j (Pmlambda m lambda) = Pmlambda m lambda := by
  fin_cases j <;> simp [signedSwapOrbit, xReflect3_Pmlambda, yReflect3_Pmlambda,
    xySwap3_Pmlambda]

/-- Orbit transforms preserve a concrete sum-of-squares witness. -/
theorem signedSwapOrbit_sum_sq {N : ℕ} (j : Fin 8)
    (H : Fin N → MvPolynomial (Fin 3) ℝ) :
    signedSwapOrbit j (∑ i : Fin N, (H i) ^ 2) =
      ∑ i : Fin N, (signedSwapOrbit j (H i)) ^ 2 := by
  fin_cases j <;> simp [signedSwapOrbit, map_sum, map_pow]

/-- Applying any orbit transform to the square roots of a `P_{m,lambda}` SOS witness
gives another witness for the same form. -/
theorem signedSwapOrbit_witness_Pmlambda {m N : ℕ} {lambda : ℝ}
    {H : Fin N → MvPolynomial (Fin 3) ℝ}
    (hH : Pmlambda m lambda = ∑ i : Fin N, (H i) ^ 2) (j : Fin 8) :
    Pmlambda m lambda = ∑ i : Fin N, (signedSwapOrbit j (H i)) ^ 2 := by
  calc
    Pmlambda m lambda = signedSwapOrbit j (Pmlambda m lambda) :=
      (signedSwapOrbit_Pmlambda j m lambda).symm
    _ = signedSwapOrbit j (∑ i : Fin N, (H i) ^ 2) := by rw [hH]
    _ = ∑ i : Fin N, (signedSwapOrbit j (H i)) ^ 2 :=
      signedSwapOrbit_sum_sq j H

/-- The normalization constant used for averaging over the eight signed/swap transforms. -/
def signedSwapAverageConst : ℝ :=
  (Real.sqrt 8)⁻¹

/-- The signed/swap orbit witness, scaled by `1 / sqrt 8`. -/
def signedSwapAverageWitness {N : ℕ} (H : Fin N → MvPolynomial (Fin 3) ℝ) :
    Fin 8 → Fin N → MvPolynomial (Fin 3) ℝ :=
  fun j i => MvPolynomial.C signedSwapAverageConst * signedSwapOrbit j (H i)

/-- The square of the signed/swap averaging constant is `1/8`, as a polynomial scalar. -/
theorem signedSwapAverageConst_sq_C :
    (MvPolynomial.C signedSwapAverageConst : MvPolynomial (Fin 3) ℝ) ^ 2 =
      MvPolynomial.C ((8 : ℝ)⁻¹) := by
  unfold signedSwapAverageConst
  rw [← MvPolynomial.C_pow]
  congr 1
  have hsqrt8_sq : (Real.sqrt 8) ^ 2 = (8 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  rw [inv_pow, hsqrt8_sq]

/-- Averaging all eight signed/swap transforms of a concrete SOS witness for `Pmlambda`
gives another concrete SOS witness for `Pmlambda`, indexed first by the transform and
then by the original square root. -/
theorem signedSwapAverageWitness_Pmlambda_iterated {m N : ℕ} {lambda : ℝ}
    {H : Fin N → MvPolynomial (Fin 3) ℝ}
    (hH : Pmlambda m lambda = ∑ i : Fin N, (H i) ^ 2) :
    Pmlambda m lambda =
      ∑ j : Fin 8, ∑ i : Fin N, (signedSwapAverageWitness H j i) ^ 2 := by
  have hinner : ∀ j : Fin 8,
      (∑ i : Fin N, (signedSwapAverageWitness H j i) ^ 2) =
        MvPolynomial.C ((8 : ℝ)⁻¹) * Pmlambda m lambda := by
    intro j
    unfold signedSwapAverageWitness
    simp_rw [mul_pow]
    rw [← Finset.mul_sum, signedSwapAverageConst_sq_C]
    rw [← signedSwapOrbit_witness_Pmlambda hH j]
  have hsumConst :
      (∑ j : Fin 8, MvPolynomial.C ((8 : ℝ)⁻¹) * Pmlambda m lambda) =
        Pmlambda m lambda := by
    rw [show (∑ j : Fin 8, MvPolynomial.C ((8 : ℝ)⁻¹) * Pmlambda m lambda) =
        (8 : MvPolynomial (Fin 3) ℝ) *
          (MvPolynomial.C ((8 : ℝ)⁻¹) * Pmlambda m lambda) by simp]
    rw [show (8 : MvPolynomial (Fin 3) ℝ) = MvPolynomial.C (8 : ℝ) from
      (MvPolynomial.C_eq_coe_nat 8).symm]
    rw [← mul_assoc, ← MvPolynomial.C_mul]
    norm_num
  calc
    Pmlambda m lambda = MvPolynomial.C (1 : ℝ) * Pmlambda m lambda := by simp
    _ = (∑ j : Fin 8, MvPolynomial.C ((8 : ℝ)⁻¹) * Pmlambda m lambda) := by
        rw [hsumConst]
        simp
    _ = ∑ j : Fin 8, ∑ i : Fin N, (signedSwapAverageWitness H j i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact (hinner j).symm

/-- Axis first derivatives of a witness symmetrized by the sign changes in `x,y` and the
swap of `x` and `y`, with the common normalization factor `1 / sqrt 8`. -/
def axisSymmDeriv {N : ℕ} (A B : Fin N → ℝ) : Fin N × Fin 8 → ℝ :=
  fun ij =>
    let i := ij.1
    match ij.2 with
    | 0 => (Real.sqrt 8)⁻¹ * A i
    | 1 => -(Real.sqrt 8)⁻¹ * A i
    | 2 => (Real.sqrt 8)⁻¹ * A i
    | 3 => -(Real.sqrt 8)⁻¹ * A i
    | 4 => (Real.sqrt 8)⁻¹ * B i
    | 5 => -(Real.sqrt 8)⁻¹ * B i
    | 6 => (Real.sqrt 8)⁻¹ * B i
    | 7 => -(Real.sqrt 8)⁻¹ * B i

/-- Diagonal first derivatives of the same symmetrized witness. -/
def diagonalSymmDeriv {N : ℕ} (A B : Fin N → ℝ) : Fin N × Fin 8 → ℝ :=
  fun ij =>
    let i := ij.1
    match ij.2 with
    | 0 => (Real.sqrt 8)⁻¹ * ((A i + B i) / Real.sqrt 2)
    | 1 => (Real.sqrt 8)⁻¹ * ((-A i + B i) / Real.sqrt 2)
    | 2 => (Real.sqrt 8)⁻¹ * ((A i - B i) / Real.sqrt 2)
    | 3 => (Real.sqrt 8)⁻¹ * ((-A i - B i) / Real.sqrt 2)
    | 4 => (Real.sqrt 8)⁻¹ * ((B i + A i) / Real.sqrt 2)
    | 5 => (Real.sqrt 8)⁻¹ * ((-B i + A i) / Real.sqrt 2)
    | 6 => (Real.sqrt 8)⁻¹ * ((B i - A i) / Real.sqrt 2)
    | 7 => (Real.sqrt 8)⁻¹ * ((-B i - A i) / Real.sqrt 2)

/-- Axis first derivatives of all signed/swap averaged orbit witnesses. -/
theorem signedSwapAverageWitness_axis_derivative
    {N : ℕ} (H : Fin N → MvPolynomial (Fin 3) ℝ) :
    (fun ij : Fin N × Fin 8 =>
      (Polynomial.derivative (axisRestrict3To1 (signedSwapAverageWitness H ij.2 ij.1))).eval 0) =
      axisSymmDeriv (fun i => axisFirstDeriv (H i)) (fun i => yAxisFirstDeriv (H i)) := by
  funext ij
  rcases ij with ⟨i, j⟩
  fin_cases j <;>
    simp [signedSwapAverageWitness, signedSwapOrbit, axisSymmDeriv,
      axisRestrict3To1_derivative_eval_zero_eq_axisFirstDeriv,
      axisFirstDeriv_xReflect3, axisFirstDeriv_yReflect3,
      axisFirstDeriv_xySwap3, signedSwapAverageConst]

/-- Diagonal first derivatives of all signed/swap averaged orbit witnesses. -/
theorem signedSwapAverageWitness_diagonal_derivative
    {N : ℕ} (H : Fin N → MvPolynomial (Fin 3) ℝ) :
    (fun ij : Fin N × Fin 8 =>
      (Polynomial.derivative
        (diagonalRestrict3To1 (signedSwapAverageWitness H ij.2 ij.1))).eval 0) =
      diagonalSymmDeriv (fun i => axisFirstDeriv (H i)) (fun i => yAxisFirstDeriv (H i)) := by
  funext ij
  rcases ij with ⟨i, j⟩
  fin_cases j <;>
    simp [signedSwapAverageWitness, signedSwapOrbit, diagonalSymmDeriv,
      diagonalFirstDeriv_eq_axis_yAxis,
      axisFirstDeriv_xReflect3, axisFirstDeriv_yReflect3, axisFirstDeriv_xySwap3,
      yAxisFirstDeriv_xReflect3, yAxisFirstDeriv_yReflect3, yAxisFirstDeriv_xySwap3,
      signedSwapAverageConst]
  all_goals ring


/-- Squared norm for product-indexed finite real vectors. -/
def prodVecSqNorm {N M : ℕ} (v : Fin N × Fin M → ℝ) : ℝ :=
  ∑ i : Fin N × Fin M, v i ^ 2

/-- Product-indexed squared norm as an iterated sum. -/
theorem prodVecSqNorm_eq_sum_sum {N M : ℕ} (v : Fin N × Fin M → ℝ) :
    prodVecSqNorm v = ∑ i : Fin N, ∑ j : Fin M, v (i, j) ^ 2 := by
  unfold prodVecSqNorm
  conv_lhs => rw [← Finset.univ_product_univ]
  rw [Finset.sum_product]

/-- The eight axis-symmetrized first derivatives have squared norm
`(‖A‖^2 + ‖B‖^2) / 2`. -/
theorem prodVecSqNorm_axisSymmDeriv {N : ℕ} (A B : Fin N → ℝ) :
    prodVecSqNorm (axisSymmDeriv A B) = (vecSqNorm A + vecSqNorm B) / 2 := by
  rw [prodVecSqNorm_eq_sum_sum]
  unfold vecSqNorm
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _hi
  have hsqrt8_sq : (Real.sqrt 8) ^ 2 = (8 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have hsqrt8_inv_sq : (Real.sqrt 8)⁻¹ ^ 2 = (8 : ℝ)⁻¹ := by
    rw [inv_pow, hsqrt8_sq]
  simp [Fin.sum_univ_succ, axisSymmDeriv]
  ring_nf
  rw [hsqrt8_inv_sq]
  ring_nf

/-- The eight diagonal-symmetrized first derivatives have the same squared norm
`(‖A‖^2 + ‖B‖^2) / 2`. -/
theorem prodVecSqNorm_diagonalSymmDeriv {N : ℕ} (A B : Fin N → ℝ) :
    prodVecSqNorm (diagonalSymmDeriv A B) = (vecSqNorm A + vecSqNorm B) / 2 := by
  rw [prodVecSqNorm_eq_sum_sum]
  unfold vecSqNorm
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _hi
  have hsqrt8_sq : (Real.sqrt 8) ^ 2 = (8 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have hsqrt2_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have hsqrt8_inv_sq : (Real.sqrt 8)⁻¹ ^ 2 = (8 : ℝ)⁻¹ := by
    rw [inv_pow, hsqrt8_sq]
  have hsqrt2_inv_sq : (Real.sqrt 2)⁻¹ ^ 2 = (2 : ℝ)⁻¹ := by
    rw [inv_pow, hsqrt2_sq]
  simp [Fin.sum_univ_succ, diagonalSymmDeriv]
  ring_nf
  rw [hsqrt8_inv_sq, hsqrt2_inv_sq]
  ring_nf

/-- The explicit eightfold signed/swap derivative vectors have equal Euclidean norm. -/
theorem vecNorm_axisSymmDeriv_eq_diagonalSymmDeriv {N : ℕ} (A B : Fin N → ℝ) :
    Real.sqrt (prodVecSqNorm (axisSymmDeriv A B)) =
      Real.sqrt (prodVecSqNorm (diagonalSymmDeriv A B)) := by
  rw [prodVecSqNorm_axisSymmDeriv, prodVecSqNorm_diagonalSymmDeriv]

/-- Evaluating an iterated univariate SOS witness at a zero forces every iterated
square root to vanish at that zero. -/
theorem IsSOSUni.eval_zero_of_iterated_witness
    {M N : ℕ} {p : Polynomial ℝ} {Q : Fin M → Fin N → Polynomial ℝ}
    (hQ : p = ∑ j : Fin M, ∑ i : Fin N, (Q j i) ^ 2) {t : ℝ}
    (ht : p.eval t = 0) :
    ∀ j : Fin M, ∀ i : Fin N, (Q j i).eval t = 0 := by
  have hsum : (∑ j : Fin M, ∑ i : Fin N, (Q j i).eval t ^ 2) = 0 := by
    rw [hQ] at ht
    simpa only [Polynomial.eval_finsetSum, Polynomial.eval_pow] using ht
  have hprod : (∑ ji : Fin M × Fin N, (Q ji.1 ji.2).eval t ^ 2) = 0 := by
    rw [← hsum]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  intro j i
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun ji _hji => sq_nonneg ((Q ji.1 ji.2).eval t))).mp hprod (j, i)
    (Finset.mem_univ _)
  simpa using hzero

/-- Every square root in an iterated univariate SOS decomposition is divisible by the
linear root factor. -/
theorem IsSOSUni.each_iterated_witness_linear_dvd_at_root
    {M N : ℕ} {p : Polynomial ℝ} {Q : Fin M → Fin N → Polynomial ℝ}
    (hQ : p = ∑ j : Fin M, ∑ i : Fin N, (Q j i) ^ 2) {t : ℝ}
    (ht : p.eval t = 0) (j : Fin M) (i : Fin N) :
    Polynomial.X - Polynomial.C t ∣ Q j i :=
  Polynomial.X_sub_C_dvd_of_eval_eq_zero (Q j i)
    (IsSOSUni.eval_zero_of_iterated_witness hQ ht j i)

/-- Product-indexed derivative norm is unchanged by stripping the normalized quadratic
factor from every square root. -/
theorem normalizedQuadraticFactor_derivative_prodVecSqNorm_eq
    {N : ℕ} (a : ℝ) {Q F : Fin 8 → Fin N → Polynomial ℝ}
    (hQ : ∀ j : Fin 8, ∀ i : Fin N,
      Q j i = (Polynomial.C a * Polynomial.X ^ 2 - 1) * F j i) :
    prodVecSqNorm (fun ij : Fin N × Fin 8 =>
        (Polynomial.derivative (Q ij.2 ij.1)).eval 0) =
      prodVecSqNorm (fun ij : Fin N × Fin 8 =>
        (Polynomial.derivative (F ij.2 ij.1)).eval 0) := by
  unfold prodVecSqNorm
  apply Finset.sum_congr rfl
  intro ij _hij
  change (Polynomial.derivative (Q ij.2 ij.1)).eval 0 ^ 2 =
    (Polynomial.derivative (F ij.2 ij.1)).eval 0 ^ 2
  rw [hQ ij.2 ij.1]
  rw [normalizedQuadraticFactor_mul_derivative_eval_zero]
  ring

/-- Reindex a `Fin 8 × Fin N` sum as a single `Fin (N*8)` sum. -/
theorem sum_finProdFinEquiv_symm_swap {N : ℕ} {α : Type*} [AddCommMonoid α]
    (f : Fin 8 → Fin N → α) :
    (∑ ij : Fin (N * 8), f ((finProdFinEquiv.symm ij).2) ((finProdFinEquiv.symm ij).1)) =
      ∑ j : Fin 8, ∑ i : Fin N, f j i := by
  calc
    (∑ ij : Fin (N * 8), f ((finProdFinEquiv.symm ij).2) ((finProdFinEquiv.symm ij).1)) =
        ∑ ij : Fin N × Fin 8, f ij.2 ij.1 := by
          simpa using (Equiv.sum_comp (finProdFinEquiv (m := N) (n := 8))
            (fun ij : Fin (N * 8) =>
              f ((finProdFinEquiv.symm ij).2) ((finProdFinEquiv.symm ij).1))).symm
    _ = ∑ j : Fin 8, ∑ i : Fin N, f j i := by
          rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_comm]

/-- Reindexing a product-indexed squared norm along `finProdFinEquiv`. -/
theorem prodVecSqNorm_eq_vecSqNorm_finProd {N M : ℕ} (v : Fin N × Fin M → ℝ) :
    prodVecSqNorm v =
      vecSqNorm (fun k : Fin (N * M) => v ((finProdFinEquiv.symm) k)) := by
  unfold prodVecSqNorm vecSqNorm
  rw [← Equiv.sum_comp (finProdFinEquiv (m := N) (n := M))
    (fun k : Fin (N * M) => v ((finProdFinEquiv.symm) k) ^ 2)]
  simp

/-- Product-indexed `vecNorm`, reindexed through `finProdFinEquiv`. -/
theorem prodVecNorm_eq_vecNorm_finProd {N M : ℕ} (v : Fin N × Fin M → ℝ) :
    Real.sqrt (prodVecSqNorm v) =
      vecNorm (fun k : Fin (N * M) => v ((finProdFinEquiv.symm) k)) := by
  unfold vecNorm
  rw [prodVecSqNorm_eq_vecSqNorm_finProd]

/-- Product-indexed axis stripped norm identity, obtained by reindexing to `Fin (N*8)`. -/
theorem axisRestriction_stripped_norm_identity_prod
    {m N : ℕ} {lambda : ℝ} {F : Fin 8 → Fin N → Polynomial ℝ}
    (hF : axisRestrict3To1 (Pmlambda m lambda) =
      ∑ j : Fin 8, ∑ i : Fin N,
        ((Polynomial.C (lambda - 1) * Polynomial.X ^ 2 - 1) * F j i) ^ 2) :
    ∑ ij : Fin (N * 8), (F ((finProdFinEquiv.symm ij).2) ((finProdFinEquiv.symm ij).1)) ^ 2 =
      (1 + Polynomial.X ^ 2) ^ m * (1 + Polynomial.C (lambda + 1) * Polynomial.X ^ 2) := by
  let G : Fin (N * 8) → Polynomial ℝ :=
    fun ij => F ((finProdFinEquiv.symm ij).2) ((finProdFinEquiv.symm ij).1)
  have hsum :
      ∑ i : Fin (N * 8), (G i) ^ 2 = ∑ j : Fin 8, ∑ i : Fin N, (F j i) ^ 2 := by
    dsimp [G]
    exact sum_finProdFinEquiv_symm_swap (fun j i => (F j i) ^ 2)
  apply axisRestriction_stripped_norm_identity
  rw [hF]
  exact (sum_finProdFinEquiv_symm_swap
    (fun j i => ((Polynomial.C (lambda - 1) * Polynomial.X ^ 2 - 1) * F j i) ^ 2)).symm

/-- Product-indexed diagonal stripped norm identity, obtained by reindexing to `Fin (N*8)`. -/
theorem diagonalRestriction_stripped_norm_identity_prod
    {m N : ℕ} {lambda : ℝ} {F : Fin 8 → Fin N → Polynomial ℝ}
    (hF : diagonalRestrict3To1 (Pmlambda m lambda) =
      ∑ j : Fin 8, ∑ i : Fin N,
        ((Polynomial.C ((lambda - 2) / 2) * Polynomial.X ^ 2 - 1) * F j i) ^ 2) :
    ∑ ij : Fin (N * 8), (F ((finProdFinEquiv.symm ij).2) ((finProdFinEquiv.symm ij).1)) ^ 2 =
      (1 + Polynomial.X ^ 2) ^ (m + 1) := by
  let G : Fin (N * 8) → Polynomial ℝ :=
    fun ij => F ((finProdFinEquiv.symm ij).2) ((finProdFinEquiv.symm ij).1)
  have hsum :
      ∑ i : Fin (N * 8), (G i) ^ 2 = ∑ j : Fin 8, ∑ i : Fin N, (F j i) ^ 2 := by
    dsimp [G]
    exact sum_finProdFinEquiv_symm_swap (fun j i => (F j i) ^ 2)
  apply diagonalRestriction_stripped_norm_identity
  rw [hF]
  exact (sum_finProdFinEquiv_symm_swap
    (fun j i =>
      ((Polynomial.C ((lambda - 2) / 2) * Polynomial.X ^ 2 - 1) * F j i) ^ 2)).symm

/-- Product-indexed axis stripped derivative lower bound. -/
theorem axisRestriction_stripped_derivative_norm_ge_prod
    {m N : ℕ} {lambda : ℝ} (hLam : 0 < lambda + 1)
    {F : Fin 8 → Fin N → Polynomial ℝ}
    (hNorm :
      ∑ ij : Fin (N * 8),
          (F ((finProdFinEquiv.symm ij).2) ((finProdFinEquiv.symm ij).1)) ^ 2 =
        (1 + Polynomial.X ^ 2) ^ m * (1 + Polynomial.C (lambda + 1) * Polynomial.X ^ 2)) :
    Real.sqrt (lambda + 1) - (m : ℝ) ≤
      Real.sqrt (prodVecSqNorm (fun ij : Fin N × Fin 8 =>
        (Polynomial.derivative (F ij.2 ij.1)).eval 0)) := by
  let G : Fin (N * 8) → Polynomial ℝ :=
    fun ij => F ((finProdFinEquiv.symm ij).2) ((finProdFinEquiv.symm ij).1)
  have hge := axisRestriction_stripped_derivative_norm_ge hLam (F := G) hNorm
  rw [prodVecNorm_eq_vecNorm_finProd]
  simpa [G] using hge

/-- Product-indexed diagonal stripped derivative upper bound. -/
theorem diagonalRestriction_stripped_derivative_norm_le_prod
    {m N : ℕ} {F : Fin 8 → Fin N → Polynomial ℝ}
    (hNorm :
      ∑ ij : Fin (N * 8),
          (F ((finProdFinEquiv.symm ij).2) ((finProdFinEquiv.symm ij).1)) ^ 2 =
        ((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ (m + 1)) :
    Real.sqrt (prodVecSqNorm (fun ij : Fin N × Fin 8 =>
        (Polynomial.derivative (F ij.2 ij.1)).eval 0)) ≤
      (m : ℝ) + 1 := by
  let G : Fin (N * 8) → Polynomial ℝ :=
    fun ij => F ((finProdFinEquiv.symm ij).2) ((finProdFinEquiv.symm ij).1)
  have hle := diagonalRestriction_stripped_derivative_norm_le (F := G) hNorm
  rw [prodVecNorm_eq_vecNorm_finProd]
  simpa [G] using hle

/-- Axis and diagonal first-derivative squared norms agree for the signed/swap averaged
witness before stripping. -/
theorem signedSwapAverageWitness_axis_diagonal_derivative_prodVecSqNorm_eq
    {N : ℕ} (H : Fin N → MvPolynomial (Fin 3) ℝ) :
    prodVecSqNorm (fun ij : Fin N × Fin 8 =>
        (Polynomial.derivative
          (axisRestrict3To1 (signedSwapAverageWitness H ij.2 ij.1))).eval 0) =
      prodVecSqNorm (fun ij : Fin N × Fin 8 =>
        (Polynomial.derivative
          (diagonalRestrict3To1 (signedSwapAverageWitness H ij.2 ij.1))).eval 0) := by
  rw [signedSwapAverageWitness_axis_derivative, signedSwapAverageWitness_diagonal_derivative]
  rw [prodVecSqNorm_axisSymmDeriv, prodVecSqNorm_diagonalSymmDeriv]

/-- After stripping the normalized axis and diagonal quadratic factors from the
signed/swap averaged witness, the product-indexed first-derivative squared norms agree. -/
theorem signedSwapAverageWitness_axis_diagonal_stripped_derivative_prodVecSqNorm_eq
    {N : ℕ} {lambda : ℝ} {H : Fin N → MvPolynomial (Fin 3) ℝ}
    {Faxis Fdiag : Fin 8 → Fin N → Polynomial ℝ}
    (hAxis : ∀ j : Fin 8, ∀ i : Fin N,
      axisRestrict3To1 (signedSwapAverageWitness H j i) =
        (Polynomial.C (lambda - 1) * Polynomial.X ^ 2 - 1) * Faxis j i)
    (hDiag : ∀ j : Fin 8, ∀ i : Fin N,
      diagonalRestrict3To1 (signedSwapAverageWitness H j i) =
        (Polynomial.C ((lambda - 2) / 2) * Polynomial.X ^ 2 - 1) * Fdiag j i) :
    prodVecSqNorm (fun ij : Fin N × Fin 8 =>
        (Polynomial.derivative (Faxis ij.2 ij.1)).eval 0) =
      prodVecSqNorm (fun ij : Fin N × Fin 8 =>
        (Polynomial.derivative (Fdiag ij.2 ij.1)).eval 0) := by
  have hAxisStrip :=
    normalizedQuadraticFactor_derivative_prodVecSqNorm_eq (a := lambda - 1)
      (Q := fun j i => axisRestrict3To1 (signedSwapAverageWitness H j i))
      (F := Faxis) hAxis
  have hDiagStrip :=
    normalizedQuadraticFactor_derivative_prodVecSqNorm_eq (a := (lambda - 2) / 2)
      (Q := fun j i => diagonalRestrict3To1 (signedSwapAverageWitness H j i))
      (F := Fdiag) hDiag
  have hRaw := signedSwapAverageWitness_axis_diagonal_derivative_prodVecSqNorm_eq H
  rw [← hAxisStrip, ← hDiagStrip]
  exact hRaw

/-- The signed/swap averaged SOS witness can be stripped simultaneously on the axis and
diagonal restrictions, preserving pointwise equations for the stripped factors. -/
theorem IsSOS.exists_signedSwap_axis_diagonalRestriction_normalized_factorization
    {m : ℕ} {lambda : ℝ} (hLam : 2 < lambda) (hSOS : IsSOS (Pmlambda m lambda)) :
    ∃ N : ℕ, ∃ H : Fin N → MvPolynomial (Fin 3) ℝ,
      ∃ Faxis Fdiag : Fin 8 → Fin N → Polynomial ℝ,
        Pmlambda m lambda = ∑ i : Fin N, (H i) ^ 2 ∧
        axisRestrict3To1 (Pmlambda m lambda) =
          ∑ j : Fin 8, ∑ i : Fin N,
            ((Polynomial.C (lambda - 1) * Polynomial.X ^ 2 - 1) * Faxis j i) ^ 2 ∧
        diagonalRestrict3To1 (Pmlambda m lambda) =
          ∑ j : Fin 8, ∑ i : Fin N,
            ((Polynomial.C ((lambda - 2) / 2) * Polynomial.X ^ 2 - 1) * Fdiag j i) ^ 2 ∧
        (∀ j : Fin 8, ∀ i : Fin N,
          axisRestrict3To1 (signedSwapAverageWitness H j i) =
            (Polynomial.C (lambda - 1) * Polynomial.X ^ 2 - 1) * Faxis j i) ∧
        ∀ j : Fin 8, ∀ i : Fin N,
          diagonalRestrict3To1 (signedSwapAverageWitness H j i) =
            (Polynomial.C ((lambda - 2) / 2) * Polynomial.X ^ 2 - 1) * Fdiag j i := by
  have hgt1 : 1 < lambda := by linarith
  obtain ⟨N, H, hH⟩ := hSOS
  let W : Fin 8 → Fin N → MvPolynomial (Fin 3) ℝ := signedSwapAverageWitness H
  have hW : Pmlambda m lambda = ∑ j : Fin 8, ∑ i : Fin N, (W j i) ^ 2 := by
    exact signedSwapAverageWitness_Pmlambda_iterated hH
  have hAxis : axisRestrict3To1 (Pmlambda m lambda) =
      ∑ j : Fin 8, ∑ i : Fin N, (axisRestrict3To1 (W j i)) ^ 2 := by
    rw [hW]
    simp only [map_sum, map_pow]
  have hDiag : diagonalRestrict3To1 (Pmlambda m lambda) =
      ∑ j : Fin 8, ∑ i : Fin N, (diagonalRestrict3To1 (W j i)) ^ 2 := by
    rw [hW]
    simp only [map_sum, map_pow]
  have hAxisDiv : ∀ j : Fin 8, ∀ i : Fin N,
      Polynomial.C (lambda - 1) * Polynomial.X ^ 2 - 1 ∣ axisRestrict3To1 (W j i) := by
    intro j i
    have hquad : Polynomial.X ^ 2 - Polynomial.C (axisRoot lambda ^ 2) ∣
        axisRestrict3To1 (W j i) := by
      apply Polynomial.X_sq_sub_C_sq_dvd_of_pos_neg_linear_dvd
      · unfold axisRoot
        exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by linarith)))
      · exact IsSOSUni.each_iterated_witness_linear_dvd_at_root hAxis
          (axisRestrict3To1_Pmlambda_eval_axisRoot_eq_zero m hgt1) j i
      · exact IsSOSUni.each_iterated_witness_linear_dvd_at_root hAxis
          (axisRestrict3To1_Pmlambda_eval_neg_axisRoot_eq_zero m hgt1) j i
    have hscaled := Polynomial.C_mul_dvd_of_dvd (by linarith : lambda - 1 ≠ 0) hquad
    rwa [axisRoot_quadratic_factor_eq hgt1] at hscaled
  have hDiagDiv : ∀ j : Fin 8, ∀ i : Fin N,
      Polynomial.C ((lambda - 2) / 2) * Polynomial.X ^ 2 - 1 ∣
        diagonalRestrict3To1 (W j i) := by
    intro j i
    have hquad : Polynomial.X ^ 2 - Polynomial.C (diagonalRoot lambda ^ 2) ∣
        diagonalRestrict3To1 (W j i) := by
      apply Polynomial.X_sq_sub_C_sq_dvd_of_pos_neg_linear_dvd
      · unfold diagonalRoot
        have hden_pos : 0 < lambda - 2 := by linarith
        have hrad_pos : 0 < 2 / (lambda - 2) := by positivity
        exact ne_of_gt (Real.sqrt_pos.2 hrad_pos)
      · exact IsSOSUni.each_iterated_witness_linear_dvd_at_root hDiag
          (diagonalRestrict3To1_Pmlambda_eval_diagonalRoot_eq_zero m hLam) j i
      · exact IsSOSUni.each_iterated_witness_linear_dvd_at_root hDiag
          (diagonalRestrict3To1_Pmlambda_eval_neg_diagonalRoot_eq_zero m hLam) j i
    have hcoef_ne : (lambda - 2) / 2 ≠ 0 := by
      exact div_ne_zero (by linarith) (by norm_num)
    have hscaled := Polynomial.C_mul_dvd_of_dvd hcoef_ne hquad
    rwa [diagonalRoot_quadratic_factor_eq hLam] at hscaled
  let Faxis : Fin 8 → Fin N → Polynomial ℝ := fun j i => (hAxisDiv j i).choose
  let Fdiag : Fin 8 → Fin N → Polynomial ℝ := fun j i => (hDiagDiv j i).choose
  refine ⟨N, H, Faxis, Fdiag, hH, ?_, ?_, ?_, ?_⟩
  · rw [hAxis]
    apply Finset.sum_congr rfl
    intro j _hj
    apply Finset.sum_congr rfl
    intro i _hi
    rw [(hAxisDiv j i).choose_spec]
  · rw [hDiag]
    apply Finset.sum_congr rfl
    intro j _hj
    apply Finset.sum_congr rfl
    intro i _hi
    rw [(hDiagDiv j i).choose_spec]
  · intro j i
    exact (hAxisDiv j i).choose_spec
  · intro j i
    exact (hDiagDiv j i).choose_spec


/-- First-order norm comparison for the symmetrized necessity proof: if `A` and `B`
are orthogonal and have equal norm, then the axis derivative norm `‖A‖` matches the
normalized diagonal derivative norm `‖(A+B)/sqrt 2‖`. -/
theorem axis_diagonal_first_derivative_norm_eq_of_orthogonal_of_norm_eq {N : ℕ}
    {A B : Fin N → ℝ} (hAB : vecDot A B = 0) (hNorm : vecNorm A = vecNorm B) :
    vecNorm A = vecNorm (fun i : Fin N => (A i + B i) / Real.sqrt 2) := by
  exact (vecNorm_add_div_sqrt_two_eq_of_orthogonal_of_norm_eq hAB hNorm).symm

/-- Signed version matching the stripped factors, whose derivative at zero contributes a
minus sign. -/
theorem axis_diagonal_stripped_first_derivative_norm_eq_of_orthogonal_of_norm_eq {N : ℕ}
    {A B : Fin N → ℝ} (hAB : vecDot A B = 0) (hNorm : vecNorm A = vecNorm B) :
    vecNorm (fun i : Fin N => -A i) =
      vecNorm (fun i : Fin N => -((A i + B i) / Real.sqrt 2)) := by
  rw [vecNorm_neg, vecNorm_neg]
  exact axis_diagonal_first_derivative_norm_eq_of_orthogonal_of_norm_eq hAB hNorm

end ScaledRobinson
end OptimalConvergenceRates

end
