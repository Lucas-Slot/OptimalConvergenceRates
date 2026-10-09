/-
  Even square-variable tails for the weighted second-derivative estimate.
-/
import OptimalConvergenceRates.BasicNotions.UnivariateParity
import OptimalConvergenceRates.GeneralArchimedean.UnivariateSupNorm

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.MFCQQuadraticLowerBound

open UnivariateParity

/-- After taking the even part and writing it in the square variable,
remove its constant term and divide by that square variable. -/
def evenTail (P : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.divX (evenContract P - Polynomial.C (P.eval 0))

theorem evenContract_coeff_zero (P : Polynomial ℝ) :
    (evenContract P).coeff 0 = P.eval 0 := by
  rw [evenContract, Polynomial.coeff_contract (by norm_num : (2 : ℕ) ≠ 0)]
  simp only [zero_mul]
  rw [evenPart_even_coeff P (by simp), Polynomial.coeff_zero_eq_eval_zero]

theorem evenTail_reconstruction (P : Polynomial ℝ) :
    Polynomial.X * evenTail P + Polynomial.C (P.eval 0) = evenContract P := by
  have h := Polynomial.X_mul_divX_add
    (evenContract P - Polynomial.C (P.eval 0))
  have hcoeff :
      (evenContract P - Polynomial.C (P.eval 0)).coeff 0 = 0 := by
    rw [Polynomial.coeff_sub, evenContract_coeff_zero]
    simp
  rw [hcoeff, Polynomial.C_0, add_zero] at h
  dsimp [evenTail]
  rw [h]
  ring

theorem evenTail_eval (P : Polynomial ℝ) (s : ℝ) :
    s ^ 2 * (evenTail P).eval (s ^ 2) =
      (P.eval s + P.eval (-s)) / 2 - P.eval 0 := by
  have h := congrArg (fun Q : Polynomial ℝ ↦ Q.eval (s ^ 2))
    (evenTail_reconstruction P)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C] at h
  rw [evenContract_eval_sq, evenPart_eval] at h
  linarith

/-- Contraction by two gives the expected halving of a supplied degree
bound for the even part. -/
theorem evenContract_natDegree_le_half {P : Polynomial ℝ} {D : ℕ}
    (hdegree : P.natDegree ≤ D) :
    (evenContract P).natDegree ≤ D / 2 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [evenContract, Polynomial.coeff_contract (by norm_num : (2 : ℕ) ≠ 0)]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  have heven := evenPart_natDegree_le P
  omega

theorem evenTail_natDegree_le_half {P : Polynomial ℝ} {D : ℕ}
    (hdegree : P.natDegree ≤ D) :
    (evenTail P).natDegree ≤ D / 2 := by
  dsimp [evenTail]
  exact Polynomial.natDegree_divX_le.trans <|
    (Polynomial.natDegree_sub_le _ _).trans <|
      max_le (evenContract_natDegree_le_half hdegree) (by simp)

theorem evenTail_coeff_zero (P : Polynomial ℝ) :
    (evenTail P).coeff 0 = P.coeff 2 := by
  rw [evenTail, Polynomial.coeff_divX, Polynomial.coeff_sub]
  rw [evenContract, Polynomial.coeff_contract (by norm_num : (2 : ℕ) ≠ 0)]
  rw [evenPart_even_coeff P (by norm_num : 2 ∣ 2)]
  simp

/-- The second derivative at zero is twice the constant coefficient of
the even square-variable tail. -/
theorem secondDerivative_eval_zero_eq (P : Polynomial ℝ) :
    (Polynomial.derivative (Polynomial.derivative P)).eval 0 =
      2 * (evenTail P).eval 0 := by
  have h := GeneralArchimedean.iterate_derivative_eval_zero P 2
  change (Polynomial.derivative (Polynomial.derivative P)).eval 0 =
      (Nat.factorial 2 : ℝ) * P.coeff 2 at h
  rw [h, ← Polynomial.coeff_zero_eq_eval_zero, evenTail_coeff_zero]
  norm_num

end OptimalConvergenceRates.MFCQQuadraticLowerBound

end
