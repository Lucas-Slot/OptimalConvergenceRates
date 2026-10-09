import OptimalConvergenceRates.CQC.RegularPenalty

/-!
# Linear algebra behind the regular equation error bound
-/

noncomputable section

open MvPolynomial Finset Set Matrix

namespace OptimalConvergenceRates
namespace CQCInternal

variable {N m : ℕ}

/-- Jacobian whose rows are the gradients of a polynomial equation family. -/
def polynomialJacobianAt (h : Fin m → MvPolynomial (Fin N) ℝ)
    (v : Fin N → ℝ) : Matrix (Fin m) (Fin N) ℝ :=
  fun i j ↦ polynomialGradientAt (h i) v j

/-- Row Gram matrix of a polynomial equation family. -/
def polynomialGramAt (h : Fin m → MvPolynomial (Fin N) ℝ)
    (v : Fin N → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  polynomialJacobianAt h v * (polynomialJacobianAt h v)ᵀ

/-- Matrix recovering a normal vector from its image under the Jacobian,
up to multiplication by the Gram determinant. -/
def normalRecoveryAt (h : Fin m → MvPolynomial (Fin N) ℝ)
    (v : Fin N → ℝ) : Matrix (Fin N) (Fin m) ℝ :=
  (polynomialJacobianAt h v)ᵀ * (polynomialGramAt h v).adjugate

theorem normalCombination_eq_transpose_mulVec
    (h : Fin m → MvPolynomial (Fin N) ℝ)
    (v : Fin N → ℝ) (coeff : Fin m → ℝ) :
    (∑ i, coeff i • polynomialGradientAt (h i) v) =
      (polynomialJacobianAt h v)ᵀ *ᵥ coeff := by
  funext j
  simp [polynomialJacobianAt, Matrix.mulVec, dotProduct,
    Finset.sum_apply, mul_comm]

/-- Adjugate recovery identity on the span of the Jacobian rows. -/
theorem normalRecoveryAt_mulVec_jacobian
    (h : Fin m → MvPolynomial (Fin N) ℝ)
    (v w : Fin N → ℝ) (coeff : Fin m → ℝ)
    (hw : w = ∑ i, coeff i • polynomialGradientAt (h i) v) :
    (normalRecoveryAt h v) *ᵥ ((polynomialJacobianAt h v) *ᵥ w) =
      (polynomialGramAt h v).det • w := by
  let J := polynomialJacobianAt h v
  let A := polynomialGramAt h v
  have hA : A = J * Jᵀ := rfl
  have hw' : w = Jᵀ *ᵥ coeff := by
    simpa [J] using hw.trans (normalCombination_eq_transpose_mulVec h v coeff)
  have hmat : (Jᵀ * A.adjugate) * (J * Jᵀ) = A.det • Jᵀ := by
    calc
      (Jᵀ * A.adjugate) * (J * Jᵀ) = Jᵀ * (A.adjugate * (J * Jᵀ)) := by
        simp [Matrix.mul_assoc]
      _ = Jᵀ * (A.adjugate * A) := by rw [← hA]
      _ = Jᵀ * (A.det • (1 : Matrix (Fin m) (Fin m) ℝ)) := by
        rw [Matrix.adjugate_mul]
      _ = A.det • Jᵀ := by
        ext i j
        rw [Matrix.mul_apply, Finset.sum_eq_single j]
        · simp [mul_comm]
        · intro k _ hkj
          simp [hkj]
        · simp
  rw [hw']
  change (Jᵀ * A.adjugate) *ᵥ (J *ᵥ (Jᵀ *ᵥ coeff)) =
    A.det • (Jᵀ *ᵥ coeff)
  simp only [Matrix.mulVec_mulVec]
  rw [hmat]
  funext j
  change (∑ i, (A.det * Jᵀ j i) * coeff i) =
    A.det * ∑ i, Jᵀ j i * coeff i
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A coarse matrix-vector estimate for the product (`sup`) norms on finite
coordinate spaces. -/
theorem norm_matrix_mulVec_le_of_entries
    (M : Matrix (Fin N) (Fin m) ℝ) (x : Fin m → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hentry : ∀ i j, |M i j| ≤ B) :
    ‖M *ᵥ x‖ ≤ (m : ℝ) * B * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  rw [Real.norm_eq_abs]
  calc
    |(M *ᵥ x) i| = |∑ j, M i j * x j| := by
      rfl
    _ ≤ ∑ j, |M i j * x j| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin m, B * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hentry i j) (norm_le_pi_norm x j)
        (abs_nonneg _) hB
    _ = (m : ℝ) * B * ‖x‖ := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      ring

end CQCInternal
end OptimalConvergenceRates

end
