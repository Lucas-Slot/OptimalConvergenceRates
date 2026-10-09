import OptimalConvergenceRates.CQC.BoxLiftDifferential

/-! Normal cancellation for the corrected squared-slack lift. -/

noncomputable section

open MvPolynomial Finset Set Matrix

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

/-- The adjugate correction kills every normal derivative on the squared-slack
variety. -/
theorem correctedSlackObjective_normal_derivative
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    {z : Fin (n + m) → ℝ} (hz : z ∈ slackZeroSet g) (i : Fin m) :
    QuarticConvergence.mvPolynomialEvalFDeriv
        (correctedSlackObjective g p) z
        (polynomialGradientAt (slackPolynomial g i) z) = 0 := by
  let J := slackJacobianAt g z
  let A := slackGramAt g z
  let w : Fin (n + m) → ℝ :=
    fun j ↦ MvPolynomial.eval z (slackW g p j)
  let b : Fin m → ℝ :=
    fun k ↦ MvPolynomial.eval z (slackCorrection g p k)
  have hb : b = A.adjugate *ᵥ (J *ᵥ w) := by
    funext k
    simp [b, A, J, w]
  have hAb : A *ᵥ b = A.det • (J *ᵥ w) := by
    rw [hb]
    calc
      A *ᵥ (A.adjugate *ᵥ (J *ᵥ w)) =
          (A * A.adjugate) *ᵥ (J *ᵥ w) :=
            Matrix.mulVec_mulVec (J *ᵥ w) A A.adjugate
      _ = (A.det • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ
          (J *ᵥ w) := by rw [Matrix.mul_adjugate]
      _ = A.det • (J *ᵥ w) := by
        rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  have hsymm : A.IsSymm := slackGramAt_isSymm g z
  rw [correctedSlackObjective, mvPolynomialEvalFDeriv_sub,
    evalFDeriv_mainSlackTerm, mvPolynomialEvalFDeriv_sum]
  have hcorr :
      ∑ k, QuarticConvergence.mvPolynomialEvalFDeriv
          (slackPolynomial g k * slackCorrection g p k) z
          (polynomialGradientAt (slackPolynomial g i) z) =
        (A *ᵥ b) i := by
    rw [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro k _
    rw [mvPolynomialEvalFDeriv_mul, hz k]
    simp only [zero_mul, zero_add]
    rw [evalFDeriv_slackPolynomial_gradient]
    change b k * A k i = A i k * b k
    rw [hsymm.apply]
    ring
  rw [hcorr, hAb]
  have hJw :
      ∑ j, w j * polynomialGradientAt (slackPolynomial g i) z j =
        (J *ᵥ w) i := by
    rw [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    rw [polynomialGradientAt_slackPolynomial]
    change w j * slackGradientAt g z i j = slackGradientAt g z i j * w j
    ring
  change MvPolynomial.eval z (slackDeterminant g) *
      ∑ j, w j * polynomialGradientAt (slackPolynomial g i) z j -
      (A.det • (J *ᵥ w)) i = 0
  rw [hJw, eval_slackDeterminant]
  change (slackGramAt g z).det * (J *ᵥ w) i -
    (slackGramAt g z).det * (J *ᵥ w) i = 0
  ring

@[simp]
theorem eval_correctedSlackObjective_on_zeroSet
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    {z : Fin (n + m) → ℝ} (hz : z ∈ slackZeroSet g) :
    MvPolynomial.eval z (correctedSlackObjective g p) =
      MvPolynomial.eval z (slackDeterminant g) ^ 2 *
        MvPolynomial.eval (basePoint z) p := by
  have hsum :
      ∑ i, MvPolynomial.eval z
          (slackPolynomial g i * slackCorrection g p i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [map_mul, hz i, zero_mul]
  rw [correctedSlackObjective, map_sub, map_mul, map_pow,
    eval_liftBasePolynomial, map_sum]
  rw [hsum, sub_zero]

theorem eval_correctedSlackObjective_nonneg_on_zeroSet
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g))
    {z : Fin (n + m) → ℝ} (hz : z ∈ slackZeroSet g) :
    0 ≤ MvPolynomial.eval z (correctedSlackObjective g p) := by
  rw [eval_correctedSlackObjective_on_zeroSet g p hz]
  exact mul_nonneg (sq_nonneg _)
    (hp (basePoint z) (basePoint_mem_basicClosedSet_of_mem_slackZeroSet hz))

end CQCInternal
end OptimalConvergenceRates

end
