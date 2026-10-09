import OptimalConvergenceRates.CQC.BoxLiftAlgebra

/-! Polynomial differential identities for the squared-slack lift. -/

noncomputable section

open MvPolynomial Finset Set Matrix

namespace OptimalConvergenceRates
namespace CQCInternal

variable {N n m : ℕ}

theorem mvPolynomialEvalFDeriv_add
    (P Q : MvPolynomial (Fin N) ℝ) (x w : Fin N → ℝ) :
    QuarticConvergence.mvPolynomialEvalFDeriv (P + Q) x w =
      QuarticConvergence.mvPolynomialEvalFDeriv P x w +
      QuarticConvergence.mvPolynomialEvalFDeriv Q x w := by
  simp [mvPolynomialEvalFDeriv_apply, polynomialGradientAt,
    Finset.sum_add_distrib, add_mul]

theorem mvPolynomialEvalFDeriv_neg
    (P : MvPolynomial (Fin N) ℝ) (x w : Fin N → ℝ) :
    QuarticConvergence.mvPolynomialEvalFDeriv (-P) x w =
      -QuarticConvergence.mvPolynomialEvalFDeriv P x w := by
  simp [mvPolynomialEvalFDeriv_apply, polynomialGradientAt,
    Finset.sum_neg_distrib]

theorem mvPolynomialEvalFDeriv_sub
    (P Q : MvPolynomial (Fin N) ℝ) (x w : Fin N → ℝ) :
    QuarticConvergence.mvPolynomialEvalFDeriv (P - Q) x w =
      QuarticConvergence.mvPolynomialEvalFDeriv P x w -
      QuarticConvergence.mvPolynomialEvalFDeriv Q x w := by
  rw [sub_eq_add_neg, mvPolynomialEvalFDeriv_add,
    mvPolynomialEvalFDeriv_neg]
  rfl

theorem mvPolynomialEvalFDeriv_mul
    (P Q : MvPolynomial (Fin N) ℝ) (x w : Fin N → ℝ) :
    QuarticConvergence.mvPolynomialEvalFDeriv (P * Q) x w =
      MvPolynomial.eval x P *
          QuarticConvergence.mvPolynomialEvalFDeriv Q x w +
      MvPolynomial.eval x Q *
          QuarticConvergence.mvPolynomialEvalFDeriv P x w := by
  simp [mvPolynomialEvalFDeriv_apply, polynomialGradientAt,
    Finset.mul_sum, add_mul, Finset.sum_add_distrib]
  ring

theorem mvPolynomialEvalFDeriv_sum
    (P : Fin m → MvPolynomial (Fin N) ℝ) (x w : Fin N → ℝ) :
    QuarticConvergence.mvPolynomialEvalFDeriv (∑ i, P i) x w =
      ∑ i, QuarticConvergence.mvPolynomialEvalFDeriv (P i) x w := by
  simp only [mvPolynomialEvalFDeriv_apply, polynomialGradientAt,
    map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

@[simp]
theorem eval_slackW
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (z : Fin (n + m) → ℝ)
    (j : Fin (n + m)) :
    MvPolynomial.eval z (slackW g p j) =
      2 * MvPolynomial.eval (basePoint z) p *
          polynomialGradientAt (slackDeterminant g) z j +
      MvPolynomial.eval z (slackDeterminant g) *
          polynomialGradientAt (liftBasePolynomial p) z j := by
  simp [slackW, polynomialGradientAt]

@[simp]
theorem eval_slackCorrection
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (z : Fin (n + m) → ℝ)
    (i : Fin m) :
    MvPolynomial.eval z (slackCorrection g p i) =
      ((slackGramAt g z).adjugate *ᵥ
        ((slackJacobianAt g z) *ᵥ
          fun j ↦ MvPolynomial.eval z (slackW g p j))) i := by
  let ev : MvPolynomial (Fin (n + m)) ℝ →+* ℝ :=
    MvPolynomial.eval₂Hom (RingHom.id ℝ) z
  have hmat : (slackGramPolynomial g).map ev = slackGramAt g z := by
    ext a b
    simp [ev, MvPolynomial.eval₂_id]
  have hadj : ∀ i k,
      MvPolynomial.eval z ((slackGramPolynomial g).adjugate i k) =
        (slackGramAt g z).adjugate i k := by
    intro i k
    have hmap := congrFun (congrFun
      (RingHom.map_adjugate ev (slackGramPolynomial g)) i) k
    calc
      MvPolynomial.eval z ((slackGramPolynomial g).adjugate i k) =
          ev ((slackGramPolynomial g).adjugate i k) := by
            simp [ev, MvPolynomial.eval₂_id]
      _ = ((slackGramPolynomial g).map ev).adjugate i k := hmap
      _ = (slackGramAt g z).adjugate i k := by rw [hmat]
  change ev (((slackGramPolynomial g).adjugate *ᵥ
    ((slackJacobianPolynomial g) *ᵥ slackW g p)) i) = _
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro k _
  change MvPolynomial.eval z ((slackGramPolynomial g).adjugate i k) *
      (∑ j, MvPolynomial.eval z (slackJacobianPolynomial g k j) *
        MvPolynomial.eval z (slackW g p j)) = _
  rw [hadj]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [eval_slackJacobianPolynomial]

theorem slackGramAt_isSymm
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin (n + m) → ℝ) : (slackGramAt g z).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i k
  simp [slackGramAt, Matrix.mul_apply, slackJacobianAt]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem evalFDeriv_slackPolynomial_gradient
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin (n + m) → ℝ) (i k : Fin m) :
    QuarticConvergence.mvPolynomialEvalFDeriv (slackPolynomial g k) z
        (polynomialGradientAt (slackPolynomial g i) z) =
      slackGramAt g z k i := by
  rw [mvPolynomialEvalFDeriv_apply]
  simp [polynomialGradientAt_slackPolynomial, slackGramAt,
    Matrix.mul_apply, slackJacobianAt, slackGradientAt]

theorem evalFDeriv_mainSlackTerm
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (z w : Fin (n + m) → ℝ) :
    QuarticConvergence.mvPolynomialEvalFDeriv
        ((slackDeterminant g) ^ 2 * liftBasePolynomial p) z w =
      MvPolynomial.eval z (slackDeterminant g) *
        ∑ j, MvPolynomial.eval z (slackW g p j) * w j := by
  have hsum :
      ∑ j, MvPolynomial.eval z (slackW g p j) * w j =
        2 * MvPolynomial.eval (basePoint z) p *
            ∑ j, polynomialGradientAt (slackDeterminant g) z j * w j +
        MvPolynomial.eval z (slackDeterminant g) *
            ∑ j, polynomialGradientAt (liftBasePolynomial p) z j * w j := by
    simp_rw [eval_slackW, add_mul]
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      ring
    · apply Finset.sum_congr rfl
      intro j _
      ring
  rw [pow_two, mvPolynomialEvalFDeriv_mul,
    mvPolynomialEvalFDeriv_mul]
  rw [mvPolynomialEvalFDeriv_apply, mvPolynomialEvalFDeriv_apply]
  simp only [map_mul]
  rw [eval_liftBasePolynomial, hsum]
  ring

end CQCInternal
end OptimalConvergenceRates

end
