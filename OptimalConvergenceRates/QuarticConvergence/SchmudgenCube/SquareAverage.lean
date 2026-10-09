/-
  Averaging parity-normal-form squares over all second-coordinate signs.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.ParityComponents
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.SignedCircle

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

variable {n : ℕ}

/-- The box-preordering polynomial obtained by squaring all parity components. -/
def circleParityPreorderingPolynomial
    (P : MvPolynomial (CubeCircleVar n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ J ∈ Finset.univ.powerset,
    (circleParityComponent P J) ^ 2 * BoxSemialgebraicGeneratorProd J

/-- The unnormalized average of the squared values over all choices of signs
is exactly `2^n` times the evaluation of the parity-component preordering
polynomial. -/
theorem sum_signedCircle_eval_sq (P : MvPolynomial (CubeCircleVar n) ℝ)
    (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    ∑ eps : Fin n → Bool,
        (MvPolynomial.eval (signedCirclePoint x eps) P) ^ 2 =
      (2 : ℝ) ^ n *
        MvPolynomial.eval x (circleParityPreorderingPolynomial P) := by
  classical
  have hpowerset :
      (Finset.univ : Finset (Finset (Fin n))) =
        (Finset.univ : Finset (Fin n)).powerset := by
    ext J
    simp
  let radiusProduct : Finset (Fin n) → ℝ :=
    fun J ↦ ∏ i ∈ J, Real.sqrt (1 - x i ^ 2)
  have heval (eps : Fin n → Bool) :
      MvPolynomial.eval (signedCirclePoint x eps) P =
        ∑ J : Finset (Fin n), cubeSignCharacter eps J *
          (MvPolynomial.eval x (circleParityComponent P J) * radiusProduct J) := by
    rw [eval_eq_sum_circleParityComponents
      (signedCirclePoint_mem_productCircle x eps hx) P]
    rw [← hpowerset]
    simp only [signedCirclePoint_first]
    apply Fintype.sum_congr
    intro J
    rw [signedCirclePoint_second_prod]
    dsimp only [radiusProduct]
    ring
  calc
    ∑ eps : Fin n → Bool,
        (MvPolynomial.eval (signedCirclePoint x eps) P) ^ 2 =
        ∑ eps : Fin n → Bool,
          (∑ J : Finset (Fin n), cubeSignCharacter eps J *
            (MvPolynomial.eval x (circleParityComponent P J) * radiusProduct J)) ^ 2 := by
      apply Fintype.sum_congr
      intro eps
      rw [heval eps]
    _ = (2 : ℝ) ^ n * ∑ J : Finset (Fin n),
          (MvPolynomial.eval x (circleParityComponent P J) * radiusProduct J) ^ 2 :=
      sum_sq_walshTransform _
    _ = (2 : ℝ) ^ n *
        MvPolynomial.eval x (circleParityPreorderingPolynomial P) := by
      congr 1
      unfold circleParityPreorderingPolynomial
      rw [map_sum, ← hpowerset]
      apply Fintype.sum_congr
      intro J
      rw [map_mul, map_pow]
      dsimp only [radiusProduct]
      rw [mul_pow, circleRadius_prod_sq x hx J]

end QuarticConvergence
end OptimalConvergenceRates

end
