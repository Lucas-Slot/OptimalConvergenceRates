/-
  Monomial-by-monomial parity reduction on the product of unit circles.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.ProductCircle

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

variable {n : ℕ}

/-- The `i`-th circle relation solved for the square of its second coordinate. -/
def circleGenerator (i : Fin n) : MvPolynomial (CubeCircleVar n) ℝ :=
  1 - X (i, false) ^ 2

@[simp] theorem eval_circleGenerator {z : CubeCircleVar n → ℝ}
    (hz : z ∈ ProductCircle n) (i : Fin n) :
    MvPolynomial.eval z (circleGenerator i) = z (i, true) ^ 2 := by
  simp only [circleGenerator, map_sub, map_one, map_pow, eval_X]
  nlinarith [hz i]

/-- Reduce one variable power by replacing every even power of `y_i` by a power of
`1 - x_i^2`, retaining only the parity power of `y_i`. -/
def circleReducedFactor (ib : CubeCircleVar n) (e : ℕ) :
    MvPolynomial (CubeCircleVar n) ℝ :=
  match ib with
  | (i, false) => X (i, false) ^ e
  | (i, true) => X (i, true) ^ (e % 2) * circleGenerator i ^ (e / 2)

/-- The parity reduction of a coefficient-free monomial. -/
def circleReduceMonomial (s : CubeCircleVar n →₀ ℕ) :
    MvPolynomial (CubeCircleVar n) ℝ :=
  s.prod circleReducedFactor

theorem eval_circleReducedFactor {z : CubeCircleVar n → ℝ}
    (hz : z ∈ ProductCircle n) (ib : CubeCircleVar n) (e : ℕ) :
    MvPolynomial.eval z (circleReducedFactor ib e) = z ib ^ e := by
  rcases ib with ⟨i, b⟩
  cases b with
  | false => simp [circleReducedFactor]
  | true =>
      simp only [circleReducedFactor, map_mul, map_pow, eval_X, eval_circleGenerator hz]
      rw [← pow_mul, ← pow_add]
      congr 1
      omega

/-- Parity reduction preserves the value of every monomial on the product of circles. -/
theorem eval_circleReduceMonomial {z : CubeCircleVar n → ℝ}
    (hz : z ∈ ProductCircle n) (s : CubeCircleVar n →₀ ℕ) :
    MvPolynomial.eval z (circleReduceMonomial s) = s.prod fun ib e ↦ z ib ^ e := by
  classical
  unfold circleReduceMonomial
  simp only [Finsupp.prod, map_prod]
  apply Finset.prod_congr rfl
  intro ib hib
  exact eval_circleReducedFactor hz ib (s ib)

/-- Reduce every monomial of a polynomial to first degree in each second coordinate. -/
def circleParityReduce (P : MvPolynomial (CubeCircleVar n) ℝ) :
    MvPolynomial (CubeCircleVar n) ℝ :=
  ∑ s ∈ P.support, MvPolynomial.C (legacyMvCoeff s P) * circleReduceMonomial s

/-- The parity-reduced polynomial agrees with the original one on the product of circles. -/
theorem eval_circleParityReduce {z : CubeCircleVar n → ℝ}
    (hz : z ∈ ProductCircle n) (P : MvPolynomial (CubeCircleVar n) ℝ) :
    MvPolynomial.eval z (circleParityReduce P) = MvPolynomial.eval z P := by
  classical
  calc
    MvPolynomial.eval z (circleParityReduce P) =
        ∑ s ∈ P.support,
          MvPolynomial.eval z (MvPolynomial.monomial s (legacyMvCoeff s P)) := by
      change MvPolynomial.eval z
        (∑ s ∈ P.support,
          MvPolynomial.C (legacyMvCoeff s P) * circleReduceMonomial s) = _
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [map_mul, eval_C, eval_circleReduceMonomial hz]
      simp only [eval_monomial]
    _ = MvPolynomial.eval z P := by
      rw [← map_sum]
      exact congrArg (MvPolynomial.eval z) (P.as_sum).symm

/-- A reduced factor has no larger total degree than the power it replaces. -/
theorem circleReducedFactor_totalDegree_le (ib : CubeCircleVar n) (e : ℕ) :
    (circleReducedFactor ib e).totalDegree ≤ e := by
  rcases ib with ⟨i, b⟩
  cases b with
  | false =>
      simp [circleReducedFactor]
  | true =>
      have hg : (circleGenerator i).totalDegree ≤ 2 := by
        unfold circleGenerator
        exact (MvPolynomial.totalDegree_sub _ _).trans
          (max_le (by simp) (by simp))
      calc
        (circleReducedFactor ((i, true) : CubeCircleVar n) e).totalDegree ≤
            (X (i, true) ^ (e % 2) : MvPolynomial (CubeCircleVar n) ℝ).totalDegree +
              (circleGenerator i ^ (e / 2)).totalDegree := by
          exact MvPolynomial.totalDegree_mul _ _
        _ ≤ (e % 2) + (e / 2) * 2 := by
          exact Nat.add_le_add
            (by simp)
            ((MvPolynomial.totalDegree_pow _ _).trans
              (Nat.mul_le_mul_left (e / 2) hg))
        _ = e := by
          rw [Nat.mul_comm (e / 2) 2]
          exact Nat.mod_add_div e 2

/-- The reduced coefficient-free monomial has degree at most its original exponent sum. -/
theorem circleReduceMonomial_totalDegree_le (s : CubeCircleVar n →₀ ℕ) :
    (circleReduceMonomial s).totalDegree ≤ s.sum fun _ e ↦ e := by
  classical
  unfold circleReduceMonomial
  calc
    (s.prod circleReducedFactor).totalDegree ≤
        ∑ ib ∈ s.support, (circleReducedFactor ib (s ib)).totalDegree := by
      simp only [Finsupp.prod]
      exact MvPolynomial.totalDegree_finsetProd s.support _
    _ ≤ ∑ ib ∈ s.support, s ib := by
      exact Finset.sum_le_sum fun ib _ ↦ circleReducedFactor_totalDegree_le ib (s ib)
    _ = s.sum fun _ e ↦ e := by
      simp only [Finsupp.sum]

/-- Parity reduction does not increase total degree. -/
theorem circleParityReduce_totalDegree_le (P : MvPolynomial (CubeCircleVar n) ℝ) :
    (circleParityReduce P).totalDegree ≤ P.totalDegree := by
  classical
  unfold circleParityReduce
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  calc
    (MvPolynomial.C (legacyMvCoeff s P) * circleReduceMonomial s).totalDegree ≤
        (MvPolynomial.C (legacyMvCoeff s P) :
          MvPolynomial (CubeCircleVar n) ℝ).totalDegree +
          (circleReduceMonomial s).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + s.sum (fun _ e ↦ e) := by
      exact Nat.add_le_add (by simp) (circleReduceMonomial_totalDegree_le s)
    _ ≤ P.totalDegree := by
      simpa only [zero_add] using MvPolynomial.le_totalDegree hs

end QuarticConvergence
end OptimalConvergenceRates

end
