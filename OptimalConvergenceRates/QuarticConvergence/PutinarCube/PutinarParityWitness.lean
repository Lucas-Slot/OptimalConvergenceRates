/-
  The same-root parity witness used by the Putinar approximation.

  A finite family of paired-variable roots is reduced componentwise.  The
  resulting cube multipliers remember every original root and therefore can
  later be estimated by finite-vector bounds without choosing a new SOS
  decomposition.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.SquareAverage
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.ConeWitnesses

open MvPolynomial Finset
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

variable {n N R : ℕ}

/-- The SOS multiplier attached to one parity set, retaining the original
finite root index. -/
def finiteCircleParityMultiplier
    (P : Fin N → MvPolynomial (CubeCircleVar n) ℝ)
    (J : Finset (Fin n)) : MvPolynomial (Fin n) ℝ :=
  ∑ ν, (circleParityComponent (P ν) J) ^ 2

/-- The box-preordering polynomial obtained from all roots and all parity
characters. -/
def finiteCircleParityPreorderingPolynomial
    (P : Fin N → MvPolynomial (CubeCircleVar n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ J ∈ Finset.univ.powerset,
    finiteCircleParityMultiplier P J * BoxSemialgebraicGeneratorProd J

/-- The finite construction is exactly the sum of the one-root parity
preordering polynomials. -/
theorem finiteCircleParityPreorderingPolynomial_eq_sum
    (P : Fin N → MvPolynomial (CubeCircleVar n) ℝ) :
    finiteCircleParityPreorderingPolynomial P =
      ∑ ν, circleParityPreorderingPolynomial (P ν) := by
  classical
  unfold finiteCircleParityPreorderingPolynomial finiteCircleParityMultiplier
    circleParityPreorderingPolynomial
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The parity construction carries a canonical root-preserving preordering
witness of total-certificate-degree `2 * R`. -/
def finiteCircleParityRootWitness
    (P : Fin N → MvPolynomial (CubeCircleVar n) ℝ)
    (hdegree : ∀ ν, (P ν).totalDegree ≤ R) :
    BoxPreorderingRootWitness
      (finiteCircleParityPreorderingPolynomial P) (2 * R) :=
  BoxPreorderingRootWitness.ofWeighted
    (fun _J ↦ N)
    (fun J ν ↦ circleParityComponent (P ν) J)
    rfl
    (by
      intro J ν
      rcases circleParityComponent_eq_zero_or_totalDegree_add_card_le
          (P ν) J with hzero | hdegree'
      · exact Or.inl hzero
      · exact Or.inr (hdegree'.trans (hdegree ν)))

/-- In particular, the same-root parity polynomial belongs to the repository's
canonical box preordering. -/
theorem finiteCircleParityPreorderingPolynomial_mem
    (P : Fin N → MvPolynomial (CubeCircleVar n) ℝ)
    (hdegree : ∀ ν, (P ν).totalDegree ≤ R) :
    finiteCircleParityPreorderingPolynomial P ∈ BoxPreordering n (2 * R) :=
  (finiteCircleParityRootWitness P hdegree).toBoxPreordering

/-- Summing the one-root Walsh identities gives the exact sign average for a
finite family of roots. -/
theorem sum_signedCircle_eval_sq_family
    (P : Fin N → MvPolynomial (CubeCircleVar n) ℝ)
    (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    ∑ eps : Fin n → Bool,
        ∑ ν, (MvPolynomial.eval (signedCirclePoint x eps) (P ν)) ^ 2 =
      (2 : ℝ) ^ n *
        MvPolynomial.eval x (finiteCircleParityPreorderingPolynomial P) := by
  classical
  calc
    ∑ eps : Fin n → Bool,
        ∑ ν, (MvPolynomial.eval (signedCirclePoint x eps) (P ν)) ^ 2 =
        ∑ ν, ∑ eps : Fin n → Bool,
          (MvPolynomial.eval (signedCirclePoint x eps) (P ν)) ^ 2 := by
      rw [Finset.sum_comm]
    _ = ∑ ν, (2 : ℝ) ^ n *
          MvPolynomial.eval x (circleParityPreorderingPolynomial (P ν)) := by
      apply Finset.sum_congr rfl
      intro ν _hν
      exact sum_signedCircle_eval_sq (P ν) x hx
    _ = (2 : ℝ) ^ n *
          ∑ ν, MvPolynomial.eval x
            (circleParityPreorderingPolynomial (P ν)) := by
      rw [Finset.mul_sum]
    _ = (2 : ℝ) ^ n *
        MvPolynomial.eval x (finiteCircleParityPreorderingPolynomial P) := by
      rw [finiteCircleParityPreorderingPolynomial_eq_sum, map_sum]

/-- Averaging a uniform square-approximation estimate over all second-coordinate
signs transfers it to the same-root parity preordering polynomial. -/
theorem abs_eval_sub_finiteCircleParityPreorderingPolynomial_le
    (h : MvPolynomial (Fin n) ℝ)
    (P : Fin N → MvPolynomial (CubeCircleVar n) ℝ)
    (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ 1)
    (E : ℝ)
    (happrox : ∀ eps : Fin n → Bool,
      |MvPolynomial.eval x h -
        ∑ ν, (MvPolynomial.eval (signedCirclePoint x eps) (P ν)) ^ 2| ≤ E) :
    |MvPolynomial.eval x h -
      MvPolynomial.eval x (finiteCircleParityPreorderingPolynomial P)| ≤ E := by
  classical
  let c : ℝ := (2 : ℝ) ^ n
  let a : ℝ := MvPolynomial.eval x h
  let q : ℝ := MvPolynomial.eval x (finiteCircleParityPreorderingPolynomial P)
  let S : (Fin n → Bool) → ℝ := fun eps ↦
    ∑ ν, (MvPolynomial.eval (signedCirclePoint x eps) (P ν)) ^ 2
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hsum : ∑ eps, S eps = c * q := by
    exact sum_signedCircle_eval_sq_family P x hx
  have hcard : ((Fintype.card (Fin n → Bool) : ℕ) : ℝ) = c := by
    simp [c]
  have hlower : c * (a - E) ≤ ∑ eps, S eps := by
    calc
      c * (a - E) = ∑ _eps : Fin n → Bool, (a - E) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
      _ ≤ ∑ eps, S eps := by
        apply Finset.sum_le_sum
        intro eps _heps
        have heps := (abs_le.mp (happrox eps)).2
        dsimp [a, S] at heps ⊢
        linarith
  have hupper : ∑ eps, S eps ≤ c * (a + E) := by
    calc
      ∑ eps, S eps ≤ ∑ _eps : Fin n → Bool, (a + E) := by
        apply Finset.sum_le_sum
        intro eps _heps
        have heps := (abs_le.mp (happrox eps)).1
        dsimp [a, S] at heps ⊢
        linarith
      _ = c * (a + E) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
  rw [hsum] at hlower hupper
  rw [abs_le]
  constructor
  · have hq : q ≤ a + E := le_of_mul_le_mul_left hupper hc
    linarith
  · have hq : a - E ≤ q := le_of_mul_le_mul_left hlower hc
    linarith

end QuarticConvergence
end OptimalConvergenceRates

end
