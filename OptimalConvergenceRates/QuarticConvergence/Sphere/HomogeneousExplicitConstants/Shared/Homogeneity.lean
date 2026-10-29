import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-! Scalar evaluation of homogeneous forms, shared by both quantitative bounds. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Foundation
open scoped BigOperators
variable {σ : Type*}

/-- Homogeneity gives the expected scalar evaluation law, proved directly
from the polynomial's finite monomial expansion. -/
theorem homogeneous_eval_scale (q : MvPolynomial σ ℝ) (d : ℕ)
    (hq : q.IsHomogeneous d) (c : ℝ) (y : σ → ℝ) :
    MvPolynomial.eval (fun i ↦ c * y i) q = c ^ d * MvPolynomial.eval y q := by
  classical
  have heval (x : σ → ℝ) : MvPolynomial.eval x q =
      ∑ a ∈ q.support, q.coeff a * a.prod (fun i e ↦ x i ^ e) := by
    conv_lhs => rw [q.as_sum]
    simp only [MvPolynomial.eval_sum, MvPolynomial.eval_monomial]
  rw [heval, heval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hdegree : a.degree = d := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp ha) (hq.coeff_eq_zero h)
  have hprod : a.prod (fun i e ↦ (c * y i) ^ e) =
      c ^ d * a.prod (fun i e ↦ y i ^ e) := by
    simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
    rw [Finset.prod_pow_eq_pow_sum]
    exact congrArg (fun k ↦ c ^ k * ∏ i ∈ a.support, y i ^ a i) hdegree
  rw [hprod]
  ring

end Foundation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
