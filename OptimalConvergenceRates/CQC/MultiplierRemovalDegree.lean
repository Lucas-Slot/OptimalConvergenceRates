import OptimalConvergenceRates.CQC.MultiplierRemovalAssembly

/-!
# Linear degree cost of multiplier removal

The exact certificate assembled in `MultiplierRemovalAssembly` has order
linear in the length of the inverse series.  This file packages that fact in
a coarse bound whose constants are independent of the accuracy parameter.
-/

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates
namespace CQCInternal

open GeneralArchimedean

variable {n m : ℕ}

private theorem multiplierRemoval_nat_budget (ell D P M R : ℕ) :
    2 * M + R + (2 * ell + 3) * D + (4 * (ell + 1) + 3) * D +
      2 * (ell * D) + 2 * P + 2 * (P + (2 * (ell + 1)) * D) ≤
    (2 * M + R + 20 * D + 6 * P + 10) * (ell + 1) := by
  nlinarith

private theorem multiplierRemoval_order_bound
    (ell r D P M R qDegree pDegree lastDegree : ℕ)
    (hq : qDegree ≤ 2 * (ell * D))
    (hp : pDegree ≤ 2 * P)
    (hlast : lastDegree ≤ 2 * (P + (2 * (ell + 1)) * D)) :
    r + (M + (2 * ell + 3) * D) +
          (M + (4 * (ell + 1) + 3) * D) + R +
          qDegree + pDegree + lastDegree ≤
      r + (2 * M + R + 20 * D + 6 * P + 10) * (ell + 1) := by
  have hbudget := multiplierRemoval_nat_budget ell D P M R
  omega

theorem inverseApproxAt_totalDegree_le
    (a : MvPolynomial (Fin n) ℝ) (α β : ℝ) (ell : ℕ) :
    (inverseApproxAt α β ell a).totalDegree ≤
      ell * (a - C α).totalDegree := by
  exact (polynomialSubst_totalDegree_le (a - C α)
    (inverseSeriesApprox α β ell)).trans
      (Nat.mul_le_mul_right _ (inverseSeriesApprox_natDegree_le α β ell))

theorem inverseResidualAt_totalDegree_le
    (a : MvPolynomial (Fin n) ℝ) (α β : ℝ) (ell : ℕ) :
    (inverseResidualAt α β ell a).totalDegree ≤
      (2 * (ell + 1)) * (a - C α).totalDegree := by
  exact (polynomialSubst_totalDegree_le (a - C α)
    (inverseSeriesResidual α β ell)).trans
      (Nat.mul_le_mul_right _ (inverseSeriesResidual_natDegree_le α β ell))

/-- A deliberately coarse fixed slope for all degree costs in the exact
multiplier-removal identity. -/
def multiplierRemovalSlope
    (p a : MvPolynomial (Fin n) ℝ)
    (α : ℝ) (rLower rUpper rBound : ℕ) : ℕ :=
  2 * max rLower rUpper + rBound +
    20 * (a - C α).totalDegree + 6 * p.totalDegree + 10

/-- Multiplier removal at a prescribed series length, with a single linear
order bound. -/
theorem multiplierRemoval_at_length_linear
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (p a : MvPolynomial (Fin n) ℝ)
    {α β B δ : ℝ} (ell r rLower rUpper rBound : ℕ)
    (hα : 0 < α) (hαβ : α < β) (hB : 0 < B) (hδ : 0 < δ)
    (hlower : a - C α ∈ GenQuadraticModule g rLower)
    (hupper : C β - a ∈ GenQuadraticModule g rUpper)
    (hpBound : C (B ^ 2) - p ^ 2 ∈ GenQuadraticModule g rBound)
    (hweighted : a ^ 2 * p + C δ ∈ GenQuadraticModule g r) :
    p + C (B * (2 * (1 - α / β) ^ (ell + 1)) + δ * α⁻¹ ^ 2) ∈
      GenQuadraticModule g
        (r + multiplierRemovalSlope p a α rLower rUpper rBound * (ell + 1)) := by
  have hq := inverseApproxAt_totalDegree_le a α β ell
  have hv := inverseResidualAt_totalDegree_le a α β ell
  have hq2 : (inverseApproxAt α β ell a ^ 2).totalDegree ≤
      2 * (ell * (a - C α).totalDegree) :=
    (MvPolynomial.totalDegree_pow _ 2).trans (Nat.mul_le_mul_left 2 hq)
  have hp2 : (p ^ 2).totalDegree ≤ 2 * p.totalDegree :=
    MvPolynomial.totalDegree_pow p 2
  have hpv :
      (p * inverseResidualAt α β ell a).totalDegree ≤
        p.totalDegree + (2 * (ell + 1)) * (a - C α).totalDegree :=
    (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add_left hv _)
  have hsum :
      (C (B * (2 * (1 - α / β) ^ (ell + 1))) +
        p * inverseResidualAt α β ell a).totalDegree ≤
          p.totalDegree + (2 * (ell + 1)) * (a - C α).totalDegree := by
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ hpv)
    rw [MvPolynomial.totalDegree_C]
    omega
  have hlast :
      ((C (B * (2 * (1 - α / β) ^ (ell + 1))) +
        p * inverseResidualAt α β ell a) ^ 2).totalDegree ≤
          2 * (p.totalDegree +
            (2 * (ell + 1)) * (a - C α).totalDegree) :=
    (MvPolynomial.totalDegree_pow _ 2).trans (Nat.mul_le_mul_left 2 hsum)
  have horder := multiplierRemoval_order_bound ell r
    (a - C α).totalDegree p.totalDegree (max rLower rUpper) rBound
    (inverseApproxAt α β ell a ^ 2).totalDegree (p ^ 2).totalDegree
    ((C (B * (2 * (1 - α / β) ^ (ell + 1))) +
      p * inverseResidualAt α β ell a) ^ 2).totalDegree hq2 hp2 hlast
  apply GenQuadraticModule_mono _
    (multiplierRemoval_at_length p a ell r rLower rUpper rBound
      hα hαβ hB hδ hlower hupper hpBound hweighted)
  simpa [multiplierRemovalSlope] using horder

end CQCInternal
end OptimalConvergenceRates

end
