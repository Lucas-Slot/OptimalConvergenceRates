/-
  The common canonical-order endpoint for the two cube hierarchies.

  The proof below contains no new approximation argument.  It combines the
  explicit Schmuedgen endpoint with the controlled-root Putinar endpoint and
  uses the repository's canonical inclusion of the box quadratic module in
  the box preordering to order the two hierarchy gaps.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.SchmudgenExplicitRate
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarConcreteEndpoint

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- Assuming the single controlled-root weighted estimate isolated in
`PutinarConcreteEndpoint`, both canonical cube hierarchies have the same
general quartic upper rate.  The values are genuine real representatives of
the `WithBot` hierarchy bounds, and their gaps occur in the natural order.

The order parameter `r` is the repository's total certificate-degree order
for both `BoxPreordering` and `BoxQuadraticModule`. -/
theorem combinedExplicitRate_of_controlledRoots
    {n : ℕ} (hn : 0 < n)
    (hweighted : HasUniformControlledWeightedParityBound n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        p.totalDegree ≤ d → c * max d 1 ≤ r →
          ∃ (putinarValue schmudgenValue : ℝ),
            lasserre_bound_box_qm p r = (putinarValue : WithBot ℝ) ∧
            lasserre_bound_box_preo p r = (schmudgenValue : WithBot ℝ) ∧
            0 ≤ polyMin p - schmudgenValue ∧
            polyMin p - schmudgenValue ≤ polyMin p - putinarValue ∧
            polyMin p - putinarValue ≤
              A * ((max d 1 : ℕ) : ℝ) ^ 6 *
                (polyMax p - polyMin p) / (r : ℝ) ^ 4 := by
  obtain ⟨As, cs, hAs, hcs, hschmudgen⟩ :=
    schmudgenExplicitRate_lasserreGap hn
  obtain ⟨Ap, cp, hAp, hcp, hputinar⟩ :=
    putinarExplicitRate_lasserreGap_of_controlledRoots hn hweighted
  refine ⟨As + Ap, cs + cp, add_pos hAs hAp, Nat.add_pos_left hcs cp, ?_⟩
  intro p d r hpdeg hr
  have he : 0 < max d 1 := by omega
  have hrs : cs * max d 1 ≤ r := by
    exact le_trans (Nat.mul_le_mul_right (max d 1) (Nat.le_add_right cs cp)) hr
  have hrp : cp * max d 1 ≤ r := by
    exact le_trans (Nat.mul_le_mul_right (max d 1) (Nat.le_add_left cp cs)) (by
      simpa [Nat.add_comm] using hr)
  obtain ⟨s, hsvalue, hsgap0, hsgap⟩ := hschmudgen p d r hpdeg hrs
  obtain ⟨q, hqvalue, hqgap0, hqgap⟩ := hputinar p d r hpdeg hrp
  have hcompare := lasserre_bound_box_qm_le p r
  rw [hqvalue, hsvalue, WithBot.coe_le_coe] at hcompare
  have hosc : 0 ≤ polyMax p - polyMin p :=
    polyMax_sub_polyMin_nonneg p
  have hrpos : 0 < r := by
    have hthreshold : 0 < (cs + cp) * max d 1 :=
      Nat.mul_pos (Nat.add_pos_left hcs cp) he
    exact hthreshold.trans_le hr
  have hscale : 0 ≤
      ((max d 1 : ℕ) : ℝ) ^ 6 *
        (polyMax p - polyMin p) / (r : ℝ) ^ 4 := by
    positivity
  refine ⟨q, s, hqvalue, hsvalue, hsgap0, ?_, ?_⟩
  · linarith
  · calc
      polyMin p - q ≤
          Ap * ((max d 1 : ℕ) : ℝ) ^ 6 *
            (polyMax p - polyMin p) / (r : ℝ) ^ 4 := hqgap
      _ = Ap * (((max d 1 : ℕ) : ℝ) ^ 6 *
            (polyMax p - polyMin p) / (r : ℝ) ^ 4) := by ring
      _ ≤ (As + Ap) * (((max d 1 : ℕ) : ℝ) ^ 6 *
            (polyMax p - polyMin p) / (r : ℝ) ^ 4) := by
        exact mul_le_mul_of_nonneg_right (by linarith) hscale
      _ = (As + Ap) * ((max d 1 : ℕ) : ℝ) ^ 6 *
            (polyMax p - polyMin p) / (r : ℝ) ^ 4 := by ring

end QuarticConvergence
end OptimalConvergenceRates

end
