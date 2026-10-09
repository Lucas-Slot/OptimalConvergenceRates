/-
  Final all-polynomial quartic certificate and hierarchy results for both
  canonical cube cones.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarGeneralRate
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.CombinedRate

open MvPolynomial Finset Set

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- A single dimension-only perturbation puts every nonnegative cube
polynomial into both canonical cones at the same total-degree order. -/
theorem cubeExplicitRate_certificates {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (h : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        h.totalDegree ≤ d → IsNonnegOn h (Hypercube n) →
          c * max d 1 ≤ r →
          let error := A * ((max d 1 : ℕ) : ℝ) ^ 6 *
            polySupNorm h / (r : ℝ) ^ 4
          h + MvPolynomial.C error ∈ BoxQuadraticModule n r ∧
            h + MvPolynomial.C error ∈ BoxPreordering n r := by
  obtain ⟨A, c, hA, hc, hputinar⟩ := putinarExplicitRate_certificate hn
  refine ⟨A, c, hA, hc, ?_⟩
  intro h d r hdeg hnonnegative hr
  dsimp only
  have hqm := hputinar h d r hdeg hnonnegative hr
  exact ⟨hqm, BoxQuadraticModule_subset_BoxPreordering hqm⟩

/-- Final general cube theorem: at every sufficiently large canonical
total-degree order, both hierarchy bounds are real and their gaps satisfy

`0 ≤ Schmuedgen gap ≤ Putinar gap ≤ Aₙ (max d 1)^6 osc(f) / r^4`.

The constants are chosen before the polynomial, degree bound, and order, and
depend only on the positive cube dimension. -/
theorem cubeHierarchiesExplicitQuarticRate {n : ℕ} (hn : 0 < n) :
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
                (polyMax p - polyMin p) / (r : ℝ) ^ 4 :=
  combinedExplicitRate_of_controlledRoots hn
    (uniformControlledWeightedParityBound hn)

end QuarticConvergence
end OptimalConvergenceRates

end
