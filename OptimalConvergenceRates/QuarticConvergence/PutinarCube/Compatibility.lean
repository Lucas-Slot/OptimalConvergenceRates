/-
  Compatibility entry point for the canonical-order Putinar rate and the
  repository's earlier box quadratic-module results.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarGeneralRate
import OptimalConvergenceRates.BaldiSlot2024.MainResults

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- The explicit quartic Putinar rate in the direct `WithBot` form used by
the Baldi--Slot hierarchy API, at the canonical total-degree order. -/
theorem putinarExplicitRateBoxQMCanonicalOrder {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        p.totalDegree ≤ d → c * max d 1 ≤ r →
          ↑(polyMin p -
              A * ((max d 1 : ℕ) : ℝ) ^ 6 *
                (polyMax p - polyMin p) / (r : ℝ) ^ 4) ≤
            lasserre_bound_box_qm p r := by
  obtain ⟨A, c, hA, hc, hgap⟩ := putinarExplicitRate_lasserreGap hn
  refine ⟨A, c, hA, hc, ?_⟩
  intro p d r hpdeg hr
  obtain ⟨ℓ, hℓ, _hlower, hupper⟩ := hgap p d r hpdeg hr
  rw [hℓ, WithBot.coe_le_coe]
  linarith

/-- At the same canonical total-degree order, the quadratic-module lower
bound is bounded above by the preordering lower bound. -/
theorem canonicalCubeHierarchyComparison {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (r : ℕ) :
    lasserre_bound_box_qm p r ≤ lasserre_bound_box_preo p r :=
  lasserre_bound_box_qm_le p r

end QuarticConvergence
end OptimalConvergenceRates

end
