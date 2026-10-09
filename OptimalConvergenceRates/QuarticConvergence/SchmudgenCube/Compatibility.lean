/-
  Compatibility entry point for the canonical-order Schmüdgen rate and the
  repository's earlier box-preordering results.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.SchmudgenExplicitRate
import OptimalConvergenceRates.SlotLaurent2022.MainResults

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- The explicit quartic Schmüdgen certificate in the direct `WithBot` form
used by the earlier hierarchy-rate APIs.

Here `r` is the canonical total certificate-degree order itself, not the
kernel parameter whose legacy Slot--Laurent order is `(r + 1) * n`. -/
theorem schmudgenExplicitRateBoxPreoCanonicalOrder {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        p.totalDegree ≤ d → c * max d 1 ≤ r →
          ↑(polyMin p -
              A * ((max d 1 : ℕ) : ℝ) ^ 6 *
                (polyMax p - polyMin p) / (r : ℝ) ^ 4) ≤
            lasserre_bound_box_preo p r := by
  obtain ⟨A, c, hA, hc, hcertificate⟩ := schmudgenExplicitRate_certificate hn
  refine ⟨A, c, hA, hc, ?_⟩
  intro p d r hpdeg hr
  exact lasserre_bound_box_preo_ge_feasible p r
    (hcertificate p d r hpdeg hr)

end QuarticConvergence
end OptimalConvergenceRates

end
