/- Additional public compact-domain Schmüdgen consequences. -/
import OptimalConvergenceRates.GeneralCompact.MainResults
import OptimalConvergenceRates.GeneralCompact.OriginalExample

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.GeneralCompact
/-- The original three-variable example also realizes the compact-domain
preordering rate. -/
theorem originalExampleCompactRate :
    ∃ c C₀ r₀, 0 < c ∧ 0 < C₀ ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        GeneralArchimedean.sharpArchimedeanObjective +
            C (C₀ * (Real.log ((max r 2 : ℕ) : ℝ) ^ 2 /
              (r : ℝ) ^ 2)) ∈
          GenPreordering
            GeneralArchimedean.sharpArchimedeanGenerators r ∧
        ∀ epsilon, 0 ≤ epsilon →
          GeneralArchimedean.sharpArchimedeanObjective + C epsilon ∈
            GenPreordering
              GeneralArchimedean.sharpArchimedeanGenerators r →
          c * (Real.log ((max r 2 : ℕ) : ℝ) ^ 2 /
            (r : ℝ) ^ 2) ≤ epsilon := by
  obtain ⟨C₀, upperOrder, hC₀, hupperOrder, hupper⟩ :=
    originalExample_upper_rate
  obtain ⟨c, lowerOrder, hc, hlowerOrder, hlower⟩ :=
    originalExample_logTwo_over_sq_lower
  refine ⟨c, C₀, max upperOrder lowerOrder, hc, hC₀, by omega, ?_⟩
  intro r hr
  have hru : upperOrder ≤ r :=
    (le_max_left upperOrder lowerOrder).trans hr
  have hrl : lowerOrder ≤ r :=
    (le_max_right upperOrder lowerOrder).trans hr
  constructor
  · simpa [logTwoOverSq] using hupper r hru
  · intro epsilon hepsilon hcertificate
    have hbound := hlower r hrl epsilon hepsilon hcertificate
    simpa [logTwoOverSq] using hbound


end OptimalConvergenceRates.GeneralCompact
end
