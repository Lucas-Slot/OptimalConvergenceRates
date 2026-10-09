/-
  Formal consequences of the general certificate-rate statement.
-/
import OptimalConvergenceRates.GeneralArchimedean.GeneralLasserre
import OptimalConvergenceRates.GeneralArchimedean.MainResultStatements
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.Geometry

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

/-- The certificate-rate theorem implies the generalized Lasserre-rate theorem. -/
theorem generalLasserreRate_of_generalUpperRate
    (hupper : GeneralArchimedeanUpperRateStatement) :
    GeneralArchimedeanLasserreRateStatement := by
  intro n m g f hK harch
  have hcentered := centered_nonnegOn harch f
  obtain ⟨C₀, r₀, hC₀, hr₀, hcert⟩ :=
    hupper g (f - C (polynomialMinimum g f)) hK harch hcentered
  refine ⟨C₀, r₀, hC₀, hr₀, ?_⟩
  exact lasserre_rate_of_centered_certificate hK harch f C₀ r₀ hcert

/-- The general upper theorem specializes to the fixed sharp example. -/
theorem sharpArchimedean_upper_of_generalUpperRate
    (hupper : GeneralArchimedeanUpperRateStatement) :
    ∃ C₀ r₀, 0 < C₀ ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        sharpArchimedeanObjective + C (C₀ * logFourOverSq r) ∈
          GenQuadraticModule sharpArchimedeanGenerators r := by
  exact hupper sharpArchimedeanGenerators sharpArchimedeanObjective
    sharpArchimedean_set_nonempty sharpArchimedean_isArchimedean
    sharpArchimedeanObjective_nonnegOn

end OptimalConvergenceRates.GeneralArchimedean

end
