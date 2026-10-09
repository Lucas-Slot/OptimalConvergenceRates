import OptimalConvergenceRates.GeneralArchimedean.SharpExample.Defs

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

/-- Locked statement of the general quantitative certificate theorem. -/
def GeneralArchimedeanUpperRateStatement : Prop :=
  ∀ {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
      (p : MvPolynomial (Fin n) ℝ),
    (KrivineStengle.basicClosedSet g).Nonempty →
    IsArchimedean g →
    IsNonnegOn p (KrivineStengle.basicClosedSet g) →
    ∃ C₀ r₀, 0 < C₀ ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        p + C (C₀ * (Real.log ((max r 2 : ℕ) : ℝ) ^ 4 / (r : ℝ) ^ 2)) ∈
          GenQuadraticModule g r

/-- Locked statement of the corresponding generalized Lasserre bound. -/
def GeneralArchimedeanLasserreRateStatement : Prop :=
  ∀ {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
      (f : MvPolynomial (Fin n) ℝ),
    (KrivineStengle.basicClosedSet g).Nonempty →
    IsArchimedean g →
    ∃ C₀ r₀, 0 < C₀ ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        (↑((polynomialMinimum g f - C₀ *
          (Real.log ((max r 2 : ℕ) : ℝ) ^ 4 / (r : ℝ) ^ 2)) : ℝ) : WithBot ℝ) ≤
            genLasserreBoundQM g f r ∧
          genLasserreBoundQM g f r ≤ ↑(polynomialMinimum g f)

/-- Locked statement of the matching fixed Archimedean example. -/
def SharpArchimedeanRateStatement : Prop :=
  ∃ c C₀ r₀, 0 < c ∧ 0 < C₀ ∧ 0 < r₀ ∧
    ∀ r, r₀ ≤ r →
      sharpArchimedeanObjective +
          C (C₀ * (Real.log ((max r 2 : ℕ) : ℝ) ^ 4 / (r : ℝ) ^ 2)) ∈
          GenQuadraticModule sharpArchimedeanGenerators r ∧
        ∀ ε, 0 ≤ ε →
          sharpArchimedeanObjective + C ε ∈
              GenQuadraticModule sharpArchimedeanGenerators r →
            c * (Real.log ((max r 2 : ℕ) : ℝ) ^ 4 / (r : ℝ) ^ 2) ≤ ε

end OptimalConvergenceRates.GeneralArchimedean

end
