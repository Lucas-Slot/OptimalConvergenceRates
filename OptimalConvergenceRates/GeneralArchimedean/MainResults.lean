import OptimalConvergenceRates.GeneralArchimedean.MainResultsProofs

/-!
# General Archimedean Putinar rates

This file is the readable public statement layer. All proofs and auxiliary
statement abbreviations live in supporting files.
-/

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

/-- Every nonnegative polynomial on a nonempty Archimedean basic closed set
has Putinar certificates with perturbation `O((log r)^4 / r^2)`. -/
theorem generalArchimedeanUpperRate :
    ∀ {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
        (p : MvPolynomial (Fin n) ℝ),
      (KrivineStengle.basicClosedSet g).Nonempty →
      IsArchimedean g →
      IsNonnegOn p (KrivineStengle.basicClosedSet g) →
      ∃ C₀ r₀, 0 < C₀ ∧ 0 < r₀ ∧
        ∀ r, r₀ ≤ r →
          p + C (C₀ * (Real.log ((max r 2 : ℕ) : ℝ) ^ 4 / (r : ℝ) ^ 2)) ∈
            GenQuadraticModule g r :=
  generalArchimedeanUpperRate_proof

/-- Inverse form of the general Archimedean rate: a perturbation `epsilon`
has a certificate at square-root/log-squared degree. -/
theorem generalArchimedeanEpsilonCertificate :
    ∀ {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
        (p : MvPolynomial (Fin n) ℝ),
      (KrivineStengle.basicClosedSet g).Nonempty →
      IsArchimedean g →
      IsNonnegOn p (KrivineStengle.basicClosedSet g) →
      ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧
        ∀ {epsilon : ℝ}, 0 < epsilon → epsilon ≤ 1 →
          p + C epsilon ∈ GenQuadraticModule g
            (Nat.ceil (D + K / Real.sqrt epsilon *
              (1 + Real.log epsilon⁻¹) ^ 2)) :=
  generalArchimedeanEpsilonCertificate_proof

/-- The generalized Lasserre hierarchy has error
`O((log r)^4 / r^2)` on every nonempty Archimedean basic closed set. -/
theorem generalArchimedean_logFour_over_sq_lasserre :
    ∀ {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
        (f : MvPolynomial (Fin n) ℝ),
      (KrivineStengle.basicClosedSet g).Nonempty →
      IsArchimedean g →
      ∃ C₀ r₀, 0 < C₀ ∧ 0 < r₀ ∧
        ∀ r, r₀ ≤ r →
          (↑((polynomialMinimum g f - C₀ *
            (Real.log ((max r 2 : ℕ) : ℝ) ^ 4 / (r : ℝ) ^ 2)) : ℝ) : WithBot ℝ) ≤
              genLasserreBoundQM g f r ∧
            genLasserreBoundQM g f r ≤ ↑(polynomialMinimum g f) :=
  generalArchimedean_logFour_over_sq_lasserre_proof

/-- The fixed three-variable Archimedean example has matching upper and lower
certificate rates of order `(log r)^4 / r^2`. -/
theorem sharpArchimedeanRate :
    ∃ c C₀ r₀, 0 < c ∧ 0 < C₀ ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        sharpArchimedeanObjective +
            C (C₀ * (Real.log ((max r 2 : ℕ) : ℝ) ^ 4 / (r : ℝ) ^ 2)) ∈
            GenQuadraticModule sharpArchimedeanGenerators r ∧
          ∀ ε, 0 ≤ ε →
            sharpArchimedeanObjective + C ε ∈
                GenQuadraticModule sharpArchimedeanGenerators r →
              c * (Real.log ((max r 2 : ℕ) : ℝ) ^ 4 / (r : ℝ) ^ 2) ≤ ε :=
  sharpArchimedeanRate_proof

/-- Inverse form of the sharp logarithmic lower rate: sufficiently small
perturbations require degree at least a constant multiple of
`log(epsilon⁻¹)^2 / sqrt epsilon`. -/
theorem sharpArchimedeanDegreeLowerBound :
    ∃ c epsilon₀ : ℝ, 0 < c ∧ 0 < epsilon₀ ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∀ r : ℕ,
          sharpArchimedeanObjective + C epsilon ∈
              GenQuadraticModule sharpArchimedeanGenerators r →
            c * Real.log epsilon⁻¹ ^ 2 / Real.sqrt epsilon ≤ (r : ℝ) :=
  sharpArchimedeanDegreeLowerBound_proof

end OptimalConvergenceRates.GeneralArchimedean

end
