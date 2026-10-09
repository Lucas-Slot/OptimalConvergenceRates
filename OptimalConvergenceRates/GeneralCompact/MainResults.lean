/-
  Locked public theorems for the compact-domain Schmüdgen rate and its
  matching fixed bivariate example.
-/
import OptimalConvergenceRates.GeneralCompact.MainResultsProofs

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.GeneralCompact

/-- Every fixed nonnegative polynomial on a nonempty compact basic closed
set has preordering certificates at the sharp universal rate. -/
theorem generalCompactUpperRate :
  ∀ {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
      (p : MvPolynomial (Fin n) ℝ),
    (KrivineStengle.basicClosedSet g).Nonempty →
    IsCompact (KrivineStengle.basicClosedSet g) →
    IsNonnegOn p (KrivineStengle.basicClosedSet g) →
    ∃ C₀ r₀, 0 < C₀ ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        p + C (C₀ * (Real.log ((max r 2 : ℕ) : ℝ) ^ 2 / (r : ℝ) ^ 2)) ∈
          GenPreordering g r :=
  MainResultsProofs.upperRate

/-- Inverse form of the compact-domain Schmüdgen rate: a perturbation
`epsilon` has a certificate at square-root/single-log degree. -/
theorem generalCompactEpsilonCertificate :
    ∀ {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
        (p : MvPolynomial (Fin n) ℝ),
      (KrivineStengle.basicClosedSet g).Nonempty →
      IsCompact (KrivineStengle.basicClosedSet g) →
      IsNonnegOn p (KrivineStengle.basicClosedSet g) →
      ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧
        ∀ {epsilon : ℝ}, 0 < epsilon → epsilon ≤ 2 →
          p + C epsilon ∈ GenPreordering g
            (Nat.ceil (D + K / Real.sqrt (epsilon / 2) *
              (1 + Real.log (epsilon / 2)⁻¹))) :=
  MainResultsProofs.epsilonCertificate

/-- The generalized Schmüdgen bounds converge to the true minimum at the
same sharp universal rate. -/
theorem generalCompactLasserreRate :
  ∀ {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
      (f : MvPolynomial (Fin n) ℝ),
    (KrivineStengle.basicClosedSet g).Nonempty →
    IsCompact (KrivineStengle.basicClosedSet g) →
    ∃ C₀ r₀, 0 < C₀ ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        (↑((GeneralArchimedean.polynomialMinimum g f - C₀ *
          (Real.log ((max r 2 : ℕ) : ℝ) ^ 2 / (r : ℝ) ^ 2)) : ℝ) : WithBot ℝ) ≤
            genLasserreBoundPO g f r ∧
          genLasserreBoundPO g f r ≤
            ↑(GeneralArchimedean.polynomialMinimum g f) :=
  MainResultsProofs.lasserreRate

/-- The fixed linear-objective, cubic-generator bivariate example has
matching upper and lower preordering certificate rates. -/
theorem sharpCompactRate :
  ∃ c C₀ r₀, 0 < c ∧ 0 < C₀ ∧ 0 < r₀ ∧
    ∀ r, r₀ ≤ r →
      sharpObjective + C (C₀ *
          (Real.log ((max r 2 : ℕ) : ℝ) ^ 2 / (r : ℝ) ^ 2)) ∈
          GenPreordering sharpGenerators r ∧
        ∀ ε, 0 ≤ ε →
          sharpObjective + C ε ∈ GenPreordering sharpGenerators r →
            c * (Real.log ((max r 2 : ℕ) : ℝ) ^ 2 / (r : ℝ) ^ 2) ≤ ε :=
  MainResultsProofs.sharpRate

/-- Inverse form of the sharp compact lower rate: sufficiently small
perturbations require degree at least a constant multiple of
`log(epsilon⁻¹) / sqrt epsilon`. -/
theorem sharpCompactDegreeLowerBound :
    ∃ c epsilon₀ : ℝ, 0 < c ∧ 0 < epsilon₀ ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∀ r : ℕ,
          sharpObjective + C epsilon ∈ GenPreordering sharpGenerators r →
            c * Real.log epsilon⁻¹ / Real.sqrt epsilon ≤ (r : ℝ) :=
  MainResultsProofs.sharpDegreeLowerBound

end OptimalConvergenceRates.GeneralCompact

end
