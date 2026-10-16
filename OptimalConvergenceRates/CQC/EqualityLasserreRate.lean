import OptimalConvergenceRates.CQC.EqualityQuarticRate
import OptimalConvergenceRates.GeneralArchimedean.GeneralLasserre

/-! # Generalized Lasserre error under CQC -/

noncomputable section
open MvPolynomial
namespace OptimalConvergenceRates.CQCInternal
open GeneralArchimedean
variable {n m : ℕ}

theorem lasserreQuarticRateWithEqualities_internal
    (hn : 0 < n)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (f : MvPolynomial (Fin n) ℝ)
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hcqc : CQCWithEqualities g) :
    ∃ A : ℝ, ∃ r₀ : ℕ, 0 < A ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        ((polynomialMinimum g f - A / (r : ℝ) ^ 4 : ℝ) : WithBot ℝ) ≤
            genLasserreBoundQM g f r ∧
          genLasserreBoundQM g f r ≤
            (polynomialMinimum g f : WithBot ℝ) := by
  let p := f - C (polynomialMinimum g f)
  have hp : IsNonnegOn p (KrivineStengle.basicClosedSet g) := by
    simpa [p] using centered_nonnegOn harch f
  obtain ⟨A, r₀, hA, hr₀, hcert⟩ :=
    putinarQuarticRateWithEqualities_internal hn hne harch hcqc hp
  refine ⟨A, r₀, hA, hr₀, ?_⟩
  intro r hr
  have hcentered : f - C (polynomialMinimum g f) +
      C (A / (r : ℝ) ^ 4) ∈ GenQuadraticModule g r := by
    simpa [p] using hcert r hr
  exact ⟨genLasserreBoundQM_ge_of_centered_certificate hne harch f r hcentered,
    genLasserreBoundQM_le_polynomialMinimum hne harch f r⟩

end OptimalConvergenceRates.CQCInternal
end
