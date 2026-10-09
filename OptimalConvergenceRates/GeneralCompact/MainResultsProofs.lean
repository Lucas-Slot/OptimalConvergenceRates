/- Proof implementations for the public compact-domain Schmüdgen results. -/
import OptimalConvergenceRates.GeneralCompact.Hierarchy
import OptimalConvergenceRates.GeneralCompact.SharpBivariate.LowerBound
import OptimalConvergenceRates.GeneralArchimedean.LogRateInversion

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.GeneralCompact.MainResultsProofs

theorem upperRate :
    ∀ {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
        (p : MvPolynomial (Fin n) ℝ),
      (KrivineStengle.basicClosedSet g).Nonempty →
      IsCompact (KrivineStengle.basicClosedSet g) →
      IsNonnegOn p (KrivineStengle.basicClosedSet g) →
      ∃ C₀ r₀, 0 < C₀ ∧ 0 < r₀ ∧
        ∀ r, r₀ ≤ r →
          p + C (C₀ * (Real.log ((max r 2 : ℕ) : ℝ) ^ 2 / (r : ℝ) ^ 2)) ∈
            GenPreordering g r := by
  intro n m g p hne hcompact hp
  obtain ⟨C₀, r₀, hC₀, hr₀, hrate⟩ :=
    upperRate_of_degreeCostBound
      (hasSchmudgenDegreeCostBound_of_compact g p hne hcompact hp)
  refine ⟨C₀, r₀, hC₀, hr₀, ?_⟩
  intro r hr
  simpa [logTwoOverSq] using hrate r hr

theorem epsilonCertificate :
    ∀ {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
        (p : MvPolynomial (Fin n) ℝ),
      (KrivineStengle.basicClosedSet g).Nonempty →
      IsCompact (KrivineStengle.basicClosedSet g) →
      IsNonnegOn p (KrivineStengle.basicClosedSet g) →
      ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧
        ∀ {epsilon : ℝ}, 0 < epsilon → epsilon ≤ 2 →
          p + C epsilon ∈ GenPreordering g
            (Nat.ceil (D + K / Real.sqrt (epsilon / 2) *
              (1 + Real.log (epsilon / 2)⁻¹))) := by
  intro n m g p hne hcompact hp
  obtain ⟨D, K, hD, hK, hcert⟩ :=
    hasSchmudgenDegreeCostBound_of_compact g p hne hcompact hp
  refine ⟨D, K, hD, hK, ?_⟩
  intro epsilon hepsilon hepsilon2
  have hhalfpos : 0 < epsilon / 2 := by positivity
  have hhalf1 : epsilon / 2 ≤ 1 := by linarith
  have heq : 2 * (epsilon / 2) = epsilon := by ring
  simpa only [schmudgenDegreeCost, heq] using hcert hhalfpos hhalf1

theorem lasserreRate :
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
              ↑(GeneralArchimedean.polynomialMinimum g f) := by
  intro n m g f hne hcompact
  let p := f - C (GeneralArchimedean.polynomialMinimum g f)
  have hp : IsNonnegOn p (KrivineStengle.basicClosedSet g) := by
    dsimp [p]
    exact centered_nonnegOn_of_compact hcompact f
  obtain ⟨C₀, r₀, hC₀, hr₀, hcert⟩ :=
    upperRate_of_degreeCostBound
      (hasSchmudgenDegreeCostBound_of_compact g p hne hcompact hp)
  refine ⟨C₀, r₀, hC₀, hr₀, ?_⟩
  intro r hr
  have hrate := lasserrePO_rate_of_centered_certificate
    hne hcompact f C₀ r₀ (by
      intro s hs
      simpa [p] using hcert s hs) r hr
  simpa [logTwoOverSq] using hrate

theorem sharpRate :
    ∃ c C₀ r₀, 0 < c ∧ 0 < C₀ ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        sharpObjective + C (C₀ *
            (Real.log ((max r 2 : ℕ) : ℝ) ^ 2 / (r : ℝ) ^ 2)) ∈
            GenPreordering sharpGenerators r ∧
          ∀ ε, 0 ≤ ε →
            sharpObjective + C ε ∈ GenPreordering sharpGenerators r →
              c * (Real.log ((max r 2 : ℕ) : ℝ) ^ 2 / (r : ℝ) ^ 2) ≤ ε := by
  obtain ⟨C₀, upperOrder, hC₀, hupperOrder, hupper⟩ :=
    upperRate_of_degreeCostBound
      (hasSchmudgenDegreeCostBound_of_compact sharpGenerators
        sharpObjective sharp_set_nonempty sharp_set_compact
        sharpObjective_nonnegOn)
  obtain ⟨c, lowerOrder, hc, hlowerOrder, hlower⟩ :=
    sharpCompact_logTwo_over_sq_lower
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

theorem sharpDegreeLowerBound :
    ∃ c epsilon₀ : ℝ, 0 < c ∧ 0 < epsilon₀ ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∀ r : ℕ,
          sharpObjective + C epsilon ∈ GenPreordering sharpGenerators r →
            c * Real.log epsilon⁻¹ / Real.sqrt epsilon ≤ (r : ℝ) := by
  obtain ⟨a, rLower, ha, _hrLower, hLower⟩ :=
    sharpCompact_logTwo_over_sq_lower
  obtain ⟨rLog, hLog⟩ := Filter.eventually_atTop.mp
    GeneralArchimedean.eventually_sharpLowerConditions
  let R := max rLower rLog
  have hRLower : rLower ≤ R := Nat.le_max_left _ _
  have hRLog : rLog ≤ R := Nat.le_max_right _ _
  have hRConditions := hLog R hRLog
  have hRThree : 3 ≤ R := hRConditions.1
  have hRLogLarge : (100000 : ℝ) ≤ Real.log (R : ℝ) := hRConditions.2.1
  have hRMax : max R 2 = R := max_eq_left (by omega)
  have hRRatePos : 0 < logTwoOverSq R := by
    rw [logTwoOverSq, hRMax]
    positivity
  let epsilon₀ := min 1 (a * logTwoOverSq R / 2)
  let c := Real.sqrt a / (2 + |Real.log a|)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hepsilon₀ : 0 < epsilon₀ := by
    dsimp [epsilon₀]
    exact lt_min one_pos (div_pos (mul_pos ha hRRatePos) (by norm_num))
  refine ⟨c, epsilon₀, hc, hepsilon₀, ?_⟩
  intro epsilon hepsilon hepsilon₀Bound r hcertificate
  have hepsilonOne : epsilon ≤ 1 :=
    hepsilon₀Bound.trans (min_le_left _ _)
  have hRle : R ≤ r := by
    by_contra hnot
    have hrR : r ≤ R := Nat.le_of_lt (Nat.lt_of_not_ge hnot)
    have hcertificateR := GenPreordering_mono hrR hcertificate
    have hlowerR := hLower R hRLower epsilon hepsilon.le hcertificateR
    have hepsilonHalf : epsilon ≤ a * logTwoOverSq R / 2 :=
      hepsilon₀Bound.trans (min_le_right _ _)
    nlinarith
  have hrConditions := hLog r (hRLog.trans hRle)
  have hrThree : 3 ≤ r := hrConditions.1
  have hrLog : 1 ≤ Real.log (r : ℝ) := by
    linarith [hrConditions.2.1]
  have hrPos : 0 < (r : ℝ) := by positivity
  have hrMax : max r 2 = r := max_eq_left (by omega)
  have hlower := hLower r (hRLower.trans hRle) epsilon hepsilon.le hcertificate
  have hrate :
      a * Real.log (r : ℝ) ^ 2 / (r : ℝ) ^ 2 ≤ epsilon := by
    rw [logTwoOverSq, hrMax] at hlower
    calc
      a * Real.log (r : ℝ) ^ 2 / (r : ℝ) ^ 2 =
          a * (Real.log (r : ℝ) ^ 2 / (r : ℝ) ^ 2) := by ring
      _ ≤ epsilon := hlower
  simpa only [c] using
    GeneralArchimedean.inverseSqrtLog_le_of_logTwo_rate
      ha hepsilon hepsilonOne hrPos hrLog hrate

end OptimalConvergenceRates.GeneralCompact.MainResultsProofs

end
