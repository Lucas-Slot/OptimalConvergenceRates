import OptimalConvergenceRates.GeneralArchimedean.MainResultStatements
import OptimalConvergenceRates.KrivineStengle.MainResults
import OptimalConvergenceRates.GeneralArchimedean.QualitativePutinar
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.Geometry
import OptimalConvergenceRates.GeneralArchimedean.UpperBoundAssembly
import OptimalConvergenceRates.GeneralArchimedean.GeneralLasserre
import OptimalConvergenceRates.GeneralArchimedean.UpperBound
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.LowerBound
import OptimalConvergenceRates.GeneralArchimedean.LogRateInversion

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

theorem generalArchimedeanUpperRate_of_degreeCost
    (hcost : ∀ {n m : ℕ}
      (g : Fin m → MvPolynomial (Fin n) ℝ)
      (p : MvPolynomial (Fin n) ℝ),
      (KrivineStengle.basicClosedSet g).Nonempty →
      IsArchimedean g →
      IsNonnegOn p (KrivineStengle.basicClosedSet g) →
      HasPutinarDegreeCostBound g p) :
    GeneralArchimedeanUpperRateStatement := by
  intro n m g p hne harch hp
  exact upperRate_of_degreeCostBound (hcost g p hne harch hp)

theorem generalArchimedean_logFour_over_sq_certificate
    {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ C₀ r₀, 0 < C₀ ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        p + C (C₀ * (Real.log ((max r 2 : ℕ) : ℝ) ^ 4 / (r : ℝ) ^ 2)) ∈
          GenQuadraticModule g r :=
  upperRate_of_degreeCostBound
    (hasPutinarDegreeCostBound_of_archimedean g p hne harch hp)

theorem generalArchimedeanUpperRate_proof :
    GeneralArchimedeanUpperRateStatement := by
  intro n m g p hne harch hp
  exact generalArchimedean_logFour_over_sq_certificate g p hne harch hp

theorem generalArchimedeanEpsilonCertificate_proof :
    ∀ {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
        (p : MvPolynomial (Fin n) ℝ),
      (KrivineStengle.basicClosedSet g).Nonempty →
      IsArchimedean g →
      IsNonnegOn p (KrivineStengle.basicClosedSet g) →
      ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧
        ∀ {epsilon : ℝ}, 0 < epsilon → epsilon ≤ 1 →
          p + C epsilon ∈ GenQuadraticModule g
            (Nat.ceil (D + K / Real.sqrt epsilon *
              (1 + Real.log epsilon⁻¹) ^ 2)) := by
  intro n m g p hne harch hp
  simpa only [HasPutinarDegreeCostBound, putinarDegreeCost] using
    hasPutinarDegreeCostBound_of_archimedean g p hne harch hp

theorem generalArchimedean_logFour_over_sq_lasserre_proof :
    GeneralArchimedeanLasserreRateStatement := by
  intro n m g f hne harch
  obtain ⟨C₀, r₀, hC₀, hr₀, hcert⟩ :=
    generalArchimedean_logFour_over_sq_certificate g
      (f - C (polynomialMinimum g f)) hne harch
      (centered_nonnegOn harch f)
  refine ⟨C₀, r₀, hC₀, hr₀, ?_⟩
  exact lasserre_rate_of_centered_certificate hne harch f C₀ r₀ hcert

theorem sharpArchimedean_logFour_over_sq_upper :
    ∃ C₀ r₀, 0 < C₀ ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        sharpArchimedeanObjective +
            C (C₀ * (Real.log ((max r 2 : ℕ) : ℝ) ^ 4 / (r : ℝ) ^ 2)) ∈
          GenQuadraticModule sharpArchimedeanGenerators r :=
  generalArchimedean_logFour_over_sq_certificate
    sharpArchimedeanGenerators sharpArchimedeanObjective
    sharpArchimedean_set_nonempty sharpArchimedean_isArchimedean
    sharpArchimedeanObjective_nonnegOn

theorem sharpArchimedeanExample_logFour_over_sq :
    SharpArchimedeanRateStatement := by
  obtain ⟨C0, rUpper, hC0, hrUpper, hUpper⟩ :=
    sharpArchimedean_logFour_over_sq_upper
  obtain ⟨c, rLower, hc, hrLower, hLower⟩ :=
    sharpArchimedean_logFour_over_sq_lower
  refine ⟨c, C0, max rUpper rLower, hc, hC0, ?_, ?_⟩
  · omega
  · intro r hrr
    have hrU : rUpper ≤ r := (Nat.le_max_left rUpper rLower).trans hrr
    have hrL : rLower ≤ r := (Nat.le_max_right rUpper rLower).trans hrr
    refine ⟨hUpper r hrU, ?_⟩
    intro eps heps hcert
    exact hLower r hrL eps heps hcert

theorem sharpArchimedeanRate_proof : SharpArchimedeanRateStatement :=
  sharpArchimedeanExample_logFour_over_sq

theorem sharpArchimedeanDegreeLowerBound_proof :
    ∃ c epsilon₀ : ℝ, 0 < c ∧ 0 < epsilon₀ ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∀ r : ℕ,
          sharpArchimedeanObjective + C epsilon ∈
              GenQuadraticModule sharpArchimedeanGenerators r →
            c * Real.log epsilon⁻¹ ^ 2 / Real.sqrt epsilon ≤ (r : ℝ) := by
  obtain ⟨a, rLower, ha, _hrLower, hLower⟩ :=
    sharpArchimedean_logFour_over_sq_lower
  obtain ⟨rLog, hLog⟩ := Filter.eventually_atTop.mp eventually_sharpLowerConditions
  let R := max rLower rLog
  have hRLower : rLower ≤ R := Nat.le_max_left _ _
  have hRLog : rLog ≤ R := Nat.le_max_right _ _
  have hRConditions := hLog R hRLog
  have hRThree : 3 ≤ R := hRConditions.1
  have hRLogLarge : (100000 : ℝ) ≤ Real.log (R : ℝ) := hRConditions.2.1
  have hRMax : max R 2 = R := max_eq_left (by omega)
  have hRRatePos : 0 < logFourOverSq R := by
    rw [logFourOverSq, hRMax]
    positivity
  let epsilon₀ := min 1 (a * logFourOverSq R / 2)
  let c := Real.sqrt a / (2 + |Real.log a|) ^ 2
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
    have hcertificateR := GenQuadraticModule_mono hrR hcertificate
    have hlowerR := hLower R hRLower epsilon hepsilon.le hcertificateR
    have hepsilonHalf : epsilon ≤ a * logFourOverSq R / 2 :=
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
      a * Real.log (r : ℝ) ^ 4 / (r : ℝ) ^ 2 ≤ epsilon := by
    rw [logFourOverSq, hrMax] at hlower
    calc
      a * Real.log (r : ℝ) ^ 4 / (r : ℝ) ^ 2 =
          a * (Real.log (r : ℝ) ^ 4 / (r : ℝ) ^ 2) := by ring
      _ ≤ epsilon := hlower
  simpa only [c] using
    inverseSqrtLogSq_le_of_logFour_rate ha hepsilon hepsilonOne hrPos hrLog hrate

theorem generalArchimedean_putinar
    {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (harch : IsArchimedean g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g))
    {ε : ℝ} (hε : 0 < ε) :
    QuadraticModuleMem g (p + C ε) :=
  qualitative_putinar g p harch hp hε

theorem sharpArchimedean_qualitative_putinar
    {ε : ℝ} (hε : 0 < ε) :
    QuadraticModuleMem sharpArchimedeanGenerators
      (sharpArchimedeanObjective + C ε) :=
  qualitative_putinar sharpArchimedeanGenerators sharpArchimedeanObjective
    sharpArchimedean_isArchimedean sharpArchimedeanObjective_nonnegOn hε

end OptimalConvergenceRates.GeneralArchimedean

end
