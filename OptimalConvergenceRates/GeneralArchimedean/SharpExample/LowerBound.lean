import OptimalConvergenceRates.GeneralArchimedean.SharpExample.LowerBoundCore

noncomputable section

open Filter Asymptotics

namespace OptimalConvergenceRates.GeneralArchimedean

theorem eventually_sharpLowerConditions :
    ∀ᶠ r : Nat in atTop,
      3 <= r /\
      (100000 : Real) <= Real.log (r : Real) /\
      (8 : Real) * Real.log (r : Real)^8 <=
        (10 : Real)^32 * (r : Real) /\
      logFourOverSq r <= 1 := by
  have hcast : Tendsto (fun r : Nat => (r : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hthree : ∀ᶠ r : Nat in atTop, 3 <= r := eventually_ge_atTop 3
  have hlog : ∀ᶠ r : Nat in atTop,
      (100000 : Real) <= Real.log (r : Real) :=
    (Real.tendsto_log_atTop.comp hcast).eventually
      (eventually_ge_atTop (100000 : Real))
  have hdomReal : ∀ᶠ x : Real in atTop,
      (8 : Real) * Real.log x^8 <= (10 : Real)^32 * x := by
    have hbound := (Real.isLittleO_pow_log_id_atTop (n := 8)).bound
      (show (0 : Real) < (10 : Real)^32 / 8 by positivity)
    filter_upwards [hbound, eventually_ge_atTop (0 : Real)] with x hx hx0
    have hp : 0 <= Real.log x^8 := by positivity
    simp only [id_eq] at hx
    rw [Real.norm_of_nonneg hp, Real.norm_of_nonneg hx0] at hx
    nlinarith
  have hdom : ∀ᶠ r : Nat in atTop,
      (8 : Real) * Real.log (r : Real)^8 <=
        (10 : Real)^32 * (r : Real) := hcast.eventually hdomReal
  have hrateReal : ∀ᶠ x : Real in atTop,
      Real.log x^4 / x^2 <= 1 := by
    have hbound := (Real.isLittleO_pow_log_id_atTop (n := 4)).bound
      (show (0 : Real) < 1 by norm_num)
    filter_upwards [hbound, eventually_ge_atTop (1 : Real)] with x hx hx1
    have hp : 0 <= Real.log x^4 := by positivity
    simp only [id_eq] at hx
    rw [Real.norm_of_nonneg hp,
      Real.norm_of_nonneg (by linarith : 0 <= x)] at hx
    rw [div_le_iff₀ (sq_pos_of_pos (lt_of_lt_of_le (by norm_num) hx1))]
    nlinarith [sq_nonneg (x - 1)]
  have hrateRaw : ∀ᶠ r : Nat in atTop,
      Real.log (r : Real)^4 / (r : Real)^2 <= 1 :=
    hcast.eventually hrateReal
  filter_upwards [hthree, hlog, hdom, hrateRaw] with r hr hL hdomR hrateR
  refine ⟨hr, hL, hdomR, ?_⟩
  have hmax : max r 2 = r := max_eq_left (by omega)
  simpa [logFourOverSq, hmax] using hrateR



/-- A fixed positive constant for the sharp lower bound. -/
def sharpArchimedeanLowerConstant : Real :=
  1 / (2 * (10 : Real)^16)

theorem sharpArchimedean_logFour_over_sq_lower_pos :
    ∃ r0 : Nat, 0 < r0 /\
      ∀ r, r0 <= r -> ∀ eps : Real, 0 < eps ->
        sharpArchimedeanObjective + MvPolynomial.C eps ∈
            GenQuadraticModule sharpArchimedeanGenerators r ->
          sharpArchimedeanLowerConstant * logFourOverSq r <= eps := by
  obtain ⟨r0, hr0⟩ := eventually_atTop.mp eventually_sharpLowerConditions
  refine ⟨max r0 1, by omega, ?_⟩
  intro r hrr eps heps hcert
  have hcond := hr0 r (le_trans (le_max_left r0 1) hrr)
  rcases hcond with ⟨hr, hL, hdom, hrate⟩
  by_contra hnot
  have hepslt : eps < sharpArchimedeanLowerConstant * logFourOverSq r :=
    lt_of_not_ge hnot
  have hmax : max r 2 = r := max_eq_left (by omega)
  have hrR : (0 : Real) < (r : Real) := by positivity
  have hL0 : 0 < Real.log (r : Real) := by linarith
  have hrateEq : logFourOverSq r =
      Real.log (r : Real)^4 / (r : Real)^2 := by
    simp [logFourOverSq, hmax]
  have htRate : 2 * eps <
      Real.log (r : Real)^4 / ((10 : Real)^16 * (r : Real)^2) := by
    calc
      2 * eps < 2 *
          (sharpArchimedeanLowerConstant * logFourOverSq r) := by
        linarith
      _ = Real.log (r : Real)^4 /
          ((10 : Real)^16 * (r : Real)^2) := by
        rw [hrateEq]
        unfold sharpArchimedeanLowerConstant
        field_simp
  have htsmall : 2 * eps <= (1 : Real) / 64 := by
    have hc : (2 : Real) * sharpArchimedeanLowerConstant <= 1 / 64 := by
      unfold sharpArchimedeanLowerConstant
      norm_num
    have hrate0 : 0 <= logFourOverSq r := by
      rw [hrateEq]
      positivity
    calc
      2 * eps <= 2 * sharpArchimedeanLowerConstant * logFourOverSq r := by
        nlinarith [hepslt]
      _ <= ((1 : Real) / 64) * logFourOverSq r :=
        mul_le_mul_of_nonneg_right hc hrate0
      _ <= (1 : Real) / 64 := by
        nlinarith
  have hY0 : 0 <= Real.log (r : Real)^2 /
      ((10 : Real)^8 * (r : Real)) := by positivity
  have htY : 2 * eps <=
      (Real.log (r : Real)^2 / ((10 : Real)^8 * (r : Real)))^2 := by
    calc
      2 * eps <= Real.log (r : Real)^4 /
          ((10 : Real)^16 * (r : Real)^2) := htRate.le
      _ = (Real.log (r : Real)^2 /
          ((10 : Real)^8 * (r : Real)))^2 := by
        field_simp
  have hsqrt : Real.sqrt (2 * eps) <=
      Real.log (r : Real)^2 / ((10 : Real)^8 * (r : Real)) := by
    calc
      Real.sqrt (2 * eps) <= Real.sqrt
          ((Real.log (r : Real)^2 / ((10 : Real)^8 * (r : Real)))^2) :=
        Real.sqrt_le_sqrt htY
      _ = _ := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hY0]
  have hu : (r : Real) * Real.sqrt (2 * eps) <=
      Real.log (r : Real)^2 / 100000000 := by
    calc
      (r : Real) * Real.sqrt (2 * eps) <=
          (r : Real) *
            (Real.log (r : Real)^2 / ((10 : Real)^8 * (r : Real))) :=
        mul_le_mul_of_nonneg_left hsqrt hrR.le
      _ = Real.log (r : Real)^2 / 100000000 := by
        field_simp
        norm_num
  have hBsmall : (8 : Real) * (r : Real)^3 * (2 * eps)^2 <= 1 := by
    calc
      (8 : Real) * (r : Real)^3 * (2 * eps)^2 <=
          8 * (r : Real)^3 *
            (Real.log (r : Real)^4 /
              ((10 : Real)^16 * (r : Real)^2))^2 := by
        gcongr
      _ = (8 * Real.log (r : Real)^8) /
          ((10 : Real)^32 * (r : Real)) := by
        field_simp
      _ <= 1 := by
        rw [div_le_one (by positivity :
          0 < (10 : Real)^32 * (r : Real))]
        exact hdom
  exact sharpNoSmallCertificate hr heps htsmall hL hu hBsmall hcert

/-- Matching lower bound for the fixed Archimedean example, including the
endpoint `eps = 0`. -/
theorem sharpArchimedean_logFour_over_sq_lower :
    ∃ c r0, 0 < c /\
      0 < r0 /\
      ∀ r, r0 <= r -> ∀ eps : Real, 0 <= eps ->
        sharpArchimedeanObjective + MvPolynomial.C eps ∈
            GenQuadraticModule sharpArchimedeanGenerators r ->
          c * logFourOverSq r <= eps := by
  obtain ⟨r0, hr0, hlower⟩ :=
    sharpArchimedean_logFour_over_sq_lower_pos
  refine ⟨sharpArchimedeanLowerConstant, max r0 3, ?_, by omega, ?_⟩
  · unfold sharpArchimedeanLowerConstant
    positivity
  · intro r hrr eps heps hcert
    have hrr0 : r0 <= r := le_trans (le_max_left r0 3) hrr
    rcases heps.eq_or_lt with rfl | hepsPos
    · have hr3 : 3 <= r := le_trans (le_max_right r0 3) hrr
      have hmax : max r 2 = r := max_eq_left (by omega)
      have hlog : 0 < Real.log (r : Real) := by
        apply Real.log_pos
        exact_mod_cast (show 1 < r by omega)
      have hratePos : 0 < logFourOverSq r := by
        rw [logFourOverSq, hmax]
        positivity
      let delta : Real :=
        sharpArchimedeanLowerConstant * logFourOverSq r / 2
      have hdelta : 0 < delta := by
        dsimp [delta]
        exact div_pos (mul_pos (by
          unfold sharpArchimedeanLowerConstant
          positivity) hratePos) (by norm_num)
      have hconst : MvPolynomial.C delta ∈
          GenQuadraticModule sharpArchimedeanGenerators 0 :=
        genQuadraticModule_C_nonneg sharpArchimedeanGenerators hdelta.le
      have hconstR : MvPolynomial.C delta ∈
          GenQuadraticModule sharpArchimedeanGenerators r :=
        GenQuadraticModule_mono (Nat.zero_le r) hconst
      have hcertDelta :
          sharpArchimedeanObjective + MvPolynomial.C delta ∈
            GenQuadraticModule sharpArchimedeanGenerators r := by
        have hsum := GenQuadraticModule_add hcert hconstR
        simpa using hsum
      have hcontra := hlower r hrr0 delta hdelta hcertDelta
      dsimp [delta] at hcontra
      nlinarith
    · exact hlower r hrr0 eps hepsPos hcert
end OptimalConvergenceRates.GeneralArchimedean

end
