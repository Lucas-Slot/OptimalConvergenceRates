import OptimalConvergenceRates.SphereDimensionBounds.Foundation.RateAssembly

/-! Arithmetic for the degree-amplified lower bound in the original order.
The two input regimes refer to one fixed polynomial and one gap value. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.DegreeAmplificationRate

open OptimalConvergenceRates.SphereDimensionBounds.Foundation

def degreeRateConstant (ρ : ℝ) (D : ℕ) : ℝ :=
  cubicRateConstant ρ D / (6 : ℝ)^4

theorem degreeRateConstant_pos (ρ : ℝ) (D : ℕ) (hρ : 0 < ρ) (hD : 0 < D) :
    0 < degreeRateConstant ρ D := by
  exact div_pos (cubicRateConstant_pos ρ D hρ hD) (by norm_num)

theorem degreeRateConstant_le_saturation (ρ : ℝ) (D : ℕ) (hD : 0 < D) :
    degreeRateConstant ρ D ≤ ρ^4 / (8712 * 64) := by
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD4 : (1 : ℝ) ≤ (D : ℝ)^4 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hDr 4
  unfold degreeRateConstant cubicRateConstant
  rw [div_div]
  apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
  nlinarith

theorem degree_rate_low (N D : ℕ) (hN : 0 < N) (hD : 0 < D)
    (ρ g : ℝ) (hlow : (1 / (8712 * (N : ℝ))) * ρ ^ 4 / 64 ≤ g) :
    degreeRateConstant ρ D * (1 / ((N + 2 : ℕ) : ℝ)) ≤ g := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hn : (N : ℝ) ≤ ((N + 2 : ℕ) : ℝ) := by push_cast; linarith
  calc
    degreeRateConstant ρ D * (1 / ((N + 2 : ℕ) : ℝ)) ≤
        (ρ^4 / (8712 * 64)) * (1 / ((N + 2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right (degreeRateConstant_le_saturation ρ D hD) (by positivity)
    _ ≤ (ρ^4 / (8712 * 64)) * (1 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hNr hn) (by positivity)
    _ = (1 / (8712 * (N : ℝ))) * ρ^4 / 64 := by ring
    _ ≤ g := hlow

theorem degree_rate_high (N D ell d r : ℕ) (hD : 0 < D) (hND : D ≤ N)
    (hNtwo : 2 ≤ N) (hr : 0 < r) (hd : d ≤ 6 * ell)
    (ρ g : ℝ) (hρ : 0 < ρ)
    (hhigh : (1 / (8712 * (N : ℝ))) *
      ((ell : ℝ) * ρ * ((N / D : ℕ) : ℝ) / (r : ℝ)) ^ 4 / 64 ≤ g) :
    degreeRateConstant ρ D *
      ((d : ℝ)^4 * ((N + 2 : ℕ) : ℝ)^3 / (r : ℝ)^4) ≤ g := by
  have hdiv : (d : ℝ) / 6 ≤ (ell : ℝ) := by
    have hcast : (d : ℝ) ≤ 6 * (ell : ℝ) := by exact_mod_cast hd
    linarith
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (d : ℝ) / 6) hdiv 4
  have hconstant : degreeRateConstant ρ D * (d : ℝ)^4 ≤
      cubicRateConstant ((ell : ℝ) * ρ) D := by
    have hcmp := mul_le_mul_of_nonneg_left hpow (cubicRateConstant_pos ρ D hρ hD).le
    convert hcmp using 1 <;> simp only [degreeRateConstant, cubicRateConstant] <;> ring
  have hbase := cubic_rate_high N D r hD hND hNtwo hr ((ell : ℝ) * ρ) g hhigh
  calc
    degreeRateConstant ρ D * ((d : ℝ)^4 * ((N + 2 : ℕ) : ℝ)^3 / (r : ℝ)^4) =
        (degreeRateConstant ρ D * (d : ℝ)^4) *
          (((N + 2 : ℕ) : ℝ)^3 / (r : ℝ)^4) := by ring
    _ ≤ cubicRateConstant ((ell : ℝ) * ρ) D *
          (((N + 2 : ℕ) : ℝ)^3 / (r : ℝ)^4) :=
      mul_le_mul_of_nonneg_right hconstant (by positivity)
    _ ≤ g := hbase

theorem degree_rate_of_two_regimes (N D ell d r : ℕ) (hD : 0 < D) (hND : D ≤ N)
    (hNtwo : 2 ≤ N) (hr : 2 ≤ r) (hd : d ≤ 6 * ell)
    (ρ : ℝ) (hρ : 0 < ρ) (g : ℝ)
    (hlow : r ≤ ell * (N / D) → (1 / (8712 * (N : ℝ))) * ρ ^ 4 / 64 ≤ g)
    (hhigh : ell * (N / D) ≤ r → (1 / (8712 * (N : ℝ))) *
      ((ell : ℝ) * ρ * ((N / D : ℕ) : ℝ) / (r : ℝ)) ^ 4 / 64 ≤ g) :
    degreeRateConstant ρ D * min (1 / ((N + 2 : ℕ) : ℝ))
      ((d : ℝ)^4 * ((N + 2 : ℕ) : ℝ)^3 / (r : ℝ)^4) ≤ g := by
  have hc : 0 ≤ degreeRateConstant ρ D := (degreeRateConstant_pos ρ D hρ hD).le
  by_cases hrK : r ≤ ell * (N / D)
  · calc
      degreeRateConstant ρ D * min (1 / ((N + 2 : ℕ) : ℝ))
          ((d : ℝ)^4 * ((N + 2 : ℕ) : ℝ)^3 / (r : ℝ)^4) ≤
          degreeRateConstant ρ D * (1 / ((N + 2 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hc
      _ ≤ g := degree_rate_low N D (by omega) hD ρ g (hlow hrK)
  · calc
      degreeRateConstant ρ D * min (1 / ((N + 2 : ℕ) : ℝ))
          ((d : ℝ)^4 * ((N + 2 : ℕ) : ℝ)^3 / (r : ℝ)^4) ≤
          degreeRateConstant ρ D *
            ((d : ℝ)^4 * ((N + 2 : ℕ) : ℝ)^3 / (r : ℝ)^4) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hc
      _ ≤ g := degree_rate_high N D ell d r hD hND hNtwo (by omega) hd ρ g hρ
        (hhigh (by omega))

end OptimalConvergenceRates.SphereDimensionBounds.DegreeAmplificationRate
