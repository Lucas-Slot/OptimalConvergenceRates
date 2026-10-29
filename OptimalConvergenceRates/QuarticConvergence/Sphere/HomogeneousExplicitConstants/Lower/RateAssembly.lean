import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.Dyadic

/-! Uniform conversion of the Boolean-level and tail estimates to dimension n=N+2. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Foundation

def cubicRateConstant (ρ : ℝ) (D : ℕ) : ℝ :=
  ρ ^ 4 / (8712 * 8192 * (D : ℝ) ^ 4)

theorem cubicRateConstant_pos (ρ : ℝ) (D : ℕ) (hρ : 0 < ρ) (hD : 0 < D) :
    0 < cubicRateConstant ρ D := by
  unfold cubicRateConstant
  positivity

theorem cubicRateConstant_le_boolean (ρ : ℝ) (D : ℕ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hD : 0 < D) :
    cubicRateConstant ρ D ≤ 1 / 8712 := by
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDfour : (1 : ℝ) ≤ (D : ℝ) ^ 4 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hDreal 4
  have hρfour : ρ ^ 4 ≤ 1 := by
    simpa using pow_le_pow_left₀ hρ0 hρ1 4
  have hden : (8712 : ℝ) ≤ 8712 * 8192 * (D : ℝ) ^ 4 := by nlinarith
  calc
    cubicRateConstant ρ D ≤ 1 / (8712 * 8192 * (D : ℝ) ^ 4) :=
      div_le_div_of_nonneg_right hρfour (by positivity)
    _ ≤ 1 / 8712 := one_div_le_one_div_of_le (by norm_num) hden

theorem cubic_rate_low (N D : ℕ) (hN : 0 < N) (hD : 0 < D)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (g : ℝ)
    (hlow : 1 / (8712 * (N : ℝ)) ≤ g) :
    cubicRateConstant ρ D * (1 / ((N + 2 : ℕ) : ℝ)) ≤ g := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hn : (N : ℝ) ≤ ((N + 2 : ℕ) : ℝ) := by push_cast; linarith
  calc
    cubicRateConstant ρ D * (1 / ((N + 2 : ℕ) : ℝ)) ≤
        (1 / 8712) * (1 / ((N + 2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right (cubicRateConstant_le_boolean ρ D hρ0 hρ1 hD)
        (by positivity)
    _ ≤ (1 / 8712) * (1 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hNreal hn) (by norm_num)
    _ = 1 / (8712 * (N : ℝ)) := by ring
    _ ≤ g := hlow

theorem cubic_rate_high (N D r : ℕ) (hD : 0 < D) (hND : D ≤ N)
    (hNtwo : 2 ≤ N) (hr : 0 < r) (ρ : ℝ) (g : ℝ)
    (hhigh : (1 / (8712 * (N : ℝ))) *
      (ρ * ((N / D : ℕ) : ℝ) / (r : ℝ)) ^ 4 / 64 ≤ g) :
    cubicRateConstant ρ D *
      (((N + 2 : ℕ) : ℝ) ^ 3 / (r : ℝ) ^ 4) ≤ g := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hK : (N : ℝ) ≤ 2 * (D : ℝ) * ((N / D : ℕ) : ℝ) := by
    exact_mod_cast nat_le_twice_mul_div N D hD hND
  have hn : ((N + 2 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast (show N + 2 ≤ 2 * N by omega)
  have hNfour := pow_le_pow_left₀ hNpos.le hK 4
  have hnthree := pow_le_pow_left₀
    (by positivity : (0 : ℝ) ≤ ((N + 2 : ℕ) : ℝ)) hn 3
  have hproduct : ((N + 2 : ℕ) : ℝ) ^ 3 * (N : ℝ) ≤
      128 * (D : ℝ) ^ 4 * ((N / D : ℕ) : ℝ) ^ 4 := by
    calc
      ((N + 2 : ℕ) : ℝ) ^ 3 * (N : ℝ) ≤ (2 * (N : ℝ)) ^ 3 * (N : ℝ) :=
        mul_le_mul_of_nonneg_right hnthree hNpos.le
      _ = 8 * (N : ℝ) ^ 4 := by ring
      _ ≤ 8 * (2 * (D : ℝ) * ((N / D : ℕ) : ℝ)) ^ 4 :=
        mul_le_mul_of_nonneg_left hNfour (by norm_num)
      _ = 128 * (D : ℝ) ^ 4 * ((N / D : ℕ) : ℝ) ^ 4 := by ring
  let T : ℝ := ρ ^ 4 /
    (8712 * 8192 * (D : ℝ) ^ 4 * (N : ℝ) * (r : ℝ) ^ 4)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  calc
    cubicRateConstant ρ D * (((N + 2 : ℕ) : ℝ) ^ 3 / (r : ℝ) ^ 4) =
        T * (((N + 2 : ℕ) : ℝ) ^ 3 * (N : ℝ)) := by
      unfold cubicRateConstant
      dsimp [T]
      field_simp [hDpos.ne', hNpos.ne', hrpos.ne'] <;> ring
    _ ≤ T * (128 * (D : ℝ) ^ 4 * ((N / D : ℕ) : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left hproduct hT
    _ = (1 / (8712 * (N : ℝ))) *
        (ρ * ((N / D : ℕ) : ℝ) / (r : ℝ)) ^ 4 / 64 := by
      dsimp [T]
      field_simp [hDpos.ne', hNpos.ne', hrpos.ne'] <;> ring
    _ ≤ g := hhigh

/-- Scalar assembly at one order. Both regimes refer to the same value g. -/
theorem cubic_rate_of_two_regimes (N D r : ℕ) (hD : 0 < D) (hND : D ≤ N)
    (hNtwo : 2 ≤ N) (hr : 2 ≤ r) (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1 / 2)
    (g : ℝ)
    (hlow : r ≤ N / D → 1 / (8712 * (N : ℝ)) ≤ g)
    (hhigh : N / D ≤ r → (1 / (8712 * (N : ℝ))) *
      (ρ * ((N / D : ℕ) : ℝ) / (r : ℝ)) ^ 4 / 64 ≤ g) :
    cubicRateConstant ρ D * min (1 / ((N + 2 : ℕ) : ℝ))
      (((N + 2 : ℕ) : ℝ) ^ 3 / (r : ℝ) ^ 4) ≤ g := by
  have hc : 0 ≤ cubicRateConstant ρ D := (cubicRateConstant_pos ρ D hρ hD).le
  by_cases hrK : r ≤ N / D
  · calc
      cubicRateConstant ρ D * min (1 / ((N + 2 : ℕ) : ℝ))
          (((N + 2 : ℕ) : ℝ) ^ 3 / (r : ℝ) ^ 4) ≤
          cubicRateConstant ρ D * (1 / ((N + 2 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hc
      _ ≤ g := cubic_rate_low N D (by omega) hD ρ hρ.le (by linarith) g (hlow hrK)
  · calc
      cubicRateConstant ρ D * min (1 / ((N + 2 : ℕ) : ℝ))
          (((N + 2 : ℕ) : ℝ) ^ 3 / (r : ℝ) ^ 4) ≤
          cubicRateConstant ρ D * (((N + 2 : ℕ) : ℝ) ^ 3 / (r : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hc
      _ ≤ g := cubic_rate_high N D r hD hND hNtwo (by omega) ρ g (hhigh (by omega))

/-- One dimension-dependent family of values satisfying the two estimates
has the claimed all-order cubic rate with a single positive constant. -/
theorem uniform_cubic_rate (N D : ℕ) (hD : 0 < D) (hND : D ≤ N)
    (hNtwo : 2 ≤ N) (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1 / 2)
    (g : ℕ → ℝ)
    (hlow : ∀ r, 2 ≤ r → r ≤ N / D → 1 / (8712 * (N : ℝ)) ≤ g r)
    (hhigh : ∀ r, 2 ≤ r → N / D ≤ r → (1 / (8712 * (N : ℝ))) *
      (ρ * ((N / D : ℕ) : ℝ) / (r : ℝ)) ^ 4 / 64 ≤ g r) :
    0 < cubicRateConstant ρ D ∧
      ∀ r : ℕ, 2 ≤ r → cubicRateConstant ρ D * min (1 / ((N + 2 : ℕ) : ℝ))
        (((N + 2 : ℕ) : ℝ) ^ 3 / (r : ℝ) ^ 4) ≤ g r := by
  refine ⟨cubicRateConstant_pos ρ D hρ hD, ?_⟩
  intro r hr
  exact cubic_rate_of_two_regimes N D r hD hND hNtwo hr ρ hρ hρhalf
    (g r) (hlow r hr) (hhigh r hr)

end Foundation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
