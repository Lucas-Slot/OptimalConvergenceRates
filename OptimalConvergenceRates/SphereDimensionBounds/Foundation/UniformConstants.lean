import OptimalConvergenceRates.SphereDimensionBounds.Foundation.Dyadic
import OptimalConvergenceRates.SphereDimensionBounds.Foundation.WeightedTaylor

/-! Uniform dyadic choices for the positive-occurrence normalization. -/

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

theorem positive_weight_polynomial_le (n : ℕ) (hn : 17 ≤ n) :
    1672704 * n * (n + 1) ^ 2 ≤ 4 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hsquare : 4 ≤ n ^ 2 := by
        exact Nat.pow_le_pow_left (by omega : 2 ≤ n) 2
      have hstep : (n + 2) ^ 2 ≤ 4 * n * (n + 1) := by nlinarith
      have hpoly : (n + 1) * (n + 2) ^ 2 ≤ 4 * (n * (n + 1) ^ 2) := by
        have hmul := Nat.mul_le_mul_left (n + 1) hstep
        nlinarith
      calc
        1672704 * (n + 1) * (n + 1 + 1) ^ 2 =
            1672704 * ((n + 1) * (n + 2) ^ 2) := by ring
        _ ≤ 1672704 * (4 * (n * (n + 1) ^ 2)) := Nat.mul_le_mul_left _ hpoly
        _ = 4 * (1672704 * n * (n + 1) ^ 2) := by ring
        _ ≤ 4 * 4 ^ n := Nat.mul_le_mul_left _ ih
        _ = 4 ^ (n + 1) := by rw [pow_succ]; ring

theorem positive_weight_error_bound (n : ℕ) (hn : 17 ≤ n) :
    (6 : ℝ) * ((n : ℝ) + 1) ^ 2 / (4 : ℝ) ^ n ≤
      1 / (32 * (8712 * (n : ℝ))) := by
  have hreal : (1672704 : ℝ) * (n : ℝ) * ((n : ℝ) + 1) ^ 2 ≤
      (4 : ℝ) ^ n := by exact_mod_cast positive_weight_polynomial_le n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith only [hreal]

/-- An absolute radius and threshold work uniformly at a linearly growing
Boolean level. The exponent remains symbolic throughout the proof. -/
theorem exists_uniform_dyadic_parameters (D : ℕ) (hD : 1 ≤ D) :
    ∃ (ρ : ℝ) (N₀ : ℕ), 0 < ρ ∧ ρ ≤ 1 / 2 ∧
      ∀ N : ℕ, N₀ ≤ N →
        N / D ≤ N ∧ 1 ≤ ρ * ((N / D : ℕ) : ℝ) ∧
        6 * (2 : ℝ) ^ N * angularTruncationFactor (N / D) ρ ≤
          1 / (32 * (8712 * (N : ℝ))) := by
  let M : ℕ := 8 * D
  let ρ : ℝ := 1 / (2 : ℝ) ^ M
  have hM : 2 ≤ M := by dsimp [M]; omega
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρhalf : ρ ≤ 1 / 2 := by
    have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ M := by
      simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by omega : 1 ≤ M))
    exact one_div_le_one_div_of_le (by norm_num) hpow
  refine ⟨ρ, max 17 (D * 2 ^ M), hρ, hρhalf, ?_⟩
  intro N hN
  have hN17 : 17 ≤ N := (le_max_left _ _).trans hN
  have hNth : D * 2 ^ M ≤ N := (le_max_right _ _).trans hN
  have hDpos : 0 < D := by omega
  have hDN : D ≤ N := by
    have hp : 1 ≤ 2 ^ M := Nat.one_le_pow _ _ (by decide)
    have hDpow : D ≤ D * 2 ^ M := by simpa using Nat.mul_le_mul_left D hp
    exact hDpow.trans hNth
  have hKlo : N ≤ 2 * D * (N / D) := nat_le_twice_mul_div N D hDpos hDN
  have hpower : 3 * N ≤ (M - 2) * (N / D) := by
    have hm : 6 * D ≤ M - 2 := by dsimp [M]; omega
    have hmul := Nat.mul_le_mul_right (N / D) hm
    nlinarith
  have hamp := dyadic_amplification_bound N (N / D) M hM hpower
  have hquot : 2 ^ M ≤ N / D := by
    apply (Nat.le_div_iff_mul_le hDpos).2
    simpa only [Nat.mul_comm] using hNth
  have hscale : 1 ≤ ρ * ((N / D : ℕ) : ℝ) := by
    have hcast : (2 : ℝ) ^ M ≤ ((N / D : ℕ) : ℝ) := by exact_mod_cast hquot
    dsimp [ρ]
    calc
      1 ≤ ((N / D : ℕ) : ℝ) / (2 : ℝ) ^ M := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ M)).2
        simpa only [one_mul] using hcast
      _ = 1 / (2 : ℝ) ^ M * ((N / D : ℕ) : ℝ) := by ring
  have hK : N / D ≤ N := Nat.div_le_self N D
  refine ⟨hK, hscale, ?_⟩
  have hKR : ((N / D : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hK
  have hfac : 4 * ρ = 4 / (2 : ℝ) ^ M := by dsimp [ρ]; ring
  calc
    6 * (2 : ℝ) ^ N * angularTruncationFactor (N / D) ρ =
        6 * (((N / D : ℕ) : ℝ) + 1) ^ 2 *
          ((2 : ℝ) ^ N * (4 / (2 : ℝ) ^ M) ^ (N / D)) := by
      unfold angularTruncationFactor
      rw [hfac]
      ring
    _ ≤ 6 * ((N : ℝ) + 1) ^ 2 * (1 / (4 : ℝ) ^ N) := by gcongr
    _ = 6 * ((N : ℝ) + 1) ^ 2 / (4 : ℝ) ^ N := by ring
    _ ≤ 1 / (32 * (8712 * (N : ℝ))) := positive_weight_error_bound N hN17

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
