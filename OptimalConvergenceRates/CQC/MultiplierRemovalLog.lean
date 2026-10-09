import Mathlib.Analysis.SpecialFunctions.Log.Basic
import OptimalConvergenceRates.CQC.MultiplierRemovalDegree

/-!
# Logarithmic inverse-series length

A fixed contraction reaches accuracy `δ` after a number of steps bounded by
a fixed multiple of `1 + log (1 / δ)`.
-/

noncomputable section

namespace OptimalConvergenceRates
namespace CQCInternal

/-- Quantitative power selection for a fixed contraction factor. -/
theorem exists_attenuation_length_log
    {θ B : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 / 2 →
        ∃ ell : ℕ,
          2 * B * θ ^ (ell + 1) ≤ δ ∧
          ((ell + 1 : ℕ) : ℝ) ≤ C * (1 + Real.log (1 / δ)) := by
  let B' : ℝ := max B 1
  have hB' : 0 < B' := lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  have hBB' : B ≤ B' := le_max_left B 1
  let q : ℝ := -Real.log θ
  have hlogθ : Real.log θ < 0 := Real.log_neg hθ0 hθ1
  have hq : 0 < q := neg_pos.mpr hlogθ
  let H : ℝ := Real.log (2 * B')
  have hH : 0 ≤ H := by
    apply Real.log_nonneg
    dsimp [B']
    nlinarith [le_max_right B 1]
  let C : ℝ := q⁻¹ * (1 + H) + 2
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδhalf
  let t : ℝ := δ / (2 * B')
  have ht0 : 0 < t := div_pos hδ (mul_pos (by norm_num) hB')
  have ht1 : t < 1 := by
    dsimp [t]
    rw [div_lt_one (mul_pos (by norm_num) hB')]
    nlinarith [le_max_right B 1]
  have hlogt : Real.log t < 0 := Real.log_neg ht0 ht1
  let ratio : ℝ := Real.log t / Real.log θ
  have hratio0 : 0 < ratio := div_pos_of_neg_of_neg hlogt hlogθ
  let ell : ℕ := Nat.ceil ratio
  have hratio_le : ratio ≤ (ell : ℝ) := Nat.le_ceil ratio
  have hlog_power : (ell : ℝ) * Real.log θ ≤ Real.log t := by
    rw [div_le_iff_of_neg hlogθ] at hratio_le
    simpa [ratio, mul_comm] using hratio_le
  have hpow : θ ^ ell ≤ t :=
    (Real.pow_le_iff_le_log hθ0 ht0).2 hlog_power
  have hθle : θ ≤ 1 := hθ1.le
  have hpow_succ : θ ^ (ell + 1) ≤ θ ^ ell := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hθ0.le ell) hθle
  have hattenuation : 2 * B * θ ^ (ell + 1) ≤ δ := by
    calc
      2 * B * θ ^ (ell + 1) ≤ 2 * B' * θ ^ (ell + 1) := by
        gcongr
      _ ≤ 2 * B' * θ ^ ell := by
        gcongr
      _ ≤ 2 * B' * t := by
        gcongr
      _ = δ := by
        dsimp [t]
        field_simp
  have hden : 2 * B' ≠ 0 := (mul_pos (by norm_num) hB').ne'
  have hratio_eq :
      ratio = (Real.log (1 / δ) + H) / q := by
    dsimp [ratio, t, q, H]
    rw [Real.log_div hδ.ne' hden, Real.log_div one_ne_zero hδ.ne']
    simp only [Real.log_one, zero_sub]
    field_simp [hlogθ.ne]
    ring
  have hceil : (ell : ℝ) < ratio + 1 :=
    Nat.ceil_lt_add_one hratio0.le
  have hL : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg
    rw [one_div]
    exact (one_le_inv₀ hδ).2 (by linarith)
  have hqinv : 0 ≤ q⁻¹ := (inv_pos.mpr hq).le
  have hHL : 0 ≤ H * Real.log (1 / δ) := mul_nonneg hH hL
  have hbound :
      ((ell + 1 : ℕ) : ℝ) ≤ C * (1 + Real.log (1 / δ)) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    rw [hratio_eq] at hceil
    have hqne : q ≠ 0 := hq.ne'
    dsimp [C]
    rw [div_eq_mul_inv] at hceil
    nlinarith [mul_nonneg hqinv (add_nonneg zero_le_one hHL)]
  exact ⟨ell, hattenuation, hbound⟩

end CQCInternal
end OptimalConvergenceRates

end
