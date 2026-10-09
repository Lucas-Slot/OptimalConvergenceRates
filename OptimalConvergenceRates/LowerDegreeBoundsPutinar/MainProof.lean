/-
  OptimalConvergenceRates/LowerDegreeBoundsPutinar/MainProof.lean

  Improved Putinar lower degree bound for the two-variable corner polynomial.
-/
import OptimalConvergenceRates.LowerDegreeBoundsPutinar.CornerEstimates

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates


/-!
## Target theorem

For all sufficiently small positive `ε`, every Putinar certificate of

```text
q_ε(x,y) = (1 - x^2)(1 - y^2) + ε
```

on the square has total certificate degree at least `c ε^(-1/4)`.
-/

/-- Improved Putinar degree lower bound for the corner polynomial on `[-1,1]^2`.

The theorem is stated for the quadratic module `BoxQuadraticModule 2 r`.
The exponent improves the existing
Baldi-Slot formalized lower bound from `1/8` to `1/4`. -/
theorem improved_lower_degree_bound
    (ε : ℝ) (hε : 0 < ε) (hε0 : ε ≤ improvedEpsilon0) (r : ℕ)
    (hmem : f_eps ε ∈ BoxQuadraticModule 2 r) :
    improvedLowerBoundConst * ε ^ (-(1 : ℝ) / 4) ≤ (r : ℝ) := by
  by_contra hcontra
  push_neg at hcontra
  have hc_pos : 0 < improvedLowerBoundConst := improvedLowerBoundConst_pos
  have hε1 : ε < 1 := by
    have hε0_lt_one : improvedEpsilon0 < 1 := by
      unfold improvedEpsilon0
      have h0 : 0 ≤ improvedLowerBoundConst / 4 :=
        div_nonneg improvedLowerBoundConst_pos.le (by norm_num)
      have hlt : improvedLowerBoundConst / 4 < 1 := by
        nlinarith [improvedLowerBoundConst_le_one]
      exact (pow_lt_one_iff_of_nonneg h0 (by norm_num : (4 : ℕ) ≠ 0)).mpr hlt
    exact lt_of_le_of_lt hε0 hε0_lt_one
  obtain ⟨σ₀, σ₁, σ₂, hsos₀, hsos₁, hsos₂, hdeg₀, hdeg₁, hdeg₂, hdecomp⟩ :=
    box_qm_decomp_n2 (f_eps ε) r hmem
  rcases Nat.eq_zero_or_pos r with rfl | hr_pos
  · have hr2 : 2 ≤ 0 :=
      two_le_of_bounded_decomp ε 0 σ₀ σ₁ σ₂ hdeg₀ hdeg₁ hdeg₂ hdecomp
    omega
  · set a : ℝ := improvedLowerBoundConst / (r : ℝ) ^ 2
    set b : ℝ := improvedLowerBoundConst / (r : ℝ) ^ 2
    have hrR_pos : 0 < (r : ℝ) := Nat.cast_pos.mpr hr_pos
    have hrR_sq_pos : 0 < (r : ℝ) ^ 2 := sq_pos_of_pos hrR_pos
    have ha : 0 < a := by
      simp only [a]
      positivity
    have hb0 : 0 ≤ b := by
      simp only [b]
      positivity
    have hbhalf : b ≤ 1 / 2 := by
      have hr_ge_one : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.mpr hr_pos
      have hc_le_half : improvedLowerBoundConst ≤ 1 / 2 := by
        unfold improvedLowerBoundConst
        norm_num
      simp only [b]
      rw [div_le_iff₀ hrR_sq_pos]
      nlinarith
    have hsmall : ε * (r : ℝ) ^ 4 ≤ improvedLowerBoundConst ^ 4 := by
      have hpow_pos : 0 < ε ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hε _
      have hmul : (r : ℝ) * ε ^ ((1 : ℝ) / 4) < improvedLowerBoundConst := by
        rw [show (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) by ring] at hcontra
        rw [Real.rpow_neg hε.le] at hcontra
        have := mul_lt_mul_of_pos_right hcontra hpow_pos
        rwa [mul_assoc, inv_mul_cancel₀ (ne_of_gt hpow_pos), mul_one] at this
      have h4 := pow_le_pow_left₀
        (by positivity : 0 ≤ (r : ℝ) * ε ^ ((1 : ℝ) / 4)) (le_of_lt hmul) 4
      have hp : (ε ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = ε := by
        rw [← Real.rpow_natCast (ε ^ ((1 : ℝ) / 4)) 4,
          ← Real.rpow_mul hε.le]
        norm_num
      rw [mul_pow, hp] at h4
      nlinarith
    have hεa : ε / a ≤ b := by
      have hc_le_one : improvedLowerBoundConst ≤ 1 := by
        unfold improvedLowerBoundConst
        norm_num
      rw [div_le_iff₀ ha]
      change ε ≤ (improvedLowerBoundConst / (r : ℝ) ^ 2) *
        (improvedLowerBoundConst / (r : ℝ) ^ 2)
      field_simp [ne_of_gt hrR_sq_pos]
      calc ε * (r : ℝ) ^ 4
          ≤ improvedLowerBoundConst ^ 4 := hsmall
        _ ≤ improvedLowerBoundConst ^ 2 := by
            have hc2_nonneg : 0 ≤ improvedLowerBoundConst ^ 2 := sq_nonneg _
            have hc2_le_one : improvedLowerBoundConst ^ 2 ≤ 1 := by
              nlinarith [hc_pos, hc_le_one]
            calc improvedLowerBoundConst ^ 4
                = improvedLowerBoundConst ^ 2 * improvedLowerBoundConst ^ 2 := by ring
              _ ≤ improvedLowerBoundConst ^ 2 * 1 :=
                  mul_le_mul_of_nonneg_left hc2_le_one hc2_nonneg
              _ = improvedLowerBoundConst ^ 2 := by ring
    have hlower := outside_point_sigma1_lower_bound ε a b ha hb0 hbhalf hεa
      σ₀ σ₁ σ₂ hsos₀ hsos₁ hsos₂ hdecomp
    have hupper := outside_point_sigma1_upper_bound ε a b r hε ha hb0
      σ₀ σ₁ σ₂ hsos₀ hsos₁ hsos₂ hdeg₀ hdeg₁ hdeg₂ hdecomp hsmall rfl rfl
    linarith

/-- Contrapositive form of `improved_lower_degree_bound`. -/
theorem improved_lower_degree_bound_contra
    (ε : ℝ) (hε : 0 < ε) (hε0 : ε ≤ improvedEpsilon0) (r : ℕ)
    (hr : (r : ℝ) < improvedLowerBoundConst * ε ^ (-(1 : ℝ) / 4)) :
    f_eps ε ∉ BoxQuadraticModule 2 r := by
  intro hmem
  have hbound := improved_lower_degree_bound ε hε hε0 r hmem
  linarith

end OptimalConvergenceRates

end

