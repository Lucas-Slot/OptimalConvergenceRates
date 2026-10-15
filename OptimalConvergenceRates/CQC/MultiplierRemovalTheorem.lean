import OptimalConvergenceRates.CQC.MultiplierRemovalLog

/-!
# Positive multiplier removal with logarithmic overhead

This is the reusable multiplier-removal theorem used by the CQC transfer.
All interval and square-bound certificates are fixed before the perturbation
parameter varies.
-/

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates
namespace CQCInternal

open GeneralArchimedean

variable {n m : ℕ}

/-- A fixed strictly positive polynomial multiplier can be removed at an
additive logarithmic certificate-order cost. -/
theorem removePositiveMultiplier_log
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p a : MvPolynomial (Fin n) ℝ)
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (ha : ∀ x ∈ KrivineStengle.basicClosedSet g,
      0 < MvPolynomial.eval x a) :
    ∃ c Clog : ℝ, 0 < c ∧ 0 < Clog ∧
      ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 / 2 → ∀ {r : ℕ},
        a ^ 2 * p + C δ ∈ GenQuadraticModule g r →
          p + C (c * δ) ∈ GenQuadraticModule g
            (r + Nat.ceil (Clog * (1 + Real.log (1 / δ)))) := by
  let amin : ℝ := polynomialMinimum g a
  obtain ⟨xmin, hxmin, haminEval⟩ := polynomialMinimum_mem hne harch a
  have hamin : 0 < amin := by
    dsimp [amin]
    rw [← haminEval]
    exact ha xmin hxmin
  let α : ℝ := amin / 2
  have hα : 0 < α := div_pos hamin (by norm_num)
  let amax : ℝ := -polynomialMinimum g (-a)
  have ha_le_amax : ∀ x ∈ KrivineStengle.basicClosedSet g,
      MvPolynomial.eval x a ≤ amax := by
    intro x hx
    have hmin := polynomialMinimum_le_eval harch (-a) hx
    simp only [eval_neg] at hmin
    dsimp [amax]
    linarith
  let β : ℝ := amax + 1
  have hαβ : α < β := by
    obtain ⟨x, hx⟩ := hne
    have hmin := polynomialMinimum_le_eval harch a hx
    have hmax := ha_le_amax x hx
    dsimp [α, amin, β]
    linarith
  have hlowerPos : ∀ x ∈ KrivineStengle.basicClosedSet g,
      0 < MvPolynomial.eval x (a - C α) := by
    intro x hx
    simp only [eval_sub, eval_C]
    have hmin := polynomialMinimum_le_eval harch a hx
    dsimp [α, amin]
    linarith
  have hupperPos : ∀ x ∈ KrivineStengle.basicClosedSet g,
      0 < MvPolynomial.eval x (C β - a) := by
    intro x hx
    simp only [eval_sub, eval_C]
    have hmax := ha_le_amax x hx
    dsimp [β]
    linarith
  obtain ⟨rLower, hlower⟩ :=
    exists_order_of_posOn g (a - C α) hne harch hlowerPos
  obtain ⟨rUpper, hupper⟩ :=
    exists_order_of_posOn g (C β - a) hne harch hupperPos
  let pmin : ℝ := polynomialMinimum g p
  let pmax : ℝ := -polynomialMinimum g (-p)
  let B : ℝ := |pmin| + |pmax| + 1
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hpBoundPos : ∀ x ∈ KrivineStengle.basicClosedSet g,
      0 < MvPolynomial.eval x (C (B ^ 2) - p ^ 2) := by
    intro x hx
    have hloRaw := polynomialMinimum_le_eval harch p hx
    have hhiRaw := polynomialMinimum_le_eval harch (-p) hx
    simp only [eval_neg] at hhiRaw
    have hlo : pmin ≤ MvPolynomial.eval x p := by
      simpa [pmin] using hloRaw
    have hhi : MvPolynomial.eval x p ≤ pmax := by
      dsimp [pmax]
      linarith
    have hpminLower : -|pmin| ≤ pmin := neg_abs_le pmin
    have hpmaxUpper : pmax ≤ |pmax| := le_abs_self pmax
    have habs : |MvPolynomial.eval x p| < B := by
      apply abs_lt.2
      constructor
      · have hstrict : -B < -|pmin| := by
          dsimp [B]
          linarith [abs_nonneg pmax]
        exact hstrict.trans_le (hpminLower.trans hlo)
      · have hstrict : |pmax| < B := by
          dsimp [B]
          linarith [abs_nonneg pmin]
        exact (hhi.trans hpmaxUpper).trans_lt hstrict
    simp only [eval_sub, eval_C, eval_pow]
    rcases abs_lt.1 habs with ⟨hneg, hpos⟩
    nlinarith
  obtain ⟨rBound, hpBound⟩ :=
    exists_order_of_posOn g (C (B ^ 2) - p ^ 2) hne harch hpBoundPos
  let θ : ℝ := 1 - α / β
  have hβ : 0 < β := hα.trans hαβ
  have hθ0 : 0 < θ := by
    dsimp [θ]
    rw [sub_pos, div_lt_one hβ]
    exact hαβ
  have hθ1 : θ < 1 := by
    dsimp [θ]
    have : 0 < α / β := div_pos hα hβ
    linarith
  obtain ⟨Catt, hCatt, hatt⟩ :=
    exists_attenuation_length_log hθ0 hθ1 hB
  let slope := multiplierRemovalSlope p a α rLower rUpper rBound
  let c : ℝ := 1 + α⁻¹ ^ 2
  let Clog : ℝ := max 1 ((slope : ℝ) * Catt)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hClog : 0 < Clog := lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
  refine ⟨c, Clog, hc, hClog, ?_⟩
  intro δ hδ hδhalf r hweighted
  obtain ⟨ell, hellAtt, hellLog⟩ := hatt hδ hδhalf
  have hcert := multiplierRemoval_at_length_linear p a ell r
    rLower rUpper rBound hα hαβ hB hδ hlower hupper hpBound hweighted
  have heta : B * (2 * θ ^ (ell + 1)) ≤ δ := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hellAtt
  have hepsilon :
      B * (2 * θ ^ (ell + 1)) + δ * α⁻¹ ^ 2 ≤ c * δ := by
    dsimp [c]
    nlinarith
  have hgap : C (c * δ -
      (B * (2 * θ ^ (ell + 1)) + δ * α⁻¹ ^ 2)) ∈
      GenQuadraticModule g 0 :=
    genQuadraticModule_C_nonneg g (sub_nonneg.mpr hepsilon)
  have hsum := genQuadraticModule_add hcert hgap
  have htarget : p + C (c * δ) ∈
      GenQuadraticModule g (r + slope * (ell + 1)) := by
    have hpoly :
        p + C (B * (2 * (1 - α / β) ^ (ell + 1)) + δ * α⁻¹ ^ 2) +
            C (c * δ - (B * (2 * θ ^ (ell + 1)) + δ * α⁻¹ ^ 2)) =
          p + C (c * δ) := by
      dsimp [θ]
      simp only [map_sub, map_add]
      ring
    rw [← hpoly]
    simpa [slope] using hsum
  have hlogNonneg : 0 ≤ 1 + Real.log (1 / δ) := by
    have hloginv : 0 ≤ Real.log (1 / δ) := by
      apply Real.log_nonneg
      rw [one_div]
      exact (one_le_inv₀ hδ).2 (by linarith)
    linarith
  have hslopeReal :
      ((slope * (ell + 1) : ℕ) : ℝ) ≤
        Clog * (1 + Real.log (1 / δ)) := by
    rw [Nat.cast_mul]
    calc
      (slope : ℝ) * ((ell + 1 : ℕ) : ℝ) ≤
          (slope : ℝ) *
            (Catt * (1 + Real.log (1 / δ))) := by
              gcongr
      _ = ((slope : ℝ) * Catt) *
          (1 + Real.log (1 / δ)) := by ring
      _ ≤ Clog * (1 + Real.log (1 / δ)) := by
        gcongr
        exact le_max_right 1 _
  have hceilReal :
      ((slope * (ell + 1) : ℕ) : ℝ) ≤
        (Nat.ceil (Clog * (1 + Real.log (1 / δ))) : ℝ) :=
    hslopeReal.trans (Nat.le_ceil _)
  have horder : slope * (ell + 1) ≤
      Nat.ceil (Clog * (1 + Real.log (1 / δ))) := by
    exact_mod_cast hceilReal
  exact GenQuadraticModule_mono (Nat.add_le_add_left horder r) htarget

end CQCInternal
end OptimalConvergenceRates

end
