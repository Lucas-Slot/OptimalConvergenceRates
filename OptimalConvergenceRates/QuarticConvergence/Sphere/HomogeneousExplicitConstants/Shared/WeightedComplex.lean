import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.AnalyticCore

/-!
# The weighted complex estimate for the uniform sphere-SOS transfer

The estimates are valid in arbitrary complex normed codomains and have no
dimension factor. Frequency conversion from polynomial certificates is kept
separate from the analytic bounded-numerator premises.
-/

open Set
open scoped Topology

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Foundation

/-- The upward imaginary shift stays uniformly away from zero on the upper
half-plane. -/
theorem upper_shift_norm_lower (s : ℝ) {z : ℂ} (hz : 0 ≤ z.im) :
    s ≤ ‖z + (s : ℂ) * Complex.I‖ := by
  calc
    s ≤ z.im + s := by linarith
    _ = (z + (s : ℂ) * Complex.I).im := by simp
    _ ≤ ‖z + (s : ℂ) * Complex.I‖ := Complex.im_le_norm _

theorem upper_shift_ne_zero {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 ≤ z.im) :
    z + (s : ℂ) * Complex.I ≠ 0 := by
  have hnorm := upper_shift_norm_lower s hz
  intro hzero
  rw [hzero, norm_zero] at hnorm
  linarith

/-- Squared norm of the shifted real-axis denominator. -/
theorem real_shift_norm_sq (s t : ℝ) :
    ‖(t : ℂ) + (s : ℂ) * Complex.I‖ ^ 2 = t ^ 2 + s ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]

/-- A quadratic boundary envelope survives in the upper half-plane after
division by the square of a pole below the boundary. The auxiliary bound `B`
disappears from the conclusion. -/
theorem weighted_upper_half_plane_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : ℂ → E} {a B s : ℝ} (ha : 0 ≤ a) (hs : 0 < s)
    (hd : DiffContOnCl ℂ F {z : ℂ | 0 < z.im})
    (hB : ∀ z : ℂ, 0 ≤ z.im → ‖F z‖ ≤ B)
    (hreal : ∀ t : ℝ, ‖F (t : ℂ)‖ ≤ a + t ^ 2)
    {z : ℂ} (hz : 0 ≤ z.im) :
    ‖F z‖ ≤ (a + s ^ 2) * (1 + ‖z‖ / s) ^ 2 := by
  let d : ℂ → ℂ := fun w ↦ w + (s : ℂ) * Complex.I
  let V : ℂ → E := fun w ↦ (d w)⁻¹ • (d w)⁻¹ • F w
  have hdne : ∀ w ∈ closure {w : ℂ | 0 < w.im}, d w ≠ 0 := by
    intro w hw
    apply upper_shift_ne_zero hs
    simpa only [Complex.closure_setOfPred_lt_im, Set.mem_ofPred_eq] using hw
  have hdinv : DiffContOnCl ℂ (fun w ↦ (d w)⁻¹) {w : ℂ | 0 < w.im} := by
    exact ((differentiable_id.add_const ((s : ℂ) * Complex.I)).diffContOnCl).inv hdne
  have hVd : DiffContOnCl ℂ V {w : ℂ | 0 < w.im} := hdinv.smul (hdinv.smul hd)
  have hVnorm (w : ℂ) : ‖V w‖ = ‖F w‖ / ‖d w‖ ^ 2 := by
    simp only [V, norm_smul, norm_inv, pow_two, div_eq_mul_inv]
    ring
  have hVB : ∀ w : ℂ, 0 ≤ w.im → ‖V w‖ ≤ B / s ^ 2 := by
    intro w hw
    have hden : s ^ 2 ≤ ‖d w‖ ^ 2 := by
      exact pow_le_pow_left₀ hs.le (upper_shift_norm_lower s hw) 2
    rw [hVnorm]
    calc
      ‖F w‖ / ‖d w‖ ^ 2 ≤ ‖F w‖ / s ^ 2 :=
        div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hs) hden
      _ ≤ B / s ^ 2 := div_le_div_of_nonneg_right (hB w hw) (sq_nonneg _)
  have hVC : ∀ t : ℝ, ‖V (t : ℂ)‖ ≤ (s ^ 2 + a) / s ^ 2 := by
    intro t
    have hdenpos : 0 < t ^ 2 + s ^ 2 := by positivity
    rw [hVnorm]
    change ‖F (t : ℂ)‖ / ‖(t : ℂ) + (s : ℂ) * Complex.I‖ ^ 2 ≤ _
    rw [real_shift_norm_sq]
    calc
      ‖F (t : ℂ)‖ / (t ^ 2 + s ^ 2) ≤ (a + t ^ 2) / (t ^ 2 + s ^ 2) :=
        div_le_div_of_nonneg_right (hreal t) hdenpos.le
      _ ≤ (s ^ 2 + a) / s ^ 2 := by
        apply (div_le_div_iff₀ hdenpos (sq_pos_of_pos hs)).2
        nlinarith [mul_nonneg ha (sq_nonneg t)]
  have hmax : ‖V z‖ ≤ (s ^ 2 + a) / s ^ 2 :=
    norm_le_of_bounded_upper_half_plane hVd hVB hVC hz
  have hdzpos : 0 < ‖d z‖ ^ 2 :=
    sq_pos_of_pos (lt_of_lt_of_le hs (upper_shift_norm_lower s hz))
  have hFbound : ‖F z‖ ≤ ((s ^ 2 + a) / s ^ 2) * ‖d z‖ ^ 2 := by
    rw [hVnorm] at hmax
    exact (div_le_iff₀ hdzpos).1 hmax
  have hdz : ‖d z‖ ≤ ‖z‖ + s := by
    calc
      ‖d z‖ ≤ ‖z‖ + ‖(s : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = ‖z‖ + s := by simp [abs_of_pos hs]
  calc
    ‖F z‖ ≤ ((s ^ 2 + a) / s ^ 2) * ‖d z‖ ^ 2 := hFbound
    _ ≤ ((s ^ 2 + a) / s ^ 2) * (‖z‖ + s) ^ 2 := by
      gcongr
    _ = (a + s ^ 2) * (1 + ‖z‖ / s) ^ 2 := by
      field_simp [hs.ne']
      ring

/-- The norm of the frequency shift records exactly the imaginary part. -/
theorem norm_exp_frequency_shift_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (r : ℝ) (z : ℂ) (v : E) :
    ‖Complex.exp ((r : ℂ) * z * Complex.I) • v‖ =
      Real.exp (-r * z.im) * ‖v‖ := by
  rw [norm_smul, Complex.norm_exp]
  congr 1
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- The requested weighted estimate on the closed upper half-plane, assuming
the upward frequency-shifted numerator is bounded there. -/
theorem weighted_complex_bound_upper
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {H : ℂ → E} {a B r : ℝ} (hr : 0 < r)
    (hH : Differentiable ℂ H)
    (hshift : ∀ z : ℂ, 0 ≤ z.im →
      ‖Complex.exp ((r : ℂ) * z * Complex.I) • H z‖ ≤ B)
    (hreal : ∀ t : ℝ, ‖H (t : ℂ)‖ ≤ a + t ^ 2)
    {z : ℂ} (hz : 0 ≤ z.im) :
    ‖H z‖ ≤ (a + r⁻¹ ^ 2) * (1 + r * ‖z‖) ^ 2 * Real.exp (r * z.im) := by
  have ha : 0 ≤ a := by
    have hzero := (norm_nonneg (H 0)).trans (hreal 0)
    simpa using hzero
  let F : ℂ → E := fun w ↦ Complex.exp ((r : ℂ) * w * Complex.I) • H w
  have hFd : DiffContOnCl ℂ F {w : ℂ | 0 < w.im} :=
    (((differentiable_id.const_mul (r : ℂ)).mul_const Complex.I).cexp.smul hH).diffContOnCl
  have hFreal : ∀ t : ℝ, ‖F (t : ℂ)‖ ≤ a + t ^ 2 := by
    intro t
    simpa only [F, norm_exp_frequency_shift_smul, Complex.ofReal_im, mul_zero,
      Real.exp_zero, one_mul] using hreal t
  have hFbound : ‖F z‖ ≤ (a + r⁻¹ ^ 2) * (1 + r * ‖z‖) ^ 2 := by
    simpa only [div_inv_eq_mul, mul_comm ‖z‖ r] using
      weighted_upper_half_plane_bound ha (inv_pos.mpr hr) hFd hshift hFreal hz
  have hcancel : Real.exp (r * z.im) * Real.exp (-r * z.im) = 1 := by
    rw [neg_mul, Real.exp_neg, mul_inv_cancel₀ (ne_of_gt (Real.exp_pos _))]
  calc
    ‖H z‖ = Real.exp (r * z.im) * ‖F z‖ := by
      dsimp only [F]
      rw [norm_exp_frequency_shift_smul, ← mul_assoc, hcancel, one_mul]
    _ ≤ Real.exp (r * z.im) * ((a + r⁻¹ ^ 2) * (1 + r * ‖z‖) ^ 2) :=
      mul_le_mul_of_nonneg_left hFbound (Real.exp_pos _).le
    _ = (a + r⁻¹ ^ 2) * (1 + r * ‖z‖) ^ 2 * Real.exp (r * z.im) := mul_comm _ _

/-- The dimension-free weighted complex estimate used in the sphere transfer.

The two bounded shifted-numerator hypotheses follow from finite frequencies
in `[-r,r]`; this theorem isolates the analytic argument from that finite
frequency conversion. The arbitrary bounds `Bupper` and `Blower` do not occur
in the conclusion. -/
theorem weighted_complex_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {H : ℂ → E} {a Bupper Blower r : ℝ} (hr : 0 < r)
    (hH : Differentiable ℂ H)
    (hupper : ∀ z : ℂ, 0 ≤ z.im →
      ‖Complex.exp ((r : ℂ) * z * Complex.I) • H z‖ ≤ Bupper)
    (hlower : ∀ z : ℂ, z.im ≤ 0 →
      ‖Complex.exp (-(r : ℂ) * z * Complex.I) • H z‖ ≤ Blower)
    (hreal : ∀ t : ℝ, ‖H (t : ℂ)‖ ≤ a + t ^ 2) (z : ℂ) :
    ‖H z‖ ≤ (a + r⁻¹ ^ 2) * (1 + r * ‖z‖) ^ 2 * Real.exp (r * |z.im|) := by
  by_cases hz : 0 ≤ z.im
  · simpa only [abs_of_nonneg hz] using weighted_complex_bound_upper hr hH hupper hreal hz
  · have hzlower : z.im ≤ 0 := le_of_lt (lt_of_not_ge hz)
    let J : ℂ → E := fun w ↦ H (-w)
    have hJ : Differentiable ℂ J := hH.comp differentiable_id.neg
    have hJreal : ∀ t : ℝ, ‖J (t : ℂ)‖ ≤ a + t ^ 2 := by
      intro t
      simpa only [J, Complex.ofReal_neg, neg_sq] using hreal (-t)
    have hJshift : ∀ w : ℂ, 0 ≤ w.im →
        ‖Complex.exp ((r : ℂ) * w * Complex.I) • J w‖ ≤ Blower := by
      intro w hw
      have hwlower : (-w).im ≤ 0 := by simpa only [Complex.neg_im, neg_nonpos] using hw
      have hbound := hlower (-w) hwlower
      have hident : -(r : ℂ) * (-w) * Complex.I = (r : ℂ) * w * Complex.I := by ring
      simpa only [J, hident] using hbound
    have hneg : 0 ≤ (-z).im := by simpa only [Complex.neg_im, neg_nonneg] using hzlower
    have hbound := weighted_complex_bound_upper hr hJ hJshift hJreal hneg
    simpa only [J, neg_neg, norm_neg, Complex.neg_im, abs_of_nonpos hzlower] using hbound

/-- A finite exponential sum is bounded by the sum of coefficient norms after
a shift that makes every frequency decay in the chosen half-plane. -/
theorem norm_shifted_frequency_sum_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (s : Finset ι) (frequency : ι → ℝ) (coefficient : ι → E)
    (shift : ℝ) (z : ℂ)
    (hphase : ∀ k ∈ s, 0 ≤ (shift + frequency k) * z.im) :
    ‖Complex.exp ((shift : ℂ) * z * Complex.I) •
      (∑ k ∈ s, Complex.exp ((frequency k : ℂ) * z * Complex.I) • coefficient k)‖ ≤
      ∑ k ∈ s, ‖coefficient k‖ := by
  rw [Finset.smul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  rw [smul_smul, ← Complex.exp_add]
  have hexponent : (shift : ℂ) * z * Complex.I + (frequency k : ℂ) * z * Complex.I =
      ((shift + frequency k : ℝ) : ℂ) * z * Complex.I := by push_cast; ring
  rw [hexponent, norm_exp_frequency_shift_smul]
  have hdecay : Real.exp (-(shift + frequency k) * z.im) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    nlinarith only [hphase k hk]
  exact mul_le_of_le_one_left (norm_nonneg _) hdecay

/-- The full weighted estimate for an actual finite vector trigonometric
polynomial with frequencies in `[-r,r]`. -/
theorem weighted_complex_bound_of_finite_frequencies
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (s : Finset ι) (frequency : ι → ℝ) (coefficient : ι → E)
    {a r : ℝ} (hr : 0 < r)
    (hfrequency : ∀ k ∈ s, -r ≤ frequency k ∧ frequency k ≤ r)
    (hreal : ∀ t : ℝ,
      ‖∑ k ∈ s, Complex.exp ((frequency k : ℂ) * (t : ℂ) * Complex.I) • coefficient k‖ ≤
        a + t ^ 2) (z : ℂ) :
    ‖∑ k ∈ s, Complex.exp ((frequency k : ℂ) * z * Complex.I) • coefficient k‖ ≤
      (a + r⁻¹ ^ 2) * (1 + r * ‖z‖) ^ 2 * Real.exp (r * |z.im|) := by
  have hdiff : Differentiable ℂ (fun w : ℂ ↦
      ∑ k ∈ s, Complex.exp ((frequency k : ℂ) * w * Complex.I) • coefficient k) := by
    apply Differentiable.fun_sum
    intro k hk
    exact (((differentiable_id.const_mul (frequency k : ℂ)).mul_const Complex.I).cexp.smul_const
      (coefficient k))
  apply weighted_complex_bound (Bupper := ∑ k ∈ s, ‖coefficient k‖)
    (Blower := ∑ k ∈ s, ‖coefficient k‖) hr hdiff ?_ ?_ hreal z
  · intro w hw
    apply norm_shifted_frequency_sum_le
    intro k hk
    apply mul_nonneg _ hw
    linarith [(hfrequency k hk).1]
  · intro w hw
    have hphase : ∀ k ∈ s, 0 ≤ (-r + frequency k) * w.im := by
      intro k hk
      apply mul_nonneg_of_nonpos_of_nonpos _ hw
      linarith [(hfrequency k hk).2]
    simpa only [Complex.ofReal_neg] using
      norm_shifted_frequency_sum_le s frequency coefficient (-r) w hphase

end Foundation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
