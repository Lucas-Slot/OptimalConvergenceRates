/-
  OptimalConvergenceRates/MarkovLukacz/UnivariateSOS.lean

  Globally nonnegative univariate real polynomials as sums of squares.
-/
import OptimalConvergenceRates.MarkovLukacz.MarkovLukacz

open Polynomial Real

noncomputable section

namespace OptimalConvergenceRates

/-! ## Elementary SOS closure lemmas -/

/-- A nonnegative constant univariate polynomial is SOS. -/
theorem IsSOSUni_C_nonneg (c : ℝ) (hc : 0 ≤ c) : IsSOSUni (Polynomial.C c) := by
  refine ⟨1, fun _ ↦ Polynomial.C (Real.sqrt c), ?_⟩
  simp only [Fin.sum_univ_one, sq, ← Polynomial.C_mul, Real.mul_self_sqrt hc]

/-- `IsSOSUni` is closed under addition. -/
theorem IsSOSUni_add {p q : Polynomial ℝ} (hp : IsSOSUni p) (hq : IsSOSUni q) :
    IsSOSUni (p + q) := by
  obtain ⟨m₁, f₁, rfl⟩ := hp
  obtain ⟨m₂, f₂, rfl⟩ := hq
  exact ⟨m₁ + m₂, Fin.append f₁ f₂, by
    rw [Fin.sum_univ_add]
    simp [Fin.append]⟩

/-- Multiplying an SOS polynomial by a square preserves being SOS. -/
theorem IsSOSUni_sq_mul {s q : Polynomial ℝ} (hq : IsSOSUni q) :
    IsSOSUni (s ^ 2 * q) := by
  obtain ⟨m, f, rfl⟩ := hq
  refine ⟨m, fun i ↦ s * f i, ?_⟩
  simp only [Finset.mul_sum, mul_pow]

/-- If `q` is SOS and `c ≥ 0`, then `C c + s² q` is SOS. -/
theorem IsSOSUni_C_add_sq_mul (c : ℝ) (hc : 0 ≤ c) (s q : Polynomial ℝ)
    (hq : IsSOSUni q) : IsSOSUni (Polynomial.C c + s ^ 2 * q) :=
  IsSOSUni_add (IsSOSUni_C_nonneg c hc) (IsSOSUni_sq_mul (s := s) hq)

/-! ## Continuity facts -/

/-- A continuous function nonnegative away from one point is nonnegative at that point. -/
theorem continuousAt_nonneg_of_nonneg_ne {f : ℝ → ℝ} {r : ℝ}
    (hf : ContinuousAt f r) (h : ∀ x, x ≠ r → 0 ≤ f x) : 0 ≤ f r := by
  by_contra hneg
  push Not at hneg
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp hf (-f r / 2) (by linarith)
  let x := r + δ / 2
  have hx_ne : x ≠ r := by
    simp [x]
    linarith
  have hx_dist : dist x r < δ := by
    rw [Real.dist_eq]
    have hδ_half : 0 < δ / 2 := by linarith
    rw [show x - r = δ / 2 by simp [x], abs_of_pos hδ_half]
    linarith
  have hx_close := hδ hx_dist
  rw [Real.dist_eq] at hx_close
  have hx_neg : f x < 0 := by
    have hupper : f x - f r < -f r / 2 := lt_of_le_of_lt (le_abs_self _) hx_close
    linarith
  exact not_le_of_gt hx_neg (h x hx_ne)

/-- A continuous function nonnegative to the right and nonpositive to the left vanishes. -/
theorem continuousAt_eq_zero_of_right_nonneg_left_nonpos {f : ℝ → ℝ} {r : ℝ}
    (hf : ContinuousAt f r) (hright : ∀ x, r < x → 0 ≤ f x)
    (hleft : ∀ x, x < r → f x ≤ 0) : f r = 0 := by
  have hnonneg : 0 ≤ f r := by
    by_contra hneg
    push Not at hneg
    obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp hf (-f r / 2) (by linarith)
    let x := r + δ / 2
    have hx_gt : r < x := by simp [x]; linarith
    have hx_dist : dist x r < δ := by
      rw [Real.dist_eq]
      have hδ_half : 0 < δ / 2 := by linarith
      rw [show x - r = δ / 2 by simp [x], abs_of_pos hδ_half]
      linarith
    have hx_close := hδ hx_dist
    rw [Real.dist_eq] at hx_close
    have hx_neg : f x < 0 := by
      have hupper : f x - f r < -f r / 2 := lt_of_le_of_lt (le_abs_self _) hx_close
      linarith
    exact not_le_of_gt hx_neg (hright x hx_gt)
  have hnonpos : f r ≤ 0 := by
    by_contra hpos
    push Not at hpos
    obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp hf (f r / 2) (by linarith)
    let x := r - δ / 2
    have hx_lt : x < r := by simp [x]; linarith
    have hx_dist : dist x r < δ := by
      rw [Real.dist_eq]
      have h : x - r = -δ / 2 := by simp [x]; ring
      rw [h, abs_of_neg]
      · linarith
      · linarith
    have hx_close := hδ hx_dist
    rw [Real.dist_eq] at hx_close
    have hx_pos : 0 < f x := by
      have hlower : -(f x - f r) < f r / 2 := lt_of_le_of_lt (neg_le_abs _) hx_close
      linarith
    exact not_le_of_gt hx_pos (hleft x hx_lt)
  exact le_antisymm hnonpos hnonneg

/-- A globally nonnegative polynomial attains a global minimum. -/
theorem exists_global_min_of_nonnegative (p : Polynomial ℝ)
    (hp : ∀ x : ℝ, 0 ≤ p.eval x) : ∃ r : ℝ, ∀ x : ℝ, p.eval r ≤ p.eval x := by
  obtain ⟨r, hr⟩ := Polynomial.exists_forall_norm_le p
  refine ⟨r, fun x ↦ ?_⟩
  have h := hr x
  rw [Real.norm_eq_abs, abs_of_nonneg (hp r), Real.norm_eq_abs, abs_of_nonneg (hp x)] at h
  exact h

/-! ## Minimum decomposition -/

/-- At a global minimum of a nonconstant globally nonnegative polynomial, the polynomial
splits as `C m + (X - C r)^2 * q`, with `q` again globally nonnegative and lower degree. -/
theorem exists_minimum_sq_decomposition (p : Polynomial ℝ) (hp_nonconst : p.natDegree ≠ 0)
    (hp : ∀ x : ℝ, 0 ≤ p.eval x) :
    ∃ (r m : ℝ) (q : Polynomial ℝ), 0 ≤ m ∧
      p = Polynomial.C m + (Polynomial.X - Polynomial.C r) ^ 2 * q ∧
      (∀ x : ℝ, 0 ≤ q.eval x) ∧ q.natDegree < p.natDegree := by
  obtain ⟨r, hmin⟩ := exists_global_min_of_nonnegative p hp
  let m := p.eval r
  have hm : 0 ≤ m := by simpa [m] using hp r
  have hdvd₁ : Polynomial.X - Polynomial.C r ∣ p - Polynomial.C m := by
    simpa [m] using (Polynomial.X_sub_C_dvd_sub_C_eval (a := r) (p := p))
  obtain ⟨u, hu⟩ := hdvd₁
  have hu_right : ∀ x, r < x → 0 ≤ u.eval x := by
    intro x hx
    have hsub_nonneg : 0 ≤ (p - Polynomial.C m).eval x := by
      simp only [Polynomial.eval_sub, Polynomial.eval_C]
      exact sub_nonneg.mpr (hmin x)
    rw [hu] at hsub_nonneg
    simp only [eval_mul, eval_sub, eval_X, eval_C] at hsub_nonneg
    exact nonneg_of_mul_nonneg_right hsub_nonneg (by linarith)
  have hu_left : ∀ x, x < r → u.eval x ≤ 0 := by
    intro x hx
    have hsub_nonneg : 0 ≤ (p - Polynomial.C m).eval x := by
      simp only [Polynomial.eval_sub, Polynomial.eval_C]
      exact sub_nonneg.mpr (hmin x)
    rw [hu] at hsub_nonneg
    simp only [eval_mul, eval_sub, eval_X, eval_C] at hsub_nonneg
    exact nonpos_of_mul_nonneg_right hsub_nonneg (by linarith)
  have hu_r : u.eval r = 0 :=
    continuousAt_eq_zero_of_right_nonneg_left_nonpos u.continuous.continuousAt hu_right hu_left
  have hdvd₂ : Polynomial.X - Polynomial.C r ∣ u := by
    rw [Polynomial.dvd_iff_isRoot]
    simpa [Polynomial.IsRoot.def] using hu_r
  obtain ⟨q, hqfac⟩ := hdvd₂
  have hsub_sq : p - Polynomial.C m = (Polynomial.X - Polynomial.C r) ^ 2 * q := by
    rw [hu, hqfac]
    ring
  have hp_decomp : p = Polynomial.C m + (Polynomial.X - Polynomial.C r) ^ 2 * q := by
    rw [← hsub_sq]
    ring
  have hq_nonneg_ne : ∀ x, x ≠ r → 0 ≤ q.eval x := by
    intro x hx
    have hsub_nonneg : 0 ≤ (p - Polynomial.C m).eval x := by
      simp only [Polynomial.eval_sub, Polynomial.eval_C]
      exact sub_nonneg.mpr (hmin x)
    rw [hsub_sq] at hsub_nonneg
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at hsub_nonneg
    exact nonneg_of_mul_nonneg_right hsub_nonneg (sq_pos_of_ne_zero (sub_ne_zero.mpr hx))
  have hq_nonneg : ∀ x : ℝ, 0 ≤ q.eval x := by
    intro x
    by_cases hx : x = r
    · subst x
      exact continuousAt_nonneg_of_nonneg_ne q.continuous.continuousAt hq_nonneg_ne
    · exact hq_nonneg_ne x hx
  have hq0 : q ≠ 0 := by
    intro hq_zero
    have hp_const : p.natDegree = 0 := by
      rw [hp_decomp, hq_zero, mul_zero, add_zero, Polynomial.natDegree_C]
    exact hp_nonconst hp_const
  have hL2_ne : (Polynomial.X - Polynomial.C r) ^ 2 ≠ (0 : Polynomial ℝ) :=
    pow_ne_zero _ (Polynomial.X_sub_C_ne_zero r)
  have hdeg_sub : (p - Polynomial.C m).natDegree = p.natDegree := Polynomial.natDegree_sub_C
  have hdeg_L2 : ((Polynomial.X - Polynomial.C r) ^ 2 : Polynomial ℝ).natDegree = 2 := by
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
  have hdeg : p.natDegree = 2 + q.natDegree := by
    rw [← hdeg_sub, hsub_sq, Polynomial.natDegree_mul hL2_ne hq0, hdeg_L2]
  refine ⟨r, m, q, hm, hp_decomp, hq_nonneg, ?_⟩
  omega

/-- Globally nonnegative univariate real polynomials are SOS. -/
theorem IsSOSUni_of_nonneg (p : Polynomial ℝ) (hp : ∀ t : ℝ, 0 ≤ p.eval t) :
    IsSOSUni p := by
  classical
  generalize hn : p.natDegree = n
  revert p
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro p hp hn
      by_cases hn0 : n = 0
      · have hpdeg : p.natDegree = 0 := by simpa [hn0] using hn
        obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hpdeg
        have hc_nonneg : 0 ≤ c := by
          have h0 := hp 0
          rw [← hc] at h0
          simpa using h0
        rw [← hc]
        exact IsSOSUni_C_nonneg c hc_nonneg
      · have hp_nonconst : p.natDegree ≠ 0 := by omega
        obtain ⟨r, m, q, hm, hp_decomp, hq_nonneg, hq_deg⟩ :=
          exists_minimum_sq_decomposition p hp_nonconst hp
        have hq_sos : IsSOSUni q := by
          exact ih q.natDegree (by omega) q hq_nonneg rfl
        rw [hp_decomp]
        exact IsSOSUni_C_add_sq_mul m hm (Polynomial.X - Polynomial.C r) q hq_sos

end OptimalConvergenceRates
