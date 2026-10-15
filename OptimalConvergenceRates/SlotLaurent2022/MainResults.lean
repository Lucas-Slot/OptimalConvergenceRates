/-
  OptimalConvergenceRates/SlotLaurent2022/MainResults.lean

  Public Slot-Laurent 2022 convergence-rate and Schmuedgen membership theorems.
-/
import OptimalConvergenceRates.SlotLaurent2022.MainProof

open MvPolynomial Finset Real

noncomputable section

namespace OptimalConvergenceRates

variable {n : ℕ}

/-! ## Main Theorem (Theorem 2) -/

/-- Theorem 2 (Main): For a polynomial f of degree d, for all r ≥ πd√(2n):
    f_min - f_{(r+1)n} ≤ C(n,d)/r² · (f_max - f_min) -/
theorem upperBoundConvergenceRateBoxPreo (f : MvPolynomial (Fin n) ℝ) (d r : ℕ)
    (hd : f.totalDegree ≤ d)
    (hr : Real.pi * d * Real.sqrt (2 * n) ≤ r)
    (hfmax : polyMin f < polyMax f) :
    ↑(polyMin f - constC n d / (r : ℝ) ^ 2 * (polyMax f - polyMin f)) ≤
    lasserre_bound_box_preo f ((r + 1) * n) := by
  -- Step 0: Derive d > 0, n > 0 from hfmax (nonconstant poly needs d,n > 0)
  have hd_pos : 0 < d := by
    by_contra hd0; push Not at hd0; exfalso
    have hfz : f.totalDegree = 0 := by omega
    set c := f.coeff 0
    have hfeq : f = MvPolynomial.C c := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hfz
    obtain ⟨x, hx, hmin⟩ := polyMin_mem f
    obtain ⟨y, hy, hmax⟩ := polyMax_mem f
    rw [hfeq] at hfmax hmin hmax
    rw [MvPolynomial.eval_C] at hmin hmax
    linarith
  have hn_pos : 0 < n := by
    by_contra hn0; push Not at hn0; interval_cases n; exfalso
    obtain ⟨x, hx, hmin⟩ := polyMin_mem f
    obtain ⟨y, hy, hmax⟩ := polyMax_mem f
    have heq : x = y := Subsingleton.elim x y
    linarith [show MvPolynomial.eval x f = MvPolynomial.eval y f by rw [heq]]
  -- Step 1: Derive d ≤ r from hr (using n > 0)
  have hdr : d ≤ r := by
    by_contra h; push Not at h
    have hd_pos' : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos
    have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * n) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ 2 * n by omega))
    have : (d : ℝ) ≤ Real.pi * d * Real.sqrt (2 * n) := by
      calc (d : ℝ) = 1 * d * 1 := by ring
        _ ≤ Real.pi * d * Real.sqrt (2 * n) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right
              (by linarith [Real.pi_gt_three]) hd_pos'.le) hsqrt
              (by linarith) (by positivity)
    linarith [show (r : ℝ) < (d : ℝ) from by exact_mod_cast h]
  have hfr : f.totalDegree ≤ r := le_trans hd hdr
  have hr_pos : 0 < r := by omega
  -- Step 2: Apply outline_lemma with ε = constC n d / r²
  exact outline_lemma f r (constC n d / (r : ℝ) ^ 2)
    (div_pos (constC_pos n d hn_pos hd_pos) (sq_pos_of_pos (Nat.cast_pos.mpr hr_pos)))
    hfr
    (fun p hp hn => kernel_property_P1 r p hp hn)
    (P2_outline_verification r d f hd hdr hfr hr)


/-! ## Corollary: Degree bound for Schmüdgen certificates -/

/-- Corollary: If f ≥ 0 on B^n, then for any η > 0,
    f + η ∈ Q(B^n)_{(r+1)n} for all r ≥ max{πd√(2n), √(C(n,d)(f_max-f_min)/η)} -/
theorem upperBoundMembershipBoxPreo (f : MvPolynomial (Fin n) ℝ) (d r : ℕ) (η : ℝ)
    (hd : f.totalDegree ≤ d)
    (hη : 0 < η)
    (hf_nonneg : IsNonnegOn f (Hypercube n))
    (hr1 : Real.pi * d * Real.sqrt (2 * n) ≤ r)
    (hr2 : Real.sqrt (constC n d * (polyMax f - polyMin f) / η) ≤ r) :
    (f + MvPolynomial.C η) ∈ BoxPreordering n ((r + 1) * n) := by
  -- Edge case: n = 0 (f is constant, f + η is a positive constant in BoxPreordering)
  by_cases hn0 : n = 0
  · subst hn0
    -- n = 0: f is a poly in 0 variables, hence constant
    set c := f.coeff 0
    have hf_const : f = MvPolynomial.C c := by
      ext m; rw [show m = 0 from Subsingleton.elim m 0]; simp [c, MvPolynomial.coeff_C]
    have hc_nonneg : 0 ≤ c := by
      obtain ⟨x, hx⟩ := Hypercube_nonempty (n := 0)
      have := hf_nonneg x hx; rw [hf_const, MvPolynomial.eval_C] at this; exact this
    rw [hf_const, ← MvPolynomial.C_add]
    exact positive_const_in_box_preordering (by linarith) 0 _
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  -- Edge case: d = 0 (f is constant with f ≥ 0, f + C(η) > 0, in BoxPreordering)
  by_cases hd0 : d = 0
  · subst hd0
    -- d = 0: f has totalDegree ≤ 0, so f is constant
    set c := f.coeff 0
    have hf_const : f = MvPolynomial.C c :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hd)
    have hc_nonneg : 0 ≤ c := by
      obtain ⟨x, hx⟩ := Hypercube_nonempty (n := n)
      have := hf_nonneg x hx; rw [hf_const, MvPolynomial.eval_C] at this; exact this
    rw [hf_const, ← MvPolynomial.C_add]
    exact positive_const_in_box_preordering (by linarith) n _
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd0
  -- Step 1: Derive d ≤ r from hr1 (using n > 0)
  have hdr : d ≤ r := by
    by_contra h; push Not at h
    have hd_pos' : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos
    have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * n) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ 2 * n by omega))
    have : (d : ℝ) ≤ Real.pi * d * Real.sqrt (2 * n) := by
      calc (d : ℝ) = 1 * d * 1 := by ring
        _ ≤ Real.pi * d * Real.sqrt (2 * n) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right
              (by linarith [Real.pi_gt_three]) hd_pos'.le) hsqrt
              (by linarith) (by positivity)
    linarith [show (r : ℝ) < (d : ℝ) from by exact_mod_cast h]
  have hfr : f.totalDegree ≤ r := le_trans hd hdr
  have hr_pos : 0 < r := by omega
  -- Step 2: Get preordering membership from outline_lemma_box_preordering
  set ε := constC n d / (r : ℝ) ^ 2
  have hε_pos : 0 < ε :=
    div_pos (constC_pos n d hn_pos hd_pos) (sq_pos_of_pos (Nat.cast_pos.mpr hr_pos))
  have hfeas : (f - MvPolynomial.C (polyMin f - ε * (polyMax f - polyMin f))) ∈
      BoxPreordering n ((r + 1) * n) :=
    outline_lemma_box_preordering f r ε hε_pos hfr
      (fun p hp hn => kernel_property_P1 r p hp hn)
      (P2_outline_verification r d f hd hdr hfr hr1)
  -- Step 3: polyMin f - ε * Δ ≥ -η
  have hfmin_nonneg : 0 ≤ polyMin f := by
    obtain ⟨x, hx, heval⟩ := polyMin_mem f
    rw [← heval]; exact hf_nonneg x hx
  have hΔ_nonneg : 0 ≤ polyMax f - polyMin f := by linarith [polyMin_le_polyMax f]
  have hε_Δ_le_η : ε * (polyMax f - polyMin f) ≤ η := by
    by_cases hr0' : (r : ℝ) = 0
    · simp [ε, hr0']; linarith
    · have hr_pos' : (0 : ℝ) < r := lt_of_le_of_ne (Nat.cast_nonneg r) (Ne.symm hr0')
      have hr2_sq : constC n d * (polyMax f - polyMin f) / η ≤ (r : ℝ) ^ 2 :=
        (Real.sqrt_le_left (Nat.cast_nonneg r)).mp hr2
      rw [div_le_iff₀ hη] at hr2_sq
      change constC n d / (r : ℝ) ^ 2 * (polyMax f - polyMin f) ≤ η
      rw [div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hr_pos')]
      linarith
  have hbound : -η ≤ polyMin f - ε * (polyMax f - polyMin f) := by linarith
  -- Step 4: By downward closure, -η is feasible
  have hdown := lasserre_feasible_downward hbound hfeas
  -- Step 5: f - C(-η) = f + C(η)
  have : f + MvPolynomial.C η = f - MvPolynomial.C (-η) := by simp [map_neg]
  rw [this]; exact hdown


end OptimalConvergenceRates

end
