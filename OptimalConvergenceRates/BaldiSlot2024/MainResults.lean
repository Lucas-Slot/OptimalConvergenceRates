/-
  OptimalConvergenceRates/BaldiSlot2024/MainResults.lean

  Public Baldi-Slot 2024 Putinar degree-bound and Lasserre-rate theorems.
  Theorem numbering follows arXiv:2302.12558v3 (21 February 2025).
-/
import OptimalConvergenceRates.BaldiSlot2024.UpperBound
import OptimalConvergenceRates.BaldiSlot2024.LowerBound

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

variable {n : ℕ}

/-! ## Degree convention

The order in `BoxQuadraticModule n r` bounds the total degree of each complete
weighted certificate term. It is not the SOS square-root degree used by sphere
certificates such as `SphereSOSMod`, whose sphere-relation multiplier is left
unbounded. In TeX that uses a half-degree order `s` for complete terms of degree
at most `2 * s`, the corresponding Lean cube order is `2 * s`.
-/

/-! ## Theorem 11 (explicit form of Theorem 3): Upper degree bound for Putinar certificates

If f is strictly positive on B^n = [-1,1]^n with degree ≤ d, then
f ∈ QM(1-x₁², ..., 1-xₙ²)_{r·n} whenever
  r ≥ constLeading · d² · (log n + 1) · ‖f‖/f_min
      + max(π·d·√(2n), √(constSqrt · C(n,d) · ‖f‖/f_min)).

The leading term has only the absolute constant constLeading = 8K+2
(where K = constCChebyshev). The Schmüdgen constant C(n,d) appears only
under a square root in the lower-order term. -/
theorem upperBoundMembershipBoxQM (f : MvPolynomial (Fin n) ℝ) (d r : ℕ)
    (hd : f.totalDegree ≤ d)
    (hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f)
    (hr : constLeading * d ^ 2 * (Real.log (n : ℝ) + 1) *
      polySupNorm f / polyMin f +
      max (Real.pi * d * Real.sqrt (2 * n))
          (Real.sqrt (constSqrt * constC n d * polySupNorm f / polyMin f))
      ≤ r) :
    f ∈ BoxQuadraticModule n (r * n) :=
  upper_degree_bound f d r hd hf_pos hr


/-! ## Theorem 4: Lower degree bound for Putinar certificates

The polynomial (1-x₁²)(1-x₂²) + ε requires QM certificate degree
at least Ω(ε^{-1/8}). This holds for all n ≥ 2 by restriction to
the first two coordinates. -/
theorem lowerBoundMembershipBoxQM (m : ℕ) (hm : 2 ≤ m)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (r : ℕ)
    (hmem : f_eps_n m hm ε ∈ BoxQuadraticModule m r) :
    lower_bound_const * ε ^ (-(1 : ℝ) / 8) ≤ (r : ℝ) :=
  lower_bound_general_n m hm ε hε hε1 r hmem


/-! ## Corollary 15: Upper bound on QM-Lasserre convergence rate

For any f on B^n with degree ≤ d, the QM-Lasserre relaxation gap is O(1/r):
  polyMin f - lasserre_bound_box_qm(f, r·n) ≤ C · (polyMax f - polyMin f) / r
where C = 2 · constUpperBound(n,d) · d² · (log(n)+1).

The hypothesis r ≥ C ensures that the shifted polynomial
g = f - (polyMin f - C·Δ/r) satisfies the condition of Theorem 11. -/
theorem upperBoundConvergenceRateBoxQM (f : MvPolynomial (Fin n) ℝ) (d r : ℕ)
    (hn : 0 < n) (hd : 0 < d)
    (hdeg : f.totalDegree ≤ d)
    (hr : constCor210 n d ≤ (r : ℝ)) :
    ↑(polyMin f - constCor210 n d * (polyMax f - polyMin f) / r) ≤
    lasserre_bound_box_qm f (r * n) := by
  set C := constCor210 n d with hC_def
  set A := constUpperBound n d * (↑d) ^ 2 * (Real.log (↑n) + 1) with hA_def
  set Δ := polyMax f - polyMin f with hΔ_def
  have hΔ_nn : 0 ≤ Δ := sub_nonneg.mpr (polyMin_le_polyMax f)
  have hA_pos : 0 < A := by
    simp only [hA_def]
    apply mul_pos (mul_pos (constUpperBound_pos n d hn hd) _) _
    · exact pow_pos (Nat.cast_pos.mpr hd) 2
    · linarith [Real.log_nonneg (by exact_mod_cast hn : (1 : ℝ) ≤ ↑n)]
  have hC_eq : C = 2 * A := by simp [hC_def, hA_def, constCor210]; ring
  have hC_pos : 0 < C := by linarith
  -- Handle r = 0: C > 0 contradicts C ≤ r.
  by_cases hr0 : r = 0
  · subst hr0
    norm_num at hr
    linarith
  have hr_pos : (0 : ℝ) < ↑r := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr0)
  have hr_ge_C : C ≤ ↑r := hC_def ▸ hr
  have hr_ge_2A : 2 * A ≤ ↑r := hC_eq ▸ hr_ge_C
  -- Handle Δ = 0 (f constant): gap = 0, need lasserre_bound_box_qm ≥ polyMin f
  by_cases hΔ0 : Δ = 0
  · have hCΔr : C * Δ / ↑r = 0 := by rw [hΔ0]; ring
    rw [hCΔr, sub_zero]
    have hmax_eq : polyMax f = polyMin f := by linarith
    -- For any l' < polyMin f, f - C(l') ∈ QM (condition number is 1)
    have key : ∀ l' : ℝ, l' < polyMin f →
        (f - MvPolynomial.C l') ∈ BoxQuadraticModule n (r * n) := by
      intro l' hl'
      have hg'_pos : ∀ x ∈ Hypercube n,
          0 < MvPolynomial.eval x (f - MvPolynomial.C l') := by
        intro x hx; simp [map_sub, MvPolynomial.eval_C]; linarith [polyMin_le_eval f x hx]
      have hg'_sup_le : polySupNorm (f - MvPolynomial.C l') ≤ polyMin f - l' :=
        calc polySupNorm (f - MvPolynomial.C l')
            ≤ polyMax (f - MvPolynomial.C l') :=
              polySupNorm_le_polyMax_of_nonneg _ (fun x hx => le_of_lt (hg'_pos x hx))
          _ = polyMax f - l' := polyMax_sub_C f l'
          _ = polyMin f - l' := by rw [hmax_eq]
      have hcond : A * polySupNorm (f - MvPolynomial.C l') /
          polyMin (f - MvPolynomial.C l') ≤ ↑r := by
        rw [polyMin_sub_C]
        calc A * polySupNorm (f - MvPolynomial.C l') / (polyMin f - l')
            ≤ A * (polyMin f - l') / (polyMin f - l') :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hg'_sup_le hA_pos.le) (by linarith)
          _ = A := by field_simp; exact div_self (ne_of_gt (by linarith))
          _ ≤ ↑r := by linarith
      exact upper_degree_bound_weak _ d r
        ((MvPolynomial.totalDegree_sub_C_le f l').trans hdeg) hg'_pos hcond
    -- Conclude: lasserre_bound_box_qm ≥ polyMin f via sSup argument
    unfold lasserre_bound_box_qm
    set S := { l : ℝ | (f - MvPolynomial.C l) ∈ BoxQuadraticModule n (r * n) }
    have hne : S.Nonempty := ⟨polyMin f - 1, key _ (by linarith)⟩
    rw [dif_pos hne]; apply WithBot.coe_le_coe.mpr
    have hbdd : BddAbove S := ⟨polyMin f, fun l hl => by
      have := BoxQuadraticModule_subset_nonneg hl
      obtain ⟨x, hx, heval⟩ := polyMin_mem f
      have := this x hx; simp [map_sub, MvPolynomial.eval_C] at this; linarith [heval]⟩
    by_contra h_neg; push_neg at h_neg
    have : (sSup S + polyMin f) / 2 ∈ S := key _ (by linarith)
    linarith [le_csSup hbdd this]
  -- Main case: Δ > 0. Set gap = C·Δ/r.
  have hΔ_pos : 0 < Δ := lt_of_le_of_ne hΔ_nn (Ne.symm hΔ0)
  set gap := C * Δ / ↑r with hgap_def
  have hgap_pos : 0 < gap := div_pos (mul_pos hC_pos hΔ_pos) hr_pos
  set l := polyMin f - gap with hl_def
  set g := f - MvPolynomial.C l with hg_def
  have hg_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x g := by
    intro x hx; simp only [hg_def, map_sub, MvPolynomial.eval_C, hl_def]
    linarith [polyMin_le_eval f x hx]
  have hg_deg : g.totalDegree ≤ d :=
    le_trans (MvPolynomial.totalDegree_sub_C_le f l) hdeg
  have hg_min : polyMin g = gap := by
    change polyMin (f - MvPolynomial.C l) = gap; rw [polyMin_sub_C, hl_def]; ring
  have hg_sup : polySupNorm g ≤ Δ + gap :=
    calc polySupNorm g
        ≤ polyMax g := polySupNorm_le_polyMax_of_nonneg g
            (fun x hx => le_of_lt (hg_pos x hx))
      _ = polyMax f - l := polyMax_sub_C f l
      _ = Δ + gap := by rw [hl_def, hΔ_def]; ring
  -- Verify: A·(Δ+gap)/gap = (r+2A)/2 ≤ r  (using 2A ≤ r)
  have hcond : A * polySupNorm g / polyMin g ≤ ↑r := by
    rw [hg_min]
    calc A * polySupNorm g / gap
        ≤ A * (Δ + gap) / gap :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hg_sup hA_pos.le) hgap_pos.le
      _ = A * (Δ + C * Δ / ↑r) / (C * Δ / ↑r) := by rw [hgap_def]
      _ = (↑r + 2 * A) / 2 := by rw [hC_eq]; field_simp
      _ ≤ ↑r := by linarith
  exact lasserre_bound_box_qm_ge_feasible f (r * n)
    (upper_degree_bound_weak g d r hg_deg hg_pos hcond)

/-- Positive-polynomial compatibility form of Corollary 15, with its former
    condition-number threshold. -/
theorem upperBoundConvergenceRateBoxQM_of_pos (f : MvPolynomial (Fin n) ℝ)
    (d r : ℕ) (hn : 0 < n) (hd : 0 < d) (hdeg : f.totalDegree ≤ d)
    (hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f)
    (hr : constCor210 n d * polyMax f / polyMin f ≤ r) :
    ↑(polyMin f - constCor210 n d * (polyMax f - polyMin f) / r) ≤
    lasserre_bound_box_qm f (r * n) := by
  apply upperBoundConvergenceRateBoxQM f d r hn hd hdeg
  have hmin_pos := polyMin_pos_of_pos f hf_pos
  have hC_pos : 0 < constCor210 n d := by
    rw [constCor210]
    have hd_cast : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
    have hlog : 0 < Real.log (n : ℝ) + 1 := by
      linarith [Real.log_nonneg (by exact_mod_cast hn : (1 : ℝ) ≤ ↑n)]
    exact
      mul_pos
        (mul_pos
          (mul_pos (by norm_num : (0 : ℝ) < 2) (constUpperBound_pos n d hn hd))
          (pow_pos hd_cast 2))
        hlog
  calc
    constCor210 n d = constCor210 n d * 1 := (mul_one _).symm
    _ ≤ constCor210 n d * (polyMax f / polyMin f) :=
      mul_le_mul_of_nonneg_left
        ((le_div_iff₀ hmin_pos).mpr (by simpa using polyMin_le_polyMax f)) hC_pos.le
    _ = constCor210 n d * polyMax f / polyMin f := by ring
    _ ≤ (r : ℝ) := hr

/-- Gap form of Corollary 15: for any finite Lasserre bound value v,
    the gap polyMin f - v is at most C · Δ / r. Vacuously true when
    lasserre_bound_box_qm = ⊥. -/
theorem upperBoundConvergenceRate_gap (f : MvPolynomial (Fin n) ℝ) (d r : ℕ)
    (hn : 0 < n) (hd : 0 < d)
    (hdeg : f.totalDegree ≤ d)
    (hr : constCor210 n d ≤ (r : ℝ)) :
    ∀ v : ℝ, lasserre_bound_box_qm f (r * n) = ↑v →
    polyMin f - v ≤ constCor210 n d * (polyMax f - polyMin f) / (r : ℝ) := by
  intro v hv
  have h := upperBoundConvergenceRateBoxQM f d r hn hd hdeg hr
  rw [hv, WithBot.coe_le_coe] at h; linarith

/-- Positive-polynomial compatibility form of the Corollary 15 gap bound. -/
theorem upperBoundConvergenceRate_gap_of_pos (f : MvPolynomial (Fin n) ℝ)
    (d r : ℕ) (hn : 0 < n) (hd : 0 < d) (hdeg : f.totalDegree ≤ d)
    (hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f)
    (hr : constCor210 n d * polyMax f / polyMin f ≤ r) :
    ∀ v : ℝ, lasserre_bound_box_qm f (r * n) = ↑v →
    polyMin f - v ≤ constCor210 n d * (polyMax f - polyMin f) / (r : ℝ) := by
  intro v hv
  have h := upperBoundConvergenceRateBoxQM_of_pos f d r hn hd hdeg hf_pos hr
  rw [hv, WithBot.coe_le_coe] at h
  linarith

/-! ## Corollary 16: Lower bound on QM-Lasserre convergence rate

For f₀ = (1-x₁²)(1-x₂²) on B², the QM-Lasserre relaxation satisfies
  lasserre_bound_box_qm(f₀, r) ≤ -(c/r)^8
where c = lower_bound_const = 1/16. Since polyMin(f₀) = 0, this means
the gap is at least (c/r)^8, giving an Ω(1/r^8) lower bound,
in contrast to the O(1/r²) upper rate of the full preordering (Slot–Laurent 2022). -/
theorem lowerBoundConvergenceRateBoxQM (r : ℕ) (hr : 0 < r) :
    lasserre_bound_box_qm ((1 - X 0 ^ 2) * (1 - X 1 ^ 2) : MvPolynomial (Fin 2) ℝ) r ≤
      ↑(-(lower_bound_const / (r : ℝ)) ^ 8) := by
  change lasserre_bound_box_qm f_zero r ≤ _
  have hr_pos : (0 : ℝ) < ↑r := Nat.cast_pos.mpr hr
  have hc_pos : 0 < lower_bound_const := lower_bound_const_pos
  -- Every feasible λ satisfies λ ≤ -(c/r)^8
  suffices key : ∀ l : ℝ,
      (f_zero - MvPolynomial.C l) ∈ BoxQuadraticModule 2 r →
      l ≤ -(lower_bound_const / ↑r) ^ 8 by
    unfold lasserre_bound_box_qm
    split_ifs with hne
    · exact WithBot.coe_le_coe.mpr (csSup_le hne (fun l hl => key l hl))
    · exact bot_le
  intro l hl
  -- f_zero - C(l) = f_eps(-l)
  have hfl : f_zero - MvPolynomial.C l = f_eps (-l) := by
    simp [f_zero, f_eps, map_neg]; ring
  rw [hfl] at hl
  -- Nonnegativity at corner (1,1) gives -l ≥ 0
  have hge0 : 0 ≤ -l := by
    have := BoxQuadraticModule_subset_nonneg hl corner_11 corner_11_in_hypercube
    rw [f_eps_eval, corner_11_val_0, corner_11_val_1] at this; linarith
  -- Case l = 0: f_zero ∉ QM, contradiction
  by_cases heq0 : l = 0
  · exfalso; subst heq0; rw [neg_zero, ← f_zero_eq] at hl
    exact f_not_in_quadratic_module r hl
  have hpos : 0 < -l := lt_of_le_of_ne hge0 (by intro h; exact heq0 (by linarith))
  -- Case -l ≥ 1: (c/r)^8 ≤ 1 ≤ -l
  by_cases hge1 : 1 ≤ -l
  · have : (lower_bound_const / ↑r) ^ 8 ≤ 1 := by
      apply pow_le_one₀ (div_nonneg hc_pos.le hr_pos.le)
      rw [div_le_one hr_pos]; unfold lower_bound_const
      calc (1:ℝ) / 16 ≤ 1 := by norm_num
        _ ≤ ↑r := by exact_mod_cast hr
    linarith
  -- Case 0 < -l < 1: apply Theorem 4 to get (-l) ≥ (c/r)^8
  push_neg at hge1
  have hbound := lower_degree_bound (-l) hpos hge1 r hl
  -- From c · (-l)^{-1/8} ≤ r, derive (c/r)^8 ≤ -l
  have h1 : lower_bound_const / ↑r ≤ (-l) ^ ((1:ℝ)/8) := by
    rw [div_le_iff₀ hr_pos]
    rw [show (-(1:ℝ)/8) = -((1:ℝ)/8) from by ring] at hbound
    rw [Real.rpow_neg hpos.le] at hbound
    rw [mul_inv_le_iff₀ (Real.rpow_pos_of_pos hpos _)] at hbound
    linarith
  have hcr_nn : 0 ≤ lower_bound_const / ↑r := div_nonneg hc_pos.le hr_pos.le
  have h2 : (lower_bound_const / ↑r) ^ 8 ≤ -l := by
    have step := pow_le_pow_left₀ hcr_nn h1 8
    have : ((-l) ^ ((1:ℝ)/8)) ^ (8 : ℕ) = -l := by
      rw [← Real.rpow_natCast ((-l) ^ ((1:ℝ)/8)) 8,
          ← Real.rpow_mul hpos.le]; simp [Real.rpow_one]
    linarith
  linarith

/-- Gap form of Corollary 16: for any finite Lasserre bound value v,
    the gap -v is at least (c/r)^8. Vacuously true when
    lasserre_bound_box_qm = ⊥. -/
theorem lowerBoundConvergenceRate_gap (r : ℕ) (hr : 0 < r) :
    ∀ v : ℝ, lasserre_bound_box_qm
      ((1 - X 0 ^ 2) * (1 - X 1 ^ 2) : MvPolynomial (Fin 2) ℝ) r = ↑v →
    (lower_bound_const / (r : ℝ)) ^ 8 ≤ -v := by
  intro v hv
  have h := lowerBoundConvergenceRateBoxQM r hr
  rw [hv, WithBot.coe_le_coe] at h; linarith

end OptimalConvergenceRates

end
