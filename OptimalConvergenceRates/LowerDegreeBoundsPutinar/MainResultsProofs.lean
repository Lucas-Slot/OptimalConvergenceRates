import OptimalConvergenceRates.LowerDegreeBoundsPutinar.MainProof
import OptimalConvergenceRates.BaldiSlot2024.LowerBound

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates.LowerDegreeBoundsPutinar.MainResultsProofs

theorem improvedLowerBoundMembershipBoxQM
    (ε : ℝ) (hε : 0 < ε) (hε0 : ε ≤ improvedEpsilon0) (r : ℕ)
    (hmem : f_eps ε ∈ BoxQuadraticModule 2 r) :
    improvedLowerBoundConst * ε ^ (-(1 : ℝ) / 4) ≤ (r : ℝ) :=
  improved_lower_degree_bound ε hε hε0 r hmem

theorem baldiSlot_bound_le_improved_bound
    (ε : ℝ) (hε : 0 < ε)
    (hε_old : ε ≤ (improvedLowerBoundConst / lower_bound_const) ^ 8) :
    lower_bound_const * ε ^ (-(1 : ℝ) / 8) ≤
      improvedLowerBoundConst * ε ^ (-(1 : ℝ) / 4) := by
  have hcnew_pos : 0 < improvedLowerBoundConst := improvedLowerBoundConst_pos
  have hcold_pos : 0 < lower_bound_const := lower_bound_const_pos
  have hratio_pos : 0 < improvedLowerBoundConst / lower_bound_const :=
    div_pos hcnew_pos hcold_pos
  have hpow : ε ^ ((1 : ℝ) / 8) ≤ improvedLowerBoundConst / lower_bound_const := by
    have h := Real.rpow_le_rpow hε.le hε_old (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 8)
    rw [← Real.rpow_natCast (improvedLowerBoundConst / lower_bound_const) 8] at h
    rw [← Real.rpow_mul hratio_pos.le] at h
    norm_num at h
    simpa using h
  have hmul : lower_bound_const * ε ^ ((1 : ℝ) / 8) ≤ improvedLowerBoundConst := by
    calc lower_bound_const * ε ^ ((1 : ℝ) / 8)
        ≤ lower_bound_const * (improvedLowerBoundConst / lower_bound_const) :=
          mul_le_mul_of_nonneg_left hpow hcold_pos.le
      _ = improvedLowerBoundConst := by
          field_simp [hcold_pos.ne']
  have hε18_pos : 0 < ε ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos hε _
  rw [show (-(1 : ℝ) / 8) = -((1 : ℝ) / 8) by ring]
  rw [show (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) by ring]
  rw [Real.rpow_neg hε.le, Real.rpow_neg hε.le]
  rw [show ε ^ ((1 : ℝ) / 4) = (ε ^ ((1 : ℝ) / 8)) ^ 2 by
    rw [← Real.rpow_natCast (ε ^ ((1 : ℝ) / 8)) 2]
    rw [← Real.rpow_mul hε.le]
    norm_num]
  field_simp [hε18_pos.ne']
  nlinarith [hmul, hcold_pos, hε18_pos]

theorem improvedLowerBoundMembershipBoxQM_implies_baldiSlot
    (ε : ℝ) (hε : 0 < ε) (hε0 : ε ≤ improvedEpsilon0)
    (hε_old : ε ≤ (improvedLowerBoundConst / lower_bound_const) ^ 8) (r : ℕ)
    (hmem : f_eps ε ∈ BoxQuadraticModule 2 r) :
    lower_bound_const * ε ^ (-(1 : ℝ) / 8) ≤ (r : ℝ) :=
  (baldiSlot_bound_le_improved_bound ε hε hε_old).trans
    (improvedLowerBoundMembershipBoxQM ε hε hε0 r hmem)

theorem improvedLowerBoundMembershipBoxQMGeneral
    (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε)
    (hε0 : ε ≤ improvedEpsilon0) (r : ℕ)
    (hmem : f_eps_n n hn ε ∈ BoxQuadraticModule n r) :
    improvedLowerBoundConst * ε ^ (-(1 : ℝ) / 4) ≤ (r : ℝ) := by
  exact improved_lower_degree_bound ε hε hε0 r
    (restriction_to_two_vars n hn ε r hmem)

theorem improved_lasserre_box_qm_gap
    (ε : ℝ) (hε : 0 < ε) (hε0 : ε ≤ improvedEpsilon0) (r : ℕ)
    (hr : (r : ℝ) < improvedLowerBoundConst * ε ^ (-(1 : ℝ) / 4)) :
    lasserre_bound_box_qm (f_eps ε) r < ↑ε := by
  have key : ∀ l : ℝ, (f_eps ε - MvPolynomial.C l) ∈ BoxQuadraticModule 2 r → l ≤ 0 := by
    intro l hl
    have hfl : f_eps ε - MvPolynomial.C l = f_eps (ε - l) := by
      simp [f_eps, map_sub]
      ring
    rw [hfl] at hl
    by_contra h_contra
    push Not at h_contra
    have hge0 : 0 ≤ ε - l := by
      have := BoxQuadraticModule_subset_nonneg hl corner_11 corner_11_in_hypercube
      rw [f_eps_eval, corner_11_val_0, corner_11_val_1] at this
      linarith
    have hεl_le : ε - l ≤ ε := by linarith
    have hεl0 : ε - l ≤ improvedEpsilon0 := le_trans hεl_le hε0
    by_cases heq : ε - l = 0
    · rw [heq, ← f_zero_eq] at hl
      exact (f_not_in_quadratic_module r) hl
    · have hpos : 0 < ε - l := lt_of_le_of_ne hge0 (Ne.symm heq)
      have hr' : (r : ℝ) < improvedLowerBoundConst * (ε - l) ^ (-(1 : ℝ) / 4) := by
        calc (r : ℝ) < improvedLowerBoundConst * ε ^ (-(1 : ℝ) / 4) := hr
          _ ≤ improvedLowerBoundConst * (ε - l) ^ (-(1 : ℝ) / 4) := by
              apply mul_le_mul_of_nonneg_left _ improvedLowerBoundConst_pos.le
              exact Real.rpow_le_rpow_of_nonpos hpos hεl_le (by norm_num)
      exact improved_lower_degree_bound_contra (ε - l) hpos hεl0 r hr' hl
  unfold lasserre_bound_box_qm
  split_ifs with hne
  · apply WithBot.coe_lt_coe.mpr
    calc sSup { l : ℝ | (f_eps ε - MvPolynomial.C l) ∈ BoxQuadraticModule 2 r }
        ≤ 0 := csSup_le hne (fun l hl ↦ key l hl)
      _ < ε := hε
  · exact WithBot.bot_lt_coe ε

end OptimalConvergenceRates.LowerDegreeBoundsPutinar.MainResultsProofs

end
