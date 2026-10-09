import OptimalConvergenceRates.LowerDegreeBoundsPutinar.MainResultsProofs

/-!
# Improved Putinar lower bounds

This file is the readable public statement layer. Proof calculations live in
`MainResultsProofs`.
-/

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

/-- Public two-variable form of the improved lower bound. -/
theorem improvedLowerBoundMembershipBoxQM
    (ε : ℝ) (hε : 0 < ε) (hε0 : ε ≤ improvedEpsilon0) (r : ℕ)
    (hmem : f_eps ε ∈ BoxQuadraticModule 2 r) :
    improvedLowerBoundConst * ε ^ (-(1 : ℝ) / 4) ≤ (r : ℝ) :=
  LowerDegreeBoundsPutinar.MainResultsProofs.improvedLowerBoundMembershipBoxQM
    ε hε hε0 r hmem

/-- On a sufficiently small range, the new `ε^(-1/4)` lower bound dominates
the Baldi-Slot `ε^(-1/8)` lower bound. -/
theorem baldiSlot_bound_le_improved_bound
    (ε : ℝ) (hε : 0 < ε)
    (hε_old : ε ≤ (improvedLowerBoundConst / lower_bound_const) ^ 8) :
    lower_bound_const * ε ^ (-(1 : ℝ) / 8) ≤
      improvedLowerBoundConst * ε ^ (-(1 : ℝ) / 4) :=
  LowerDegreeBoundsPutinar.MainResultsProofs.baldiSlot_bound_le_improved_bound
    ε hε hε_old

/-- In the range where the new numerical bound dominates the Baldi-Slot one,
the improved theorem implies the old lower-bound conclusion. -/
theorem improvedLowerBoundMembershipBoxQM_implies_baldiSlot
    (ε : ℝ) (hε : 0 < ε) (hε0 : ε ≤ improvedEpsilon0)
    (hε_old : ε ≤ (improvedLowerBoundConst / lower_bound_const) ^ 8) (r : ℕ)
    (hmem : f_eps ε ∈ BoxQuadraticModule 2 r) :
    lower_bound_const * ε ^ (-(1 : ℝ) / 8) ≤ (r : ℝ) :=
  LowerDegreeBoundsPutinar.MainResultsProofs.improvedLowerBoundMembershipBoxQM_implies_baldiSlot
    ε hε hε0 hε_old r hmem

/-- Public general-n form, obtained by restricting to the first two coordinates. -/
theorem improvedLowerBoundMembershipBoxQMGeneral
    (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε)
    (hε0 : ε ≤ improvedEpsilon0) (r : ℕ)
    (hmem : f_eps_n n hn ε ∈ BoxQuadraticModule n r) :
    improvedLowerBoundConst * ε ^ (-(1 : ℝ) / 4) ≤ (r : ℝ) :=
  LowerDegreeBoundsPutinar.MainResultsProofs.improvedLowerBoundMembershipBoxQMGeneral
    n hn ε hε hε0 r hmem

/-- Improved lower-bound consequence for the QM Lasserre relaxation gap. -/
theorem improved_lasserre_box_qm_gap
    (ε : ℝ) (hε : 0 < ε) (hε0 : ε ≤ improvedEpsilon0) (r : ℕ)
    (hr : (r : ℝ) < improvedLowerBoundConst * ε ^ (-(1 : ℝ) / 4)) :
    lasserre_bound_box_qm (f_eps ε) r < ↑ε :=
  LowerDegreeBoundsPutinar.MainResultsProofs.improved_lasserre_box_qm_gap
    ε hε hε0 r hr

end OptimalConvergenceRates

end
