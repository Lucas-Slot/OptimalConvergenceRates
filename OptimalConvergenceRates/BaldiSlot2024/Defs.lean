/-
  OptimalConvergenceRates/BaldiSlot2024/Defs.lean

  Constants used in the Baldi-Slot 2024 Putinar upper and lower degree bounds.
-/
import OptimalConvergenceRates.Chebyshev.ChebyshevGrowth
import OptimalConvergenceRates.SlotLaurent2022.Defs

open MvPolynomial Finset Real

noncomputable section

namespace OptimalConvergenceRates

variable {n : ℕ}

/-! ## Upper bound constants -/

/-- The combined constant for the qualitative upper degree bound
    (arXiv v3, Theorem 3).
    Incorporates the Chebyshev growth constant K and the Schmüdgen constant C(n,d).
    The precise value is not important; what matters is that it depends
    only on n and d (not on f). -/
noncomputable def constUpperBound (n d : ℕ) : ℝ :=
  4 * constCChebyshev * (constC n d + 1) + 4 * constCChebyshev + 2

theorem constUpperBound_pos (n d : ℕ) (hn : 0 < n) (hd : 0 < d) :
    0 < constUpperBound n d := by
  unfold constUpperBound
  have h1 := constCChebyshev_pos
  have h2 := constC_pos n d hn hd
  positivity

/-- The leading-term constant: depends only on the Chebyshev growth constant K.
    Controls the 2q term from the scaling parameter choice. -/
noncomputable def constLeading : ℝ := 8 * constCChebyshev + 2

theorem constLeading_pos : 0 < constLeading := by
  unfold constLeading; linarith [constCChebyshev_pos]

theorem one_le_constLeading : 1 ≤ constLeading := by
  unfold constLeading; linarith [one_le_constCChebyshev]

/-- The square-root-term constant: multiplies constC(n,d) under √ in the lower-order term.
    Arises from spread(g) ≤ 4·S and min(g) ≥ M/2, giving factor 4/(1/2) = 8. -/
noncomputable def constSqrt : ℝ := 8

theorem constSqrt_pos : 0 < constSqrt := by unfold constSqrt; norm_num

theorem one_le_constSqrt : 1 ≤ constSqrt := by unfold constSqrt; norm_num

/-! ## Lower bound constant -/

/-- The absolute constant appearing in the lower bound
    (arXiv v3, Proposition 13 and Theorem 4). -/
def lower_bound_const : ℝ := 1 / 16

theorem lower_bound_const_pos : 0 < lower_bound_const := by
  unfold lower_bound_const; positivity

/-! ## Convergence rate constant -/

/-- The constant for the upper convergence-rate bound (arXiv v3, Corollary 15).

    The declaration name is retained for compatibility with earlier versions
    of the formalization, which followed the former paper numbering. Its value
    is `2 · constUpperBound(n,d) · d² · (log n + 1)`. -/
noncomputable def constCor210 (n d : ℕ) : ℝ :=
  2 * constUpperBound n d * d ^ 2 * (Real.log (↑n) + 1)

end OptimalConvergenceRates

end
