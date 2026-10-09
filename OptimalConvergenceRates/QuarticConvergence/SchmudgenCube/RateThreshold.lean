/-
  Eventual-order arithmetic shared by the quartic rate statements.
-/
import Mathlib

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- A positive fourth-power numerator is eventually smaller than any positive
real tolerance after division by the hierarchy order. -/
theorem exists_nat_for_div_pow_four_le {c epsilon : ℝ} (hc : 0 < c)
    (hepsilon : 0 < epsilon) :
    ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r → (c / (r : ℝ)) ^ 4 ≤ epsilon := by
  let root : ℝ := epsilon ^ ((1 : ℝ) / 4)
  have hroot : 0 < root := Real.rpow_pos_of_pos hepsilon _
  obtain ⟨r₀, hr₀⟩ := exists_nat_gt (c / root)
  have hr₀Pos : 0 < r₀ := by
    have : (0 : ℝ) < r₀ := (div_pos hc hroot).trans hr₀
    exact_mod_cast this
  refine ⟨r₀, hr₀Pos, ?_⟩
  intro r hrr₀
  have hrPos : (0 : ℝ) < r := Nat.cast_pos.mpr (hr₀Pos.trans_le hrr₀)
  have hthreshold : c / root < (r : ℝ) := by
    exact hr₀.trans_le (by exact_mod_cast hrr₀)
  have hcLt : c < (r : ℝ) * root := (div_lt_iff₀ hroot).mp hthreshold
  have hdiv : c / (r : ℝ) ≤ root := by
    rw [div_le_iff₀ hrPos]
    nlinarith
  have hpow := pow_le_pow_left₀ (div_nonneg hc.le hrPos.le) hdiv 4
  have hrootPow : root ^ (4 : ℕ) = epsilon := by
    dsimp [root]
    rw [← Real.rpow_natCast (epsilon ^ ((1 : ℝ) / 4)) 4,
      ← Real.rpow_mul hepsilon.le]
    norm_num
  simpa [hrootPow] using hpow

end QuarticConvergence
end OptimalConvergenceRates

end
