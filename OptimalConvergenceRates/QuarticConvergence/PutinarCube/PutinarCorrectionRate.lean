/-
  Finite-dimensional aggregation and quartic decay for the explicit
  preordering-to-Putinar correction.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarCorrectionBounds
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Choose.Sum

open MvPolynomial Finset
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

variable {n r R : ℕ}

/-! ## Counting nested subsets -/

/-- Exact aggregation of a function of `|J|` over pairs `J ⊆ I ⊆ Fin n`.
The factor `2^(n-j)` counts the possible supersets `I` of a fixed `J`. -/
theorem sum_powerset_sum_powerset_apply_card
    (f : ℕ → ℝ) :
    (∑ I ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∑ J ∈ I.powerset, f J.card) =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℝ) * (2 : ℝ) ^ (n - j) * f j := by
  classical
  let U : Finset (Fin n) := Finset.univ
  have hUcard : U.card = n := by simp [U]
  calc
    (∑ I ∈ U.powerset, ∑ J ∈ I.powerset, f J.card) =
        ∑ I ∈ U.powerset, ∑ J ∈ U.powerset,
          if J ⊆ I then f J.card else 0 := by
      apply Finset.sum_congr rfl
      intro I hI
      have hIU : I ⊆ U := Finset.mem_powerset.mp hI
      have hpowerset : I.powerset = U.powerset.filter fun J ↦ J ⊆ I := by
        ext J
        simp only [Finset.mem_powerset, Finset.mem_filter]
        constructor
        · intro hJI
          exact ⟨hJI.trans hIU, hJI⟩
        · exact fun h ↦ h.2
      rw [hpowerset, Finset.sum_filter]
    _ = ∑ J ∈ U.powerset, ∑ I ∈ U.powerset,
          if J ⊆ I then f J.card else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ J ∈ U.powerset,
          (2 : ℝ) ^ (n - J.card) * f J.card := by
      apply Finset.sum_congr rfl
      intro J hJ
      have hJU : J ⊆ U := Finset.mem_powerset.mp hJ
      rw [← Finset.sum_filter]
      rw [← Finset.Icc_eq_filter_powerset J U]
      rw [Finset.sum_const, Finset.card_Icc_finset hJU, nsmul_eq_mul]
      rw [hUcard]
      norm_cast
    _ = ∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℝ) * (2 : ℝ) ^ (n - j) * f j := by
      have hgroup := Finset.sum_powerset_apply_card
        (fun j ↦ (2 : ℝ) ^ (n - j) * f j) (x := U)
      rw [hUcard] at hgroup
      simpa only [nsmul_eq_mul, Nat.cast_ofNat, mul_assoc] using hgroup

/-! ## The finite-dimensional aggregation factor -/

/-- The exact dimension-dependent factor left after applying a weighted
bound of the form `H * M^(2j-4)` to every term with `j = |J|`. -/
def putinarCorrectionScaleFactor (n k : ℕ) (M : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (n.choose j : ℝ) * (2 : ℝ) ^ (n - j) *
      (if 2 ≤ j then putinarPairMu k ^ j * M ^ (2 * j - 4) else 0)

/-- The aggregation factor is nonnegative at a nonnegative scale. -/
theorem putinarCorrectionScaleFactor_nonneg
    (n k : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ putinarCorrectionScaleFactor n k M := by
  unfold putinarCorrectionScaleFactor
  apply Finset.sum_nonneg
  intro j hj
  by_cases htwo : 2 ≤ j
  · simp only [htwo, ite_eq_left]
    have hmu : 0 ≤ putinarPairMu k := by
      unfold putinarPairMu delta
      positivity
    positivity
  · simp [htwo]

/-- Pointwise aggregation of all weighted correction terms.  The hypothesis
retains the full generator product and the complete SOS multiplier. -/
theorem eval_putinarConversionCorrection_nonneg_le_scaleFactor
    {q : MvPolynomial (Fin n) ℝ}
    (k : ℕ) (hk : 1 ≤ k) (w : BoxPreorderingRootWitness q r)
    (x : Fin n → ℝ) (hx : x ∈ Hypercube n) (H M : ℝ)
    (hweighted : ∀ I ∈ Finset.univ.powerset, ∀ J ∈ I.powerset,
      2 ≤ J.card →
      MvPolynomial.eval x
          (BoxSemialgebraicGeneratorProd (I \ J) *
            boxPreorderingRootMultiplier w I) ≤
        H * M ^ (2 * J.card - 4)) :
    0 ≤ MvPolynomial.eval x (putinarConversionCorrection k w) ∧
      MvPolynomial.eval x (putinarConversionCorrection k w) ≤
        H * putinarCorrectionScaleFactor n k M := by
  constructor
  · exact (eval_putinarConversionCorrection_nonneg_le_majorant
      k hk w x hx).1
  · have hupper := eval_putinarConversionCorrection_le_of_weighted
      k hk w x hx (fun _ J ↦ H * M ^ (2 * J.card - 4)) hweighted
    apply hupper.trans_eq
    rw [sum_powerset_sum_powerset_apply_card
      (n := n) (fun j ↦ if 2 ≤ j then
        putinarPairMu k ^ j * (H * M ^ (2 * j - 4)) else 0)]
    unfold putinarCorrectionScaleFactor
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases htwo : 2 ≤ j
    · simp only [htwo, ite_eq_left]
      ring
    · simp [htwo]

/-! ## Quartic specialization -/

/-- The dimension-only coefficient after the scale is specialized to
`M = B k`. -/
def putinarCorrectionRateConstant (n : ℕ) (B : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (n.choose j : ℝ) * (2 : ℝ) ^ (n - j) *
      (if 2 ≤ j then B ^ (2 * j - 4) else 0)

/-- The dimension-only rate coefficient is nonnegative for a nonnegative
scale constant. -/
theorem putinarCorrectionRateConstant_nonneg
    (n : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ putinarCorrectionRateConstant n B := by
  unfold putinarCorrectionRateConstant
  apply Finset.sum_nonneg
  intro j hj
  by_cases htwo : 2 ≤ j
  · simp only [htwo, ite_eq_left]
    positivity
  · simp [htwo]

/-- Each retained `μ^j` weight cancels all but four powers of `k` from a
weighted estimate at scale `B k`. -/
theorem putinarPairMu_pow_mul_scaled_pow
    (k j : ℕ) (hk : 1 ≤ k) (B : ℝ) (hj : 2 ≤ j) :
    putinarPairMu k ^ j * (B * (k : ℝ)) ^ (2 * j - 4) =
      B ^ (2 * j - 4) / (k : ℝ) ^ 4 := by
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hexp : 2 * j = (2 * j - 4) + 4 := by omega
  unfold putinarPairMu delta
  rw [div_pow, one_pow, mul_pow, ← pow_mul]
  rw [hexp, pow_add]
  field_simp [hk0]
  have hcancel : 2 * j - 4 + 4 - 4 = 2 * j - 4 := by omega
  rw [hcancel]
  ring

/-- At scale `M = B k`, the exact finite-dimensional aggregation factor is
the dimension-only coefficient divided by `k⁴`. -/
theorem putinarCorrectionScaleFactor_scaled_eq
    (n k : ℕ) (hk : 1 ≤ k) (B : ℝ) :
    putinarCorrectionScaleFactor n k (B * (k : ℝ)) =
      putinarCorrectionRateConstant n B / (k : ℝ) ^ 4 := by
  unfold putinarCorrectionScaleFactor putinarCorrectionRateConstant
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases htwo : 2 ≤ j
  · simp only [htwo, ite_eq_left]
    rw [putinarPairMu_pow_mul_scaled_pow k j hk B htwo]
    ring
  · simp [htwo]

/-- Explicit quartic pointwise rate for the retained correction.  The only
analytic input is the supplied bound on each complete weighted multiplier
term; no estimate on the number or the unweighted size of roots is used. -/
theorem eval_putinarConversionCorrection_nonneg_le_quartic
    {q : MvPolynomial (Fin n) ℝ}
    (k : ℕ) (hk : 1 ≤ k) (w : BoxPreorderingRootWitness q r)
    (x : Fin n → ℝ) (hx : x ∈ Hypercube n) (H B : ℝ)
    (hweighted : ∀ I ∈ Finset.univ.powerset, ∀ J ∈ I.powerset,
      2 ≤ J.card →
      MvPolynomial.eval x
          (BoxSemialgebraicGeneratorProd (I \ J) *
            boxPreorderingRootMultiplier w I) ≤
        H * (B * (k : ℝ)) ^ (2 * J.card - 4)) :
    0 ≤ MvPolynomial.eval x (putinarConversionCorrection k w) ∧
      MvPolynomial.eval x (putinarConversionCorrection k w) ≤
        putinarCorrectionRateConstant n B * H / (k : ℝ) ^ 4 := by
  have haggregate := eval_putinarConversionCorrection_nonneg_le_scaleFactor
    k hk w x hx H (B * (k : ℝ)) hweighted
  refine ⟨haggregate.1, haggregate.2.trans_eq ?_⟩
  rw [putinarCorrectionScaleFactor_scaled_eq n k hk B]
  ring

/-- Certificate-compatible package: the same explicit correction is SOS,
has the established total-degree bound, performs the canonical Putinar
conversion, and satisfies the quartic pointwise estimate. -/
theorem BoxPreorderingRootWitness.putinarCorrection_quarticRate
    {q : MvPolynomial (Fin n) ℝ}
    (w : BoxPreorderingRootWitness q r)
    (hroot : ∀ I j, (w.root I j).totalDegree ≤ R)
    (k : ℕ) (hk : 1 ≤ k)
    (x : Fin n → ℝ) (hx : x ∈ Hypercube n) (H B : ℝ)
    (hweighted : ∀ I ∈ Finset.univ.powerset, ∀ J ∈ I.powerset,
      2 ≤ J.card →
      MvPolynomial.eval x
          (BoxSemialgebraicGeneratorProd (I \ J) *
            boxPreorderingRootMultiplier w I) ≤
        H * (B * (k : ℝ)) ^ (2 * J.card - 4)) :
    IsSOS (putinarConversionCorrection k w) ∧
      (putinarConversionCorrection k w).totalDegree ≤ 2 * R + 2 * n * k ∧
      q + putinarConversionCorrection k w ∈
        BoxQuadraticModule n (2 * R + 4 * n * k) ∧
      0 ≤ MvPolynomial.eval x (putinarConversionCorrection k w) ∧
      MvPolynomial.eval x (putinarConversionCorrection k w) ≤
        putinarCorrectionRateConstant n B * H / (k : ℝ) ^ 4 := by
  refine ⟨putinarConversionCorrection_isSOS k hk w,
    putinarConversionCorrection_totalDegree_le k hk w hroot,
    w.add_putinarConversionCorrection_mem hroot k hk, ?_⟩
  exact eval_putinarConversionCorrection_nonneg_le_quartic
    k hk w x hx H B hweighted

end QuarticConvergence
end OptimalConvergenceRates

end
