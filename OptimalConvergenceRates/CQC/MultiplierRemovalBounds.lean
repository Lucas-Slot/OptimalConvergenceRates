import OptimalConvergenceRates.CQC.MultiplierRemoval

/-!
# Certified bounds for the inverse-series approximants

The numerical bounds in this file are turned into interval SOS certificates
in `MultiplierRemovalCertificates.lean`.
-/

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates
namespace CQCInternal

/-- The square upper-bound polynomial for the inverse approximant. -/
def inverseSeriesApproxGap (α β : ℝ) (ell : ℕ) : Polynomial ℝ :=
  Polynomial.C (α⁻¹ ^ 2) - inverseSeriesApprox α β ell ^ 2

/-- The exponentially small square upper-bound polynomial for the residual. -/
def inverseSeriesResidualGap (α β : ℝ) (ell : ℕ) : Polynomial ℝ :=
  Polynomial.C ((2 * (1 - α / β) ^ (ell + 1)) ^ 2) -
    inverseSeriesResidual α β ell ^ 2

theorem inverseSeriesVariable_natDegree_le (α β : ℝ) :
    (inverseSeriesVariable α β).natDegree ≤ 1 := by
  unfold inverseSeriesVariable
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)

theorem inverseSeriesApprox_natDegree_le (α β : ℝ) (ell : ℕ) :
    (inverseSeriesApprox α β ell).natDegree ≤ ell := by
  unfold inverseSeriesApprox
  refine Polynomial.natDegree_mul_le.trans ?_
  simp only [Polynomial.natDegree_C, zero_add]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  have hjle : j ≤ ell := by simpa using hj
  exact (Polynomial.natDegree_pow_le.trans
    (Nat.mul_le_mul_left j (inverseSeriesVariable_natDegree_le α β))).trans
      (by simpa using hjle)

theorem inverseSeriesResidual_natDegree_le (α β : ℝ) (ell : ℕ) :
    (inverseSeriesResidual α β ell).natDegree ≤ 2 * (ell + 1) := by
  unfold inverseSeriesResidual
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · calc
      ((Polynomial.X + Polynomial.C α) ^ 2 *
          inverseSeriesApprox α β ell ^ 2).natDegree ≤
          ((Polynomial.X + Polynomial.C α) ^ 2).natDegree +
            (inverseSeriesApprox α β ell ^ 2).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 2 + 2 * ell := by
        apply Nat.add_le_add
        · exact Polynomial.natDegree_pow_le.trans (by simp)
        · exact Polynomial.natDegree_pow_le.trans
            (Nat.mul_le_mul_left 2
              (inverseSeriesApprox_natDegree_le α β ell))
      _ = 2 * (ell + 1) := by omega

theorem inverseSeriesApproxGap_natDegree_le (α β : ℝ) (ell : ℕ) :
    (inverseSeriesApproxGap α β ell).natDegree ≤ 2 * ell := by
  unfold inverseSeriesApproxGap
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · rw [Polynomial.natDegree_C]
    omega
  · exact Polynomial.natDegree_pow_le.trans
      (Nat.mul_le_mul_left 2 (inverseSeriesApprox_natDegree_le α β ell))

theorem inverseSeriesResidualGap_natDegree_le (α β : ℝ) (ell : ℕ) :
    (inverseSeriesResidualGap α β ell).natDegree ≤ 4 * (ell + 1) := by
  unfold inverseSeriesResidualGap
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · rw [Polynomial.natDegree_C]
    omega
  · exact Polynomial.natDegree_pow_le.trans
      (Nat.mul_le_mul_left 2 (inverseSeriesResidual_natDegree_le α β ell)) |>.trans
        (by omega)

/-- On the shifted interval, the geometric-series variable lies between
zero and its fixed contraction factor. -/
theorem inverseSeriesVariable_eval_bounds
    {α β u : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hu0 : 0 ≤ u) (huB : u ≤ β - α) :
    0 ≤ (inverseSeriesVariable α β).eval u ∧
      (inverseSeriesVariable α β).eval u ≤ 1 - α / β := by
  rw [inverseSeriesVariable_eval]
  have hβ : 0 < β := hα.trans hαβ
  constructor
  · apply sub_nonneg.mpr
    exact (div_le_one hβ).2 (by linarith)
  · have hdiv : α / β ≤ (u + α) / β :=
      div_le_div_of_nonneg_right (by linarith) hβ.le
    linarith

/-- The inverse approximant is between zero and `α⁻¹` on the shifted
interval. -/
theorem inverseSeriesApprox_eval_bounds
    {α β u : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hu0 : 0 ≤ u) (huB : u ≤ β - α) (ell : ℕ) :
    0 ≤ (inverseSeriesApprox α β ell).eval u ∧
      (inverseSeriesApprox α β ell).eval u ≤ α⁻¹ := by
  have hβ : 0 < β := hα.trans hαβ
  obtain ⟨hz0, hzθ⟩ :=
    inverseSeriesVariable_eval_bounds hα hαβ hu0 huB
  let z := (inverseSeriesVariable α β).eval u
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range (ell + 1), z ^ j :=
    Finset.sum_nonneg fun j _ ↦ pow_nonneg hz0 j
  have hq0 : 0 ≤ (inverseSeriesApprox α β ell).eval u := by
    rw [inverseSeriesApprox_eval]
    apply mul_nonneg (one_div_nonneg.mpr hβ.le)
    simpa [z, inverseSeriesVariable_eval] using hsum0
  refine ⟨hq0, ?_⟩
  have htpos : 0 < u + α := by linarith
  have hgeom := add_mul_inverseSeriesApprox_eval (α := α) hβ.ne' u ell
  have hzpow0 : 0 ≤ z ^ (ell + 1) := pow_nonneg hz0 _
  have htq : (u + α) * (inverseSeriesApprox α β ell).eval u ≤ 1 := by
    calc
      (u + α) * (inverseSeriesApprox α β ell).eval u =
          1 - z ^ (ell + 1) := by
            simpa [z, inverseSeriesVariable_eval] using hgeom
      _ ≤ 1 := sub_le_self 1 hzpow0
  have hq_le_t : (inverseSeriesApprox α β ell).eval u ≤ (u + α)⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ htpos).2 (by simpa [mul_comm] using htq)
  exact hq_le_t.trans ((inv_le_inv₀ htpos hα).2 (by linarith))

/-- The multiplicative residual is nonnegative and at most twice the
contracted power. -/
theorem inverseSeriesResidual_eval_bounds
    {α β u : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hu0 : 0 ≤ u) (huB : u ≤ β - α) (ell : ℕ) :
    0 ≤ (inverseSeriesResidual α β ell).eval u ∧
      (inverseSeriesResidual α β ell).eval u ≤
        2 * (1 - α / β) ^ (ell + 1) := by
  have hβ : 0 < β := hα.trans hαβ
  obtain ⟨hz0, hzθ⟩ :=
    inverseSeriesVariable_eval_bounds hα hαβ hu0 huB
  let z := (inverseSeriesVariable α β).eval u
  let w := z ^ (ell + 1)
  have hθ0 : 0 < 1 - α / β := by
    rw [sub_pos, div_lt_one hβ]
    exact hαβ
  have hθ1 : 1 - α / β < 1 := by
    linarith [div_pos hα hβ]
  have hw0 : 0 ≤ w := pow_nonneg hz0 _
  have hw1 : w ≤ 1 := by
    dsimp [w]
    exact pow_le_one₀ hz0 (hzθ.trans hθ1.le)
  have hwθ : w ≤ (1 - α / β) ^ (ell + 1) :=
    pow_le_pow_left₀ hz0 hzθ _
  rw [inverseSeriesResidual_eval_eq hβ.ne']
  have hz : z = 1 - (u + α) / β := inverseSeriesVariable_eval α β u
  rw [← hz]
  have hpow : z ^ (2 * (ell + 1)) = w ^ 2 := by
    dsimp [w]
    rw [show 2 * (ell + 1) = (ell + 1) * 2 by omega, pow_mul]
  rw [hpow]
  change 0 ≤ 2 * w - w ^ 2 ∧
    2 * w - w ^ 2 ≤ 2 * (1 - α / β) ^ (ell + 1)
  constructor
  · nlinarith [sq_nonneg w]
  · nlinarith [sq_nonneg w]

theorem inverseSeriesApproxGap_nonnegOn
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β) (ell : ℕ) :
    ∀ u ∈ Set.Icc (0 : ℝ) (β - α),
      0 ≤ (inverseSeriesApproxGap α β ell).eval u := by
  intro u hu
  obtain ⟨hq0, hq⟩ :=
    inverseSeriesApprox_eval_bounds hα hαβ hu.1 hu.2 ell
  simp only [inverseSeriesApproxGap, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_pow]
  nlinarith [sq_nonneg ((inverseSeriesApprox α β ell).eval u)]

theorem inverseSeriesResidualGap_nonnegOn
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β) (ell : ℕ) :
    ∀ u ∈ Set.Icc (0 : ℝ) (β - α),
      0 ≤ (inverseSeriesResidualGap α β ell).eval u := by
  intro u hu
  obtain ⟨hv0, hv⟩ :=
    inverseSeriesResidual_eval_bounds hα hαβ hu.1 hu.2 ell
  simp only [inverseSeriesResidualGap, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_pow]
  nlinarith [sq_nonneg ((inverseSeriesResidual α β ell).eval u)]

end CQCInternal
end OptimalConvergenceRates

end
