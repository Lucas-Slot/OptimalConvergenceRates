/-
  Homogeneity of the quartic quadratic-module approximation datum.

  The controlled-root construction is naturally normalized by the lifted
  sphere `C^6` norm.  This file isolates the elementary scaling argument so
  that the analytic construction only has to prove the normalized case.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarApproximationAssembly

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

variable {n B m : ℕ} {h : MvPolynomial (Fin n) ℝ} {L M : ℝ}

/-- Scaling a polynomial by a scalar costs at most the absolute value of the
scalar in the cube sup norm. -/
theorem polySupNorm_smul_le (c : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    polySupNorm (c • p) ≤ |c| * polySupNorm p := by
  apply polySupNorm_le_of_bound
  intro x hx
  have hp := polySupNorm_eval_le p (polySupNorm p) le_rfl x hx
  simpa only [MvPolynomial.smul_eq_C_mul, map_mul, eval_C, abs_mul] using
    mul_le_mul_of_nonneg_left hp (abs_nonneg c)

/-- A nonnegative scalar multiple of a quartic quadratic-module approximant
has the same canonical order and the correspondingly scaled error. -/
theorem HasQuarticBoxQMApproximationAt.nonneg_smul
    (happrox : HasQuarticBoxQMApproximationAt h B m L)
    (c : ℝ) (hc : 0 ≤ c) :
    HasQuarticBoxQMApproximationAt (c • h) B m (c * L) := by
  refine {
    nonnegative := ?_
    approximant_exists := ?_ }
  · intro x hx
    simpa only [MvPolynomial.smul_eq_C_mul, map_mul, eval_C] using
      mul_nonneg hc (happrox.nonnegative x hx)
  · obtain ⟨b, hb, herror⟩ := happrox.approximant_exists
    refine ⟨c • b, ?_, ?_⟩
    · simpa only [MvPolynomial.smul_eq_C_mul] using
        BoxQuadraticModule_nonneg_scale c hc hb
    · rw [← smul_sub]
      calc
        polySupNorm (c • (h - b)) ≤ |c| * polySupNorm (h - b) :=
          polySupNorm_smul_le c (h - b)
        _ ≤ c * (L / (m : ℝ) ^ 4) := by
          rw [abs_of_nonneg hc]
          exact mul_le_mul_of_nonneg_left herror hc
        _ = c * L / (m : ℝ) ^ 4 := by ring

/-- Remove an arbitrary nonnegative normalization factor.  The zero-factor
branch is handled intrinsically from the supplied cube sup-norm bound, so no
nondegeneracy assumption is exposed by downstream theorems. -/
theorem hasQuarticBoxQMApproximationAt_of_normalized
    (hnonnegative : IsNonnegOn h (Hypercube n))
    (hM : 0 ≤ M) (hsup : polySupNorm h ≤ M)
    (hnormalized : M ≠ 0 →
      HasQuarticBoxQMApproximationAt (M⁻¹ • h) B m L) :
    HasQuarticBoxQMApproximationAt h B m (M * L) := by
  by_cases hMzero : M = 0
  · have hzero : h = 0 :=
      eq_zero_of_polySupNorm_le_zero h (hsup.trans_eq hMzero)
    subst h
    refine {
      nonnegative := hnonnegative
      approximant_exists := ⟨0, zero_mem_BoxQuadraticModule n (B * m), ?_⟩ }
    apply polySupNorm_le_of_bound
    simp [hMzero]
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hMzero)
    have hscaled := (hnormalized hMzero).nonneg_smul M hMpos.le
    have hpoly : M • (M⁻¹ • h) = h := by
      rw [smul_smul, mul_inv_cancel₀ hMzero, one_smul]
    simpa only [hpoly] using hscaled

end QuarticConvergence
end OptimalConvergenceRates

end
