import OptimalConvergenceRates.CQC.MultiplierRemovalCertificates

/-!
# Exact assembly for multiplier removal

This file combines the two interval certificates with a fixed square bound
for the objective and with a certificate for `a^2 p + δ`.
-/

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

/-- Exact certificate assembly at a fixed inverse-series length. -/
theorem multiplierRemoval_at_length
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (p a : MvPolynomial (Fin n) ℝ)
    {α β B δ : ℝ} (ell r rLower rUpper rBound : ℕ)
    (hα : 0 < α) (hαβ : α < β) (hB : 0 < B) (hδ : 0 < δ)
    (hlower : a - C α ∈ GenQuadraticModule g rLower)
    (hupper : C β - a ∈ GenQuadraticModule g rUpper)
    (hpBound : C (B ^ 2) - p ^ 2 ∈ GenQuadraticModule g rBound)
    (hweighted : a ^ 2 * p + C δ ∈ GenQuadraticModule g r) :
    p + C (B * (2 * (1 - α / β) ^ (ell + 1)) + δ * α⁻¹ ^ 2) ∈
      GenQuadraticModule g
        (r +
          (max rLower rUpper + (2 * ell + 3) * (a - C α).totalDegree) +
          (max rLower rUpper +
            (4 * (ell + 1) + 3) * (a - C α).totalDegree) +
          rBound + (inverseApproxAt α β ell a ^ 2).totalDegree +
          (p ^ 2).totalDegree +
          ((C (B * (2 * (1 - α / β) ^ (ell + 1))) +
            p * inverseResidualAt α β ell a) ^ 2).totalDegree) := by
  let q := inverseApproxAt α β ell a
  let v := inverseResidualAt α β ell a
  let eta : ℝ := 2 * (1 - α / β) ^ (ell + 1)
  let rq := max rLower rUpper + (2 * ell + 3) * (a - C α).totalDegree
  let rv := max rLower rUpper +
    (4 * (ell + 1) + 3) * (a - C α).totalDegree
  let R := r + rq + rv + rBound + (q ^ 2).totalDegree +
    (p ^ 2).totalDegree + ((C (B * eta) + p * v) ^ 2).totalDegree
  have hθ0 : 0 < 1 - α / β := by
    have hβ : 0 < β := hα.trans hαβ
    rw [sub_pos, div_lt_one hβ]
    exact hαβ
  have heta : 0 < eta := mul_pos (by norm_num) (pow_pos hθ0 _)
  have hqGap : C (α⁻¹ ^ 2) - q ^ 2 ∈ GenQuadraticModule g rq := by
    exact inverseApproxAt_sq_upper_mem ell hα hαβ hlower hupper
  have hvGap : C (eta ^ 2) - v ^ 2 ∈ GenQuadraticModule g rv := by
    exact inverseResidualAt_sq_upper_mem ell hα hαβ hlower hupper
  have hfirstRaw : q ^ 2 * (a ^ 2 * p + C δ) ∈
      GenQuadraticModule g (r + (q ^ 2).totalDegree) :=
    genQuadraticModule_sos_mul (IsSOS_sq q) hweighted
  have hfirst : q ^ 2 * (a ^ 2 * p + C δ) ∈
      GenQuadraticModule g R := by
    apply GenQuadraticModule_mono _ hfirstRaw
    dsimp [R]
    omega
  have hqScaledRaw : C δ * (C (α⁻¹ ^ 2) - q ^ 2) ∈
      GenQuadraticModule g rq :=
    GenQuadraticModule_nonneg_scale δ hδ.le hqGap
  have hqScaled : C δ * (C (α⁻¹ ^ 2) - q ^ 2) ∈
      GenQuadraticModule g R := by
    apply GenQuadraticModule_mono _ hqScaledRaw
    dsimp [R]
    omega
  have hfixedRaw : C (eta ^ 2) * (C (B ^ 2) - p ^ 2) ∈
      GenQuadraticModule g rBound :=
    GenQuadraticModule_nonneg_scale (eta ^ 2) (sq_nonneg eta) hpBound
  have hvMulRaw : p ^ 2 * (C (eta ^ 2) - v ^ 2) ∈
      GenQuadraticModule g (rv + (p ^ 2).totalDegree) :=
    genQuadraticModule_sos_mul (IsSOS_sq p) hvGap
  have hfixed : C (eta ^ 2) * (C (B ^ 2) - p ^ 2) ∈
      GenQuadraticModule g R := by
    apply GenQuadraticModule_mono _ hfixedRaw
    dsimp [R]
    omega
  have hvMul : p ^ 2 * (C (eta ^ 2) - v ^ 2) ∈
      GenQuadraticModule g R := by
    apply GenQuadraticModule_mono _ hvMulRaw
    dsimp [R]
    omega
  have hdiffRaw := GenQuadraticModule_add hfixed hvMul
  have hdiff : C ((B * eta) ^ 2) - (p * v) ^ 2 ∈
      GenQuadraticModule g R := by
    convert hdiffRaw using 1
    simp only [map_mul, map_pow]
    ring
  have hsquareRaw : (C (B * eta) + p * v) ^ 2 ∈
      GenQuadraticModule g ((C (B * eta) + p * v) ^ 2).totalDegree :=
    genQuadraticModule_sos g (IsSOS_sq _) le_rfl
  have hsquare : (C (B * eta) + p * v) ^ 2 ∈
      GenQuadraticModule g R := by
    apply GenQuadraticModule_mono _ hsquareRaw
    dsimp [R]
    omega
  have hsignedSum := GenQuadraticModule_add hsquare hdiff
  have hscale : 0 ≤ (2 * B * eta)⁻¹ :=
    (inv_pos.mpr (mul_pos (mul_pos (by norm_num) hB) heta)).le
  have hsignedScaled :=
    GenQuadraticModule_nonneg_scale ((2 * B * eta)⁻¹) hscale hsignedSum
  have hden : 2 * B * eta ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hB.ne') heta.ne'
  have hnum :
      (C (B * eta) + p * v) ^ 2 +
          (C ((B * eta) ^ 2) - (p * v) ^ 2) =
        C (2 * B * eta) * (C (B * eta) + p * v) := by
    have hc2 : (C 2 : MvPolynomial (Fin n) ℝ) = 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, map_add, map_one]
      norm_num
    simp only [map_mul, map_pow]
    rw [hc2]
    ring
  have hsigned : C (B * eta) + p * v ∈ GenQuadraticModule g R := by
    convert hsignedScaled using 1
    rw [hnum]
    symm
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hden, map_one, one_mul]
  have hsum := GenQuadraticModule_add hfirst
    (GenQuadraticModule_add hsigned hqScaled)
  have hid := inverseApproxAt_residual_identity a α β ell
  change a ^ 2 * q ^ 2 + v = 1 at hid
  change p + C (B * eta + δ * α⁻¹ ^ 2) ∈ GenQuadraticModule g R
  have hpoly :
      p + C (B * eta + δ * α⁻¹ ^ 2) =
        q ^ 2 * (a ^ 2 * p + C δ) +
          (C (B * eta) + p * v + C δ * (C (α⁻¹ ^ 2) - q ^ 2)) := by
    simp only [map_add, map_mul]
    calc
      p + (C B * C eta + C δ * C (α⁻¹ ^ 2)) =
          p * (a ^ 2 * q ^ 2 + v) +
            (C B * C eta + C δ * C (α⁻¹ ^ 2)) := by rw [hid, mul_one]
      _ = q ^ 2 * (a ^ 2 * p + C δ) +
          (C B * C eta + p * v + C δ * (C (α⁻¹ ^ 2) - q ^ 2)) := by ring
  rw [hpoly]
  exact hsum

end CQCInternal
end OptimalConvergenceRates

end
