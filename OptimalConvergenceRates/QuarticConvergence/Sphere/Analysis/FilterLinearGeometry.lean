/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Analysis/FilterLinearGeometry.lean

  Elementary operator identities for a map and its inverse, used in the centered
  rotation estimate for the spherical filter.
-/
import Mathlib.Analysis.Normed.Operator.Basic

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- If `Q R = I`, the centered sum `Q + R - 2I` factors as a product of the two
first-order displacements. -/
theorem clm_add_inverse_sub_two_id_factor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q R : E →L[ℝ] E)
    (hQR : Q.comp R = ContinuousLinearMap.id ℝ E) :
    Q + R - 2 • ContinuousLinearMap.id ℝ E =
      (Q - ContinuousLinearMap.id ℝ E).comp
        (ContinuousLinearMap.id ℝ E - R) := by
  ext x
  have hQRx : Q (R x) = x := by
    have := DFunLike.congr_fun hQR x
    simpa using this
  simp [hQRx]
  abel

/-- Consequently, first-order displacement bounds for inverse maps automatically give a
quadratic bound for their centered sum. -/
theorem norm_clm_add_inverse_sub_two_id_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q R : E →L[ℝ] E)
    (hQR : Q.comp R = ContinuousLinearMap.id ℝ E)
    {dQ dR : ℝ}
    (hQ : ‖Q - ContinuousLinearMap.id ℝ E‖ ≤ dQ)
    (hR : ‖R - ContinuousLinearMap.id ℝ E‖ ≤ dR) :
    ‖Q + R - 2 • ContinuousLinearMap.id ℝ E‖ ≤ dQ * dR := by
  rw [clm_add_inverse_sub_two_id_factor Q R hQR]
  calc
    _ ≤ ‖Q - ContinuousLinearMap.id ℝ E‖ *
        ‖ContinuousLinearMap.id ℝ E - R‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖Q - ContinuousLinearMap.id ℝ E‖ *
        ‖R - ContinuousLinearMap.id ℝ E‖ := by
      have hnormR : ‖ContinuousLinearMap.id ℝ E - R‖ =
          ‖R - ContinuousLinearMap.id ℝ E‖ := norm_sub_rev _ _
      rw [hnormR]
    _ ≤ dQ * dR := mul_le_mul hQ hR (norm_nonneg _)
      ((norm_nonneg _).trans hQ)

/-- If `R Q = I`, the displacement of `R` is the negative of `R` composed with the
displacement of `Q`. -/
theorem inverse_sub_id_eq_neg_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q R : E →L[ℝ] E)
    (hRQ : R.comp Q = ContinuousLinearMap.id ℝ E) :
    R - ContinuousLinearMap.id ℝ E =
      -(R.comp (Q - ContinuousLinearMap.id ℝ E)) := by
  ext x
  have hRQx : R (Q x) = x := by
    have := DFunLike.congr_fun hRQ x
    simpa using this
  simp [hRQx]

/-- A bounded inverse inherits a first-order displacement bound from the original map. -/
theorem norm_inverse_sub_id_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q R : E →L[ℝ] E)
    (hRQ : R.comp Q = ContinuousLinearMap.id ℝ E)
    {B d : ℝ} (hR : ‖R‖ ≤ B)
    (hQ : ‖Q - ContinuousLinearMap.id ℝ E‖ ≤ d)
    (hB : 0 ≤ B) :
    ‖R - ContinuousLinearMap.id ℝ E‖ ≤ B * d := by
  rw [inverse_sub_id_eq_neg_comp Q R hRQ, norm_neg]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul hR hQ (norm_nonneg _) hB)

end QuarticConvergence
end OptimalConvergenceRates

end
