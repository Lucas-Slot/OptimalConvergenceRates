/-
  A negative-axis witness showing that the linear feasibility exponent is
  sharp at the origin.
-/
import OptimalConvergenceRates.MFCQQuadraticLowerBound.ErrorBound

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.MFCQQuadraticLowerBound

/-- The point `(0,0,-h)` below the unique feasible minimizer. -/
def negativeAxisPoint (h : ℝ) : Fin 3 → ℝ := ![0, 0, -h]

theorem violation_negativeAxisPoint (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    violation (negativeAxisPoint h) = h := by
  have hsquare : h ^ 2 - 1 ≤ h := by
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  simp [violation, negativeAxisPoint, max_eq_left hsquare, h0]

theorem distance_negativeAxisPoint (h : ℝ) (h0 : 0 ≤ h) :
    euclideanDistanceToSet (negativeAxisPoint h) feasibleSet = h := by
  have hset : (WithLp.toLp 2 '' feasibleSet).Nonempty :=
    ⟨WithLp.toLp 2 origin, origin, origin_mem, rfl⟩
  apply le_antisymm
  · have hupper := Metric.infDist_le_dist_of_mem
      (x := WithLp.toLp 2 (negativeAxisPoint h))
      (show WithLp.toLp 2 origin ∈ WithLp.toLp 2 '' feasibleSet from
        ⟨origin, origin_mem, rfl⟩)
    apply hupper.trans_eq
    have hsq : dist (WithLp.toLp 2 (negativeAxisPoint h))
        (WithLp.toLp 2 origin) ^ 2 = h ^ 2 := by
      rw [EuclideanSpace.dist_sq_eq]
      simp [negativeAxisPoint, origin, Fin.sum_univ_succ]
    have hdist : 0 ≤ dist (WithLp.toLp 2 (negativeAxisPoint h))
        (WithLp.toLp 2 origin) := dist_nonneg
    nlinarith
  · apply (Metric.le_infDist hset).2
    rintro _ ⟨z, hz, rfl⟩
    have ht : 0 ≤ z 2 := feasible_t_nonneg hz
    have hsq : h ^ 2 ≤ dist (WithLp.toLp 2 (negativeAxisPoint h))
        (WithLp.toLp 2 z) ^ 2 := by
      rw [EuclideanSpace.dist_sq_eq]
      simp [negativeAxisPoint, Fin.sum_univ_succ, Real.dist_eq]
      nlinarith [sq_nonneg (z 0), sq_nonneg (z 1), sq_nonneg (z 2)]
    have hdist : 0 ≤ dist (WithLp.toLp 2 (negativeAxisPoint h))
        (WithLp.toLp 2 z) := dist_nonneg
    nlinarith

/-- Along points converging vertically to the origin from below, both the
constraint violation and the distance to the feasible set are exactly `h`.
This is the witness showing that the global linear exponent cannot be
improved locally. -/
theorem linear_error_exponent_witness_proof
    (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    violation (negativeAxisPoint h) = h ∧
      euclideanDistanceToSet (negativeAxisPoint h) feasibleSet = h :=
  ⟨violation_negativeAxisPoint h h0 h1, distance_negativeAxisPoint h h0⟩

end OptimalConvergenceRates.MFCQQuadraticLowerBound

end
