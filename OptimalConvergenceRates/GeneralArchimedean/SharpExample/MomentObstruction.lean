/-
  The quantitative two-variable obstruction, in its root-vector form.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.TailLocalizers

noncomputable section

open Finset MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

/-- Applying the truncated signed moment to a bounded-root refutation forces
the common tail penalty to be nontrivial.  This is the algebraic heart of the
two-variable obstruction; the separate decay lemma turns the conclusion into
the logarithmic lower bound. -/
theorem momentObstruction_of_root_bounds
    {N0 N1 N2 N3 N4 D d : Nat} {eta rho M E : Real}
    (heta : 0 < eta) (hetaOne : eta <= 1)
    (hrho : (1 : Real) / 2 <= rho) (hrhoOne : rho <= 1)
    (hM : 0 <= M) (hE : 0 <= E) (hD : 1 <= D)
    (hsmall : eta ^ 2 * Real.exp (32 * (D : Real) + 16) <=
      (1 : Real) / 12)
    (hdecay : SharpTailDecay eta D d E)
    (q0 : Fin N0 -> MvPolynomial (Fin 2) Real)
    (q1 : Fin N1 -> MvPolynomial (Fin 2) Real)
    (q2 : Fin N2 -> MvPolynomial (Fin 2) Real)
    (q3 : Fin N3 -> MvPolynomial (Fin 2) Real)
    (q4 : Fin N4 -> MvPolynomial (Fin 2) Real)
    (hdeg0 : forall k, (q0 k).totalDegree <= d)
    (hdeg1 : forall k, (q1 k).totalDegree <= d)
    (hdeg2 : forall k, (q2 k).totalDegree <= d)
    (hdeg3 : forall k, (q3 k).totalDegree <= d)
    (hdeg4 : forall k, (q4 k).totalDegree <= d)
    (hbound0 : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      OptimalConvergenceRates.interiorVecNorm
        (fun k => MvPolynomial.eval ![a, b] (q0 k)) <= M)
    (hbound1 : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      OptimalConvergenceRates.interiorVecNorm
        (fun k => MvPolynomial.eval ![a, b] (q1 k)) <= M)
    (hbound2 : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      OptimalConvergenceRates.interiorVecNorm
        (fun k => MvPolynomial.eval ![a, b] (q2 k)) <= M)
    (hbound3 : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      OptimalConvergenceRates.interiorVecNorm
        (fun k => MvPolynomial.eval ![a, b] (q3 k)) <= M)
    (hbound4 : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      OptimalConvergenceRates.interiorVecNorm
        (fun k => MvPolynomial.eval ![a, b] (q4 k)) <= M)
    (hrefute :
      (-1 : MvPolynomial (Fin 2) Real) =
        (∑ k : Fin N0, (q0 k) ^ 2) +
        obstructionA * (∑ k : Fin N1, (q1 k) ^ 2) +
        obstructionB * (∑ k : Fin N2, (q2 k) ^ 2) +
        (-(obstructionA * obstructionB + C (eta ^ 2))) *
          (∑ k : Fin N3, (q3 k) ^ 2) +
        (C rho - obstructionA ^ 2 - obstructionB ^ 2) *
          (∑ k : Fin N4, (q4 k) ^ 2)) :
    1 <= 8 * sharpTailPenalty D d M E := by
  let P := sharpTailPenalty D d M E
  have hP : 0 <= P := sharpTailPenalty_nonneg hE
  have htail0 := abs_sharpTruncatedMoment_tail_le_penalty
    heta.le hM hE hdecay q0 hdeg0 hbound0
  have htail1 := abs_sharpTruncatedMoment_a_tail_le_penalty
    heta.le hM hE hdecay q1 hdeg1 hbound1
  have htail2 := abs_sharpTruncatedMoment_b_tail_le_penalty
    heta.le hM hE hdecay q2 hdeg2 hbound2
  have htail3 := abs_sharpTruncatedMoment_neg_ab_tail_le_two_penalty
    heta.le hetaOne hM hE hdecay q3 hdeg3 hbound3
  have htail4 := abs_sharpTruncatedMoment_ball_tail_le_three_penalty
    heta.le (by linarith [hrho]) hrhoOne hM hE hdecay q4 hdeg4 hbound4
  have h0 : -P <= sharpTruncatedMoment eta D
      (∑ k : Fin N0, (q0 k) ^ 2) := by
    exact (neg_le_neg htail0).trans
      (sharpTruncatedMoment_sum_sq_ge_neg_tail heta hD q0)
  have h1 : -P <= sharpTruncatedMoment eta D
      (obstructionA * ∑ k : Fin N1, (q1 k) ^ 2) := by
    exact (neg_le_neg htail1).trans
      (sharpTruncatedMoment_a_sum_sq_ge_neg_tail heta hD q1)
  have h2 : -P <= sharpTruncatedMoment eta D
      (obstructionB * ∑ k : Fin N2, (q2 k) ^ 2) := by
    exact (neg_le_neg htail2).trans
      (sharpTruncatedMoment_b_sum_sq_ge_neg_tail heta hD q2)
  have h3 : -(2 * P) <= sharpTruncatedMoment eta D
      (-(obstructionA * obstructionB + C (eta ^ 2)) *
        ∑ k : Fin N3, (q3 k) ^ 2) := by
    exact (neg_le_neg htail3).trans
      (sharpTruncatedMoment_neg_ab_sum_sq_ge_neg_tail heta hD q3)
  have h4 : -(3 * P) <= sharpTruncatedMoment eta D
      ((C rho - obstructionA ^ 2 - obstructionB ^ 2) *
        ∑ k : Fin N4, (q4 k) ^ 2) := by
    exact (neg_le_neg htail4).trans
      (sharpTruncatedMoment_ball_sum_sq_ge_neg_tail
        heta hD hrho hsmall q4)
  have hid := congrArg (fun p => sharpTruncatedMoment eta D p) hrefute
  simp only [map_add, map_neg] at hid
  rw [sharpTruncatedMoment_one] at hid
  change 1 <= 8 * P
  linarith

end OptimalConvergenceRates.GeneralArchimedean

end
