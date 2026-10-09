/-
  One common tail penalty for the five localizers in the obstruction.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.TailBudgetBound

noncomputable section

open Finset MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

theorem sharpTailPenalty_nonneg {D d : Nat} {M E : Real}
    (hE : 0 <= E) : 0 <= sharpTailPenalty D d M E := by
  unfold sharpTailPenalty
  positivity

private theorem abs_tail_shift_le_penalty
    {N D d u v : Nat} {eta M E : Real}
    (heta : 0 <= eta) (hM : 0 <= M) (hE : 0 <= E)
    (huv : u + v <= 2) (hdecay : SharpTailDecay eta D d E)
    (q : Fin N -> MvPolynomial (Fin 2) Real)
    (hdeg : forall k, (q k).totalDegree <= d)
    (hbound : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      OptimalConvergenceRates.interiorVecNorm
        (fun k => MvPolynomial.eval ![a, b] (q k)) <= M) :
    |sharpTruncatedMoment eta D
        (obstructionA ^ u * obstructionB ^ v * sharpTailPolynomial D q)| <=
      sharpTailPenalty D d M E := by
  exact (abs_sharpTruncatedMoment_pow_mul_tail_le
    heta hM q hdeg hbound u v).trans
      (sharpTailMomentBudget_le_penalty heta hM hE huv hdecay q hdeg)

theorem abs_sharpTruncatedMoment_tail_le_penalty
    {N D d : Nat} {eta M E : Real}
    (heta : 0 <= eta) (hM : 0 <= M) (hE : 0 <= E)
    (hdecay : SharpTailDecay eta D d E)
    (q : Fin N -> MvPolynomial (Fin 2) Real)
    (hdeg : forall k, (q k).totalDegree <= d)
    (hbound : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      OptimalConvergenceRates.interiorVecNorm
        (fun k => MvPolynomial.eval ![a, b] (q k)) <= M) :
    |sharpTruncatedMoment eta D (sharpTailPolynomial D q)| <=
      sharpTailPenalty D d M E := by
  simpa using abs_tail_shift_le_penalty heta hM hE (by omega)
    hdecay q hdeg hbound (u := 0) (v := 0)

theorem abs_sharpTruncatedMoment_a_tail_le_penalty
    {N D d : Nat} {eta M E : Real}
    (heta : 0 <= eta) (hM : 0 <= M) (hE : 0 <= E)
    (hdecay : SharpTailDecay eta D d E)
    (q : Fin N -> MvPolynomial (Fin 2) Real)
    (hdeg : forall k, (q k).totalDegree <= d)
    (hbound : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      OptimalConvergenceRates.interiorVecNorm
        (fun k => MvPolynomial.eval ![a, b] (q k)) <= M) :
    |sharpTruncatedMoment eta D
        (obstructionA * sharpTailPolynomial D q)| <=
      sharpTailPenalty D d M E := by
  simpa using abs_tail_shift_le_penalty heta hM hE (by omega)
    hdecay q hdeg hbound (u := 1) (v := 0)

theorem abs_sharpTruncatedMoment_b_tail_le_penalty
    {N D d : Nat} {eta M E : Real}
    (heta : 0 <= eta) (hM : 0 <= M) (hE : 0 <= E)
    (hdecay : SharpTailDecay eta D d E)
    (q : Fin N -> MvPolynomial (Fin 2) Real)
    (hdeg : forall k, (q k).totalDegree <= d)
    (hbound : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      OptimalConvergenceRates.interiorVecNorm
        (fun k => MvPolynomial.eval ![a, b] (q k)) <= M) :
    |sharpTruncatedMoment eta D
        (obstructionB * sharpTailPolynomial D q)| <=
      sharpTailPenalty D d M E := by
  simpa using abs_tail_shift_le_penalty heta hM hE (by omega)
    hdecay q hdeg hbound (u := 0) (v := 1)

/-- The mixed localizer costs at most two copies of the common penalty. -/
theorem abs_sharpTruncatedMoment_neg_ab_tail_le_two_penalty
    {N D d : Nat} {eta M E : Real}
    (heta : 0 <= eta) (hetaOne : eta <= 1)
    (hM : 0 <= M) (hE : 0 <= E)
    (hdecay : SharpTailDecay eta D d E)
    (q : Fin N -> MvPolynomial (Fin 2) Real)
    (hdeg : forall k, (q k).totalDegree <= d)
    (hbound : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      OptimalConvergenceRates.interiorVecNorm
        (fun k => MvPolynomial.eval ![a, b] (q k)) <= M) :
    |sharpTruncatedMoment eta D
        (-(obstructionA * obstructionB + C (eta ^ 2)) *
          sharpTailPolynomial D q)| <=
      2 * sharpTailPenalty D d M E := by
  let T := sharpTailPolynomial D q
  let P := sharpTailPenalty D d M E
  have hzero : |sharpTruncatedMoment eta D T| <= P := by
    exact abs_sharpTruncatedMoment_tail_le_penalty
      heta hM hE hdecay q hdeg hbound
  have hab : |sharpTruncatedMoment eta D (obstructionA * obstructionB * T)| <= P := by
    simpa [T] using abs_tail_shift_le_penalty heta hM hE (by omega)
      hdecay q hdeg hbound (u := 1) (v := 1)
  have hetaSq : eta ^ 2 <= 1 := by nlinarith [sq_nonneg (eta - 1)]
  have hP : 0 <= P := sharpTailPenalty_nonneg hE
  have hscaled :
      |sharpTruncatedMoment eta D (C (eta ^ 2) * T)| <= P := by
    rw [MvPolynomial.C_mul', map_smul]
    simp only [smul_eq_mul, abs_mul, abs_of_nonneg (sq_nonneg eta)]
    calc
      eta ^ 2 * |sharpTruncatedMoment eta D T| <= eta ^ 2 * P := by
        gcongr
      _ <= P := by nlinarith [sq_nonneg eta]
  have hpoly :
      -(obstructionA * obstructionB + C (eta ^ 2)) * T =
        -(obstructionA * obstructionB * T + C (eta ^ 2) * T) := by ring
  rw [hpoly, map_neg, map_add, abs_neg]
  exact (abs_add_le _ _).trans (by linarith)

/-- The ball localizer costs at most three copies of the common penalty. -/
theorem abs_sharpTruncatedMoment_ball_tail_le_three_penalty
    {N D d : Nat} {eta rho M E : Real}
    (heta : 0 <= eta) (hrho : 0 <= rho) (hrhoOne : rho <= 1)
    (hM : 0 <= M) (hE : 0 <= E)
    (hdecay : SharpTailDecay eta D d E)
    (q : Fin N -> MvPolynomial (Fin 2) Real)
    (hdeg : forall k, (q k).totalDegree <= d)
    (hbound : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      OptimalConvergenceRates.interiorVecNorm
        (fun k => MvPolynomial.eval ![a, b] (q k)) <= M) :
    |sharpTruncatedMoment eta D
        ((C rho - obstructionA ^ 2 - obstructionB ^ 2) *
          sharpTailPolynomial D q)| <=
      3 * sharpTailPenalty D d M E := by
  let T := sharpTailPolynomial D q
  let P := sharpTailPenalty D d M E
  have hzero : |sharpTruncatedMoment eta D T| <= P := by
    exact abs_sharpTruncatedMoment_tail_le_penalty
      heta hM hE hdecay q hdeg hbound
  have ha : |sharpTruncatedMoment eta D (obstructionA ^ 2 * T)| <= P := by
    simpa [T] using abs_tail_shift_le_penalty heta hM hE (by omega)
      hdecay q hdeg hbound (u := 2) (v := 0)
  have hb : |sharpTruncatedMoment eta D (obstructionB ^ 2 * T)| <= P := by
    simpa [T] using abs_tail_shift_le_penalty heta hM hE (by omega)
      hdecay q hdeg hbound (u := 0) (v := 2)
  have hP : 0 <= P := sharpTailPenalty_nonneg hE
  have hscaled : |sharpTruncatedMoment eta D (C rho * T)| <= P := by
    rw [MvPolynomial.C_mul', map_smul]
    simp only [smul_eq_mul, abs_mul, abs_of_nonneg hrho]
    calc
      rho * |sharpTruncatedMoment eta D T| <= rho * P := by gcongr
      _ <= P := by nlinarith
  have hpoly :
      (C rho - obstructionA ^ 2 - obstructionB ^ 2) * T =
        C rho * T - obstructionA ^ 2 * T - obstructionB ^ 2 * T := by ring
  rw [hpoly, map_sub, map_sub]
  calc
    |_ - _ - _| <=
        |sharpTruncatedMoment eta D (C rho * T) -
          sharpTruncatedMoment eta D (obstructionA ^ 2 * T)| +
        |sharpTruncatedMoment eta D (obstructionB ^ 2 * T)| := abs_sub _ _
    _ <= (|sharpTruncatedMoment eta D (C rho * T)| +
        |sharpTruncatedMoment eta D (obstructionA ^ 2 * T)|) +
        |sharpTruncatedMoment eta D (obstructionB ^ 2 * T)| := by
      have hxy :
          |sharpTruncatedMoment eta D (C rho * T) -
            sharpTruncatedMoment eta D (obstructionA ^ 2 * T)| <=
          |sharpTruncatedMoment eta D (C rho * T)| +
            |sharpTruncatedMoment eta D (obstructionA ^ 2 * T)| := abs_sub _ _
      linarith
    _ = |sharpTruncatedMoment eta D (C rho * T)| +
        |sharpTruncatedMoment eta D (obstructionA ^ 2 * T)| +
        |sharpTruncatedMoment eta D (obstructionB ^ 2 * T)| := rfl
    _ <= 3 * P := by linarith

end OptimalConvergenceRates.GeneralArchimedean

end
