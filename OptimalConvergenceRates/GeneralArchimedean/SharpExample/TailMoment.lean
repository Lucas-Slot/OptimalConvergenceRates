/-
  Quantitative reduction of truncated tail moments to an explicit finite sum.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.TailSupport

noncomputable section

open Finset MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

def sharpTailCoefficientEnvelope (d : Nat) (M : Real)
    (alpha : Fin 2 →₀ Nat) : Real :=
  3 * (bivarTotal alpha + 1 : Nat) ^ 2 *
    (8 : Real) ^ bivarTotal alpha *
    (d : Real) ^ (2 * bivarTotal alpha) * M ^ 2

def sharpShiftedMomentEnvelope (eta : Real) (u v : Nat)
    (alpha : Fin 2 →₀ Nat) : Real :=
  eta ^ (bivarTotal alpha + u + v) *
    Real.exp (4 * ((bivarTotal alpha + u + v : Nat) : Real) ^ 2)

/-- The explicit finite sum which bounds a shifted, truncated moment of an
SOS tail. -/
def sharpTailMomentBudget {N : Nat} (eta : Real) (D d : Nat) (M : Real)
    (u v : Nat) (q : Fin N -> MvPolynomial (Fin 2) Real) : Real :=
  ∑ alpha ∈ (sharpTailPolynomial D q).support,
    if bivarTotal alpha + u + v <= 2 * D then
      sharpTailCoefficientEnvelope d M alpha *
        sharpShiftedMomentEnvelope eta u v alpha
    else 0

theorem bivarTotal_bivarExponent_add (u v : Nat)
    (alpha : Fin 2 →₀ Nat) :
    bivarTotal (bivarExponent u v + alpha) =
      bivarTotal alpha + u + v := by
  dsimp [bivarTotal]
  simp [bivarExponent]
  omega

theorem abs_sharpMoment_le_total {eta : Real} (heta : 0 <= eta)
    (alpha : Fin 2 →₀ Nat) :
    |sharpMoment eta alpha| <=
      eta ^ bivarTotal alpha *
        Real.exp (4 * ((bivarTotal alpha : Nat) : Real) ^ 2) := by
  rw [sharpMoment]
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg heta, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg heta _)
  apply Real.exp_le_exp.mpr
  have hi : 0 <= (alpha 0 : Real) := Nat.cast_nonneg _
  have hj : 0 <= (alpha 1 : Real) := Nat.cast_nonneg _
  norm_num
  nlinarith

theorem abs_sharpMoment_bivarExponent_add_le {eta : Real}
    (heta : 0 <= eta) (u v : Nat) (alpha : Fin 2 →₀ Nat) :
    |sharpMoment eta (bivarExponent u v + alpha)| <=
      sharpShiftedMomentEnvelope eta u v alpha := by
  have h := abs_sharpMoment_le_total heta (bivarExponent u v + alpha)
  rwa [bivarTotal_bivarExponent_add] at h

/-- Exact support-sum formula for a shifted truncated moment. -/
theorem sharpTruncatedMoment_monomial_mul_apply
    (eta : Real) (D u v : Nat) (p : MvPolynomial (Fin 2) Real) :
    sharpTruncatedMoment eta D
        (monomial (bivarExponent u v) 1 * p) =
      ∑ alpha ∈ p.support,
        (if bivarTotal alpha + u + v <= 2 * D then
          sharpMoment eta (bivarExponent u v + alpha)
        else 0) * p.coeff alpha := by
  conv_lhs => rw [MvPolynomial.as_sum p]
  rw [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro alpha _halpha
  simp only [monomial_mul, one_mul, sharpTruncatedMoment_monomial]
  rw [finsupp_sum_fin_two, bivarTotal_bivarExponent_add]

/-- A shifted truncated tail moment is bounded by the explicit finite budget.
The bound is uniform in the number of square roots. -/
theorem abs_sharpTruncatedMoment_monomial_mul_tail_le
    {N D d : Nat} {eta M : Real}
    (heta : 0 <= eta) (hM : 0 <= M)
    (q : Fin N -> MvPolynomial (Fin 2) Real)
    (hdeg : forall k, (q k).totalDegree <= d)
    (hbound : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      OptimalConvergenceRates.interiorVecNorm
        (fun k => MvPolynomial.eval ![a, b] (q k)) <= M)
    (u v : Nat) :
    |sharpTruncatedMoment eta D
        (monomial (bivarExponent u v) 1 * sharpTailPolynomial D q)| <=
      sharpTailMomentBudget eta D d M u v q := by
  rw [sharpTruncatedMoment_monomial_mul_apply]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro alpha halpha
  by_cases hcut : bivarTotal alpha + u + v <= 2 * D
  · rw [if_pos hcut, abs_mul]
    have hcoeff := abs_sharpTailPolynomial_coeff_le_closed
      (D := D) q hM hdeg hbound alpha
    have hmoment := abs_sharpMoment_bivarExponent_add_le heta u v alpha
    have hmomentNonneg : 0 <=
        sharpShiftedMomentEnvelope eta u v alpha := by
      unfold sharpShiftedMomentEnvelope
      positivity
    simp only [hcut, if_true]
    simpa [sharpTailCoefficientEnvelope, mul_comm] using
      mul_le_mul hmoment hcoeff (abs_nonneg _) hmomentNonneg
  · rw [if_neg hcut]
    simp [hcut]

theorem monomial_bivarExponent_eq_pow (u v : Nat) :
    (monomial (bivarExponent u v) 1 : MvPolynomial (Fin 2) Real) =
      obstructionA ^ u * obstructionB ^ v := by
  rw [show obstructionA ^ u = monomial (Finsupp.single (0 : Fin 2) u) 1 by
      simp [obstructionA, X_pow_eq_monomial],
    show obstructionB ^ v = monomial (Finsupp.single (1 : Fin 2) v) 1 by
      simp [obstructionB, X_pow_eq_monomial],
    monomial_mul]
  simp [bivarExponent]

theorem abs_sharpTruncatedMoment_pow_mul_tail_le
    {N D d : Nat} {eta M : Real}
    (heta : 0 <= eta) (hM : 0 <= M)
    (q : Fin N -> MvPolynomial (Fin 2) Real)
    (hdeg : forall k, (q k).totalDegree <= d)
    (hbound : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      OptimalConvergenceRates.interiorVecNorm
        (fun k => MvPolynomial.eval ![a, b] (q k)) <= M)
    (u v : Nat) :
    |sharpTruncatedMoment eta D
        (obstructionA ^ u * obstructionB ^ v * sharpTailPolynomial D q)| <=
      sharpTailMomentBudget eta D d M u v q := by
  rw [← monomial_bivarExponent_eq_pow]
  exact abs_sharpTruncatedMoment_monomial_mul_tail_le
    heta hM q hdeg hbound u v

end OptimalConvergenceRates.GeneralArchimedean

end
