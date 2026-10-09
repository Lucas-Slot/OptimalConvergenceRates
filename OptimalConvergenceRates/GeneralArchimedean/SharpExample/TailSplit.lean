/-
  Low/high total-degree splitting for the truncated signed-moment argument.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.BivariateCoefficients

noncomputable section

open Finset MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

/-- Terms whose total monomial degree is strictly below `D`. -/
def sharpLowPart (D : Nat) (p : MvPolynomial (Fin 2) Real) :
    MvPolynomial (Fin 2) Real :=
  p.filter fun alpha => alpha.sum (fun _ e => e) < D

/-- Terms whose total monomial degree is at least `D`. -/
def sharpHighPart (D : Nat) (p : MvPolynomial (Fin 2) Real) :
    MvPolynomial (Fin 2) Real :=
  p.filter fun alpha => D <= alpha.sum (fun _ e => e)

@[simp] theorem sharpLowPart_coeff (D : Nat)
    (p : MvPolynomial (Fin 2) Real) (alpha : Fin 2 →₀ Nat) :
    (sharpLowPart D p).coeff alpha =
      if alpha.sum (fun _ e => e) < D then p.coeff alpha else 0 :=
  rfl

@[simp] theorem sharpHighPart_coeff (D : Nat)
    (p : MvPolynomial (Fin 2) Real) (alpha : Fin 2 →₀ Nat) :
    (sharpHighPart D p).coeff alpha =
      if D <= alpha.sum (fun _ e => e) then p.coeff alpha else 0 :=
  rfl

theorem sharpLowPart_add_highPart (D : Nat)
    (p : MvPolynomial (Fin 2) Real) :
    sharpLowPart D p + sharpHighPart D p = p := by
  ext alpha
  change (sharpLowPart D p).coeff alpha + (sharpHighPart D p).coeff alpha = p.coeff alpha
  by_cases h : alpha.sum (fun _ e => e) < D
  · have hnle : ¬ D <= alpha.sum (fun _ e => e) := Nat.not_le_of_lt h
    rw [sharpLowPart_coeff, sharpHighPart_coeff, if_pos h, if_neg hnle]
    simp
  · have hle : D <= alpha.sum (fun _ e => e) := Nat.le_of_not_gt h
    rw [sharpLowPart_coeff, sharpHighPart_coeff, if_neg h, if_pos hle]
    simp

theorem sharpLowPart_totalDegree_add_one_le {D : Nat} (hD : 1 <= D)
    (p : MvPolynomial (Fin 2) Real) :
    (sharpLowPart D p).totalDegree + 1 <= D := by
  rw [MvPolynomial.totalDegree]
  apply Nat.succ_le_iff.mpr
  rw [Finset.sup_lt_iff (by omega : 0 < D)]
  intro alpha halpha
  have hcoeff : (sharpLowPart D p).coeff alpha ≠ 0 :=
    MvPolynomial.mem_support_iff.mp halpha
  rw [sharpLowPart_coeff] at hcoeff
  by_contra hnot
  rw [if_neg hnot] at hcoeff
  exact hcoeff rfl

theorem sharpHighPart_support_degree {D : Nat}
    {p : MvPolynomial (Fin 2) Real} {alpha : Fin 2 →₀ Nat}
    (halpha : alpha ∈ (sharpHighPart D p).support) :
    D <= alpha.sum (fun _ e => e) := by
  have hcoeff : (sharpHighPart D p).coeff alpha ≠ 0 :=
    MvPolynomial.mem_support_iff.mp halpha
  rw [sharpHighPart_coeff] at hcoeff
  by_contra hnot
  rw [if_neg hnot] at hcoeff
  exact hcoeff rfl

theorem sharpLowPart_support_degree {D : Nat}
    {p : MvPolynomial (Fin 2) Real} {alpha : Fin 2 →₀ Nat}
    (halpha : alpha ∈ (sharpLowPart D p).support) :
    alpha.sum (fun _ e => e) < D := by
  have hcoeff : (sharpLowPart D p).coeff alpha ≠ 0 :=
    MvPolynomial.mem_support_iff.mp halpha
  rw [sharpLowPart_coeff] at hcoeff
  by_contra hnot
  rw [if_neg hnot] at hcoeff
  exact hcoeff rfl

theorem sharpTruncatedMoment_sum_low_sq_nonneg
    {eta : Real} (heta : 0 < eta) {D N : Nat} (hD : 1 <= D)
    (q : Fin N -> MvPolynomial (Fin 2) Real) :
    0 <= sharpTruncatedMoment eta D
      (∑ k : Fin N, (sharpLowPart D (q k)) ^ 2) := by
  rw [map_sum]
  exact Finset.sum_nonneg fun k _ =>
    sharpTruncatedMoment_sq_nonneg heta _
      (sharpLowPart_totalDegree_add_one_le hD (q k))

theorem sharpTruncatedMoment_a_sum_low_sq_nonneg
    {eta : Real} (heta : 0 < eta) {D N : Nat} (hD : 1 <= D)
    (q : Fin N -> MvPolynomial (Fin 2) Real) :
    0 <= sharpTruncatedMoment eta D
      (obstructionA * ∑ k : Fin N, (sharpLowPart D (q k)) ^ 2) := by
  rw [Finset.mul_sum, map_sum]
  exact Finset.sum_nonneg fun k _ =>
    sharpTruncatedMoment_a_sq_nonneg heta _
      (sharpLowPart_totalDegree_add_one_le hD (q k))

theorem sharpTruncatedMoment_b_sum_low_sq_nonneg
    {eta : Real} (heta : 0 < eta) {D N : Nat} (hD : 1 <= D)
    (q : Fin N -> MvPolynomial (Fin 2) Real) :
    0 <= sharpTruncatedMoment eta D
      (obstructionB * ∑ k : Fin N, (sharpLowPart D (q k)) ^ 2) := by
  rw [Finset.mul_sum, map_sum]
  exact Finset.sum_nonneg fun k _ =>
    sharpTruncatedMoment_b_sq_nonneg heta _
      (sharpLowPart_totalDegree_add_one_le hD (q k))

theorem sharpTruncatedMoment_neg_ab_sum_low_sq_nonneg
    {eta : Real} (heta : 0 < eta) {D N : Nat} (hD : 1 <= D)
    (q : Fin N -> MvPolynomial (Fin 2) Real) :
    0 <= sharpTruncatedMoment eta D
      (-(obstructionA * obstructionB + C (eta ^ 2)) *
        ∑ k : Fin N, (sharpLowPart D (q k)) ^ 2) := by
  rw [Finset.mul_sum, map_sum]
  exact Finset.sum_nonneg fun k _ =>
    sharpTruncatedMoment_neg_ab_etaSq_sq_nonneg heta _
      (sharpLowPart_totalDegree_add_one_le hD (q k))

theorem sharpTruncatedMoment_ball_sum_low_sq_nonneg
    {eta rho : Real} (heta : 0 < eta) {D N : Nat} (hD : 1 <= D)
    (hrho : (1 : Real) / 2 <= rho)
    (hsmall : eta ^ 2 * Real.exp (32 * (D : Real) + 16) <=
      (1 : Real) / 12)
    (q : Fin N -> MvPolynomial (Fin 2) Real) :
    0 <= sharpTruncatedMoment eta D
      ((C rho - obstructionA ^ 2 - obstructionB ^ 2) *
        ∑ k : Fin N, (sharpLowPart D (q k)) ^ 2) := by
  rw [Finset.mul_sum, map_sum]
  exact Finset.sum_nonneg fun k _ =>
    sharpTruncatedMoment_ball_sq_nonneg heta hrho hsmall _
      (sharpLowPart_totalDegree_add_one_le hD (q k))


/-- The part of a vector sum of squares containing at least one monomial of
degree at least `D`. -/
def sharpTailPolynomial {N : Nat} (D : Nat)
    (q : Fin N -> MvPolynomial (Fin 2) Real) :
    MvPolynomial (Fin 2) Real :=
  ∑ k : Fin N,
    (C (2 : Real) *
        (sharpLowPart D (q k) * sharpHighPart D (q k)) +
      (sharpHighPart D (q k)) ^ 2)

theorem sum_sq_eq_low_add_tail {N D : Nat}
    (q : Fin N -> MvPolynomial (Fin 2) Real) :
    (∑ k : Fin N, (q k) ^ 2) =
      (∑ k : Fin N, (sharpLowPart D (q k)) ^ 2) +
        sharpTailPolynomial D q := by
  rw [sharpTailPolynomial, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  nth_rw 1 [<- sharpLowPart_add_highPart D (q k)]
  have htwo : (2 : MvPolynomial (Fin 2) Real) = C (2 : Real) := by
    exact (map_ofNat
      (MvPolynomial.C : Real →+* MvPolynomial (Fin 2) Real) 2).symm
  rw [<- htwo]
  ring

theorem sharpTruncatedMoment_localizer_sum_sq_ge_neg_tail
    {eta : Real} {D N : Nat} (ell : MvPolynomial (Fin 2) Real)
    (q : Fin N -> MvPolynomial (Fin 2) Real)
    (hlow : 0 <= sharpTruncatedMoment eta D
      (ell * ∑ k : Fin N, (sharpLowPart D (q k)) ^ 2)) :
    -|sharpTruncatedMoment eta D (ell * sharpTailPolynomial D q)| <=
      sharpTruncatedMoment eta D (ell * ∑ k : Fin N, (q k) ^ 2) := by
  rw [sum_sq_eq_low_add_tail, mul_add, map_add]
  have htail : -|sharpTruncatedMoment eta D (ell * sharpTailPolynomial D q)| <=
      sharpTruncatedMoment eta D (ell * sharpTailPolynomial D q) :=
    neg_abs_le _
  linarith

theorem sharpTruncatedMoment_sum_sq_ge_neg_tail
    {eta : Real} (heta : 0 < eta) {D N : Nat} (hD : 1 <= D)
    (q : Fin N -> MvPolynomial (Fin 2) Real) :
    -|sharpTruncatedMoment eta D (sharpTailPolynomial D q)| <=
      sharpTruncatedMoment eta D (∑ k : Fin N, (q k) ^ 2) := by
  have h := sharpTruncatedMoment_localizer_sum_sq_ge_neg_tail
    (eta := eta) (D := D) (1 : MvPolynomial (Fin 2) Real) q
    (by simpa using sharpTruncatedMoment_sum_low_sq_nonneg heta hD q)
  simpa using h

theorem sharpTruncatedMoment_a_sum_sq_ge_neg_tail
    {eta : Real} (heta : 0 < eta) {D N : Nat} (hD : 1 <= D)
    (q : Fin N -> MvPolynomial (Fin 2) Real) :
    -|sharpTruncatedMoment eta D
        (obstructionA * sharpTailPolynomial D q)| <=
      sharpTruncatedMoment eta D
        (obstructionA * ∑ k : Fin N, (q k) ^ 2) :=
  sharpTruncatedMoment_localizer_sum_sq_ge_neg_tail obstructionA q
    (sharpTruncatedMoment_a_sum_low_sq_nonneg heta hD q)

theorem sharpTruncatedMoment_b_sum_sq_ge_neg_tail
    {eta : Real} (heta : 0 < eta) {D N : Nat} (hD : 1 <= D)
    (q : Fin N -> MvPolynomial (Fin 2) Real) :
    -|sharpTruncatedMoment eta D
        (obstructionB * sharpTailPolynomial D q)| <=
      sharpTruncatedMoment eta D
        (obstructionB * ∑ k : Fin N, (q k) ^ 2) :=
  sharpTruncatedMoment_localizer_sum_sq_ge_neg_tail obstructionB q
    (sharpTruncatedMoment_b_sum_low_sq_nonneg heta hD q)

theorem sharpTruncatedMoment_neg_ab_sum_sq_ge_neg_tail
    {eta : Real} (heta : 0 < eta) {D N : Nat} (hD : 1 <= D)
    (q : Fin N -> MvPolynomial (Fin 2) Real) :
    -|sharpTruncatedMoment eta D
        (-(obstructionA * obstructionB + C (eta ^ 2)) *
          sharpTailPolynomial D q)| <=
      sharpTruncatedMoment eta D
        (-(obstructionA * obstructionB + C (eta ^ 2)) *
          ∑ k : Fin N, (q k) ^ 2) :=
  sharpTruncatedMoment_localizer_sum_sq_ge_neg_tail
    (-(obstructionA * obstructionB + C (eta ^ 2))) q
    (sharpTruncatedMoment_neg_ab_sum_low_sq_nonneg heta hD q)

theorem sharpTruncatedMoment_ball_sum_sq_ge_neg_tail
    {eta rho : Real} (heta : 0 < eta) {D N : Nat} (hD : 1 <= D)
    (hrho : (1 : Real) / 2 <= rho)
    (hsmall : eta ^ 2 * Real.exp (32 * (D : Real) + 16) <=
      (1 : Real) / 12)
    (q : Fin N -> MvPolynomial (Fin 2) Real) :
    -|sharpTruncatedMoment eta D
        ((C rho - obstructionA ^ 2 - obstructionB ^ 2) *
          sharpTailPolynomial D q)| <=
      sharpTruncatedMoment eta D
        ((C rho - obstructionA ^ 2 - obstructionB ^ 2) *
          ∑ k : Fin N, (q k) ^ 2) :=
  sharpTruncatedMoment_localizer_sum_sq_ge_neg_tail
    (C rho - obstructionA ^ 2 - obstructionB ^ 2) q
    (sharpTruncatedMoment_ball_sum_low_sq_nonneg
      heta hD hrho hsmall q)


end OptimalConvergenceRates.GeneralArchimedean
end
