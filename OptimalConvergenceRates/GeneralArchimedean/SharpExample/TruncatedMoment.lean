/-
  The finite-degree truncation of the signed moment functional.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.BallLocalizer

noncomputable section

open Finset MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

/-- The signed moment functional with all moments of total degree above
`2 * D` set to zero.  Defining it on the ambient polynomial space makes it
directly applicable to certificate identities. -/
def sharpTruncatedMoment (eta : Real) (D : Nat) :
    MvPolynomial (Fin 2) Real →ₗ[Real] Real :=
  (Finsupp.lsum Real)
    (fun alpha : Fin 2 →₀ Nat =>
      (LinearMap.lsmul Real Real)
        (if alpha.sum (fun _ e => e) <= 2 * D then
          sharpMoment eta alpha
        else 0))

@[simp] theorem sharpTruncatedMoment_apply (eta : Real) (D : Nat)
    (p : MvPolynomial (Fin 2) Real) :
    sharpTruncatedMoment eta D p =
      p.sum fun alpha c =>
        (if alpha.sum (fun _ e => e) <= 2 * D then
          sharpMoment eta alpha
        else 0) * c :=
  rfl

@[simp] theorem sharpTruncatedMoment_monomial
    (eta c : Real) (D : Nat) (alpha : Fin 2 →₀ Nat) :
    sharpTruncatedMoment eta D (monomial alpha c) =
      (if alpha.sum (fun _ e => e) <= 2 * D then
        sharpMoment eta alpha
      else 0) * c := by
  change (Finsupp.lsum Real) _ (Finsupp.single alpha c) = _
  rw [Finsupp.lsum_single]
  rfl

/-- Below the cutoff, truncation agrees exactly with the original moment
functional. -/
theorem sharpTruncatedMoment_eq_sharpMomentFunctional
    (eta : Real) (D : Nat) (p : MvPolynomial (Fin 2) Real)
    (hdeg : p.totalDegree <= 2 * D) :
    sharpTruncatedMoment eta D p = sharpMomentFunctional eta p := by
  rw [sharpTruncatedMoment_apply, sharpMomentFunctional_apply]
  apply Finset.sum_congr rfl
  intro alpha halpha
  have halphaDegree : alpha.sum (fun _ e => e) <= 2 * D :=
    (MvPolynomial.le_totalDegree halpha).trans hdeg
  simp [halphaDegree]

@[simp] theorem sharpTruncatedMoment_one (eta : Real) (D : Nat) :
    sharpTruncatedMoment eta D (1 : MvPolynomial (Fin 2) Real) = 1 := by
  rw [sharpTruncatedMoment_eq_sharpMomentFunctional eta D]
  · exact sharpMomentFunctional_one eta
  · simp

/-- A localizer of degree at most two times the square of a polynomial of
degree at most `D - 1` lies below the truncation cutoff `2 * D`. -/
theorem totalDegree_localizer_mul_sq_le
    (ell q : MvPolynomial (Fin 2) Real) (D : Nat)
    (hell : ell.totalDegree <= 2) (hq : q.totalDegree + 1 <= D) :
    (ell * q ^ 2).totalDegree <= 2 * D := by
  calc
    (ell * q ^ 2).totalDegree
        <= ell.totalDegree + (q ^ 2).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ <= 2 + 2 * q.totalDegree :=
      Nat.add_le_add hell (MvPolynomial.totalDegree_pow q 2)
    _ <= 2 * D := by omega

theorem sharpTruncatedMoment_sq_nonneg
    {eta : Real} (heta : 0 < eta) {D : Nat}
    (q : MvPolynomial (Fin 2) Real) (hq : q.totalDegree + 1 <= D) :
    0 <= sharpTruncatedMoment eta D (q ^ 2) := by
  rw [sharpTruncatedMoment_eq_sharpMomentFunctional eta D]
  · exact sharpMomentFunctional_sq_nonneg heta q
  · have hdeg := totalDegree_localizer_mul_sq_le
        (1 : MvPolynomial (Fin 2) Real) q D (by simp) hq
    simpa using hdeg

theorem sharpTruncatedMoment_a_sq_nonneg
    {eta : Real} (heta : 0 < eta) {D : Nat}
    (q : MvPolynomial (Fin 2) Real) (hq : q.totalDegree + 1 <= D) :
    0 <= sharpTruncatedMoment eta D (obstructionA * q ^ 2) := by
  rw [sharpTruncatedMoment_eq_sharpMomentFunctional eta D]
  · exact sharpMomentFunctional_a_sq_nonneg heta q
  · exact totalDegree_localizer_mul_sq_le obstructionA q D (by simp) hq

theorem sharpTruncatedMoment_b_sq_nonneg
    {eta : Real} (heta : 0 < eta) {D : Nat}
    (q : MvPolynomial (Fin 2) Real) (hq : q.totalDegree + 1 <= D) :
    0 <= sharpTruncatedMoment eta D (obstructionB * q ^ 2) := by
  rw [sharpTruncatedMoment_eq_sharpMomentFunctional eta D]
  · exact sharpMomentFunctional_b_sq_nonneg heta q
  · exact totalDegree_localizer_mul_sq_le obstructionB q D (by simp) hq

theorem sharpTruncatedMoment_neg_ab_etaSq_sq_nonneg
    {eta : Real} (heta : 0 < eta) {D : Nat}
    (q : MvPolynomial (Fin 2) Real) (hq : q.totalDegree + 1 <= D) :
    0 <= sharpTruncatedMoment eta D
      (-(obstructionA * obstructionB + C (eta ^ 2)) * q ^ 2) := by
  rw [sharpTruncatedMoment_eq_sharpMomentFunctional eta D]
  · exact sharpMomentFunctional_neg_ab_etaSq_sq_nonneg heta q
  · have hab : (obstructionA * obstructionB).totalDegree <= 2 := by
      calc
        (obstructionA * obstructionB).totalDegree
            <= obstructionA.totalDegree + obstructionB.totalDegree :=
          MvPolynomial.totalDegree_mul _ _
        _ = 2 := by simp [obstructionA, obstructionB]
    have hc : (C (eta ^ 2) : MvPolynomial (Fin 2) Real).totalDegree <= 2 := by
      rw [MvPolynomial.totalDegree_C]
      omega
    apply totalDegree_localizer_mul_sq_le _ q D _ hq
    exact (MvPolynomial.totalDegree_neg _).le.trans
      ((MvPolynomial.totalDegree_add _ _).trans
        (max_le hab hc))

theorem sharpTruncatedMoment_ball_sq_nonneg
    {eta rho : Real} {D : Nat} (heta : 0 < eta)
    (hrho : (1 : Real) / 2 <= rho)
    (hsmall : eta ^ 2 * Real.exp (32 * (D : Real) + 16) <=
      (1 : Real) / 12)
    (q : MvPolynomial (Fin 2) Real) (hq : q.totalDegree + 1 <= D) :
    0 <= sharpTruncatedMoment eta D
      ((C rho - obstructionA ^ 2 - obstructionB ^ 2) * q ^ 2) := by
  rw [sharpTruncatedMoment_eq_sharpMomentFunctional eta D]
  · exact sharpMomentFunctional_ball_sq_nonneg heta hrho hsmall q
      (Nat.le_of_succ_le hq)
  · apply totalDegree_localizer_mul_sq_le _ q D _ hq
    exact (MvPolynomial.totalDegree_sub _ _).trans
      ((max_le_iff).2 ⟨
        (MvPolynomial.totalDegree_sub _ _).trans
          ((max_le_iff).2 ⟨by simp, (MvPolynomial.totalDegree_pow _ 2).trans (by simp)⟩),
        (MvPolynomial.totalDegree_pow _ 2).trans (by simp)⟩)

end OptimalConvergenceRates.GeneralArchimedean

end
