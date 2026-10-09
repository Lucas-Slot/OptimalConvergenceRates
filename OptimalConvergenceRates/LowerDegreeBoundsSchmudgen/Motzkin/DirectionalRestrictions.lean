/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/Motzkin/DirectionalRestrictions.lean

  Linear and low-order directional-derivative estimates for weighted jets.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.LocalControl
import OptimalConvergenceRates.BasicNotions.SOSVector
import OptimalConvergenceRates.MarkovInequality.MarkovInequalityCorollaries
import OptimalConvergenceRates.MarkovInequality.ChebyshevEndpoint
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

open MvPolynomial Finset
open scoped Pointwise

noncomputable section

namespace OptimalConvergenceRates

namespace Motzkin


lemma sum_sub_single_one_of_mem (α : Fin 3 →₀ ℕ) {j : Fin 3}
    (hj : j ∈ α.support) :
    (α - Finsupp.single j 1).sum (fun _ e => e) =
      α.sum (fun _ e => e) - 1 := by
  have hjpos : 1 ≤ α j := by
    have hjne : α j ≠ 0 := Finsupp.mem_support_iff.mp hj
    omega
  rw [Finsupp.sum_fintype, Finsupp.sum_fintype]
  · fin_cases j <;> simp [Fin.sum_univ_three] at hjpos ⊢ <;> omega
  · intro i
    rfl
  · intro i
    rfl

lemma homogeneousPart3_succ_mul_X (m : ℕ) (p : MvPolynomial (Fin 3) ℝ) (j : Fin 3) :
    homogeneousPart3 (m + 1) (p * MvPolynomial.X j) =
      homogeneousPart3 m p * MvPolynomial.X j := by
  ext α
  rw [coeff_homogeneousPart3]
  rw [MvPolynomial.coeff_mul_X']
  rw [MvPolynomial.coeff_mul_X']
  by_cases hj : j ∈ α.support
  · simp [hj]
    have hsumsub := sum_sub_single_one_of_mem α hj
    have hsumpos : 1 ≤ α.sum (fun _ e => e) := by
      have hjpos : 1 ≤ α j := by
        have hjne : α j ≠ 0 := Finsupp.mem_support_iff.mp hj
        omega
      rw [Finsupp.sum_fintype]
      · exact hjpos.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
      · intro i
        rfl
    by_cases hdeg : α.sum (fun _ e => e) = m + 1
    · have hpred : (α - Finsupp.single j 1).sum (fun _ e => e) = m := by omega
      simp [hdeg, coeff_homogeneousPart3, hpred]
    · have hpred : ¬ (α - Finsupp.single j 1).sum (fun _ e => e) = m := by omega
      simp [hdeg, coeff_homogeneousPart3, hpred]
  · simp [hj]

lemma homogeneousPart3_two_mul_X (p : MvPolynomial (Fin 3) ℝ) (j : Fin 3) :
    homogeneousPart3 2 (p * MvPolynomial.X j) = homogeneousPart3 1 p * MvPolynomial.X j := by
  ext α
  rw [coeff_homogeneousPart3]
  rw [MvPolynomial.coeff_mul_X']
  rw [MvPolynomial.coeff_mul_X']
  by_cases hj : j ∈ α.support
  · simp [hj]
    have hsumsub := sum_sub_single_one_of_mem α hj
    by_cases hdeg : α.sum (fun _ e => e) = 2
    · have hpred : (α - Finsupp.single j 1).sum (fun _ e => e) = 1 := by omega
      simp [hdeg, coeff_homogeneousPart3, hpred]
    · have hpred : ¬ (α - Finsupp.single j 1).sum (fun _ e => e) = 1 := by omega
      simp [hdeg, coeff_homogeneousPart3, hpred]
  · simp [hj]

lemma univariateRestriction_mul_X_zero
    (p : MvPolynomial (Fin 3) ℝ) (z : Fin 3 → ℝ) (j : Fin 3) :
    univariateRestriction (p * MvPolynomial.X j) (0 : Fin 3 → ℝ) z =
      univariateRestriction p (0 : Fin 3 → ℝ) z * (Polynomial.C (z j) * Polynomial.X) := by
  unfold univariateRestriction
  simp

lemma polynomial_second_derivative_mul_CX_eval_zero (P : Polynomial ℝ) (a : ℝ) :
    (Polynomial.derivative (Polynomial.derivative (P * (Polynomial.C a * Polynomial.X)))).eval 0 =
      2 * a * (Polynomial.derivative P).eval 0 := by
  rw [Polynomial.derivative_mul]
  simp [Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X,
    Polynomial.eval_mul, Polynomial.eval_add]
  ring

lemma polynomial_iterate_derivative_eval_zero (P : Polynomial ℝ) (m : ℕ) :
    ((Polynomial.derivative^[m]) P).eval 0 = (Nat.factorial m : ℝ) * P.coeff m := by
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  rw [Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self]

lemma polynomial_coeff_mul_CX_succ (P : Polynomial ℝ) (a : ℝ) (m : ℕ) :
    (P * (Polynomial.C a * Polynomial.X)).coeff (m + 1) = a * P.coeff m := by
  rw [mul_comm (Polynomial.C a) Polynomial.X]
  rw [show P * (Polynomial.X * Polynomial.C a) = Polynomial.X * (Polynomial.C a * P) by ring]
  rw [Polynomial.coeff_X_mul]
  simp [mul_comm]

lemma polynomial_coeff_mul_CX_zero (P : Polynomial ℝ) (a : ℝ) :
    (P * (Polynomial.C a * Polynomial.X)).coeff 0 = 0 := by
  rw [mul_comm (Polynomial.C a) Polynomial.X]
  rw [show P * (Polynomial.X * Polynomial.C a) = Polynomial.X * (Polynomial.C a * P) by ring]
  simp

theorem coeff_univariateRestriction_zero_eq_eval_homogeneousPart
    (p : MvPolynomial (Fin 3) ℝ) (z : Fin 3 → ℝ) (m : ℕ) :
    (univariateRestriction p (0 : Fin 3 → ℝ) z).coeff m =
      MvPolynomial.eval z (homogeneousPart3 m p) := by
  induction p using MvPolynomial.induction_on generalizing m with
  | C a =>
      cases m with
      | zero =>
          have hC : homogeneousPart3 0 (MvPolynomial.C a : MvPolynomial (Fin 3) ℝ) =
              MvPolynomial.C a := by
            ext α
            rw [coeff_homogeneousPart3]
            by_cases hα : α = 0
            · subst α
              simp
            · have h0α : (0 : Fin 3 →₀ ℕ) ≠ α := fun h => hα h.symm
              simp [MvPolynomial.coeff_C, h0α]
          unfold univariateRestriction
          rw [hC]
          simp
      | succ m =>
          have hC : homogeneousPart3 (m + 1)
                (MvPolynomial.C a : MvPolynomial (Fin 3) ℝ) = 0 := by
            ext α
            rw [coeff_homogeneousPart3]
            by_cases hα : α = 0
            · subst α
              simp
            · have h0α : (0 : Fin 3 →₀ ℕ) ≠ α := fun h => hα h.symm
              simp [MvPolynomial.coeff_C, h0α]
          unfold univariateRestriction
          rw [hC]
          simp
  | add p q ihp ihq =>
      unfold univariateRestriction at ihp ihq ⊢
      rw [map_add, Polynomial.coeff_add, homogeneousPart3_add, MvPolynomial.eval_add]
      rw [ihp m, ihq m]
  | mul_X p j ihp =>
      cases m with
      | zero =>
          rw [univariateRestriction_mul_X_zero]
          rw [polynomial_coeff_mul_CX_zero]
          have hzero : homogeneousPart3 0 (p * MvPolynomial.X j) = 0 := by
            ext α
            rw [coeff_homogeneousPart3]
            rw [MvPolynomial.coeff_mul_X']
            by_cases hdeg : α.sum (fun _ e => e) = 0
            · have hnot : j ∉ α.support := by
                intro hj
                have hjpos : 1 ≤ α j := by
                  have hjne : α j ≠ 0 := Finsupp.mem_support_iff.mp hj
                  omega
                have hsumpos : 1 ≤ α.sum (fun _ e => e) := by
                  rw [Finsupp.sum_fintype]
                  · exact hjpos.trans
                      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
                  · intro i
                    rfl
                omega
              simp [hdeg, hnot]
            · simp [hdeg]
          rw [hzero]
          simp
      | succ m =>
          rw [univariateRestriction_mul_X_zero]
          rw [polynomial_coeff_mul_CX_succ]
          rw [homogeneousPart3_succ_mul_X]
          rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]
          rw [ihp m]
          ring

theorem iterateDirectionalDeriv_zero_eq_eval_homogeneousPart
    (p : MvPolynomial (Fin 3) ℝ) (z : Fin 3 → ℝ) (m : ℕ) :
    ((Polynomial.derivative^[m]) (univariateRestriction p (0 : Fin 3 → ℝ) z)).eval 0 =
      (Nat.factorial m : ℝ) * MvPolynomial.eval z (homogeneousPart3 m p) := by
  rw [polynomial_iterate_derivative_eval_zero]
  rw [coeff_univariateRestriction_zero_eq_eval_homogeneousPart]

theorem polynomialTailDivX2_univariateRestriction_coeff_eq_eval_homogeneousPart
    (p : MvPolynomial (Fin 3) ℝ) (z : Fin 3 → ℝ) (n : ℕ) :
    (polynomialTailDivX2 (univariateRestriction p (0 : Fin 3 → ℝ) z)).coeff n =
      MvPolynomial.eval z (homogeneousPart3 (n + 2) p) := by
  rw [polynomialTailDivX2_coeff]
  exact coeff_univariateRestriction_zero_eq_eval_homogeneousPart p z (n + 2)

theorem iterateDerivative_tail_univariateRestriction_eval_zero_eq_homogeneousPart
    (p : MvPolynomial (Fin 3) ℝ) (z : Fin 3 → ℝ) (ell : ℕ) :
    ((Polynomial.derivative^[ell])
        (polynomialTailDivX2 (univariateRestriction p (0 : Fin 3 → ℝ) z))).eval 0 =
      (Nat.factorial ell : ℝ) * MvPolynomial.eval z (homogeneousPart3 (ell + 2) p) := by
  rw [polynomial_iterate_derivative_eval_zero]
  rw [polynomialTailDivX2_univariateRestriction_coeff_eq_eval_homogeneousPart]

/-- Remove the terms of degree below three and divide by `X^3`. -/
noncomputable def polynomialTailDivX3 (P : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.divX (polynomialTailDivX2 P)

theorem polynomialTailDivX3_coeff (P : Polynomial ℝ) (n : ℕ) :
    (polynomialTailDivX3 P).coeff n = P.coeff (n + 3) := by
  simp [polynomialTailDivX3, Polynomial.coeff_divX, polynomialTailDivX2_coeff,
    Nat.add_assoc]

theorem polynomial_eq_low_three_add_X_cube_tail (P : Polynomial ℝ) :
    P = Polynomial.C (P.coeff 0) + Polynomial.C (P.coeff 1) * Polynomial.X +
      Polynomial.C (P.coeff 2) * Polynomial.X ^ 2 +
      Polynomial.X ^ 3 * polynomialTailDivX3 P := by
  ext n
  rcases n with _ | n
  · rw [show Polynomial.X ^ 3 * polynomialTailDivX3 P =
        Polynomial.X * (Polynomial.X * (Polynomial.X * polynomialTailDivX3 P)) by ring]
    simp
  · rcases n with _ | n
    · rw [show Polynomial.X ^ 3 * polynomialTailDivX3 P =
          Polynomial.X * (Polynomial.X * (Polynomial.X * polynomialTailDivX3 P)) by ring]
      simp
    · rcases n with _ | n
      · rw [show Polynomial.X ^ 3 * polynomialTailDivX3 P =
            Polynomial.X * (Polynomial.X * (Polynomial.X * polynomialTailDivX3 P)) by ring]
        simp
      · rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add]
        have htail :
            (Polynomial.X ^ 3 * polynomialTailDivX3 P).coeff (n + 3) =
              P.coeff (n + 3) := by
          rw [Polynomial.coeff_X_pow_mul]
          exact polynomialTailDivX3_coeff P n
        simp [htail]

theorem polynomialTailDivX3_eval_identity (P : Polynomial ℝ) (t : ℝ) :
    P.eval t = P.coeff 0 + P.coeff 1 * t + P.coeff 2 * t ^ 2 +
      t ^ 3 * (polynomialTailDivX3 P).eval t := by
  have h := congrArg (fun q : Polynomial ℝ => q.eval t)
    (polynomial_eq_low_three_add_X_cube_tail P)
  simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X] using h

theorem polynomialTailDivX3_natDegree_le (P : Polynomial ℝ) :
    (polynomialTailDivX3 P).natDegree ≤ P.natDegree := by
  exact (Polynomial.natDegree_divX_le (p := polynomialTailDivX2 P)).trans
    (polynomialTailDivX2_natDegree_le P)

theorem interiorVecNorm_polynomialTailDivX3_eval_le_of_residual_bound
    {N : ℕ} (P : Fin N → Polynomial ℝ) {M t : ℝ} (ht : t ≠ 0)
    (hres : interiorVecNorm
        (fun i : Fin N =>
          (P i).eval t - (P i).coeff 0 - (P i).coeff 1 * t -
            (P i).coeff 2 * t ^ 2) ≤ M * |t| ^ 3) :
    interiorVecNorm (fun i : Fin N => (polynomialTailDivX3 (P i)).eval t) ≤ M := by
  let R : Fin N → ℝ := fun i =>
    (P i).eval t - (P i).coeff 0 - (P i).coeff 1 * t - (P i).coeff 2 * t ^ 2
  have ht3 : t ^ 3 ≠ 0 := pow_ne_zero 3 ht
  have habs3 : |t| ^ 3 ≠ 0 := pow_ne_zero 3 (abs_ne_zero.mpr ht)
  have heq : (fun i : Fin N => (polynomialTailDivX3 (P i)).eval t) =
      fun i : Fin N => (t ^ 3)⁻¹ * R i := by
    funext i
    dsimp [R]
    have h := polynomialTailDivX3_eval_identity (P i) t
    field_simp [ht3]
    nlinarith
  rw [heq, interiorVecNorm_smul_abs]
  have habsinv : |(t ^ 3)⁻¹| = (|t| ^ 3)⁻¹ := by
    rw [abs_inv, abs_pow]
  rw [habsinv]
  have hresR : interiorVecNorm R ≤ M * |t| ^ 3 := by simpa [R] using hres
  calc
    (|t| ^ 3)⁻¹ * interiorVecNorm R ≤
        (|t| ^ 3)⁻¹ * (M * |t| ^ 3) :=
      mul_le_mul_of_nonneg_left hresR (inv_nonneg.mpr (pow_nonneg (abs_nonneg t) 3))
    _ = M := by field_simp [habs3]

theorem iterateDerivative_tail3_univariateRestriction_eval_zero_eq_homogeneousPart
    (p : MvPolynomial (Fin 3) ℝ) (z : Fin 3 → ℝ) (ell : ℕ) :
    ((Polynomial.derivative^[ell])
        (polynomialTailDivX3
          (univariateRestriction p (0 : Fin 3 → ℝ) z))).eval 0 =
      (Nat.factorial ell : ℝ) * MvPolynomial.eval z (homogeneousPart3 (ell + 3) p) := by
  rw [polynomial_iterate_derivative_eval_zero, polynomialTailDivX3_coeff]
  rw [coeff_univariateRestriction_zero_eq_eval_homogeneousPart]

end Motzkin

end OptimalConvergenceRates

end
