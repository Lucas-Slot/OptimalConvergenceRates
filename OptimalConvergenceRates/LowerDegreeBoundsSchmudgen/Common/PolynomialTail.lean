/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/Common/PolynomialTail.lean

  Generic univariate polynomial-tail identities used by the new Schmuedgen bounds.
-/
import OptimalConvergenceRates.BasicNotions.SOSVector
import Mathlib.Algebra.Polynomial.Inductions

open Finset

noncomputable section

namespace OptimalConvergenceRates

/-- The polynomial obtained after removing the constant and linear terms and
dividing by `X^2`. Coefficients are shifted by two. -/
noncomputable def polynomialTailDivX2 (P : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.divX (Polynomial.divX P)

theorem polynomialTailDivX2_coeff (P : Polynomial ℝ) (n : ℕ) :
    (polynomialTailDivX2 P).coeff n = P.coeff (n + 2) := by
  simp [polynomialTailDivX2, Polynomial.coeff_divX, Nat.add_assoc]

theorem polynomial_eq_const_add_linear_add_X_sq_tail (P : Polynomial ℝ) :
    P = Polynomial.C (P.coeff 0) + Polynomial.C (P.coeff 1) * Polynomial.X +
      Polynomial.X ^ 2 * polynomialTailDivX2 P := by
  ext n
  rcases n with _ | n
  · rw [show (Polynomial.X ^ 2 * polynomialTailDivX2 P) =
        Polynomial.X * (Polynomial.X * polynomialTailDivX2 P) by ring]
    simp
  · rcases n with _ | n
    · rw [show (Polynomial.X ^ 2 * polynomialTailDivX2 P) =
          Polynomial.X * (Polynomial.X * polynomialTailDivX2 P) by ring]
      simp
    · rw [Polynomial.coeff_add, Polynomial.coeff_add]
      have htail : (Polynomial.X ^ 2 * polynomialTailDivX2 P).coeff (n + 2) =
          P.coeff (n + 2) := by
        rw [Polynomial.coeff_X_pow_mul]
        exact polynomialTailDivX2_coeff P n
      simp [htail]

theorem polynomialTailDivX2_eval_identity (P : Polynomial ℝ) (t : ℝ) :
    P.eval t = P.coeff 0 + P.coeff 1 * t + t ^ 2 * (polynomialTailDivX2 P).eval t := by
  have h := congrArg (fun q : Polynomial ℝ ↦ q.eval t)
    (polynomial_eq_const_add_linear_add_X_sq_tail P)
  simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X] using h

theorem polynomialTailDivX2_natDegree_le (P : Polynomial ℝ) :
    (polynomialTailDivX2 P).natDegree ≤ P.natDegree := by
  unfold polynomialTailDivX2
  exact (Polynomial.natDegree_divX_le (p := Polynomial.divX P)).trans
    (Polynomial.natDegree_divX_le (p := P))

theorem polynomialTailDivX2_natDegree_le_sub_two {P : Polynomial ℝ} {k : ℕ}
    (hdeg : P.natDegree ≤ k + 2) :
    (polynomialTailDivX2 P).natDegree ≤ k := by
  unfold polynomialTailDivX2
  rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
  rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
  omega

theorem polynomialTailDivX2_eval_eq_div_residual (P : Polynomial ℝ) {t : ℝ} (ht : t ≠ 0) :
    (polynomialTailDivX2 P).eval t =
      (P.eval t - P.coeff 0 - P.coeff 1 * t) / t ^ 2 := by
  have h := polynomialTailDivX2_eval_identity P t
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
  field_simp [ht2]
  nlinarith

theorem interiorVecNorm_polynomialTailDivX2_eval_le_of_residual_bound
    {N : ℕ} (P : Fin N → Polynomial ℝ) {M t : ℝ} (ht : t ≠ 0)
    (hres : interiorVecNorm
        (fun i : Fin N ↦ (P i).eval t - (P i).coeff 0 - (P i).coeff 1 * t) ≤
      M * t ^ 2) :
    interiorVecNorm (fun i : Fin N ↦ (polynomialTailDivX2 (P i)).eval t) ≤ M := by
  let R : Fin N → ℝ := fun i ↦ (P i).eval t - (P i).coeff 0 - (P i).coeff 1 * t
  have ht2pos : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  have heq : (fun i : Fin N ↦ (polynomialTailDivX2 (P i)).eval t) =
      fun i : Fin N ↦ (t ^ 2)⁻¹ * R i := by
    funext i
    dsimp [R]
    have h := polynomialTailDivX2_eval_identity (P i) t
    have ht2 : t ^ 2 ≠ 0 := ht2pos.ne'
    field_simp [ht2]
    nlinarith
  have hscale : interiorVecNorm (fun i : Fin N ↦ (t ^ 2)⁻¹ * R i) =
      (t ^ 2)⁻¹ * interiorVecNorm R := by
    rw [interiorVecNorm_smul_abs, abs_of_nonneg (inv_nonneg.mpr ht2pos.le)]
  rw [heq, hscale]
  have hres' : interiorVecNorm R ≤ M * t ^ 2 := by simpa [R] using hres
  calc
    (t ^ 2)⁻¹ * interiorVecNorm R ≤ (t ^ 2)⁻¹ * (M * t ^ 2) := by
      exact mul_le_mul_of_nonneg_left hres' (inv_nonneg.mpr ht2pos.le)
    _ = M := by field_simp [ht2pos.ne']

end OptimalConvergenceRates

end
