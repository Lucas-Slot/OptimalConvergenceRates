import OptimalConvergenceRates.CQC.AffineBox

/-! Algebraic identities used to certify normalized slack cube generators. -/

noncomputable section
open MvPolynomial
namespace OptimalConvergenceRates.CQCInternal

variable {n : ℕ}

theorem localized_generator_identity
    (U : ℝ) (hU : U ≠ 0) (q : MvPolynomial (Fin n) ℝ) :
    C U⁻¹ * (C U - q) ^ 2 * q + C U⁻¹ * q ^ 2 * (C U - q) =
      q * (C U - q) := by
  have hInv : (C U⁻¹ : MvPolynomial (Fin n) ℝ) * C U = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hU, map_one]
  calc
    C U⁻¹ * (C U - q) ^ 2 * q + C U⁻¹ * q ^ 2 * (C U - q) =
        (C U⁻¹ * C U) * (q * (C U - q)) := by ring
    _ = q * (C U - q) := by rw [hInv, one_mul]

theorem normalized_slack_generator_identity
    (U : ℝ) (hU : U ≠ 0) (q : MvPolynomial (Fin n) ℝ) :
    1 - (C (2 / U) * q - 1) ^ 2 =
      C (4 / U ^ 2) * (q * (C U - q)) := by
  have ht2 : (C (2 / U) : MvPolynomial (Fin n) ℝ) ^ 2 = C (4 / U ^ 2) := by
    rw [← C_pow]
    congr 1
    field_simp
    norm_num
  have htwo : (2 : MvPolynomial (Fin n) ℝ) = C (2 : ℝ) :=
    (C_eq_coe_nat 2).symm
  have hlin : (2 : MvPolynomial (Fin n) ℝ) * C (2 / U) =
      C (4 / U ^ 2) * C U := by
    rw [htwo, ← C_mul, ← C_mul]
    congr 1
    field_simp
    norm_num
  calc
    1 - (C (2 / U) * q - 1) ^ 2 =
        (2 * C (2 / U)) * q - C (2 / U) ^ 2 * q ^ 2 := by ring
    _ = (C (4 / U ^ 2) * C U) * q - C (4 / U ^ 2) * q ^ 2 := by
      rw [hlin, ht2]
    _ = C (4 / U ^ 2) * (q * (C U - q)) := by ring

end OptimalConvergenceRates.CQCInternal
end
