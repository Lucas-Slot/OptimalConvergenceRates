/-
  The quantitative three-arc SOS obstruction and its numerical conclusion.
-/
import OptimalConvergenceRates.MFCQQuadraticLowerBound.JetIdentities

noncomputable section

open Finset MvPolynomial Polynomial

namespace OptimalConvergenceRates.MFCQQuadraticLowerBound

variable {epsilon : ℝ} {r : ℕ}

private def arcDerivativeBound (epsilon : ℝ) (r : ℕ) : ℝ :=
  9 * (r : ℝ) + 72 * (r : ℝ) ^ 2 * Real.sqrt epsilon

theorem rootCoeffTwoVector_norm_le
    (certificate : ExtractedCertificate epsilon r) (hr : 1 ≤ r)
    (j : Fin 3) :
    interiorVecNorm (rootCoeffTwoVector certificate j) ≤
      arcDerivativeBound epsilon r / 2 := by
  have hderivative := arcRootPolynomials_secondDerivative_le certificate hr j
  have hvector :
      (fun i ↦
        (derivative (derivative (arcRootPolynomials certificate j i))).eval 0) =
      fun i ↦ 2 * rootCoeffTwoVector certificate j i := by
    funext i
    have h := GeneralArchimedean.iterate_derivative_eval_zero
      (arcRootPolynomials certificate j i) 2
    change
      (derivative (derivative (arcRootPolynomials certificate j i))).eval 0 =
        (Nat.factorial 2 : ℝ) *
          (arcRootPolynomials certificate j i).coeff 2 at h
    simpa [rootCoeffTwoVector] using h
  rw [hvector] at hderivative
  have hscale := interiorVecNorm_smul_abs (N := certificate.rootCount) 2
    (rootCoeffTwoVector certificate j)
  rw [hscale, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hderivative
  dsimp [arcDerivativeBound]
  linarith

theorem rootCoeffTwo_combination_norm_le
    (certificate : ExtractedCertificate epsilon r) (hr : 1 ≤ r) :
    interiorVecNorm
        (fun i ↦ rootCoeffTwoVector certificate 1 i +
          rootCoeffTwoVector certificate 2 i -
          2 * rootCoeffTwoVector certificate 0 i) ≤
      2 * arcDerivativeBound epsilon r := by
  have h0 := rootCoeffTwoVector_norm_le certificate hr 0
  have h1 := rootCoeffTwoVector_norm_le certificate hr 1
  have h2 := rootCoeffTwoVector_norm_le certificate hr 2
  have hadd := interiorVecNorm_add_le
    (rootCoeffTwoVector certificate 1) (rootCoeffTwoVector certificate 2)
  have hscale := interiorVecNorm_smul_abs (N := certificate.rootCount) 2
    (rootCoeffTwoVector certificate 0)
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hscale
  have hsub := interiorVecNorm_sub_le
    (fun i ↦ rootCoeffTwoVector certificate 1 i +
      rootCoeffTwoVector certificate 2 i)
    (fun i ↦ 2 * rootCoeffTwoVector certificate 0 i)
  dsimp [arcDerivativeBound] at h0 h1 h2 ⊢
  nlinarith

theorem activeMultiplierSum_nonneg
    (certificate : ExtractedCertificate epsilon r) :
    0 ≤ activeMultiplierSum certificate := by
  unfold activeMultiplierSum
  apply Finset.sum_nonneg
  intro i _
  exact IsSOS_nonneg _ (certificate.sos i.castSucc) _ (Set.mem_univ _)

theorem activeMultiplierSum_upper_bound
    (certificate : ExtractedCertificate epsilon r) (hr : 1 ≤ r) :
    activeMultiplierSum certificate ≤
      epsilon + 8 * arcDerivativeBound epsilon r * Real.sqrt epsilon := by
  let combination : Fin certificate.rootCount → ℝ := fun i ↦
    rootCoeffTwoVector certificate 1 i +
      rootCoeffTwoVector certificate 2 i -
      2 * rootCoeffTwoVector certificate 0 i
  have hidentity := second_jet_identity certificate
  have hsq1 := interiorVecSqNorm_nonneg
    (rootCoeffOneVector certificate 1)
  have hsq2 := interiorVecSqNorm_nonneg
    (rootCoeffOneVector certificate 2)
  have hball := ballMultiplier_value_le certificate
  have hcombination : interiorVecNorm combination ≤
      2 * arcDerivativeBound epsilon r := by
    exact rootCoeffTwo_combination_norm_le certificate hr
  have hdot := abs_vecDot_le_vecNorm_mul
    (rootValueVector certificate) combination
  have hdot' :
      |vecDot (rootValueVector certificate) combination| ≤
        Real.sqrt epsilon * (2 * arcDerivativeBound epsilon r) := by
    calc
      |vecDot (rootValueVector certificate) combination| ≤
          interiorVecNorm (rootValueVector certificate) *
            interiorVecNorm combination := by
        simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm] using hdot
      _ ≤ Real.sqrt epsilon * (2 * arcDerivativeBound epsilon r) := by
        rw [rootValue_norm_eq]
        exact mul_le_mul_of_nonneg_left hcombination
          (Real.sqrt_nonneg epsilon)
  change 0 =
      2 * vecDot (rootValueVector certificate) combination +
      interiorVecSqNorm (rootCoeffOneVector certificate 1) +
      interiorVecSqNorm (rootCoeffOneVector certificate 2) +
      (1 / 2 : ℝ) * activeMultiplierSum certificate -
      (1 / 2 : ℝ) * MvPolynomial.eval origin (certificate.sigma 4) at hidentity
  have hnegdot :
      -vecDot (rootValueVector certificate) combination ≤
        |vecDot (rootValueVector certificate) combination| := neg_le_abs _
  nlinarith

/-- The quantitative obstruction before the final numerical contradiction. -/
theorem certificate_obstruction
    (certificate : ExtractedCertificate epsilon r) (hr : 1 ≤ r) :
    1 ≤ epsilon + 108 * (r : ℝ) * Real.sqrt epsilon +
      864 * (r : ℝ) ^ 2 * epsilon := by
  have hfirst := first_jet_identity certificate
  have hlambda := activeMultiplierSum_upper_bound certificate hr
  have hcoeff := rootCoeffTwoVector_norm_le certificate hr 0
  have hdot := abs_vecDot_le_vecNorm_mul
    (rootValueVector certificate) (rootCoeffTwoVector certificate 0)
  have hdot' :
      |vecDot (rootValueVector certificate)
          (rootCoeffTwoVector certificate 0)| ≤
        Real.sqrt epsilon * (arcDerivativeBound epsilon r / 2) := by
    calc
      |vecDot (rootValueVector certificate)
          (rootCoeffTwoVector certificate 0)| ≤
          interiorVecNorm (rootValueVector certificate) *
            interiorVecNorm (rootCoeffTwoVector certificate 0) := by
        simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm] using hdot
      _ ≤ Real.sqrt epsilon * (arcDerivativeBound epsilon r / 2) := by
        rw [rootValue_norm_eq]
        exact mul_le_mul_of_nonneg_left hcoeff (Real.sqrt_nonneg epsilon)
  have hsqrt : (Real.sqrt epsilon) ^ 2 = epsilon :=
    Real.sq_sqrt certificate.epsilon_nonneg
  have hleabs := le_abs_self
    (vecDot (rootValueVector certificate) (rootCoeffTwoVector certificate 0))
  dsimp [arcDerivativeBound] at hlambda hdot' ⊢
  nlinarith

/-- The headline certificate lower bound for an already extracted
certificate. -/
theorem extractedCertificate_lower_bound
    (certificate : ExtractedCertificate epsilon r) (hr : 1 ≤ r) :
    (1 : ℝ) / (2 ^ 14 * (r : ℝ) ^ 2) < epsilon := by
  have hepsilon := certificate.epsilon_nonneg
  have hobs := certificate_obstruction certificate hr
  by_contra hnot
  have hepsUpper : epsilon ≤ (1 : ℝ) / (2 ^ 14 * (r : ℝ) ^ 2) :=
    le_of_not_gt hnot
  have hrReal : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrPos : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hrReal
  let x : ℝ := (r : ℝ) * Real.sqrt epsilon
  have hx0 : 0 ≤ x := mul_nonneg hrPos.le (Real.sqrt_nonneg epsilon)
  have hxSq : x ^ 2 = (r : ℝ) ^ 2 * epsilon := by
    dsimp [x]
    rw [mul_pow, Real.sq_sqrt hepsilon]
  have hcancel :
      (r : ℝ) ^ 2 * ((1 : ℝ) / (2 ^ 14 * (r : ℝ) ^ 2)) =
        (1 : ℝ) / 2 ^ 14 := by
    field_simp
  have hxSqUpper : x ^ 2 ≤ (1 / 128 : ℝ) ^ 2 := by
    rw [hxSq]
    have hmul := mul_le_mul_of_nonneg_left hepsUpper
      (sq_nonneg (r : ℝ))
    rw [hcancel] at hmul
    norm_num at hmul ⊢
    exact hmul
  have hxUpper : x ≤ (1 / 128 : ℝ) := by
    nlinarith [sq_nonneg (x - 1 / 128)]
  have hepsLeX : epsilon ≤ x ^ 2 := by
    rw [hxSq]
    have hrSq : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg (r : ℝ)) hepsilon]
  have hobsX : 1 ≤ epsilon + 108 * x + 864 * x ^ 2 := by
    dsimp [x]
    nlinarith
  have hlinear : 108 * x ≤ (108 : ℝ) / 128 := by linarith
  have hquadratic : 865 * x ^ 2 ≤ (865 : ℝ) / 128 ^ 2 := by
    nlinarith
  have hcontradiction :
      (1 : ℝ) ≤ 108 / 128 + 865 / 128 ^ 2 := by
    nlinarith
  norm_num at hcontradiction

/-- Public proof object for the certificate-level headline theorem. -/
theorem certificate_lower_bound_proof
    (r : ℕ) (hr : 1 ≤ r) (epsilon : ℝ)
    (hcertificate : objective + MvPolynomial.C epsilon ∈
      GenQuadraticModule generators (2 * r)) :
    (1 : ℝ) / (2 ^ 14 * (r : ℝ) ^ 2) < epsilon := by
  obtain ⟨certificate⟩ := extractedCertificate_of_mem hcertificate
  exact extractedCertificate_lower_bound certificate hr

end OptimalConvergenceRates.MFCQQuadraticLowerBound

end
