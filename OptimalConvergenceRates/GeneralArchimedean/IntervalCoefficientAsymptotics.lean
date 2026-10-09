/-
  Log-square coefficient bounds for the quantitative interval certificate.
-/
import OptimalConvergenceRates.GeneralArchimedean.LogSquareBounds
import OptimalConvergenceRates.GeneralArchimedean.QuantitativeIntervalCertificate

noncomputable section

namespace OptimalConvergenceRates.GeneralArchimedean

/-- An explicit exponent constant for the interval-certificate coefficient
bound.  `D` controls the degree on the logarithmic scale and `K` controls
the embedded coefficient norm. -/
def intervalCertificateLogSquareConstant (B D K : ℝ) : ℝ :=
  let M := D + 3
  let Kvalue := (D + 1 + K) + D * Real.log B
  let Kmarkov := (D + 4) + 2 * M ^ 2 + Kvalue
  let Kzero := Kmarkov + M * Real.log 3
  let Kproduct := Real.log 17 + Kmarkov + M * Real.log 6
  let Kfactor := Real.log (((B + 1) ^ 2 + 1) + 1)
  Real.log 3 + Kzero + (Kfactor + Kproduct)

theorem intervalCertificateLogSquareConstant_nonneg
    {B D K : ℝ} (hB : 1 ≤ B) (hD : 0 ≤ D) (hK : 0 ≤ K) :
    0 ≤ intervalCertificateLogSquareConstant B D K := by
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hlog3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog6 : 0 ≤ Real.log (6 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog17 : 0 ≤ Real.log (17 : ℝ) := Real.log_nonneg (by norm_num)
  have hfactor : 1 ≤ ((B + 1) ^ 2 + 1) + 1 := by nlinarith [sq_nonneg (B + 1)]
  have hlogfactor : 0 ≤ Real.log (((B + 1) ^ 2 + 1) + 1) :=
    Real.log_nonneg hfactor
  unfold intervalCertificateLogSquareConstant
  positivity

/-- Quantitative interval certificates preserve the
`exp(O((1+log x)^2))` coefficient class. -/
theorem intervalCertificateCoefficientBound_le_logSquareEnvelope
    {B D K x : ℝ} (hB : 1 ≤ B) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hx : 1 ≤ x) (p : Polynomial ℝ)
    (hdegree : (p.natDegree : ℝ) ≤ D * (1 + Real.log x))
    (hnorm : embeddedPolynomialCoeffL1Norm p ≤
      logSquareEnvelope K x) :
    intervalCertificateCoefficientBound B p ≤
      logSquareEnvelope (intervalCertificateLogSquareConstant B D K) x := by
  let L : ℝ := 1 + Real.log x
  let M : ℕ := intervalCertificateDegree p
  let DM : ℝ := D + 3
  let Kvalue : ℝ := (D + 1 + K) + D * Real.log B
  let Kmarkov : ℝ := (D + 4) + 2 * DM ^ 2 + Kvalue
  let Kzero : ℝ := Kmarkov + DM * Real.log 3
  let Kproduct : ℝ := Real.log 17 + Kmarkov + DM * Real.log 6
  let Kfactor : ℝ := Real.log (((B + 1) ^ 2 + 1) + 1)
  have hL : 1 ≤ L := by
    dsimp [L]
    linarith [Real.log_nonneg hx]
  have hM : (M : ℝ) ≤ DM * L := by
    dsimp [M, intervalCertificateDegree, DM, L]
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    nlinarith
  have hMpos : 1 ≤ M := by
    dsimp [M, intervalCertificateDegree]
    omega
  have hMone : ((M + 1 : ℕ) : ℝ) ≤ (D + 4) * L := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    dsimp [DM] at hM
    nlinarith
  have hcount : ((p.natDegree + 1 : ℕ) : ℝ) ≤ (D + 1) * L := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    dsimp [L] at hdegree ⊢
    nlinarith
  have hcountEnv : ((p.natDegree + 1 : ℕ) : ℝ) ≤
      logSquareEnvelope (D + 1) x :=
    linear_log_le_logSquareEnvelope (by positivity) (by linarith) hx
      (by simpa [L] using hcount)
  have hpolyNorm : polynomialCoeffL1Norm p ≤
      logSquareEnvelope (D + 1 + K) x := by
    calc
      polynomialCoeffL1Norm p ≤
          (p.natDegree + 1 : ℕ) * embeddedPolynomialCoeffL1Norm p :=
        polynomialCoeffL1Norm_le_natDegree_succ_mul_embedded p
      _ ≤ logSquareEnvelope (D + 1) x * logSquareEnvelope K x := by
        exact mul_le_mul hcountEnv hnorm
          (embeddedPolynomialCoeffL1Norm_nonneg p)
          (logSquareEnvelope_pos (D + 1) x).le
      _ = logSquareEnvelope (D + 1 + K) x :=
        logSquareEnvelope_mul _ _ _
  have hBpow : B ^ p.natDegree ≤
      logSquareEnvelope (D * Real.log B) x :=
    fixed_pow_le_logSquareEnvelope hB hD hx hdegree
  have hvalue : intervalValueBound B p ≤
      logSquareEnvelope Kvalue x := by
    unfold intervalValueBound
    simpa [Kvalue, add_assoc] using
      mul_le_logSquareEnvelope
        (polynomialCoeffL1Norm_nonneg p) (pow_nonneg (by linarith) _)
        hpolyNorm hBpow
  have hMoneEnv : ((M + 1 : ℕ) : ℝ) ≤
      logSquareEnvelope (D + 4) x :=
    linear_log_le_logSquareEnvelope (by positivity) (by linarith) hx
      (by simpa [L] using hMone)
  have hMself : (M : ℝ) ^ (2 * M) ≤
      logSquareEnvelope (2 * DM ^ 2) x :=
    nat_self_pow_le_logSquareEnvelope (by dsimp [DM]; linarith) hx hMpos
      (by simpa [DM, L] using hM)
  have hmarkov : intervalMarkovCoefficientBound B p ≤
      logSquareEnvelope Kmarkov x := by
    unfold intervalMarkovCoefficientBound
    change ((M + 1 : ℕ) : ℝ) * (M : ℝ) ^ (2 * M) *
        intervalValueBound B p ≤ logSquareEnvelope Kmarkov x
    have hfirst := mul_le_logSquareEnvelope
      (Nat.cast_nonneg (M + 1)) (pow_nonneg (by positivity) _)
      hMoneEnv hMself
    have hfirst0 : 0 ≤ ((M + 1 : ℕ) : ℝ) * (M : ℝ) ^ (2 * M) :=
      mul_nonneg (by positivity) (pow_nonneg (by positivity) _)
    simpa [Kmarkov, Kvalue, DM, add_assoc] using
      mul_le_logSquareEnvelope hfirst0
        (intervalValueBound_nonneg hB p) hfirst hvalue
  have hthree : (3 : ℝ) ^ M ≤
      logSquareEnvelope (DM * Real.log 3) x :=
    fixed_pow_le_logSquareEnvelope (by norm_num) (by dsimp [DM]; linarith)
      hx (by simpa [DM, L] using hM)
  have hsix : (6 : ℝ) ^ M ≤
      logSquareEnvelope (DM * Real.log 6) x :=
    fixed_pow_le_logSquareEnvelope (by norm_num) (by dsimp [DM]; linarith)
      hx (by simpa [DM, L] using hM)
  have hzero : intervalSigmaZeroCoefficientBound B p ≤
      logSquareEnvelope Kzero x := by
    unfold intervalSigmaZeroCoefficientBound
    simpa [Kzero, add_assoc] using
      mul_le_logSquareEnvelope
        (intervalMarkovCoefficientBound_nonneg hB p)
        (pow_nonneg (by norm_num) M) hmarkov hthree
  have hsixteen : (16 : ℝ) ≤ logSquareEnvelope (Real.log 17) x := by
    have heq : Real.log ((16 : ℝ) + 1) = Real.log 17 := by norm_num
    rw [← heq]
    exact le_logSquareEnvelope_log_add_one (by norm_num) hx
  have hproduct : intervalSigmaProductCoefficientBound B p ≤
      logSquareEnvelope Kproduct x := by
    unfold intervalSigmaProductCoefficientBound
    have h16markov := mul_le_logSquareEnvelope (by norm_num)
      (intervalMarkovCoefficientBound_nonneg hB p) hsixteen hmarkov
    have h16markov0 : 0 ≤ 16 * intervalMarkovCoefficientBound B p :=
      mul_nonneg (by norm_num) (intervalMarkovCoefficientBound_nonneg hB p)
    simpa [Kproduct, add_assoc] using
      mul_le_logSquareEnvelope h16markov0 (pow_nonneg (by norm_num) M)
        h16markov hsix
  have hfactor : 0 ≤ (B + 1) ^ 2 + 1 := by positivity
  have hfactorEnv : (B + 1) ^ 2 + 1 ≤ logSquareEnvelope Kfactor x := by
    dsimp [Kfactor]
    exact le_logSquareEnvelope_log_add_one hfactor hx
  have hfactorProduct :
      ((B + 1) ^ 2 + 1) * intervalSigmaProductCoefficientBound B p ≤
        logSquareEnvelope (Kfactor + Kproduct) x :=
    mul_le_logSquareEnvelope hfactor
      (intervalSigmaProductCoefficientBound_nonneg hB p)
      hfactorEnv hproduct
  unfold intervalCertificateCoefficientBound
  simpa [intervalCertificateLogSquareConstant, Kzero, Kproduct,
    Kfactor, Kmarkov, Kvalue, DM, add_assoc] using
    add_le_logSquareEnvelope
      (intervalSigmaZeroCoefficientBound_nonneg hB p)
      (mul_nonneg hfactor
        (intervalSigmaProductCoefficientBound_nonneg hB p))
      (by
        dsimp [Kzero, Kmarkov, Kvalue, DM]
        have hlogB := Real.log_nonneg hB
        positivity)
      (by
        dsimp [Kfactor, Kproduct, Kmarkov, Kvalue, DM]
        have hlogB := Real.log_nonneg hB
        have hfactorOne : 1 ≤ ((B + 1) ^ 2 + 1) + 1 := by
          nlinarith [sq_nonneg (B + 1)]
        have hlogfactor := Real.log_nonneg hfactorOne
        positivity)
      hx hzero hfactorProduct

end OptimalConvergenceRates.GeneralArchimedean

end
