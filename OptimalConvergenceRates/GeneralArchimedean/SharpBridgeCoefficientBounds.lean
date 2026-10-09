/-
  Log-square coefficient estimates for the denominator certificate and the
  composed sharp Archimedean bridge.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpComponentCoefficientBounds
import OptimalConvergenceRates.GeneralArchimedean.SharpBoundedBridge

noncomputable section

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

namespace RationalSquareRoot.Package

/-- The denominator positivity polynomial has degree at most the package
degree bound. -/
theorem denominatorPolynomial_degree_le
    {δ B theta : ℝ} (pkg : Package δ B theta) :
    (pkg.V ^ 2 - 1).natDegree ≤ pkg.degreeBound := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le pkg.V_sq_degree_le
  simp

/-- A coarse embedded coefficient norm bound for the denominator positivity
polynomial. -/
theorem denominatorPolynomial_embedded_norm_le
    {δ B theta : ℝ} (pkg : Package δ B theta) :
    embeddedPolynomialCoeffL1Norm (pkg.V ^ 2 - 1) ≤
      2 * pkg.coefficientBound ^ 2 := by
  let Z := pkg.coefficientBound
  have hZ : 1 ≤ Z := pkg.one_le_coefficientBound
  have hV : embeddedPolynomialCoeffL1Norm pkg.V ≤ Z :=
    pkg.V_coeffL1Norm_le_coefficientBound
  have hV2 : embeddedPolynomialCoeffL1Norm (pkg.V ^ 2) ≤ Z ^ 2 :=
    (embeddedPolynomialCoeffL1Norm_pow_le pkg.V 2).trans
      (pow_le_pow_left₀ (embeddedPolynomialCoeffL1Norm_nonneg pkg.V) hV 2)
  have hone : embeddedPolynomialCoeffL1Norm (1 : Polynomial ℝ) ≤ 1 := by
    simpa using embeddedPolynomialCoeffL1Norm_C_le (1 : ℝ)
  calc
    embeddedPolynomialCoeffL1Norm (pkg.V ^ 2 - 1) ≤
        embeddedPolynomialCoeffL1Norm (pkg.V ^ 2) +
          embeddedPolynomialCoeffL1Norm (1 : Polynomial ℝ) :=
      embeddedPolynomialCoeffL1Norm_sub_le _ _
    _ ≤ Z ^ 2 + 1 := add_le_add hV2 hone
    _ ≤ 2 * Z ^ 2 := by nlinarith

end RationalSquareRoot.Package

/-- Exponent constant for the positive-coefficient denominator-factor
certificate. -/
def sharpDenominatorFactorLogSquareConstant
    (s : ℕ) (B Bprime G Ha : ℝ) : ℝ :=
  let D := sharpPackageDegreeLogConstant s B Bprime
  let K := sharpPackageLogSquareConstant s B Bprime
  let Kpoly := D + 1 + Real.log 3 + 2 * K
  (D + 1) +
    (((Real.log 3 + Kpoly) + D * Real.log (G + 1)) +
      Real.log (Ha + 2))

theorem sharpDenominatorFactorLogSquareConstant_nonneg
    (s : ℕ) (B Bprime : ℝ) {G Ha : ℝ}
    (hG : 1 ≤ G) (hHa : 0 ≤ Ha) :
    0 ≤ sharpDenominatorFactorLogSquareConstant s B Bprime G Ha := by
  have hD := sharpPackageDegreeLogConstant_nonneg s B Bprime
  have hK := sharpPackageLogSquareConstant_nonneg s B Bprime
  have hlog3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hlogG : 0 ≤ Real.log (G + 1) :=
    Real.log_nonneg (by linarith)
  have hlogHa : 0 ≤ Real.log (Ha + 2) :=
    Real.log_nonneg (by linarith)
  unfold sharpDenominatorFactorLogSquareConstant
  positivity

theorem RationalSquareRoot.Package.denominatorFactorCertificateBound_le_sharp_log
    {s : ℕ} {H B Bprime G Ha : ℝ}
    (hH : 0 ≤ H) (hB : 0 ≤ B) (hBprime : 0 ≤ Bprime)
    (hG : 1 ≤ G) (hHa : 0 ≤ Ha)
    (pkg : Package (sharpDeltaScale s H Bprime) B (sharpThetaScale s))
    (hell : (pkg.ell : ℝ) ≤
      Real.log (sharpThetaScale s / 4) / Real.log (1 / 9) + 1)
    (hJ : (pkg.J : ℝ) ≤
      Real.log
          (Real.sqrt (B + sharpDeltaScale s H Bprime) /
            Real.sqrt (sharpDeltaScale s H Bprime)) /
        Real.log 2) :
    pkg.denominatorFactorCertificateBound G Ha ≤
      logSquareEnvelope
        (sharpDenominatorFactorLogSquareConstant s B Bprime G Ha)
        (H + 1) := by
  let D := sharpPackageDegreeLogConstant s B Bprime
  let K := sharpPackageLogSquareConstant s B Bprime
  let Kpoly := D + 1 + Real.log 3 + 2 * K
  let x : ℝ := H + 1
  let P : Polynomial ℝ := pkg.V ^ 2 - 1
  have hx : 1 ≤ x := by dsimp [x]; linarith
  have hD : 0 ≤ D := sharpPackageDegreeLogConstant_nonneg s B Bprime
  have hK : 0 ≤ K := sharpPackageLogSquareConstant_nonneg s B Bprime
  have hdegreeBound := pkg.degreeBound_cast_le_sharp_log
    hH hB hBprime hell hJ
  have hdegree : (P.natDegree : ℝ) ≤ D * (1 + Real.log x) := by
    have hcast : (P.natDegree : ℝ) ≤ pkg.degreeBound := by
      exact_mod_cast pkg.denominatorPolynomial_degree_le
    exact hcast.trans (by simpa [D, x] using hdegreeBound)
  have hcount : ((P.natDegree + 1 : ℕ) : ℝ) ≤
      (D + 1) * (1 + Real.log x) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
    nlinarith
  have hcountEnv : ((P.natDegree + 1 : ℕ) : ℝ) ≤
      logSquareEnvelope (D + 1) x :=
    linear_log_le_logSquareEnvelope (by positivity) (by linarith) hx hcount
  have hcoeff := pkg.coefficientBound_le_sharp_log
    hH hB hBprime hell hJ
  have hcoeffSq : pkg.coefficientBound ^ 2 ≤
      logSquareEnvelope (2 * K) x := by
    calc
      pkg.coefficientBound ^ 2 ≤ logSquareEnvelope K x ^ 2 :=
        pow_le_pow_left₀ (by linarith [pkg.one_le_coefficientBound])
          (by simpa [K, x] using hcoeff) 2
      _ = logSquareEnvelope (2 * K) x := by
        rw [logSquareEnvelope_pow]
        norm_num
  have htwo : (2 : ℝ) ≤ logSquareEnvelope (Real.log 3) x := by
    have heq : Real.log ((2 : ℝ) + 1) = Real.log 3 := by norm_num
    rw [← heq]
    exact le_logSquareEnvelope_log_add_one (by norm_num) hx
  have hembed : embeddedPolynomialCoeffL1Norm P ≤
      logSquareEnvelope (Real.log 3 + 2 * K) x := by
    calc
      embeddedPolynomialCoeffL1Norm P ≤ 2 * pkg.coefficientBound ^ 2 := by
        simpa [P] using pkg.denominatorPolynomial_embedded_norm_le
      _ ≤ logSquareEnvelope (Real.log 3) x *
          logSquareEnvelope (2 * K) x :=
        mul_le_mul htwo hcoeffSq (sq_nonneg _)
          (logSquareEnvelope_pos _ _).le
      _ = logSquareEnvelope (Real.log 3 + 2 * K) x :=
        logSquareEnvelope_mul _ _ _
  have hpoly : polynomialCoeffL1Norm P ≤
      logSquareEnvelope Kpoly x := by
    calc
      polynomialCoeffL1Norm P ≤
          (P.natDegree + 1 : ℕ) * embeddedPolynomialCoeffL1Norm P :=
        polynomialCoeffL1Norm_le_natDegree_succ_mul_embedded P
      _ ≤ logSquareEnvelope (D + 1) x *
          logSquareEnvelope (Real.log 3 + 2 * K) x :=
        mul_le_mul hcountEnv hembed
          (embeddedPolynomialCoeffL1Norm_nonneg P)
          (logSquareEnvelope_pos _ _).le
      _ = logSquareEnvelope Kpoly x := by
        rw [logSquareEnvelope_mul]
        dsimp [Kpoly]
        congr 1
        ring
  have hKpoly : 0 ≤ Kpoly := by
    dsimp [Kpoly]
    positivity
  have hpolyPlus : polynomialCoeffL1Norm P + 1 ≤
      logSquareEnvelope (Real.log 3 + Kpoly) x := by
    have hEone : 1 ≤ logSquareEnvelope Kpoly x :=
      one_le_logSquareEnvelope hKpoly hx
    have hsum : polynomialCoeffL1Norm P + 1 ≤
        2 * logSquareEnvelope Kpoly x := by linarith
    calc
      polynomialCoeffL1Norm P + 1 ≤
          2 * logSquareEnvelope Kpoly x := hsum
      _ ≤ logSquareEnvelope (Real.log 3) x *
          logSquareEnvelope Kpoly x :=
        mul_le_mul_of_nonneg_right htwo (logSquareEnvelope_pos _ _).le
      _ = logSquareEnvelope (Real.log 3 + Kpoly) x :=
        logSquareEnvelope_mul _ _ _
  have hpower : (G + 1) ^ P.natDegree ≤
      logSquareEnvelope (D * Real.log (G + 1)) x :=
    fixed_pow_le_logSquareEnvelope (by linarith) hD hx hdegree
  have hHaEnv : Ha + 1 ≤ logSquareEnvelope (Real.log (Ha + 2)) x := by
    convert le_logSquareEnvelope_log_add_one
      (c := Ha + 1) (x := x) (by linarith) hx using 1; ring
  have hpolyPlus0 : 0 ≤ polynomialCoeffL1Norm P + 1 := by
    linarith [polynomialCoeffL1Norm_nonneg P]
  have hpower0 : 0 ≤ (G + 1) ^ P.natDegree :=
    pow_nonneg (by linarith) P.natDegree
  have hHa0 : 0 ≤ Ha + 1 := by linarith
  have hmiddle := mul_le_logSquareEnvelope
    hpolyPlus0 hpower0 hpolyPlus hpower
  have hterm := mul_le_logSquareEnvelope
    (mul_nonneg hpolyPlus0 hpower0) hHa0 hmiddle hHaEnv
  have hfull := mul_le_logSquareEnvelope
    (Nat.cast_nonneg' (P.natDegree + 1))
    (mul_nonneg
      (mul_nonneg hpolyPlus0 hpower0) hHa0)
    hcountEnv hterm
  unfold denominatorFactorCertificateBound
  unfold positiveSubstitutionCertificateBound positiveSubstitutionTermBound
  simpa [P, D, K, Kpoly, x, sharpDenominatorFactorLogSquareConstant]
    using hfull

/-- Exponent constant for the telescoped product of denominator-square
certificates. -/
def sharpDenominatorProductLogSquareConstant
    (s : ℕ) (B Bprime G Ha : ℝ) : ℝ :=
  Real.log ((3 : ℝ) ^ s + 1) +
    (s : ℝ) * sharpConversionFactorLogSquareConstant s B Bprime G +
    sharpDenominatorFactorLogSquareConstant s B Bprime G Ha

theorem sharpDenominatorProductLogSquareConstant_nonneg
    (s : ℕ) (B Bprime : ℝ) {G Ha : ℝ}
    (hG : 1 ≤ G) (hHa : 0 ≤ Ha) :
    0 ≤ sharpDenominatorProductLogSquareConstant s B Bprime G Ha := by
  have hpow : 1 ≤ (3 : ℝ) ^ s + 1 := by
    linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) s]
  unfold sharpDenominatorProductLogSquareConstant
  exact add_nonneg
    (add_nonneg (Real.log_nonneg hpow)
      (mul_nonneg (by positivity)
        (sharpConversionFactorLogSquareConstant_nonneg s B Bprime hG)))
    (sharpDenominatorFactorLogSquareConstant_nonneg s B Bprime hG hHa)

theorem boundedDenominatorProductBudget_le_sharp_log
    {s : ℕ} {H B Bprime G Ha : ℝ}
    (hH : 0 ≤ H) (hB : 0 ≤ B) (hBprime : 0 ≤ Bprime)
    (hG : 1 ≤ G) (hHa : 0 ≤ Ha)
    (pkg : Package (sharpDeltaScale s H Bprime) B (sharpThetaScale s))
    (hell : (pkg.ell : ℝ) ≤
      Real.log (sharpThetaScale s / 4) / Real.log (1 / 9) + 1)
    (hJ : (pkg.J : ℝ) ≤
      Real.log
          (Real.sqrt (B + sharpDeltaScale s H Bprime) /
            Real.sqrt (sharpDeltaScale s H Bprime)) /
        Real.log 2) :
    boundedDenominatorProductBudget pkg s Bprime G Ha ≤
      logSquareEnvelope
        (sharpDenominatorProductLogSquareConstant s B Bprime G Ha)
        (H + 1) := by
  let Kf := sharpConversionFactorLogSquareConstant s B Bprime G
  let Kd := sharpDenominatorFactorLogSquareConstant s B Bprime G Ha
  let x : ℝ := H + 1
  let E := logSquareEnvelope Kf x
  have hx : 1 ≤ x := by dsimp [x]; linarith
  have hKf : 0 ≤ Kf := sharpConversionFactorLogSquareConstant_nonneg
    s B Bprime hG
  have hfactor := conversionFactorCoefficientBound_le_sharp_log
    hH hB hBprime hG pkg hell hJ
  have hdenominator := pkg.denominatorFactorCertificateBound_le_sharp_log
    hH hB hBprime hG hHa hell hJ
  have hEone : 1 ≤ E := one_le_logSquareEnvelope hKf hx
  have hbase : conversionFactorCoefficientBound pkg Bprime G + 1 + 1 ≤
      3 * E := by
    dsimp [E, Kf, x]
    nlinarith
  have hbase0 : 0 ≤ conversionFactorCoefficientBound pkg Bprime G + 1 + 1 := by
    linarith [conversionFactorCoefficientBound_nonneg pkg Bprime G]
  have hpow :
      (conversionFactorCoefficientBound pkg Bprime G + 1 + 1) ^ s ≤
        (3 * E) ^ s :=
    pow_le_pow_left₀ hbase0 hbase s
  have hfixed : (3 : ℝ) ^ s ≤
      logSquareEnvelope (Real.log ((3 : ℝ) ^ s + 1)) x :=
    le_logSquareEnvelope_log_add_one (pow_nonneg (by norm_num) s) hx
  have hEpow : E ^ s ≤ logSquareEnvelope ((s : ℝ) * Kf) x := by
    rw [logSquareEnvelope_pow]
  have hproductPower :
      (conversionFactorCoefficientBound pkg Bprime G + 1 + 1) ^ s ≤
        logSquareEnvelope
          (Real.log ((3 : ℝ) ^ s + 1) + (s : ℝ) * Kf) x := by
    calc
      (conversionFactorCoefficientBound pkg Bprime G + 1 + 1) ^ s ≤
          (3 * E) ^ s := hpow
      _ = (3 : ℝ) ^ s * E ^ s := by rw [mul_pow]
      _ ≤ logSquareEnvelope (Real.log ((3 : ℝ) ^ s + 1)) x *
          logSquareEnvelope ((s : ℝ) * Kf) x :=
        mul_le_mul hfixed hEpow (pow_nonneg (logSquareEnvelope_pos _ _).le s)
          (logSquareEnvelope_pos _ _).le
      _ = logSquareEnvelope
          (Real.log ((3 : ℝ) ^ s + 1) + (s : ℝ) * Kf) x :=
        logSquareEnvelope_mul _ _ _
  unfold boundedDenominatorProductBudget
  calc
    (conversionFactorCoefficientBound pkg Bprime G + 1 + 1) ^ s *
        pkg.denominatorFactorCertificateBound G Ha ≤
      logSquareEnvelope
          (Real.log ((3 : ℝ) ^ s + 1) + (s : ℝ) * Kf) x *
        logSquareEnvelope Kd x := by
      exact mul_le_mul hproductPower (by simpa [Kd, x] using hdenominator)
        (pkg.denominatorFactorCertificateBound_nonneg hG hHa)
        (logSquareEnvelope_pos _ _).le
    _ = logSquareEnvelope
        (sharpDenominatorProductLogSquareConstant s B Bprime G Ha)
        (H + 1) := by
      rw [logSquareEnvelope_mul]
      rfl

end OptimalConvergenceRates.GeneralArchimedean

end
