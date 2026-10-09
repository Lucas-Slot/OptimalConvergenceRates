/-
  Log-square coefficient bounds for the component polynomials and interval
  comparisons used by the sharp conversion.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpCoefficientBounds
import OptimalConvergenceRates.GeneralArchimedean.IntervalCoefficientAsymptotics
import OptimalConvergenceRates.GeneralArchimedean.BoundedConversion

noncomputable section

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

/-- A nonnegative package-degree constant, convenient for generic envelope
lemmas. -/
def sharpPackageDegreeLogConstant (s : ℕ) (B Bprime : ℝ) : ℝ :=
  max 0 (sharpPackageDegreeConstant s B Bprime)

/-- A nonnegative package-coefficient exponent constant. -/
def sharpPackageLogSquareConstant (s : ℕ) (B Bprime : ℝ) : ℝ :=
  max 0 (Real.log 6 + 2 *
    sharpPackageCoefficientExponentConstant s B Bprime)

theorem sharpPackageDegreeLogConstant_nonneg (s : ℕ) (B Bprime : ℝ) :
    0 ≤ sharpPackageDegreeLogConstant s B Bprime :=
  le_max_left _ _

theorem sharpPackageLogSquareConstant_nonneg (s : ℕ) (B Bprime : ℝ) :
    0 ≤ sharpPackageLogSquareConstant s B Bprime :=
  le_max_left _ _

theorem RationalSquareRoot.Package.degreeBound_cast_le_sharp_log
    {s : ℕ} {H B Bprime : ℝ}
    (hH : 0 ≤ H) (hB : 0 ≤ B) (hBprime : 0 ≤ Bprime)
    (pkg : Package (sharpDeltaScale s H Bprime) B (sharpThetaScale s))
    (hell : (pkg.ell : ℝ) ≤
      Real.log (sharpThetaScale s / 4) / Real.log (1 / 9) + 1)
    (hJ : (pkg.J : ℝ) ≤
      Real.log
          (Real.sqrt (B + sharpDeltaScale s H Bprime) /
            Real.sqrt (sharpDeltaScale s H Bprime)) /
        Real.log 2) :
    (pkg.degreeBound : ℝ) ≤
      sharpPackageDegreeLogConstant s B Bprime *
        (1 + Real.log (H + 1)) := by
  apply (package_degreeBound_le_of_sharpDeltaScale
    hH hB hBprime pkg hell hJ).trans
  apply mul_le_mul_of_nonneg_right
  · exact le_max_right _ _
  · have hx : 1 ≤ H + 1 := by linarith
    linarith [Real.log_nonneg hx]

theorem RationalSquareRoot.Package.coefficientBound_le_sharp_log
    {s : ℕ} {H B Bprime : ℝ}
    (hH : 0 ≤ H) (hB : 0 ≤ B) (hBprime : 0 ≤ Bprime)
    (pkg : Package (sharpDeltaScale s H Bprime) B (sharpThetaScale s))
    (hell : (pkg.ell : ℝ) ≤
      Real.log (sharpThetaScale s / 4) / Real.log (1 / 9) + 1)
    (hJ : (pkg.J : ℝ) ≤
      Real.log
          (Real.sqrt (B + sharpDeltaScale s H Bprime) /
            Real.sqrt (sharpDeltaScale s H Bprime)) /
        Real.log 2) :
    pkg.coefficientBound ≤
      logSquareEnvelope (sharpPackageLogSquareConstant s B Bprime) (H + 1) := by
  apply (pkg.coefficientBound_le_logSquareEnvelope
    hH hB hBprime hell hJ).trans
  apply logSquareEnvelope_mono
  · exact le_max_right _ _
  · linarith

namespace RationalSquareRoot.Package

theorem errorGap_embedded_norm_le
    {δ B theta : ℝ} (pkg : Package δ B theta) :
    embeddedPolynomialCoeffL1Norm pkg.errorGap ≤
      (|theta| + |δ| + 1) * pkg.coefficientBound ^ 2 := by
  let Z := pkg.coefficientBound
  have hZ : 1 ≤ Z := pkg.one_le_coefficientBound
  have hP := pkg.P_coeffL1Norm_le_coefficientBound
  have hV := pkg.V_coeffL1Norm_le_coefficientBound
  have hE := pkg.E_coeffL1Norm_le_coefficientBound
  have hP2 : embeddedPolynomialCoeffL1Norm (pkg.P ^ 2) ≤ Z ^ 2 :=
    (embeddedPolynomialCoeffL1Norm_pow_le pkg.P 2).trans
      (pow_le_pow_left₀ (embeddedPolynomialCoeffL1Norm_nonneg pkg.P) hP 2)
  have hV2 : embeddedPolynomialCoeffL1Norm (pkg.V ^ 2) ≤ Z ^ 2 :=
    (embeddedPolynomialCoeffL1Norm_pow_le pkg.V 2).trans
      (pow_le_pow_left₀ (embeddedPolynomialCoeffL1Norm_nonneg pkg.V) hV 2)
  have htheta : embeddedPolynomialCoeffL1Norm
      (Polynomial.C theta * pkg.P ^ 2) ≤ |theta| * Z ^ 2 := by
    exact (embeddedPolynomialCoeffL1Norm_mul_le _ _).trans
      (mul_le_mul (embeddedPolynomialCoeffL1Norm_C_le theta) hP2
        (embeddedPolynomialCoeffL1Norm_nonneg _) (abs_nonneg theta))
  have hdelta : embeddedPolynomialCoeffL1Norm
      (Polynomial.C δ * pkg.V ^ 2) ≤ |δ| * Z ^ 2 := by
    exact (embeddedPolynomialCoeffL1Norm_mul_le _ _).trans
      (mul_le_mul (embeddedPolynomialCoeffL1Norm_C_le δ) hV2
        (embeddedPolynomialCoeffL1Norm_nonneg _) (abs_nonneg δ))
  have hZsq : Z ≤ Z ^ 2 := by nlinarith
  unfold errorGap
  calc
    embeddedPolynomialCoeffL1Norm
        (Polynomial.C theta * pkg.P ^ 2 +
          Polynomial.C δ * pkg.V ^ 2 - pkg.E) ≤
        embeddedPolynomialCoeffL1Norm
            (Polynomial.C theta * pkg.P ^ 2 +
              Polynomial.C δ * pkg.V ^ 2) +
          embeddedPolynomialCoeffL1Norm pkg.E :=
      embeddedPolynomialCoeffL1Norm_sub_le _ _
    _ ≤ (embeddedPolynomialCoeffL1Norm
            (Polynomial.C theta * pkg.P ^ 2) +
          embeddedPolynomialCoeffL1Norm
            (Polynomial.C δ * pkg.V ^ 2)) +
          embeddedPolynomialCoeffL1Norm pkg.E := by
      gcongr
      exact embeddedPolynomialCoeffL1Norm_add_le _ _
    _ ≤ (|theta| + |δ| + 1) * Z ^ 2 := by
      nlinarith

theorem numeratorGap_embedded_norm_le
    {δ B theta : ℝ} (pkg : Package δ B theta) (Bprime : ℝ) :
    embeddedPolynomialCoeffL1Norm (pkg.numeratorGap Bprime) ≤
      (|Bprime| + 1) * pkg.coefficientBound ^ 2 := by
  let Z := pkg.coefficientBound
  have hP := pkg.P_coeffL1Norm_le_coefficientBound
  have hV := pkg.V_coeffL1Norm_le_coefficientBound
  have hP2 : embeddedPolynomialCoeffL1Norm (pkg.P ^ 2) ≤ Z ^ 2 :=
    (embeddedPolynomialCoeffL1Norm_pow_le pkg.P 2).trans
      (pow_le_pow_left₀ (embeddedPolynomialCoeffL1Norm_nonneg pkg.P) hP 2)
  have hV2 : embeddedPolynomialCoeffL1Norm (pkg.V ^ 2) ≤ Z ^ 2 :=
    (embeddedPolynomialCoeffL1Norm_pow_le pkg.V 2).trans
      (pow_le_pow_left₀ (embeddedPolynomialCoeffL1Norm_nonneg pkg.V) hV 2)
  have hB : embeddedPolynomialCoeffL1Norm
      (Polynomial.C Bprime * pkg.V ^ 2) ≤ |Bprime| * Z ^ 2 := by
    exact (embeddedPolynomialCoeffL1Norm_mul_le _ _).trans
      (mul_le_mul (embeddedPolynomialCoeffL1Norm_C_le Bprime) hV2
        (embeddedPolynomialCoeffL1Norm_nonneg _) (abs_nonneg Bprime))
  unfold numeratorGap
  exact (embeddedPolynomialCoeffL1Norm_sub_le _ _).trans <| by
    nlinarith

end RationalSquareRoot.Package

/-- Exponent constants for the two gap-polynomial norms. -/
def sharpErrorGapLogSquareConstant (s : ℕ) (B Bprime : ℝ) : ℝ :=
  Real.log 4 + 2 * sharpPackageLogSquareConstant s B Bprime

def sharpNumeratorGapLogSquareConstant (s : ℕ) (B Bprime : ℝ) : ℝ :=
  Real.log (|Bprime| + 2) +
    2 * sharpPackageLogSquareConstant s B Bprime

theorem sharpErrorGapLogSquareConstant_nonneg
    (s : ℕ) (B Bprime : ℝ) :
    0 ≤ sharpErrorGapLogSquareConstant s B Bprime := by
  unfold sharpErrorGapLogSquareConstant
  positivity [sharpPackageLogSquareConstant_nonneg s B Bprime]

theorem sharpNumeratorGapLogSquareConstant_nonneg
    (s : ℕ) (B Bprime : ℝ) :
    0 ≤ sharpNumeratorGapLogSquareConstant s B Bprime := by
  have hbase : 1 ≤ |Bprime| + 2 := by linarith [abs_nonneg Bprime]
  unfold sharpNumeratorGapLogSquareConstant
  exact add_nonneg (Real.log_nonneg hbase)
    (mul_nonneg (by norm_num)
      (sharpPackageLogSquareConstant_nonneg s B Bprime))

theorem RationalSquareRoot.Package.errorGap_norm_le_sharp_log
    {s : ℕ} {H B Bprime : ℝ}
    (hH : 0 ≤ H) (hB : 0 ≤ B) (hBprime : 0 ≤ Bprime)
    (pkg : Package (sharpDeltaScale s H Bprime) B (sharpThetaScale s))
    (hell : (pkg.ell : ℝ) ≤
      Real.log (sharpThetaScale s / 4) / Real.log (1 / 9) + 1)
    (hJ : (pkg.J : ℝ) ≤
      Real.log
          (Real.sqrt (B + sharpDeltaScale s H Bprime) /
            Real.sqrt (sharpDeltaScale s H Bprime)) /
        Real.log 2) :
    embeddedPolynomialCoeffL1Norm pkg.errorGap ≤
      logSquareEnvelope (sharpErrorGapLogSquareConstant s B Bprime)
        (H + 1) := by
  let K := sharpPackageLogSquareConstant s B Bprime
  let x : ℝ := H + 1
  have hx : 1 ≤ x := by dsimp [x]; linarith
  have hcoeff := pkg.coefficientBound_le_sharp_log
    hH hB hBprime hell hJ
  have htheta : |sharpThetaScale s| ≤ 1 := by
    rw [abs_of_pos (sharpThetaScale_pos s)]
    exact (sharpThetaScale_le_half s).trans (by norm_num)
  have hdelta : |sharpDeltaScale s H Bprime| ≤ 1 := by
    rw [abs_of_pos (sharpDeltaScale_pos hH hBprime)]
    exact (sharpDeltaScale_le_half hH hBprime).trans (by norm_num)
  have hraw := pkg.errorGap_embedded_norm_le
  have hfactor : |sharpThetaScale s| +
      |sharpDeltaScale s H Bprime| + 1 ≤ (3 : ℝ) := by linarith
  have hsq : pkg.coefficientBound ^ 2 ≤
      logSquareEnvelope (2 * K) x := by
    calc
      pkg.coefficientBound ^ 2 ≤ logSquareEnvelope K x ^ 2 :=
        pow_le_pow_left₀ (by linarith [pkg.one_le_coefficientBound])
          (by simpa [x, K] using hcoeff) 2
      _ = logSquareEnvelope (2 * K) x := by
        rw [logSquareEnvelope_pow]
        norm_num
  have hthree : (3 : ℝ) ≤ logSquareEnvelope (Real.log 4) x := by
    have heq : Real.log ((3 : ℝ) + 1) = Real.log 4 := by norm_num
    rw [← heq]
    exact le_logSquareEnvelope_log_add_one (by norm_num) hx
  calc
    embeddedPolynomialCoeffL1Norm pkg.errorGap ≤
        (|sharpThetaScale s| + |sharpDeltaScale s H Bprime| + 1) *
          pkg.coefficientBound ^ 2 := hraw
    _ ≤ 3 * pkg.coefficientBound ^ 2 :=
      mul_le_mul_of_nonneg_right hfactor (sq_nonneg _)
    _ ≤ logSquareEnvelope (Real.log 4) x *
        logSquareEnvelope (2 * K) x :=
      mul_le_mul hthree hsq (sq_nonneg _)
        (logSquareEnvelope_pos (Real.log 4) x).le
    _ = logSquareEnvelope (sharpErrorGapLogSquareConstant s B Bprime) x := by
      rw [logSquareEnvelope_mul]
      rfl

theorem RationalSquareRoot.Package.numeratorGap_norm_le_sharp_log
    {s : ℕ} {H B Bprime : ℝ}
    (hH : 0 ≤ H) (hB : 0 ≤ B) (hBprime : 0 ≤ Bprime)
    (pkg : Package (sharpDeltaScale s H Bprime) B (sharpThetaScale s))
    (hell : (pkg.ell : ℝ) ≤
      Real.log (sharpThetaScale s / 4) / Real.log (1 / 9) + 1)
    (hJ : (pkg.J : ℝ) ≤
      Real.log
          (Real.sqrt (B + sharpDeltaScale s H Bprime) /
            Real.sqrt (sharpDeltaScale s H Bprime)) /
        Real.log 2) :
    embeddedPolynomialCoeffL1Norm (pkg.numeratorGap Bprime) ≤
      logSquareEnvelope (sharpNumeratorGapLogSquareConstant s B Bprime)
        (H + 1) := by
  let K := sharpPackageLogSquareConstant s B Bprime
  let x : ℝ := H + 1
  have hx : 1 ≤ x := by dsimp [x]; linarith
  have hcoeff := pkg.coefficientBound_le_sharp_log
    hH hB hBprime hell hJ
  have hsq : pkg.coefficientBound ^ 2 ≤
      logSquareEnvelope (2 * K) x := by
    calc
      pkg.coefficientBound ^ 2 ≤ logSquareEnvelope K x ^ 2 :=
        pow_le_pow_left₀ (by linarith [pkg.one_le_coefficientBound])
          (by simpa [x, K] using hcoeff) 2
      _ = logSquareEnvelope (2 * K) x := by
        rw [logSquareEnvelope_pow]
        norm_num
  have hfactor : |Bprime| + 1 ≤
      logSquareEnvelope (Real.log (|Bprime| + 2)) x := by
    convert le_logSquareEnvelope_log_add_one
      (c := |Bprime| + 1) (x := x) (by positivity) hx using 1; ring
  calc
    embeddedPolynomialCoeffL1Norm (pkg.numeratorGap Bprime) ≤
        (|Bprime| + 1) * pkg.coefficientBound ^ 2 :=
      pkg.numeratorGap_embedded_norm_le Bprime
    _ ≤ logSquareEnvelope (Real.log (|Bprime| + 2)) x *
        logSquareEnvelope (2 * K) x :=
      mul_le_mul hfactor hsq (sq_nonneg _)
        (logSquareEnvelope_pos _ _).le
    _ = logSquareEnvelope
        (sharpNumeratorGapLogSquareConstant s B Bprime) x := by
      rw [logSquareEnvelope_mul]
      rfl

/-- Exponent constants for the substituted interval comparisons. -/
def sharpErrorComparisonLogSquareConstant
    (s : ℕ) (B Bprime G : ℝ) : ℝ :=
  intervalCertificateLogSquareConstant B
      (sharpPackageDegreeLogConstant s B Bprime)
      (sharpErrorGapLogSquareConstant s B Bprime) +
    (sharpPackageDegreeLogConstant s B Bprime + 3) * Real.log G

def sharpNumeratorComparisonLogSquareConstant
    (s : ℕ) (B Bprime G : ℝ) : ℝ :=
  intervalCertificateLogSquareConstant B
      (sharpPackageDegreeLogConstant s B Bprime)
      (sharpNumeratorGapLogSquareConstant s B Bprime) +
    (sharpPackageDegreeLogConstant s B Bprime + 3) * Real.log G

theorem sharpErrorComparisonLogSquareConstant_nonneg
    (s : ℕ) {B Bprime G : ℝ} (hB : 1 ≤ B) (hG : 1 ≤ G) :
    0 ≤ sharpErrorComparisonLogSquareConstant s B Bprime G := by
  unfold sharpErrorComparisonLogSquareConstant
  exact add_nonneg
    (intervalCertificateLogSquareConstant_nonneg hB
      (sharpPackageDegreeLogConstant_nonneg s B Bprime)
      (sharpErrorGapLogSquareConstant_nonneg s B Bprime))
    (mul_nonneg
      (by linarith [sharpPackageDegreeLogConstant_nonneg s B Bprime])
      (Real.log_nonneg hG))

theorem sharpNumeratorComparisonLogSquareConstant_nonneg
    (s : ℕ) {B Bprime G : ℝ} (hB : 1 ≤ B) (hG : 1 ≤ G) :
    0 ≤ sharpNumeratorComparisonLogSquareConstant s B Bprime G := by
  unfold sharpNumeratorComparisonLogSquareConstant
  exact add_nonneg
    (intervalCertificateLogSquareConstant_nonneg hB
      (sharpPackageDegreeLogConstant_nonneg s B Bprime)
      (sharpNumeratorGapLogSquareConstant_nonneg s B Bprime))
    (mul_nonneg
      (by linarith [sharpPackageDegreeLogConstant_nonneg s B Bprime])
      (Real.log_nonneg hG))

theorem RationalSquareRoot.Package.errorComparisonCoefficientBound_le_sharp_log
    {s : ℕ} {H B Bprime G : ℝ}
    (hH : 0 ≤ H) (hB : 1 ≤ B) (hBprime : 0 ≤ Bprime)
    (hG : 1 ≤ G)
    (pkg : Package (sharpDeltaScale s H Bprime) B (sharpThetaScale s))
    (hell : (pkg.ell : ℝ) ≤
      Real.log (sharpThetaScale s / 4) / Real.log (1 / 9) + 1)
    (hJ : (pkg.J : ℝ) ≤
      Real.log
          (Real.sqrt (B + sharpDeltaScale s H Bprime) /
            Real.sqrt (sharpDeltaScale s H Bprime)) /
        Real.log 2) :
    pkg.errorComparisonCoefficientBound G ≤
      logSquareEnvelope
        (sharpErrorComparisonLogSquareConstant s B Bprime G) (H + 1) := by
  let D := sharpPackageDegreeLogConstant s B Bprime
  let K := sharpErrorGapLogSquareConstant s B Bprime
  let x : ℝ := H + 1
  have hx : 1 ≤ x := by dsimp [x]; linarith
  have hdegreeBound := pkg.degreeBound_cast_le_sharp_log
    hH (zero_le_one.trans hB) hBprime hell hJ
  have hdegree : (pkg.errorGap.natDegree : ℝ) ≤
      D * (1 + Real.log x) := by
    have hcast : (pkg.errorGap.natDegree : ℝ) ≤ pkg.degreeBound := by
      exact_mod_cast pkg.errorGap_degree_le
    exact hcast.trans (by simpa [D, x] using hdegreeBound)
  have hinterval : intervalCertificateCoefficientBound B pkg.errorGap ≤
      logSquareEnvelope (intervalCertificateLogSquareConstant B D K) x :=
    intervalCertificateCoefficientBound_le_logSquareEnvelope hB
      (sharpPackageDegreeLogConstant_nonneg s B Bprime)
      (sharpErrorGapLogSquareConstant_nonneg s B Bprime) hx pkg.errorGap
      hdegree (by
        simpa [K, x] using
          (pkg.errorGap_norm_le_sharp_log hH (zero_le_one.trans hB)
            hBprime hell hJ))
  have hdegreePlus : ((pkg.errorGap.natDegree + 3 : ℕ) : ℝ) ≤
      (D + 3) * (1 + Real.log x) := by
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
    nlinarith
  have hpower : G ^ (pkg.errorGap.natDegree + 3) ≤
      logSquareEnvelope ((D + 3) * Real.log G) x :=
    fixed_pow_le_logSquareEnvelope hG
      (by dsimp [D]; linarith [sharpPackageDegreeLogConstant_nonneg s B Bprime])
      hx hdegreePlus
  unfold errorComparisonCoefficientBound
  calc
    intervalCertificateCoefficientBound B pkg.errorGap *
        G ^ (pkg.errorGap.natDegree + 3) ≤
      logSquareEnvelope (intervalCertificateLogSquareConstant B D K) x *
        logSquareEnvelope ((D + 3) * Real.log G) x := by
          exact mul_le_mul hinterval hpower (pow_nonneg (by linarith) _)
            (logSquareEnvelope_pos _ _).le
    _ = logSquareEnvelope
        (sharpErrorComparisonLogSquareConstant s B Bprime G) (H + 1) := by
      rw [logSquareEnvelope_mul]
      rfl

theorem RationalSquareRoot.Package.numeratorComparisonCoefficientBound_le_sharp_log
    {s : ℕ} {H B Bprime G : ℝ}
    (hH : 0 ≤ H) (hB : 1 ≤ B) (hBprime : 0 ≤ Bprime)
    (hG : 1 ≤ G)
    (pkg : Package (sharpDeltaScale s H Bprime) B (sharpThetaScale s))
    (hell : (pkg.ell : ℝ) ≤
      Real.log (sharpThetaScale s / 4) / Real.log (1 / 9) + 1)
    (hJ : (pkg.J : ℝ) ≤
      Real.log
          (Real.sqrt (B + sharpDeltaScale s H Bprime) /
            Real.sqrt (sharpDeltaScale s H Bprime)) /
        Real.log 2) :
    pkg.numeratorComparisonCoefficientBound Bprime G ≤
      logSquareEnvelope
        (sharpNumeratorComparisonLogSquareConstant s B Bprime G) (H + 1) := by
  let D := sharpPackageDegreeLogConstant s B Bprime
  let K := sharpNumeratorGapLogSquareConstant s B Bprime
  let x : ℝ := H + 1
  have hx : 1 ≤ x := by dsimp [x]; linarith
  have hdegreeBound := pkg.degreeBound_cast_le_sharp_log
    hH (zero_le_one.trans hB) hBprime hell hJ
  have hdegree : ((pkg.numeratorGap Bprime).natDegree : ℝ) ≤
      D * (1 + Real.log x) := by
    have hcast : ((pkg.numeratorGap Bprime).natDegree : ℝ) ≤
        pkg.degreeBound := by
      exact_mod_cast pkg.numeratorGap_degree_le
    exact hcast.trans (by simpa [D, x] using hdegreeBound)
  have hinterval :
      intervalCertificateCoefficientBound B (pkg.numeratorGap Bprime) ≤
        logSquareEnvelope (intervalCertificateLogSquareConstant B D K) x :=
    intervalCertificateCoefficientBound_le_logSquareEnvelope hB
      (sharpPackageDegreeLogConstant_nonneg s B Bprime)
      (sharpNumeratorGapLogSquareConstant_nonneg s B Bprime) hx
      (pkg.numeratorGap Bprime) hdegree
      (by
        simpa [K, x] using
          (pkg.numeratorGap_norm_le_sharp_log hH (zero_le_one.trans hB)
            hBprime hell hJ))
  have hdegreePlus : (((pkg.numeratorGap Bprime).natDegree + 3 : ℕ) : ℝ) ≤
      (D + 3) * (1 + Real.log x) := by
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
    nlinarith
  have hpower : G ^ ((pkg.numeratorGap Bprime).natDegree + 3) ≤
      logSquareEnvelope ((D + 3) * Real.log G) x :=
    fixed_pow_le_logSquareEnvelope hG
      (by dsimp [D]; linarith [sharpPackageDegreeLogConstant_nonneg s B Bprime])
      hx hdegreePlus
  unfold numeratorComparisonCoefficientBound
  calc
    intervalCertificateCoefficientBound B (pkg.numeratorGap Bprime) *
        G ^ ((pkg.numeratorGap Bprime).natDegree + 3) ≤
      logSquareEnvelope (intervalCertificateLogSquareConstant B D K) x *
        logSquareEnvelope ((D + 3) * Real.log G) x := by
          exact mul_le_mul hinterval hpower (pow_nonneg (by linarith) _)
            (logSquareEnvelope_pos _ _).le
    _ = logSquareEnvelope
        (sharpNumeratorComparisonLogSquareConstant s B Bprime G) (H + 1) := by
      rw [logSquareEnvelope_mul]
      rfl

/-- Exponent constant for the coefficient budget after substituting a
fixed-norm multivariate polynomial into any package polynomial. -/
def sharpSubstitutionLogSquareConstant
    (s : ℕ) (B Bprime G : ℝ) : ℝ :=
  sharpPackageLogSquareConstant s B Bprime +
    sharpPackageDegreeLogConstant s B Bprime * Real.log G

theorem sharpSubstitutionLogSquareConstant_nonneg
    (s : ℕ) (B Bprime : ℝ) {G : ℝ} (hG : 1 ≤ G) :
    0 ≤ sharpSubstitutionLogSquareConstant s B Bprime G := by
  unfold sharpSubstitutionLogSquareConstant
  exact add_nonneg (sharpPackageLogSquareConstant_nonneg s B Bprime)
    (mul_nonneg (sharpPackageDegreeLogConstant_nonneg s B Bprime)
      (Real.log_nonneg hG))

theorem RationalSquareRoot.Package.substitutionCoefficientBound_le_sharp_log
    {s : ℕ} {H B Bprime G : ℝ}
    (hH : 0 ≤ H) (hB : 0 ≤ B) (hBprime : 0 ≤ Bprime)
    (hG : 1 ≤ G)
    (pkg : Package (sharpDeltaScale s H Bprime) B (sharpThetaScale s))
    (hell : (pkg.ell : ℝ) ≤
      Real.log (sharpThetaScale s / 4) / Real.log (1 / 9) + 1)
    (hJ : (pkg.J : ℝ) ≤
      Real.log
          (Real.sqrt (B + sharpDeltaScale s H Bprime) /
            Real.sqrt (sharpDeltaScale s H Bprime)) /
        Real.log 2) :
    pkg.substitutionCoefficientBound G ≤
      logSquareEnvelope (sharpSubstitutionLogSquareConstant s B Bprime G)
        (H + 1) := by
  let D := sharpPackageDegreeLogConstant s B Bprime
  let K := sharpPackageLogSquareConstant s B Bprime
  let x : ℝ := H + 1
  have hx : 1 ≤ x := by dsimp [x]; linarith
  have hcoeff := pkg.coefficientBound_le_sharp_log
    hH hB hBprime hell hJ
  have hdegree := pkg.degreeBound_cast_le_sharp_log
    hH hB hBprime hell hJ
  have hpower : G ^ pkg.degreeBound ≤
      logSquareEnvelope (D * Real.log G) x :=
    fixed_pow_le_logSquareEnvelope hG
      (sharpPackageDegreeLogConstant_nonneg s B Bprime) hx
      (by simpa [D, x] using hdegree)
  unfold substitutionCoefficientBound
  calc
    pkg.coefficientBound * G ^ pkg.degreeBound ≤
      logSquareEnvelope K x * logSquareEnvelope (D * Real.log G) x := by
        exact mul_le_mul (by simpa [K, x] using hcoeff) hpower
          (pow_nonneg (by linarith) _) (logSquareEnvelope_pos K x).le
    _ = logSquareEnvelope
        (sharpSubstitutionLogSquareConstant s B Bprime G) (H + 1) := by
      rw [logSquareEnvelope_mul]
      rfl

/-- Exponent constant for the common error/numerator interval-certificate
budget used by bounded conversion. -/
def sharpConversionIntervalLogSquareConstant
    (s : ℕ) (B Bprime G Ha Hb : ℝ) : ℝ :=
  Real.log ((1 + Ha + Hb) + 1) +
    sharpErrorComparisonLogSquareConstant s B Bprime G +
    sharpNumeratorComparisonLogSquareConstant s B Bprime G

theorem sharpConversionIntervalLogSquareConstant_nonneg
    (s : ℕ) {B Bprime G Ha Hb : ℝ}
    (hB : 1 ≤ B) (hG : 1 ≤ G) (hHa : 0 ≤ Ha) (hHb : 0 ≤ Hb) :
    0 ≤ sharpConversionIntervalLogSquareConstant s B Bprime G Ha Hb := by
  have hscale : 1 ≤ (1 + Ha + Hb) + 1 := by linarith
  unfold sharpConversionIntervalLogSquareConstant
  exact add_nonneg
    (add_nonneg (Real.log_nonneg hscale)
      (sharpErrorComparisonLogSquareConstant_nonneg s hB hG))
    (sharpNumeratorComparisonLogSquareConstant_nonneg s hB hG)

theorem conversionIntervalCertificateBound_le_sharp_log
    {s : ℕ} {H B Bprime G Ha Hb : ℝ}
    (hH : 0 ≤ H) (hB : 1 ≤ B) (hBprime : 0 ≤ Bprime)
    (hG : 1 ≤ G) (hHa : 0 ≤ Ha) (hHb : 0 ≤ Hb)
    (pkg : Package (sharpDeltaScale s H Bprime) B (sharpThetaScale s))
    (hell : (pkg.ell : ℝ) ≤
      Real.log (sharpThetaScale s / 4) / Real.log (1 / 9) + 1)
    (hJ : (pkg.J : ℝ) ≤
      Real.log
          (Real.sqrt (B + sharpDeltaScale s H Bprime) /
            Real.sqrt (sharpDeltaScale s H Bprime)) /
        Real.log 2) :
    conversionIntervalCertificateBound pkg Bprime G Ha Hb ≤
      logSquareEnvelope
        (sharpConversionIntervalLogSquareConstant s B Bprime G Ha Hb)
        (H + 1) := by
  let Ke := sharpErrorComparisonLogSquareConstant s B Bprime G
  let Kn := sharpNumeratorComparisonLogSquareConstant s B Bprime G
  let x : ℝ := H + 1
  let A : ℝ := 1 + Ha + Hb
  have hx : 1 ≤ x := by dsimp [x]; linarith
  have hKe : 0 ≤ Ke := by
    exact sharpErrorComparisonLogSquareConstant_nonneg s hB hG
  have hKn : 0 ≤ Kn := by
    exact sharpNumeratorComparisonLogSquareConstant_nonneg s hB hG
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have herror := pkg.errorComparisonCoefficientBound_le_sharp_log
    hH hB hBprime hG hell hJ
  have hnumerator := pkg.numeratorComparisonCoefficientBound_le_sharp_log
    hH hB hBprime hG hell hJ
  have herrorCommon : pkg.errorComparisonCoefficientBound G ≤
      logSquareEnvelope (Ke + Kn) x := by
    have hbase : pkg.errorComparisonCoefficientBound G ≤
        logSquareEnvelope Ke x := by simpa [Ke, x] using herror
    exact hbase.trans (logSquareEnvelope_mono (by linarith) hx)
  have hnumeratorCommon : pkg.numeratorComparisonCoefficientBound Bprime G ≤
      logSquareEnvelope (Ke + Kn) x := by
    have hbase : pkg.numeratorComparisonCoefficientBound Bprime G ≤
        logSquareEnvelope Kn x := by simpa [Kn, x] using hnumerator
    exact hbase.trans (logSquareEnvelope_mono (by linarith) hx)
  have hAenv : A ≤ logSquareEnvelope (Real.log (A + 1)) x :=
    le_logSquareEnvelope_log_add_one hA hx
  have herror0 : 0 ≤ pkg.errorComparisonCoefficientBound G := by
    unfold RationalSquareRoot.Package.errorComparisonCoefficientBound
    exact mul_nonneg (intervalCertificateCoefficientBound_nonneg hB pkg.errorGap)
      (pow_nonneg (zero_le_one.trans hG) _)
  have hnumerator0 : 0 ≤ pkg.numeratorComparisonCoefficientBound Bprime G := by
    unfold RationalSquareRoot.Package.numeratorComparisonCoefficientBound
    exact mul_nonneg
      (intervalCertificateCoefficientBound_nonneg hB (pkg.numeratorGap Bprime))
      (pow_nonneg (zero_le_one.trans hG) _)
  have herrBranch :
      pkg.errorComparisonCoefficientBound G +
          (pkg.errorComparisonCoefficientBound G * Ha +
            pkg.errorComparisonCoefficientBound G * Hb) ≤
        logSquareEnvelope (Real.log (A + 1) + (Ke + Kn)) x := by
    calc
      pkg.errorComparisonCoefficientBound G +
          (pkg.errorComparisonCoefficientBound G * Ha +
            pkg.errorComparisonCoefficientBound G * Hb) =
        A * pkg.errorComparisonCoefficientBound G := by
          dsimp [A]
          ring
      _ ≤ logSquareEnvelope (Real.log (A + 1)) x *
          logSquareEnvelope (Ke + Kn) x :=
        mul_le_mul hAenv herrorCommon herror0
          (logSquareEnvelope_pos _ _).le
      _ = logSquareEnvelope (Real.log (A + 1) + (Ke + Kn)) x :=
        logSquareEnvelope_mul _ _ _
  have hnumBranch :
      pkg.numeratorComparisonCoefficientBound Bprime G +
          (pkg.numeratorComparisonCoefficientBound Bprime G * Ha +
            pkg.numeratorComparisonCoefficientBound Bprime G * Hb) ≤
        logSquareEnvelope (Real.log (A + 1) + (Ke + Kn)) x := by
    calc
      pkg.numeratorComparisonCoefficientBound Bprime G +
          (pkg.numeratorComparisonCoefficientBound Bprime G * Ha +
            pkg.numeratorComparisonCoefficientBound Bprime G * Hb) =
        A * pkg.numeratorComparisonCoefficientBound Bprime G := by
          dsimp [A]
          ring
      _ ≤ logSquareEnvelope (Real.log (A + 1)) x *
          logSquareEnvelope (Ke + Kn) x :=
        mul_le_mul hAenv hnumeratorCommon hnumerator0
          (logSquareEnvelope_pos _ _).le
      _ = logSquareEnvelope (Real.log (A + 1) + (Ke + Kn)) x :=
        logSquareEnvelope_mul _ _ _
  unfold conversionIntervalCertificateBound
  have hK : Real.log (A + 1) + (Ke + Kn) =
      sharpConversionIntervalLogSquareConstant s B Bprime G Ha Hb := by
    dsimp [A, Ke, Kn]
    unfold sharpConversionIntervalLogSquareConstant
    ring
  simpa only [hK, x] using (max_le herrBranch hnumBranch)

/-- Exponent constant for the common polynomial factor coefficient budget. -/
def sharpConversionFactorLogSquareConstant
    (s : ℕ) (B Bprime G : ℝ) : ℝ :=
  Real.log (4 * (2 * |Bprime| + 5) + 1) +
    2 * sharpSubstitutionLogSquareConstant s B Bprime G

theorem sharpConversionFactorLogSquareConstant_nonneg
    (s : ℕ) (B Bprime : ℝ) {G : ℝ} (hG : 1 ≤ G) :
    0 ≤ sharpConversionFactorLogSquareConstant s B Bprime G := by
  have hbase : 1 ≤ 4 * (2 * |Bprime| + 5) + 1 := by
    nlinarith [abs_nonneg Bprime]
  unfold sharpConversionFactorLogSquareConstant
  exact add_nonneg (Real.log_nonneg hbase)
    (mul_nonneg (by norm_num)
      (sharpSubstitutionLogSquareConstant_nonneg s B Bprime hG))

theorem conversionFactorCoefficientBound_le_sharp_log
    {s : ℕ} {H B Bprime G : ℝ}
    (hH : 0 ≤ H) (hB : 0 ≤ B) (hBprime : 0 ≤ Bprime)
    (hG : 1 ≤ G)
    (pkg : Package (sharpDeltaScale s H Bprime) B (sharpThetaScale s))
    (hell : (pkg.ell : ℝ) ≤
      Real.log (sharpThetaScale s / 4) / Real.log (1 / 9) + 1)
    (hJ : (pkg.J : ℝ) ≤
      Real.log
          (Real.sqrt (B + sharpDeltaScale s H Bprime) /
            Real.sqrt (sharpDeltaScale s H Bprime)) /
        Real.log 2) :
    conversionFactorCoefficientBound pkg Bprime G ≤
      logSquareEnvelope
        (sharpConversionFactorLogSquareConstant s B Bprime G) (H + 1) := by
  let K := sharpSubstitutionLogSquareConstant s B Bprime G
  let x : ℝ := H + 1
  let E := logSquareEnvelope K x
  let C : ℝ := 2 * |Bprime| + 5
  have hx : 1 ≤ x := by dsimp [x]; linarith
  have hK : 0 ≤ K := sharpSubstitutionLogSquareConstant_nonneg s B Bprime hG
  have hE : 1 ≤ E := one_le_logSquareEnvelope hK hx
  have hsubst := pkg.substitutionCoefficientBound_le_sharp_log
    hH hB hBprime hG hell hJ
  have htheta : |sharpThetaScale s| ≤ 1 := by
    rw [abs_of_pos (sharpThetaScale_pos s)]
    exact (sharpThetaScale_le_half s).trans (by norm_num)
  have hdelta : |sharpDeltaScale s H Bprime| ≤ 1 := by
    rw [abs_of_pos (sharpDeltaScale_pos hH hBprime)]
    exact (sharpDeltaScale_le_half hH hBprime).trans (by norm_num)
  have hmix : |sharpThetaScale s * Bprime + sharpDeltaScale s H Bprime| ≤
      |Bprime| + 1 := by
    calc
      |sharpThetaScale s * Bprime + sharpDeltaScale s H Bprime| ≤
          |sharpThetaScale s * Bprime| + |sharpDeltaScale s H Bprime| :=
        abs_add_le _ _
      _ = |sharpThetaScale s| * |Bprime| +
          |sharpDeltaScale s H Bprime| := by rw [abs_mul]
      _ ≤ |Bprime| + 1 := by
        have habs := abs_nonneg Bprime
        nlinarith
  have hscalar : |sharpThetaScale s| + |sharpDeltaScale s H Bprime| +
      |Bprime| + |sharpThetaScale s * Bprime + sharpDeltaScale s H Bprime| + 2 ≤
      C := by
    dsimp [C]
    linarith
  have hplus : pkg.substitutionCoefficientBound G + 1 ≤ 2 * E := by
    dsimp [E, K, x]
    nlinarith
  have hsquare : (pkg.substitutionCoefficientBound G + 1) ^ 2 ≤
      (2 * E) ^ 2 := by
    apply pow_le_pow_left₀
    · linarith [pkg.one_le_substitutionCoefficientBound hG]
    · exact hplus
  have hfixed : 4 * C ≤ logSquareEnvelope (Real.log (4 * C + 1)) x :=
    le_logSquareEnvelope_log_add_one (by dsimp [C]; positivity) hx
  have hEsquare : E ^ 2 ≤ logSquareEnvelope (2 * K) x := by
    rw [logSquareEnvelope_pow]
    norm_num
  unfold conversionFactorCoefficientBound
  calc
    (|sharpThetaScale s| + |sharpDeltaScale s H Bprime| + |Bprime| +
          |sharpThetaScale s * Bprime + sharpDeltaScale s H Bprime| + 2) *
        (pkg.substitutionCoefficientBound G + 1) ^ 2 ≤ C * (2 * E) ^ 2 :=
      mul_le_mul hscalar hsquare (sq_nonneg _)
        (by positivity)
    _ = (4 * C) * E ^ 2 := by ring
    _ ≤ logSquareEnvelope (Real.log (4 * C + 1)) x *
        logSquareEnvelope (2 * K) x :=
      mul_le_mul hfixed hEsquare (sq_nonneg _)
        (logSquareEnvelope_pos _ _).le
    _ = logSquareEnvelope
        (sharpConversionFactorLogSquareConstant s B Bprime G) (H + 1) := by
      rw [logSquareEnvelope_mul]
      rfl

end OptimalConvergenceRates.GeneralArchimedean

end
