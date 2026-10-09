/-
  The concrete coefficient bound delivered by the sharp Archimedean bridge
  is exponential in the square of the logarithm of its input bound.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpBudgetAsymptotics
import OptimalConvergenceRates.GeneralArchimedean.SharpBoundedBridge

noncomputable section

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

/-- Fixed exponent constant for the bounded Archimedean certificate of an
active preordering coefficient. -/
def sharpBridgeSigmaLogSquareConstant
    (n d : ℕ) (R Hcoord : ℝ) : ℝ :=
  let C₁ : ℝ := (boundedMonomialCount n d : ℝ) *
    (boundedMonomialSquareBudget n d R Hcoord + 1)
  Real.log 3 + 1 + (Real.log (C₁ + 1) + 2)

theorem sharpBridgeSigmaLogSquareConstant_nonneg
    (n d : ℕ) {R Hcoord : ℝ} (hR : 0 ≤ R) (hHcoord : 0 ≤ Hcoord) :
    0 ≤ sharpBridgeSigmaLogSquareConstant n d R Hcoord := by
  let C₁ : ℝ := (boundedMonomialCount n d : ℝ) *
    (boundedMonomialSquareBudget n d R Hcoord + 1)
  have hC₁ : 0 ≤ C₁ := by
    dsimp [C₁]
    exact mul_nonneg (by positivity)
      (by linarith [boundedMonomialSquareBudget_nonneg n d hR hHcoord])
  unfold sharpBridgeSigmaLogSquareConstant
  dsimp only
  have hlogC : 0 ≤ Real.log (C₁ + 1) := Real.log_nonneg (by linarith)
  have hlog3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  positivity

/-- The certificate budget for an active preordering coefficient is bounded
by a log-square envelope in the common conversion bound. -/
theorem boundedBridgeSigmaBudget_le_logSquareEnvelope
    (n d : ℕ) {R Hcoord H Hconvert : ℝ}
    (hR : 0 ≤ R) (hHcoord : 0 ≤ Hcoord)
    (hH : 0 ≤ H) (hHle : H ≤ Hconvert) :
    boundedBridgeSigmaBudget n d R Hcoord H Hconvert ≤
      logSquareEnvelope
        (sharpBridgeSigmaLogSquareConstant n d R Hcoord)
        (Hconvert + 1) := by
  let Q := boundedMonomialSquareBudget n d R Hcoord
  let C₁ : ℝ := (boundedMonomialCount n d : ℝ) * (Q + 1)
  let x : ℝ := Hconvert + 1
  have hHconvert : 0 ≤ Hconvert := hH.trans hHle
  have hx : 1 ≤ x := by dsimp [x]; linarith
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact boundedMonomialSquareBudget_nonneg n d hR hHcoord
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hHconvertEnv : Hconvert ≤ logSquareEnvelope 1 x := by
    exact (show Hconvert ≤ x by dsimp [x]; linarith).trans
      (self_le_logSquareEnvelope_one hx)
  have hHplus : H + 1 ≤ x := by dsimp [x]; linarith
  have hHplus0 : 0 ≤ H + 1 := by linarith
  have hxEnv := self_le_logSquareEnvelope_one hx
  have hHsq : (H + 1) ^ 2 ≤ logSquareEnvelope 2 x := by
    calc
      (H + 1) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hHplus0 hHplus 2
      _ ≤ logSquareEnvelope 1 x ^ 2 :=
        pow_le_pow_left₀ (by positivity) hxEnv 2
      _ = logSquareEnvelope 2 x := by
        rw [logSquareEnvelope_pow]
        norm_num
  have hCenv : C₁ ≤ logSquareEnvelope (Real.log (C₁ + 1)) x :=
    le_logSquareEnvelope_log_add_one hC₁ hx
  have hprod : C₁ * (H + 1) ^ 2 ≤
      logSquareEnvelope (Real.log (C₁ + 1) + 2) x :=
    mul_le_logSquareEnvelope hC₁ (sq_nonneg _) hCenv hHsq
  have hrearrange :
      boundedBridgeSigmaBudget n d R Hcoord H Hconvert =
        Hconvert + C₁ * (H + 1) ^ 2 := by
    unfold boundedBridgeSigmaBudget boundedArchimedeanEnvelopeBudget
      boundedCoeffEnvelopeBudgetUpper
    dsimp [C₁, Q]
    ring
  rw [hrearrange]
  exact add_le_logSquareEnvelope hHconvert
    (mul_nonneg hC₁ (sq_nonneg _)) (by norm_num)
    (by exact add_nonneg (Real.log_nonneg (by linarith)) (by norm_num))
    hx hHconvertEnv hprod

theorem sharpDeltaCoefficient_nonneg
    {s : ℕ} {H Bprime theta delta : ℝ}
    (hH : 0 ≤ H) (hBprime : 0 ≤ Bprime)
    (htheta : 0 ≤ theta) (hdelta : 0 ≤ delta) :
    0 ≤ sharpDeltaCoefficient s H Bprime theta delta := by
  classical
  unfold sharpDeltaCoefficient refinedRemainderCoefficient
  positivity

/-- The chosen sharp delta leaves at least half of the denominator channel
available in the final absorption. -/
theorem sharpDeltaCoefficient_scale_le_half
    {s : ℕ} {H Bprime theta : ℝ}
    (hH : 0 ≤ H) (hBprime : 0 ≤ Bprime)
    (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    sharpDeltaCoefficient s H Bprime theta
      (sharpDeltaScale s H Bprime) ≤ 1 / 2 := by
  let count : ℝ := sharpTripleCount s
  let M : ℝ := Bprime + 1
  let delta : ℝ := sharpDeltaScale s H Bprime
  have hcount : 0 ≤ count := by positivity
  have hdelta : 0 < delta := sharpDeltaScale_pos hH hBprime
  have hdeltaHalf : delta ≤ 1 / 2 :=
    sharpDeltaScale_le_half hH hBprime
  have hupper : sharpDeltaCoefficient s H Bprime theta delta ≤
      (sharpTripleCount s : ℝ) *
        (H * delta * (Bprime + 1) ^ s) :=
    sharpDeltaCoefficient_le (s := s) hH hBprime htheta htheta1 hdelta.le
      (hdeltaHalf.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have hvalue :
      count * (H * delta * M ^ s) =
        count * H / (2 * (count + 1) * (H + 1)) := by
    dsimp [delta, sharpDeltaScale, count, M]
    rw [inv_eq_one_div]
    field_simp
  have hratio :
      count * H / (2 * (count + 1) * (H + 1)) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hcount hH]
  exact hupper.trans (hvalue.trans_le hratio)

/-- Fixed exponent constant for the complete coefficient budget of the
bounded sharp Archimedean bridge. -/
def sharpBridgeLogSquareConstant
    (s n d : ℕ) (R Hcoord G B : ℝ) : ℝ :=
  let Bprime : ℝ := 2 * (B + 1)
  let Hb : ℝ := boundedBridgeGeneratorBudget n d R Hcoord G B
  let Ksigma := sharpBridgeSigmaLogSquareConstant n d R Hcoord
  let Kcomparison :=
    sharpConversionIntervalLogSquareConstant s B Bprime G 1 Hb
  let Kfactor := sharpConversionFactorLogSquareConstant s B Bprime G
  let Kodd := sharpConvertedOddLogSquareConstant s Ksigma 1
    Kcomparison Kfactor
  let Keven := sharpEvenLogSquareConstant s 1 Kfactor
  let Kdenominator :=
    sharpDenominatorProductLogSquareConstant s B Bprime G 1
  sharpFinalBudgetLogSquareConstant Kodd Keven Kdenominator

/-- The actual nested bridge budget has the advertised
`exp(O((1+log H)^2))` dependence. -/
theorem boundedSharpBridgeRefutationBudget_le_sharp_log
    {s n d : ℕ} {R Hcoord G B H Hconvert : ℝ}
    (hR : 1 ≤ R) (hHcoord : 0 ≤ Hcoord) (hG : 1 ≤ G)
    (hB : 1 ≤ B) (hH : 0 ≤ H) (hHle : H ≤ Hconvert)
    (pkg : Package (sharpDeltaScale s Hconvert (2 * (B + 1))) B
      (sharpThetaScale s))
    (hell : (pkg.ell : ℝ) ≤
      Real.log (sharpThetaScale s / 4) / Real.log (1 / 9) + 1)
    (hJ : (pkg.J : ℝ) ≤
      Real.log
          (Real.sqrt (B + sharpDeltaScale s Hconvert (2 * (B + 1))) /
            Real.sqrt (sharpDeltaScale s Hconvert (2 * (B + 1)))) /
        Real.log 2) :
    boundedSharpBridgeRefutationBudget pkg s n d R Hcoord G H Hconvert ≤
      logSquareEnvelope
        (sharpBridgeLogSquareConstant s n d R Hcoord G B)
        (Hconvert + 1) := by
  let Bprime : ℝ := 2 * (B + 1)
  let Hb : ℝ := boundedBridgeGeneratorBudget n d R Hcoord G B
  let HsigmaCert : ℝ := boundedBridgeSigmaBudget n d R Hcoord H Hconvert
  let Ksigma := sharpBridgeSigmaLogSquareConstant n d R Hcoord
  let Kcomparison :=
    sharpConversionIntervalLogSquareConstant s B Bprime G 1 Hb
  let Kfactor := sharpConversionFactorLogSquareConstant s B Bprime G
  let Kodd := sharpConvertedOddLogSquareConstant s Ksigma 1
    Kcomparison Kfactor
  let Keven := sharpEvenLogSquareConstant s 1 Kfactor
  let Kdenominator :=
    sharpDenominatorProductLogSquareConstant s B Bprime G 1
  let x : ℝ := Hconvert + 1
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hHconvert : 0 ≤ Hconvert := hH.trans hHle
  have hx : 1 ≤ x := by dsimp [x]; linarith
  have hBprime : 0 ≤ Bprime := by dsimp [Bprime]; positivity
  have hHb : 0 ≤ Hb := by
    dsimp [Hb, boundedBridgeGeneratorBudget]
    exact add_nonneg hB0
      (boundedArchimedeanEnvelopeBudget_nonneg n d hR0 hHcoord hG0)
  have hHsigmaCert : 0 ≤ HsigmaCert := by
    dsimp [HsigmaCert, boundedBridgeSigmaBudget]
    exact add_nonneg hHconvert
      (boundedArchimedeanEnvelopeBudget_nonneg n d hR0 hHcoord hH)
  have hfactor0 : 0 ≤ conversionFactorCoefficientBound pkg Bprime G :=
    conversionFactorCoefficientBound_nonneg pkg Bprime G
  have hcomparison0 : 0 ≤
      conversionIntervalCertificateBound pkg Bprime G 1 Hb :=
    conversionIntervalCertificateBound_nonneg pkg Bprime hB hG
      (by norm_num) hHb
  have hKsigma : 0 ≤ Ksigma := by
    dsimp [Ksigma]
    exact sharpBridgeSigmaLogSquareConstant_nonneg n d hR0 hHcoord
  have hKcomparison : 0 ≤ Kcomparison := by
    dsimp [Kcomparison]
    exact sharpConversionIntervalLogSquareConstant_nonneg s hB hG
      (by norm_num) hHb
  have hKfactor : 0 ≤ Kfactor := by
    dsimp [Kfactor]
    exact sharpConversionFactorLogSquareConstant_nonneg s B Bprime hG
  have hsigmaCert : HsigmaCert ≤ logSquareEnvelope Ksigma x := by
    dsimp [HsigmaCert, Ksigma, x]
    exact boundedBridgeSigmaBudget_le_logSquareEnvelope n d hR0 hHcoord hH hHle
  have hsigmaNorm : H ≤ logSquareEnvelope 1 x := by
    exact hHle.trans ((show Hconvert ≤ x by dsimp [x]; linarith).trans
      (self_le_logSquareEnvelope_one hx))
  have hcomparison : conversionIntervalCertificateBound pkg Bprime G 1 Hb ≤
      logSquareEnvelope Kcomparison x := by
    dsimp [Kcomparison, x, Bprime]
    exact conversionIntervalCertificateBound_le_sharp_log
      hHconvert hB hBprime hG (by norm_num) hHb pkg hell hJ
  have hfactor : conversionFactorCoefficientBound pkg Bprime G ≤
      logSquareEnvelope Kfactor x := by
    dsimp [Kfactor, x, Bprime]
    exact conversionFactorCoefficientBound_le_sharp_log
      hHconvert hB0 hBprime hG pkg hell hJ
  have htheta : 0 ≤ sharpThetaScale s := (sharpThetaScale_pos s).le
  have htheta1 : sharpThetaScale s ≤ 1 :=
    (sharpThetaScale_le_half s).trans (by norm_num)
  have hodd := boundedSharpConvertedOddBudget_le_logSquareEnvelope (s := s)
    hHsigmaCert hH htheta htheta1 hcomparison0 hfactor0
    hKsigma (by norm_num) hKcomparison hKfactor hx
    hsigmaCert hsigmaNorm hcomparison hfactor
  have heven := boundedConvertedEvenNorm_le_logSquareEnvelope (s := s)
    hH hfactor0 (by norm_num) hKfactor hx hsigmaNorm hfactor
  have hdenominator := boundedDenominatorProductBudget_le_sharp_log
    (Ha := (1 : ℝ)) hHconvert hB0 hBprime hG (by norm_num) pkg hell hJ
  let Kcount := Real.log (conversionSubsetCount s + 1)
  let Kpair := Real.log ((oddPairCount s : ℝ) + 1)
  let Kterm := sharpConvertedTermLogSquareConstant s 1 Kfactor
  let Kexp := sharpExpansionLogSquareConstant s 1 Kcomparison Kfactor
  let Kscalar := sharpScalarLogSquareConstant s Ksigma 1 Kcomparison Kfactor
  let KoddTerm := sharpOddTermLogSquareConstant s Ksigma 1 Kcomparison Kfactor
  let Ktheta := sharpThetaAbsorptionLogSquareConstant s 1 Kfactor
  have hlog3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hcount0 : 0 ≤ (conversionSubsetCount s : ℝ) := by
    unfold conversionSubsetCount
    positivity
  have hpair0 : 0 ≤ (oddPairCount s : ℝ) := by
    unfold oddPairCount
    positivity
  have hKcount : 0 ≤ Kcount := by
    dsimp [Kcount]
    exact Real.log_nonneg (by linarith)
  have hKpair : 0 ≤ Kpair := by
    dsimp [Kpair]
    exact Real.log_nonneg (by linarith)
  have hKterm : 0 ≤ Kterm := by
    dsimp [Kterm, sharpConvertedTermLogSquareConstant]
    positivity
  have hKexp : 0 ≤ Kexp := by
    dsimp [Kexp, sharpExpansionLogSquareConstant]
    positivity
  have hKscalar : 0 ≤ Kscalar := by
    dsimp [Kscalar, sharpScalarLogSquareConstant]
    positivity
  have hKoddTerm : 0 ≤ KoddTerm := by
    dsimp [KoddTerm, sharpOddTermLogSquareConstant]
    exact add_nonneg (add_nonneg hlog3 hKexp)
      (add_nonneg (add_nonneg hlog3 hKterm)
        (add_nonneg hKcount hKscalar))
  have hKeven : 0 ≤ Keven := by
    dsimp [Keven, sharpEvenLogSquareConstant]
    exact add_nonneg hKcount (add_nonneg hKcount hKterm)
  have hKtheta : 0 ≤ Ktheta := by
    dsimp [Ktheta, sharpThetaAbsorptionLogSquareConstant]
    exact add_nonneg
      (add_nonneg hlog3 (add_nonneg hKcount (add_nonneg hKpair hKterm)))
      (add_nonneg hKpair hKeven)
  have hKodd : 0 ≤ Kodd := by
    dsimp [Kodd, sharpConvertedOddLogSquareConstant]
    exact add_nonneg
      (add_nonneg hlog3 (add_nonneg hKcount (add_nonneg hKcount hKoddTerm)))
      hKtheta
  have hKdenominator : 0 ≤ Kdenominator := by
    dsimp [Kdenominator]
    exact sharpDenominatorProductLogSquareConstant_nonneg
      s B Bprime hG (by norm_num)
  let odd := boundedSharpConvertedOddBudget s H (sharpThetaScale s)
    (conversionFactorCoefficientBound pkg Bprime G)
    (boundedSharpOddTermBudget s HsigmaCert H (sharpThetaScale s)
      (conversionIntervalCertificateBound pkg Bprime G 1 Hb)
      (conversionFactorCoefficientBound pkg Bprime G))
  let even := boundedConvertedEvenNorm s H
    (conversionFactorCoefficientBound pkg Bprime G)
  let denominator := boundedDenominatorProductBudget pkg s Bprime G 1
  have hterm0 : 0 ≤ boundedConvertedTermNorm s H
      (conversionFactorCoefficientBound pkg Bprime G) := by
    unfold boundedConvertedTermNorm
    exact mul_nonneg hH (pow_nonneg (by linarith) _)
  have hscalar0 : 0 ≤ boundedSharpScalarBudget s HsigmaCert H
      (sharpThetaScale s) (conversionIntervalCertificateBound pkg Bprime G 1 Hb)
      (conversionFactorCoefficientBound pkg Bprime G) := by
    unfold boundedSharpScalarBudget
    positivity
  have hexp0 : 0 ≤ boundedConversionExpansionBudget s H
      (conversionIntervalCertificateBound pkg Bprime G 1 Hb)
      (conversionFactorCoefficientBound pkg Bprime G) := by
    unfold boundedConversionExpansionBudget boundedConversionContextBound
      boundedConversionProductBudget
    positivity
  have hoddTerm0 : 0 ≤ boundedSharpOddTermBudget s HsigmaCert H
      (sharpThetaScale s) (conversionIntervalCertificateBound pkg Bprime G 1 Hb)
      (conversionFactorCoefficientBound pkg Bprime G) := by
    unfold boundedSharpOddTermBudget boundedSharpPureThetaBudget
    exact add_nonneg hexp0
      (add_nonneg hterm0 (mul_nonneg hcount0 hscalar0))
  have hconvertedOdd0 : 0 ≤ boundedConvertedOddBudget s
      (boundedSharpOddTermBudget s HsigmaCert H (sharpThetaScale s)
        (conversionIntervalCertificateBound pkg Bprime G 1 Hb)
        (conversionFactorCoefficientBound pkg Bprime G)) := by
    unfold boundedConvertedOddBudget
    exact mul_nonneg hcount0 (mul_nonneg hcount0 hoddTerm0)
  have hevenActual0 : 0 ≤ boundedConvertedEvenNorm s H
      (conversionFactorCoefficientBound pkg Bprime G) := by
    unfold boundedConvertedEvenNorm
    exact mul_nonneg hcount0 (mul_nonneg hcount0 hterm0)
  have halpha0 : 0 ≤ sharpThetaCoefficient s (sharpThetaScale s) := by
    unfold sharpThetaCoefficient
    exact mul_nonneg hpair0 htheta
  have hodd0 : 0 ≤ odd := by
    dsimp [odd, boundedSharpConvertedOddBudget]
    apply add_nonneg hconvertedOdd0
    unfold boundedSharpThetaAbsorptionBudget
    exact add_nonneg (mul_nonneg hcount0 (mul_nonneg halpha0 hterm0))
      (mul_nonneg halpha0 hevenActual0)
  have heven0 : 0 ≤ even := by
    simpa [even] using hevenActual0
  have hdenominator0 : 0 ≤ denominator := by
    dsimp [denominator, boundedDenominatorProductBudget]
    exact mul_nonneg (pow_nonneg (by linarith) _)
      (pkg.denominatorFactorCertificateBound_nonneg hG (by norm_num))
  have hbeta0 : 0 ≤ sharpDeltaCoefficient s Hconvert Bprime
      (sharpThetaScale s) (sharpDeltaScale s Hconvert Bprime) :=
    sharpDeltaCoefficient_nonneg hHconvert hBprime htheta
      (sharpDeltaScale_pos hHconvert hBprime).le
  have hbetaHalf : sharpDeltaCoefficient s Hconvert Bprime
      (sharpThetaScale s) (sharpDeltaScale s Hconvert Bprime) ≤ 1 / 2 :=
    sharpDeltaCoefficient_scale_le_half hHconvert hBprime htheta htheta1
  unfold boundedSharpBridgeRefutationBudget sharpBridgeLogSquareConstant
  dsimp only
  exact boundedSharpRefutationBudget_le_logSquareEnvelope hbeta0 hbetaHalf
    hodd0 heven0 hdenominator0 hKodd hKeven hKdenominator hx
    (by simpa [odd, Kodd] using hodd)
    (by simpa [even, Keven] using heven)
    (by simpa [denominator, Kdenominator, Bprime, x] using hdenominator)

end OptimalConvergenceRates.GeneralArchimedean

end
