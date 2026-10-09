/-
  Closure of the coefficient budgets used by the sharp conversion under
  log-square envelopes.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpBridgeCoefficientBounds

noncomputable section

namespace OptimalConvergenceRates.GeneralArchimedean

/-- Adding one to an enveloped nonnegative quantity costs a fixed `log 3`
in the exponent constant. -/
theorem add_one_le_logSquareEnvelope
    {a K x : ℝ} (hK : 0 ≤ K) (hx : 1 ≤ x)
    (ha : a ≤ logSquareEnvelope K x) :
    a + 1 ≤ logSquareEnvelope (Real.log 3 + K) x := by
  have hEone : 1 ≤ logSquareEnvelope K x :=
    one_le_logSquareEnvelope hK hx
  have htwo : (2 : ℝ) ≤ logSquareEnvelope (Real.log 3) x := by
    have heq : Real.log ((2 : ℝ) + 1) = Real.log 3 := by norm_num
    rw [← heq]
    exact le_logSquareEnvelope_log_add_one (by norm_num) hx
  calc
    a + 1 ≤ 2 * logSquareEnvelope K x := by linarith
    _ ≤ logSquareEnvelope (Real.log 3) x *
        logSquareEnvelope K x :=
      mul_le_mul_of_nonneg_right htwo (logSquareEnvelope_pos _ _).le
    _ = logSquareEnvelope (Real.log 3 + K) x :=
      logSquareEnvelope_mul _ _ _

/-- Exponent constant for one converted even term. -/
def sharpConvertedTermLogSquareConstant (s : ℕ) (Knorm Kfactor : ℝ) : ℝ :=
  Knorm + ((3 * s : ℕ) : ℝ) * (Real.log 3 + Kfactor)

theorem boundedConvertedTermNorm_le_logSquareEnvelope
    {s : ℕ} {sigmaNorm factor Knorm Kfactor x : ℝ}
    (hsigma : 0 ≤ sigmaNorm) (hfactor : 0 ≤ factor)
    (hKnorm : 0 ≤ Knorm) (hKfactor : 0 ≤ Kfactor) (hx : 1 ≤ x)
    (hsigmaBound : sigmaNorm ≤ logSquareEnvelope Knorm x)
    (hfactorBound : factor ≤ logSquareEnvelope Kfactor x) :
    boundedConvertedTermNorm s sigmaNorm factor ≤
      logSquareEnvelope
        (sharpConvertedTermLogSquareConstant s Knorm Kfactor) x := by
  have hsucc := add_one_le_logSquareEnvelope hKfactor hx hfactorBound
  have hpow : (factor + 1) ^ (3 * s) ≤
      logSquareEnvelope
        (((3 * s : ℕ) : ℝ) * (Real.log 3 + Kfactor)) x := by
    calc
      (factor + 1) ^ (3 * s) ≤
          logSquareEnvelope (Real.log 3 + Kfactor) x ^ (3 * s) :=
        pow_le_pow_left₀ (by linarith) hsucc _
      _ = logSquareEnvelope
          (((3 * s : ℕ) : ℝ) * (Real.log 3 + Kfactor)) x :=
        logSquareEnvelope_pow _ _ _
  unfold boundedConvertedTermNorm sharpConvertedTermLogSquareConstant
  exact mul_le_logSquareEnvelope hsigma (pow_nonneg (by linarith) _)
    hsigmaBound hpow

/-- Exponent constant for one full interval-error expansion certificate. -/
def sharpExpansionLogSquareConstant
    (s : ℕ) (Knorm Kcomparison Kfactor : ℝ) : ℝ :=
  let L := Real.log 3 + Kfactor
  (Knorm + ((2 * s : ℕ) : ℝ) * L) +
    (((s : ℝ) * L) + Kcomparison)

theorem boundedConversionExpansionBudget_le_logSquareEnvelope
    {s : ℕ} {sigmaNorm comparison factor Knorm Kcomparison Kfactor x : ℝ}
    (hsigma : 0 ≤ sigmaNorm) (hcomparison : 0 ≤ comparison)
    (hfactor : 0 ≤ factor)
    (hKnorm : 0 ≤ Knorm) (hKcomparison : 0 ≤ Kcomparison)
    (hKfactor : 0 ≤ Kfactor) (hx : 1 ≤ x)
    (hsigmaBound : sigmaNorm ≤ logSquareEnvelope Knorm x)
    (hcomparisonBound : comparison ≤ logSquareEnvelope Kcomparison x)
    (hfactorBound : factor ≤ logSquareEnvelope Kfactor x) :
    boundedConversionExpansionBudget s sigmaNorm comparison factor ≤
      logSquareEnvelope
        (sharpExpansionLogSquareConstant s Knorm Kcomparison Kfactor) x := by
  let L := Real.log 3 + Kfactor
  have hsucc := add_one_le_logSquareEnvelope hKfactor hx hfactorBound
  have hpow (s' : ℕ) : (factor + 1) ^ s' ≤
      logSquareEnvelope ((s' : ℝ) * L) x := by
    calc
      (factor + 1) ^ s' ≤ logSquareEnvelope L x ^ s' := by
        exact pow_le_pow_left₀ (by linarith) (by simpa [L] using hsucc) s'
      _ = logSquareEnvelope ((s' : ℝ) * L) x :=
        logSquareEnvelope_pow _ _ _
  have hcontext : boundedConversionContextBound s sigmaNorm factor ≤
      logSquareEnvelope (Knorm + ((2 * s : ℕ) : ℝ) * L) x := by
    unfold boundedConversionContextBound
    exact mul_le_logSquareEnvelope hsigma (pow_nonneg (by linarith) _)
      hsigmaBound (hpow (2 * s))
  have hproduct : boundedConversionProductBudget s comparison factor ≤
      logSquareEnvelope (((s : ℝ) * L) + Kcomparison) x := by
    unfold boundedConversionProductBudget
    exact mul_le_logSquareEnvelope (pow_nonneg (by linarith) _) hcomparison
      (hpow s) hcomparisonBound
  unfold boundedConversionExpansionBudget sharpExpansionLogSquareConstant
  dsimp [L]
  exact mul_le_logSquareEnvelope
    (mul_nonneg hsigma (pow_nonneg (by linarith) _))
    (mul_nonneg (pow_nonneg (by linarith) _) hcomparison)
    hcontext hproduct

/-- Exponent constant for the refined scalar comparison. -/
def sharpScalarLogSquareConstant
    (s : ℕ) (Kcertificate Knorm Kcomparison Kfactor : ℝ) : ℝ :=
  let KP := (s : ℝ) * (Real.log 3 + Kfactor)
  let KHP := KP + Kcomparison
  let KHT := KP + Kcomparison
  let K1 := Real.log 3 + (KP + Kcertificate) + (Knorm + KHP)
  let K2 := KP + K1
  let K3 := Real.log 3 + (KP + K2) + ((Knorm + 2 * KP) + KHT)
  KP + K3

theorem boundedSharpScalarBudget_le_logSquareEnvelope
    {s : ℕ}
    {sigmaCertificate sigmaNorm theta comparison factor
      Kcertificate Knorm Kcomparison Kfactor x : ℝ}
    (hcertificate : 0 ≤ sigmaCertificate) (hsigma : 0 ≤ sigmaNorm)
    (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hcomparison : 0 ≤ comparison) (hfactor : 0 ≤ factor)
    (hKcertificate : 0 ≤ Kcertificate) (hKnorm : 0 ≤ Knorm)
    (hKcomparison : 0 ≤ Kcomparison) (hKfactor : 0 ≤ Kfactor)
    (hx : 1 ≤ x)
    (hcertificateBound : sigmaCertificate ≤
      logSquareEnvelope Kcertificate x)
    (hsigmaBound : sigmaNorm ≤ logSquareEnvelope Knorm x)
    (hcomparisonBound : comparison ≤ logSquareEnvelope Kcomparison x)
    (hfactorBound : factor ≤ logSquareEnvelope Kfactor x) :
    boundedSharpScalarBudget s sigmaCertificate sigmaNorm theta
        comparison factor ≤
      logSquareEnvelope
        (sharpScalarLogSquareConstant s Kcertificate Knorm
          Kcomparison Kfactor) x := by
  let KP := (s : ℝ) * (Real.log 3 + Kfactor)
  let KHP := KP + Kcomparison
  let KHT := KP + Kcomparison
  let K1 := Real.log 3 + (KP + Kcertificate) + (Knorm + KHP)
  let K2 := KP + K1
  let K3 := Real.log 3 + (KP + K2) + ((Knorm + 2 * KP) + KHT)
  let P := (factor + 1) ^ s
  let HP := P * comparison
  let HT := P * (theta * comparison)
  let H1 := P * sigmaCertificate + sigmaNorm * HP
  let H2 := P * H1
  let H3 := P * H2 + (sigmaNorm * P ^ 2) * HT
  have hlog3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hKP : 0 ≤ KP := by dsimp [KP]; positivity
  have hKHP : 0 ≤ KHP := by dsimp [KHP]; positivity
  have hKHT : 0 ≤ KHT := by dsimp [KHT]; positivity
  have hK1 : 0 ≤ K1 := by dsimp [K1]; positivity
  have hK2 : 0 ≤ K2 := by dsimp [K2]; positivity
  have hK3 : 0 ≤ K3 := by dsimp [K3]; positivity
  have hsucc := add_one_le_logSquareEnvelope hKfactor hx hfactorBound
  have hP : P ≤ logSquareEnvelope KP x := by
    dsimp [P, KP]
    calc
      (factor + 1) ^ s ≤
          logSquareEnvelope (Real.log 3 + Kfactor) x ^ s :=
        pow_le_pow_left₀ (by linarith) hsucc s
      _ = logSquareEnvelope
          ((s : ℝ) * (Real.log 3 + Kfactor)) x :=
        logSquareEnvelope_pow _ _ _
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hHP : HP ≤ logSquareEnvelope KHP x := by
    dsimp [HP, KHP]
    exact mul_le_logSquareEnvelope hP0 hcomparison hP hcomparisonBound
  have hHP0 : 0 ≤ HP := mul_nonneg hP0 hcomparison
  have hthetaComparison : theta * comparison ≤
      logSquareEnvelope Kcomparison x := by
    calc
      theta * comparison ≤ 1 * comparison :=
        mul_le_mul_of_nonneg_right htheta1 hcomparison
      _ ≤ logSquareEnvelope Kcomparison x := by simpa using hcomparisonBound
  have hthetaComparison0 : 0 ≤ theta * comparison :=
    mul_nonneg htheta hcomparison
  have hHT : HT ≤ logSquareEnvelope KHT x := by
    dsimp [HT, KHT]
    exact mul_le_logSquareEnvelope hP0 hthetaComparison0 hP hthetaComparison
  have hHT0 : 0 ≤ HT := mul_nonneg hP0 hthetaComparison0
  have hH1 : H1 ≤ logSquareEnvelope K1 x := by
    dsimp [H1, K1]
    exact add_le_logSquareEnvelope
      (mul_nonneg hP0 hcertificate) (mul_nonneg hsigma hHP0)
      (add_nonneg hKP hKcertificate) (add_nonneg hKnorm hKHP) hx
      (mul_le_logSquareEnvelope hP0 hcertificate hP hcertificateBound)
      (mul_le_logSquareEnvelope hsigma hHP0 hsigmaBound hHP)
  have hH10 : 0 ≤ H1 := by
    dsimp [H1]
    exact add_nonneg (mul_nonneg hP0 hcertificate)
      (mul_nonneg hsigma hHP0)
  have hH2 : H2 ≤ logSquareEnvelope K2 x := by
    dsimp [H2, K2]
    exact mul_le_logSquareEnvelope hP0 hH10 hP hH1
  have hH20 : 0 ≤ H2 := mul_nonneg hP0 hH10
  have hP2 : P ^ 2 ≤ logSquareEnvelope (2 * KP) x := by
    calc
      P ^ 2 ≤ logSquareEnvelope KP x ^ 2 :=
        pow_le_pow_left₀ hP0 hP 2
      _ = logSquareEnvelope (2 * KP) x := by
        rw [logSquareEnvelope_pow]
        norm_num
  have hP20 : 0 ≤ P ^ 2 := sq_nonneg P
  have hright : (sigmaNorm * P ^ 2) * HT ≤
      logSquareEnvelope ((Knorm + 2 * KP) + KHT) x :=
    mul_le_logSquareEnvelope (mul_nonneg hsigma hP20) hHT0
      (mul_le_logSquareEnvelope hsigma hP20 hsigmaBound hP2) hHT
  have hright0 : 0 ≤ (sigmaNorm * P ^ 2) * HT :=
    mul_nonneg (mul_nonneg hsigma hP20) hHT0
  have hH3 : H3 ≤ logSquareEnvelope K3 x := by
    dsimp [H3, K3]
    exact add_le_logSquareEnvelope
      (mul_nonneg hP0 hH20) hright0
      (add_nonneg hKP hK2) (add_nonneg (add_nonneg hKnorm (mul_nonneg (by norm_num) hKP)) hKHT)
      hx (mul_le_logSquareEnvelope hP0 hH20 hP hH2) hright
  have hH30 : 0 ≤ H3 := by
    dsimp [H3]
    exact add_nonneg (mul_nonneg hP0 hH20) hright0
  unfold boundedSharpScalarBudget sharpScalarLogSquareConstant
  dsimp [P, HP, HT, H1, H2, H3, KP, KHP, KHT, K1, K2, K3] at hP hH3 ⊢
  exact mul_le_logSquareEnvelope hP0 hH30 hP hH3

/-- Exponent constant for one sharp odd expansion term. -/
def sharpOddTermLogSquareConstant
    (s : ℕ) (Kcertificate Knorm Kcomparison Kfactor : ℝ) : ℝ :=
  let Kexp := sharpExpansionLogSquareConstant s Knorm Kcomparison Kfactor
  let Kterm := sharpConvertedTermLogSquareConstant s Knorm Kfactor
  let Kscalar := sharpScalarLogSquareConstant s Kcertificate Knorm
    Kcomparison Kfactor
  let Kcount := Real.log (conversionSubsetCount s + 1)
  Real.log 3 + Kexp +
    (Real.log 3 + Kterm + (Kcount + Kscalar))

theorem boundedSharpOddTermBudget_le_logSquareEnvelope
    {s : ℕ}
    {sigmaCertificate sigmaNorm theta comparison factor
      Kcertificate Knorm Kcomparison Kfactor x : ℝ}
    (hcertificate : 0 ≤ sigmaCertificate) (hsigma : 0 ≤ sigmaNorm)
    (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hcomparison : 0 ≤ comparison) (hfactor : 0 ≤ factor)
    (hKcertificate : 0 ≤ Kcertificate) (hKnorm : 0 ≤ Knorm)
    (hKcomparison : 0 ≤ Kcomparison) (hKfactor : 0 ≤ Kfactor)
    (hx : 1 ≤ x)
    (hcertificateBound : sigmaCertificate ≤ logSquareEnvelope Kcertificate x)
    (hsigmaBound : sigmaNorm ≤ logSquareEnvelope Knorm x)
    (hcomparisonBound : comparison ≤ logSquareEnvelope Kcomparison x)
    (hfactorBound : factor ≤ logSquareEnvelope Kfactor x) :
    boundedSharpOddTermBudget s sigmaCertificate sigmaNorm theta
        comparison factor ≤
      logSquareEnvelope
        (sharpOddTermLogSquareConstant s Kcertificate Knorm
          Kcomparison Kfactor) x := by
  let Kexp := sharpExpansionLogSquareConstant s Knorm Kcomparison Kfactor
  let Kterm := sharpConvertedTermLogSquareConstant s Knorm Kfactor
  let Kscalar := sharpScalarLogSquareConstant s Kcertificate Knorm
    Kcomparison Kfactor
  let Kcount := Real.log (conversionSubsetCount s + 1)
  have hlog3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hKexp : 0 ≤ Kexp := by dsimp [Kexp, sharpExpansionLogSquareConstant]; positivity
  have hKterm : 0 ≤ Kterm := by dsimp [Kterm, sharpConvertedTermLogSquareConstant]; positivity
  have hKscalar : 0 ≤ Kscalar := by dsimp [Kscalar, sharpScalarLogSquareConstant]; positivity
  have hcount0 : 0 ≤ conversionSubsetCount s := by
    unfold conversionSubsetCount; positivity
  have hKcount : 0 ≤ Kcount := by
    dsimp [Kcount]
    exact Real.log_nonneg (by linarith)
  have hcount : conversionSubsetCount s ≤ logSquareEnvelope Kcount x := by
    dsimp [Kcount]
    exact le_logSquareEnvelope_log_add_one hcount0 hx
  have hexp := boundedConversionExpansionBudget_le_logSquareEnvelope (s := s)
    hsigma hcomparison hfactor hKnorm hKcomparison hKfactor hx
    hsigmaBound hcomparisonBound hfactorBound
  have hterm := boundedConvertedTermNorm_le_logSquareEnvelope (s := s)
    hsigma hfactor hKnorm hKfactor hx hsigmaBound hfactorBound
  have hscalar := boundedSharpScalarBudget_le_logSquareEnvelope (s := s)
    hcertificate hsigma htheta htheta1 hcomparison hfactor
    hKcertificate hKnorm hKcomparison hKfactor hx
    hcertificateBound hsigmaBound hcomparisonBound hfactorBound
  have hscalar0 : 0 ≤ boundedSharpScalarBudget s sigmaCertificate sigmaNorm
      theta comparison factor := by
    unfold boundedSharpScalarBudget
    positivity
  have hcountScalar := mul_le_logSquareEnvelope hcount0 hscalar0
    hcount hscalar
  have hpure0 : 0 ≤ boundedSharpPureThetaBudget s sigmaNorm factor := by
    unfold boundedSharpPureThetaBudget boundedConvertedTermNorm
    positivity
  have hinner := add_le_logSquareEnvelope
    hpure0
    (mul_nonneg hcount0 hscalar0) hKterm (add_nonneg hKcount hKscalar)
    hx (by simpa [boundedSharpPureThetaBudget] using hterm) hcountScalar
  have hexp0 : 0 ≤ boundedConversionExpansionBudget s sigmaNorm comparison factor := by
    unfold boundedConversionExpansionBudget boundedConversionContextBound
      boundedConversionProductBudget
    positivity
  have hinner0 : 0 ≤ boundedSharpPureThetaBudget s sigmaNorm factor +
      conversionSubsetCount s * boundedSharpScalarBudget s sigmaCertificate
        sigmaNorm theta comparison factor := by
    exact add_nonneg
      hpure0
      (mul_nonneg hcount0 hscalar0)
  unfold boundedSharpOddTermBudget sharpOddTermLogSquareConstant
  dsimp [Kexp, Kterm, Kscalar, Kcount]
  exact add_le_logSquareEnvelope hexp0 hinner0 hKexp
    (add_nonneg (add_nonneg hlog3 hKterm)
      (add_nonneg hKcount hKscalar)) hx hexp hinner

/-- Exponent constants for the even aggregate and theta absorption. -/
def sharpEvenLogSquareConstant (s : ℕ) (Knorm Kfactor : ℝ) : ℝ :=
  let Kcount := Real.log (conversionSubsetCount s + 1)
  Kcount + (Kcount + sharpConvertedTermLogSquareConstant s Knorm Kfactor)

def sharpThetaAbsorptionLogSquareConstant
    (s : ℕ) (Knorm Kfactor : ℝ) : ℝ :=
  let Kcount := Real.log (conversionSubsetCount s + 1)
  let Kpair := Real.log ((oddPairCount s : ℝ) + 1)
  let Kterm := sharpConvertedTermLogSquareConstant s Knorm Kfactor
  let Keven := sharpEvenLogSquareConstant s Knorm Kfactor
  Real.log 3 + (Kcount + (Kpair + Kterm)) + (Kpair + Keven)

def sharpConvertedOddLogSquareConstant
    (s : ℕ) (Kcertificate Knorm Kcomparison Kfactor : ℝ) : ℝ :=
  let Kcount := Real.log (conversionSubsetCount s + 1)
  let Kodd := sharpOddTermLogSquareConstant s Kcertificate Knorm
    Kcomparison Kfactor
  let Ktheta := sharpThetaAbsorptionLogSquareConstant s Knorm Kfactor
  Real.log 3 + (Kcount + (Kcount + Kodd)) + Ktheta

theorem boundedConvertedEvenNorm_le_logSquareEnvelope
    {s : ℕ} {sigmaNorm factor Knorm Kfactor x : ℝ}
    (hsigma : 0 ≤ sigmaNorm) (hfactor : 0 ≤ factor)
    (hKnorm : 0 ≤ Knorm) (hKfactor : 0 ≤ Kfactor) (hx : 1 ≤ x)
    (hsigmaBound : sigmaNorm ≤ logSquareEnvelope Knorm x)
    (hfactorBound : factor ≤ logSquareEnvelope Kfactor x) :
    boundedConvertedEvenNorm s sigmaNorm factor ≤
      logSquareEnvelope (sharpEvenLogSquareConstant s Knorm Kfactor) x := by
  let Kcount := Real.log (conversionSubsetCount s + 1)
  let Kterm := sharpConvertedTermLogSquareConstant s Knorm Kfactor
  have hcount0 : 0 ≤ conversionSubsetCount s := by
    unfold conversionSubsetCount; positivity
  have hcount : conversionSubsetCount s ≤ logSquareEnvelope Kcount x := by
    dsimp [Kcount]
    exact le_logSquareEnvelope_log_add_one hcount0 hx
  have hterm := boundedConvertedTermNorm_le_logSquareEnvelope (s := s)
    hsigma hfactor hKnorm hKfactor hx hsigmaBound hfactorBound
  have hterm0 : 0 ≤ boundedConvertedTermNorm s sigmaNorm factor := by
    unfold boundedConvertedTermNorm
    positivity
  unfold boundedConvertedEvenNorm sharpEvenLogSquareConstant
  dsimp [Kcount, Kterm]
  exact mul_le_logSquareEnvelope hcount0 (mul_nonneg hcount0 hterm0) hcount
    (mul_le_logSquareEnvelope hcount0 hterm0 hcount hterm)

theorem boundedSharpThetaAbsorptionBudget_le_logSquareEnvelope
    {s : ℕ} {sigmaNorm theta factor Knorm Kfactor x : ℝ}
    (hsigma : 0 ≤ sigmaNorm) (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hfactor : 0 ≤ factor) (hKnorm : 0 ≤ Knorm)
    (hKfactor : 0 ≤ Kfactor) (hx : 1 ≤ x)
    (hsigmaBound : sigmaNorm ≤ logSquareEnvelope Knorm x)
    (hfactorBound : factor ≤ logSquareEnvelope Kfactor x) :
    boundedSharpThetaAbsorptionBudget s sigmaNorm theta factor ≤
      logSquareEnvelope
        (sharpThetaAbsorptionLogSquareConstant s Knorm Kfactor) x := by
  let Kcount := Real.log (conversionSubsetCount s + 1)
  let Kpair := Real.log ((oddPairCount s : ℝ) + 1)
  let Kterm := sharpConvertedTermLogSquareConstant s Knorm Kfactor
  let Keven := sharpEvenLogSquareConstant s Knorm Kfactor
  have hcount0 : 0 ≤ conversionSubsetCount s := by
    unfold conversionSubsetCount; positivity
  have hpair0 : 0 ≤ (oddPairCount s : ℝ) := by positivity
  have hthetaCoeff0 : 0 ≤ sharpThetaCoefficient s theta := by
    unfold sharpThetaCoefficient
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
  have hKeven : 0 ≤ Keven := by
    dsimp [Keven, sharpEvenLogSquareConstant]
    positivity
  have hcount : conversionSubsetCount s ≤ logSquareEnvelope Kcount x := by
    dsimp [Kcount]
    exact le_logSquareEnvelope_log_add_one hcount0 hx
  have hpair : (oddPairCount s : ℝ) ≤ logSquareEnvelope Kpair x := by
    dsimp [Kpair]
    exact le_logSquareEnvelope_log_add_one hpair0 hx
  have hthetaCoeff : sharpThetaCoefficient s theta ≤
      logSquareEnvelope Kpair x := by
    unfold sharpThetaCoefficient
    calc
      (oddPairCount s : ℝ) * theta ≤ (oddPairCount s : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left htheta1 hpair0
      _ ≤ logSquareEnvelope Kpair x := by simpa using hpair
  have hterm := boundedConvertedTermNorm_le_logSquareEnvelope (s := s)
    hsigma hfactor hKnorm hKfactor hx hsigmaBound hfactorBound
  have heven := boundedConvertedEvenNorm_le_logSquareEnvelope (s := s)
    hsigma hfactor hKnorm hKfactor hx hsigmaBound hfactorBound
  have hterm0 : 0 ≤ boundedConvertedTermNorm s sigmaNorm factor := by
    unfold boundedConvertedTermNorm
    positivity
  have heven0 : 0 ≤ boundedConvertedEvenNorm s sigmaNorm factor := by
    unfold boundedConvertedEvenNorm boundedConvertedTermNorm
    positivity
  have hleft := mul_le_logSquareEnvelope hcount0
    (mul_nonneg hthetaCoeff0 hterm0) hcount
    (mul_le_logSquareEnvelope hthetaCoeff0 hterm0 hthetaCoeff hterm)
  have hright := mul_le_logSquareEnvelope hthetaCoeff0 heven0
    hthetaCoeff heven
  unfold boundedSharpThetaAbsorptionBudget
    sharpThetaAbsorptionLogSquareConstant
  dsimp [Kcount, Kpair, Kterm, Keven]
  exact add_le_logSquareEnvelope
    (mul_nonneg hcount0 (mul_nonneg hthetaCoeff0 hterm0))
    (mul_nonneg hthetaCoeff0 heven0)
    (add_nonneg hKcount (add_nonneg hKpair hKterm))
    (add_nonneg hKpair hKeven)
    hx hleft hright

theorem boundedSharpConvertedOddBudget_le_logSquareEnvelope
    {s : ℕ}
    {sigmaCertificate sigmaNorm theta comparison factor
      Kcertificate Knorm Kcomparison Kfactor x : ℝ}
    (hcertificate : 0 ≤ sigmaCertificate) (hsigma : 0 ≤ sigmaNorm)
    (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hcomparison : 0 ≤ comparison) (hfactor : 0 ≤ factor)
    (hKcertificate : 0 ≤ Kcertificate) (hKnorm : 0 ≤ Knorm)
    (hKcomparison : 0 ≤ Kcomparison) (hKfactor : 0 ≤ Kfactor)
    (hx : 1 ≤ x)
    (hcertificateBound : sigmaCertificate ≤ logSquareEnvelope Kcertificate x)
    (hsigmaBound : sigmaNorm ≤ logSquareEnvelope Knorm x)
    (hcomparisonBound : comparison ≤ logSquareEnvelope Kcomparison x)
    (hfactorBound : factor ≤ logSquareEnvelope Kfactor x) :
    boundedSharpConvertedOddBudget s sigmaNorm theta factor
        (boundedSharpOddTermBudget s sigmaCertificate sigmaNorm theta
          comparison factor) ≤
      logSquareEnvelope
        (sharpConvertedOddLogSquareConstant s Kcertificate Knorm
          Kcomparison Kfactor) x := by
  let Kcount := Real.log (conversionSubsetCount s + 1)
  let Kodd := sharpOddTermLogSquareConstant s Kcertificate Knorm
    Kcomparison Kfactor
  let Ktheta := sharpThetaAbsorptionLogSquareConstant s Knorm Kfactor
  have hcount0 : 0 ≤ conversionSubsetCount s := by
    unfold conversionSubsetCount; positivity
  have hcount : conversionSubsetCount s ≤ logSquareEnvelope Kcount x := by
    dsimp [Kcount]
    exact le_logSquareEnvelope_log_add_one hcount0 hx
  have hKcount : 0 ≤ Kcount := by
    dsimp [Kcount]
    exact Real.log_nonneg (by linarith)
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hKexp : 0 ≤
      sharpExpansionLogSquareConstant s Knorm Kcomparison Kfactor := by
    dsimp [sharpExpansionLogSquareConstant]
    positivity
  have hKterm : 0 ≤ sharpConvertedTermLogSquareConstant s Knorm Kfactor := by
    dsimp [sharpConvertedTermLogSquareConstant]
    positivity
  have hKscalar : 0 ≤
      sharpScalarLogSquareConstant s Kcertificate Knorm Kcomparison Kfactor := by
    dsimp [sharpScalarLogSquareConstant]
    positivity
  have hKodd : 0 ≤ Kodd := by
    dsimp [Kodd, sharpOddTermLogSquareConstant]
    exact add_nonneg (add_nonneg hlog3 hKexp)
      (add_nonneg (add_nonneg hlog3 hKterm)
        (add_nonneg hKcount hKscalar))
  have hpair0 : 0 ≤ (oddPairCount s : ℝ) := by positivity
  have hKpair : 0 ≤ Real.log ((oddPairCount s : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  have hKeven : 0 ≤ sharpEvenLogSquareConstant s Knorm Kfactor := by
    dsimp [sharpEvenLogSquareConstant]
    exact add_nonneg hKcount (add_nonneg hKcount hKterm)
  have hKtheta : 0 ≤ Ktheta := by
    dsimp [Ktheta, sharpThetaAbsorptionLogSquareConstant]
    exact add_nonneg
      (add_nonneg hlog3 (add_nonneg hKcount (add_nonneg hKpair hKterm)))
      (add_nonneg hKpair hKeven)
  have hodd := boundedSharpOddTermBudget_le_logSquareEnvelope (s := s)
    hcertificate hsigma htheta htheta1 hcomparison hfactor
    hKcertificate hKnorm hKcomparison hKfactor hx
    hcertificateBound hsigmaBound hcomparisonBound hfactorBound
  have hodd0 : 0 ≤ boundedSharpOddTermBudget s sigmaCertificate sigmaNorm
      theta comparison factor := by
    unfold boundedSharpOddTermBudget boundedConversionExpansionBudget
      boundedConversionContextBound boundedConversionProductBudget
      boundedSharpPureThetaBudget boundedConvertedTermNorm
      boundedSharpScalarBudget
    positivity
  have hconverted := mul_le_logSquareEnvelope hcount0
    (mul_nonneg hcount0 hodd0) hcount
    (mul_le_logSquareEnvelope hcount0 hodd0 hcount hodd)
  have htheta := boundedSharpThetaAbsorptionBudget_le_logSquareEnvelope (s := s)
    hsigma htheta htheta1 hfactor hKnorm hKfactor hx
    hsigmaBound hfactorBound
  have htheta0 : 0 ≤ boundedSharpThetaAbsorptionBudget s sigmaNorm theta factor := by
    unfold boundedSharpThetaAbsorptionBudget sharpThetaCoefficient
      boundedConvertedEvenNorm boundedConvertedTermNorm
    positivity
  unfold boundedSharpConvertedOddBudget boundedConvertedOddBudget
    sharpConvertedOddLogSquareConstant
  dsimp [Kcount, Kodd, Ktheta]
  exact add_le_logSquareEnvelope
    (mul_nonneg hcount0 (mul_nonneg hcount0 hodd0)) htheta0
    (add_nonneg hKcount (add_nonneg hKcount hKodd)) hKtheta
    hx hconverted htheta

/-- Exponent constant for the final absorption and denominator assembly. -/
def sharpFinalBudgetLogSquareConstant (Kodd Keven Kdenominator : ℝ) : ℝ :=
  Real.log 3 +
    (Real.log 3 + (Real.log 3 + Kodd + Keven)) + Kdenominator

theorem boundedSharpRefutationBudget_le_logSquareEnvelope
    {beta odd even denominator Kodd Keven Kdenominator x : ℝ}
    (hbeta0 : 0 ≤ beta) (hbetaHalf : beta ≤ 1 / 2)
    (hodd0 : 0 ≤ odd) (heven0 : 0 ≤ even) (hdenominator0 : 0 ≤ denominator)
    (hKodd : 0 ≤ Kodd) (hKeven : 0 ≤ Keven)
    (hKdenominator : 0 ≤ Kdenominator) (hx : 1 ≤ x)
    (hodd : odd ≤ logSquareEnvelope Kodd x)
    (heven : even ≤ logSquareEnvelope Keven x)
    (hdenominator : denominator ≤ logSquareEnvelope Kdenominator x) :
    boundedSharpRefutationBudget beta odd even denominator ≤
      logSquareEnvelope
        (sharpFinalBudgetLogSquareConstant Kodd Keven Kdenominator) x := by
  have honeMinus : 1 / 2 ≤ 1 - beta := by linarith
  have honeMinusPos : 0 < 1 - beta := by linarith
  have hinv : (1 - beta)⁻¹ ≤ 2 := by
    exact (inv_le_iff_one_le_mul₀' honeMinusPos).2 (by nlinarith)
  have hinv0 : 0 ≤ (1 - beta)⁻¹ := inv_nonneg.mpr honeMinusPos.le
  have htwo : (2 : ℝ) ≤ logSquareEnvelope (Real.log 3) x := by
    have heq : Real.log ((2 : ℝ) + 1) = Real.log 3 := by norm_num
    rw [← heq]
    exact le_logSquareEnvelope_log_add_one (by norm_num) hx
  have hsum := add_le_logSquareEnvelope hodd0 heven0 hKodd hKeven hx hodd heven
  have hsum0 : 0 ≤ odd + even := add_nonneg hodd0 heven0
  have hscaled := mul_le_logSquareEnvelope hinv0 hsum0
    (hinv.trans htwo) hsum
  have hKscaled : 0 ≤ Real.log 3 + (Real.log 3 + Kodd + Keven) := by
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)]
  unfold boundedSharpRefutationBudget sharpFinalBudgetLogSquareConstant
  exact add_le_logSquareEnvelope (mul_nonneg hinv0 hsum0) hdenominator0
    hKscaled
    hKdenominator hx hscaled hdenominator

end OptimalConvergenceRates.GeneralArchimedean

end
