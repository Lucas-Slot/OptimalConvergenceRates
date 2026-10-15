/-
  Coefficient-tracked aggregation for the sharp two-channel conversion.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpBoundedConversion

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

variable {n m : ℕ}

/-- Budget for the pure-theta comparison in one odd pair. -/
def boundedSharpPureThetaBudget
    (s : ℕ) (sigmaNormBound factorBound : ℝ) : ℝ :=
  boundedConvertedTermNorm s sigmaNormBound factorBound

/-- The no-delta term of an odd pair is bounded by the corresponding
theta multiple, with an explicit SOS free-term certificate. -/
theorem bounded_refinedErrorBoundTerm_empty_le_theta_zero_at
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    {d : ℕ} {G HsigmaNorm : ℝ}
    (hsigma : ∀ I, IsSOS (sigma I))
    (hsigmaDegree : ∀ I, (sigma I).totalDegree ≤ d)
    (hsigmaNorm : ∀ I, coeffL1Norm (sigma I) ≤ HsigmaNorm)
    (hHsigmaNorm : 0 ≤ HsigmaNorm)
    (haDegree : ∀ i, (a i).totalDegree ≤ d)
    (haNorm : ∀ i, coeffL1Norm (a i) ≤ G)
    (hG : 1 ≤ G) (hδ : 0 < δ)
    (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (B' : ℝ) (I K : Finset (Fin s))
    (hKI : K ⊆ I) (hKodd : ¬ Even K.card) :
    Nonempty (BoundedModuleLEAt g
      (d + 3 * s * conversionFactorDegree pkg d)
      (boundedSharpPureThetaBudget s HsigmaNorm
        (conversionFactorCoefficientBound pkg B' G))
      (refinedErrorBoundTerm (fun _ => pkg) a sigma I K ∅)
      (C theta * zeroErrorTerm (fun _ => pkg) a sigma I)) := by
  let F := conversionFactorDegree pkg d
  let Z := zeroErrorTerm (fun _ => pkg) a sigma I
  let Kfactor := conversionFactorCoefficientBound pkg B' G
  let Hterm := boundedConvertedTermNorm s HsigmaNorm Kfactor
  have hodd : Odd K.card := Nat.not_even_iff_odd.mp hKodd
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hodd.pos.ne'
  have hpow : theta ^ K.card ≤ theta := by
    rw [hj, pow_succ']
    exact (mul_le_mul_of_nonneg_left
      (pow_le_one₀ htheta htheta1) htheta).trans_eq (mul_one theta)
  have hgap : 0 ≤ theta - theta ^ K.card := sub_nonneg.mpr hpow
  have hgapOne : theta - theta ^ K.card ≤ 1 := by
    have hpow0 : 0 ≤ theta ^ K.card := pow_nonneg htheta _
    linarith
  have hZSOS : IsSOS Z := by
    dsimp [Z, zeroErrorTerm]
    exact errorExpansionTerm_isSOS (fun _ => pkg) a sigma hsigma hδ I ∅
  have hZDegree : Z.totalDegree ≤ d + 3 * s * F := by
    dsimp [Z, zeroErrorTerm]
    exact errorExpansionTerm_totalDegree_le pkg a sigma
      hsigmaDegree haDegree I ∅
  have hZNorm : coeffL1Norm Z ≤ Hterm := by
    dsimp [Z, zeroErrorTerm, Hterm, Kfactor]
    exact errorExpansionTerm_coeffL1Norm_le pkg a sigma
      hsigmaNorm hHsigmaNorm haNorm hG B' I ∅
  have hdiffSOS : IsSOS (C (theta - theta ^ K.card) * Z) :=
    IsSOS_mul (IsSOS_C_nonneg _ hgap) hZSOS
  have hdiffDegree :
      (C (theta - theta ^ K.card) * Z).totalDegree ≤
        d + 3 * s * F :=
    (mv_C_mul_totalDegree_le _ Z).trans hZDegree
  let cRaw := BoundedQuadraticModuleCertificate.ofSOS g
    (C (theta - theta ^ K.card) * Z) hdiffSOS hdiffDegree
  have hdiffNorm :
      coeffL1Norm (C (theta - theta ^ K.card) * Z) ≤ Hterm := by
    calc
      _ ≤ |theta - theta ^ K.card| * coeffL1Norm Z :=
        coeffL1Norm_C_mul_le _ _
      _ = (theta - theta ^ K.card) * coeffL1Norm Z := by
        rw [abs_of_nonneg hgap]
      _ ≤ 1 * Hterm := by
        exact mul_le_mul hgapOne hZNorm (coeffL1Norm_nonneg Z)
          (by positivity)
      _ = Hterm := one_mul _
  have c : BoundedModuleLEAt g (d + 3 * s * F) Hterm
      (C (theta ^ K.card) * Z) (C theta * Z) := by
    exact (cRaw.weakenBound hdiffNorm).congr (by
      rw [map_sub]
      ring)
  rw [refinedErrorBoundTerm_empty (fun _ => pkg) a sigma I K hKI]
  exact ⟨by simpa [F, Z, Hterm, Kfactor, boundedSharpPureThetaBudget] using c⟩

/-- Budget for one complete odd expansion term in the sharp comparison. -/
def boundedSharpOddTermBudget
    (s : ℕ) (sigmaCertificateBound sigmaNormBound theta
      comparisonBound factorBound : ℝ) : ℝ :=
  boundedConversionExpansionBudget s sigmaNormBound comparisonBound factorBound +
    (boundedSharpPureThetaBudget s sigmaNormBound factorBound +
      conversionSubsetCount s *
        boundedSharpScalarBudget s sigmaCertificateBound sigmaNormBound
          theta comparisonBound factorBound)

/-- A single odd expansion term satisfies the sharp pair comparison with an
explicit coefficient budget. -/
theorem bounded_errorExpansionTerm_le_sharpPairBound_at
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta H B' : ℝ} (pkg : Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    {d rSigma rA rB : ℕ}
    {Ha Hb G HsigmaNorm HsigmaCert : ℝ}
    (hsigma : ∀ I, IsSOS (sigma I))
    (hsigmaDegree : ∀ I, (sigma I).totalDegree ≤ d)
    (hsigmaNorm : ∀ I, coeffL1Norm (sigma I) ≤ HsigmaNorm)
    (hHsigmaNorm : 0 ≤ HsigmaNorm)
    (csigma : ∀ I, BoundedModuleLEAt g rSigma HsigmaCert
      (sigma I) (C H))
    (hHa : 0 ≤ Ha) (hHb : 0 ≤ Hb)
    (ca : ∀ i, BoundedQuadraticModuleCertificate g (a i) rA Ha)
    (cBa : ∀ i, BoundedQuadraticModuleCertificate g (C B - a i) rB Hb)
    (haDegree : ∀ i, (a i).totalDegree ≤ d)
    (haNorm : ∀ i, coeffL1Norm (a i) ≤ G)
    (hG : 1 ≤ G) (hδ : 0 < δ) (hB : 1 ≤ B)
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hB' : 0 ≤ B')
    (hBcondition : B + δ ≤ (1 - theta) * B')
    (I K : Finset (Fin s)) (hKI : K ⊆ I)
    (hKodd : ¬ Even K.card) :
    Nonempty (BoundedModuleLEAt g
      (conversionSharpOddTermOrder pkg s d rSigma rA rB)
      (boundedSharpOddTermBudget s HsigmaCert HsigmaNorm theta
        (conversionIntervalCertificateBound pkg B' G Ha Hb)
        (conversionFactorCoefficientBound pkg B' G))
      (errorExpansionTerm (fun _ => pkg) a sigma I K)
      (C theta * zeroErrorTerm (fun _ => pkg) a sigma I +
        ∑ L ∈ K.powerset.erase ∅,
          C (refinedRemainderCoefficient H B' theta δ I K L) *
            denominatorProduct (fun _ => pkg) a)) := by
  classical
  let Rexp := conversionExpansionOrder pkg s d rA rB
  let RE := d + 3 * s * conversionFactorDegree pkg d
  let RS := conversionSharpScalarTermOrder pkg s d rSigma rA rB
  let Hint := conversionIntervalCertificateBound pkg B' G Ha Hb
  let Kfactor := conversionFactorCoefficientBound pkg B' G
  let Hexp := boundedConversionExpansionBudget s HsigmaNorm Hint Kfactor
  let Hpure := boundedSharpPureThetaBudget s HsigmaNorm Kfactor
  let Hscalar := boundedSharpScalarBudget s HsigmaCert HsigmaNorm theta
    Hint Kfactor
  let Csub := conversionSubsetCount s
  obtain ⟨cexp⟩ := bounded_errorExpansionTerm_le_errorBoundTerm_at
    pkg a sigma hsigma hsigmaDegree hsigmaNorm hHsigmaNorm (B' := B') hHa hHb
    ca cBa haDegree haNorm hG hδ hB htheta I K
  obtain ⟨cpure⟩ :=
    bounded_refinedErrorBoundTerm_empty_le_theta_zero_at
      (g := g) pkg a sigma hsigma hsigmaDegree hsigmaNorm hHsigmaNorm
      haDegree haNorm hG hδ htheta (le_of_lt htheta1) B' I K hKI hKodd
  have hHscalar : 0 ≤ Hscalar := by
    dsimp [Hscalar, boundedSharpScalarBudget, Hint, Kfactor]
    have hcert : 0 ≤ HsigmaCert := (csigma ∅).bound_nonneg
    have hfactor := conversionFactorCoefficientBound_nonneg pkg B' G
    have hinter := conversionIntervalCertificateBound_nonneg
      pkg B' hB hG hHa hHb
    positivity
  obtain ⟨cremRaw⟩ := BoundedModuleLEAt.sum_nonempty
    (K.powerset.erase ∅)
    (fun L => refinedErrorBoundTerm (fun _ => pkg) a sigma I K L)
    (fun L => C (refinedRemainderCoefficient H B' theta δ I K L) *
      denominatorProduct (fun _ => pkg) a)
    (fun L hL => by
      have hLK : L ⊆ K :=
        Finset.mem_powerset.mp (Finset.mem_erase.mp hL).2
      obtain ⟨c⟩ :=
        bounded_refinedErrorBoundTerm_le_refinedScalarBoundTerm_at
          pkg a sigma hsigma hsigmaDegree hsigmaNorm hHsigmaNorm
          csigma hHa hHb ca cBa haDegree haNorm hG hδ hB
          htheta htheta1 hB' hBcondition I K L
      rw [refinedScalarBoundTerm_eq_coefficient_mul_denominator
        (fun _ => pkg) a H B' I K L hKI hLK] at c
      exact ⟨c⟩)
  have hcardNat : (K.powerset.erase ∅).card ≤
      (Finset.univ : Finset (Finset (Fin s))).card := by
    apply Finset.card_le_card
    intro L hL
    exact Finset.mem_univ L
  have hcard :
      ((K.powerset.erase ∅).card : ℝ) ≤ Csub := by
    dsimp [Csub, conversionSubsetCount]
    exact_mod_cast hcardNat
  let crem : BoundedModuleLEAt g RS (Csub * Hscalar)
      (∑ L ∈ K.powerset.erase ∅,
        refinedErrorBoundTerm (fun _ => pkg) a sigma I K L)
      (∑ L ∈ K.powerset.erase ∅,
        C (refinedRemainderCoefficient H B' theta δ I K L) *
          denominatorProduct (fun _ => pkg) a) :=
    cremRaw.weakenBound (mul_le_mul_of_nonneg_right hcard hHscalar)
  have cboundRaw := cpure.add crem
  have hsplit :
      errorBoundTerm (fun _ => pkg) a sigma I K =
        refinedErrorBoundTerm (fun _ => pkg) a sigma I K ∅ +
          ∑ L ∈ K.powerset.erase ∅,
            refinedErrorBoundTerm (fun _ => pkg) a sigma I K L := by
    rw [errorBoundTerm_eq_sum_refined]
    have hempty : (∅ : Finset (Fin s)) ∈ K.powerset := by simp
    calc
      ∑ L ∈ K.powerset,
          refinedErrorBoundTerm (fun _ => pkg) a sigma I K L =
          (∑ L ∈ K.powerset.erase ∅,
            refinedErrorBoundTerm (fun _ => pkg) a sigma I K L) +
              refinedErrorBoundTerm (fun _ => pkg) a sigma I K ∅ :=
        (Finset.sum_erase_add K.powerset
          (fun L => refinedErrorBoundTerm (fun _ => pkg) a sigma I K L)
          hempty).symm
      _ = _ := add_comm _ _
  let cbound : BoundedModuleLEAt g (max RE RS)
      (Hpure + Csub * Hscalar)
      (errorBoundTerm (fun _ => pkg) a sigma I K)
      (C theta * zeroErrorTerm (fun _ => pkg) a sigma I +
        ∑ L ∈ K.powerset.erase ∅,
          C (refinedRemainderCoefficient H B' theta δ I K L) *
            denominatorProduct (fun _ => pkg) a) := by
    change BoundedQuadraticModuleCertificate g
      ((C theta * zeroErrorTerm (fun _ => pkg) a sigma I +
          ∑ L ∈ K.powerset.erase ∅,
            C (refinedRemainderCoefficient H B' theta δ I K L) *
              denominatorProduct (fun _ => pkg) a) -
        errorBoundTerm (fun _ => pkg) a sigma I K) _ _
    rw [hsplit]
    simpa [RE, RS, Hpure, Hscalar, Csub] using cboundRaw
  have cfinal := cexp.trans cbound
  exact ⟨by
    simpa [conversionSharpOddTermOrder, boundedSharpOddTermBudget,
      Rexp, RE, RS, Hint, Kfactor, Hexp, Hpure, Hscalar, Csub]
      using cfinal⟩
/-- The positive-even remainder has the same coarse coefficient envelope as
the complete even aggregate. -/
theorem convertedPositiveEven_coeffL1Norm_le
    {s : ℕ} {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    {G HsigmaNorm : ℝ}
    (hsigmaNorm : ∀ I, coeffL1Norm (sigma I) ≤ HsigmaNorm)
    (hHsigmaNorm : 0 ≤ HsigmaNorm)
    (haNorm : ∀ i, coeffL1Norm (a i) ≤ G)
    (hG : 1 ≤ G) (B' : ℝ) :
    coeffL1Norm (convertedPositiveEven (fun _ => pkg) a sigma) ≤
      boundedConvertedEvenNorm s HsigmaNorm
        (conversionFactorCoefficientBound pkg B' G) := by
  classical
  let Sall : Finset (Finset (Fin s)) :=
    (Finset.univ : Finset (Fin s)).powerset
  let Kfactor := conversionFactorCoefficientBound pkg B' G
  let HT := boundedConvertedTermNorm s HsigmaNorm Kfactor
  have hKfactor : 0 ≤ Kfactor := by
    dsimp [Kfactor]
    exact conversionFactorCoefficientBound_nonneg pkg B' G
  have hHT : 0 ≤ HT := by
    dsimp [HT, boundedConvertedTermNorm]
    exact mul_nonneg hHsigmaNorm (pow_nonneg (by linarith) _)
  unfold convertedPositiveEven
  calc
    coeffL1Norm
        (∑ I ∈ Sall,
          ∑ K ∈ (I.powerset.filter (fun K => Even K.card)).erase ∅,
            errorExpansionTerm (fun _ => pkg) a sigma I K) ≤
        ∑ I ∈ Sall,
          coeffL1Norm
            (∑ K ∈ (I.powerset.filter (fun K => Even K.card)).erase ∅,
              errorExpansionTerm (fun _ => pkg) a sigma I K) :=
      coeffL1Norm_sum_le Sall _
    _ ≤ ∑ _I ∈ Sall, (Sall.card : ℝ) * HT := by
      apply Finset.sum_le_sum
      intro I hI
      calc
        coeffL1Norm
            (∑ K ∈ (I.powerset.filter (fun K => Even K.card)).erase ∅,
              errorExpansionTerm (fun _ => pkg) a sigma I K) ≤
            ∑ K ∈ (I.powerset.filter (fun K => Even K.card)).erase ∅,
              coeffL1Norm (errorExpansionTerm (fun _ => pkg) a sigma I K) :=
          coeffL1Norm_sum_le _ _
        _ ≤ ∑ _K ∈ (I.powerset.filter (fun K => Even K.card)).erase ∅,
              HT :=
          Finset.sum_le_sum fun K hK =>
            errorExpansionTerm_coeffL1Norm_le pkg a sigma
              hsigmaNorm hHsigmaNorm haNorm hG B' I K
        _ ≤ (Sall.card : ℝ) * HT := by
          rw [Finset.sum_const, nsmul_eq_mul]
          have hsubset :
              (I.powerset.filter (fun K => Even K.card)).erase ∅ ⊆
                Sall := by
            intro K hK
            have hKI : K ⊆ I := Finset.mem_powerset.mp
              (Finset.mem_filter.mp (Finset.mem_erase.mp hK).2).1
            have hIuniv : I ⊆ (Finset.univ : Finset (Fin s)) :=
              Finset.mem_powerset.mp hI
            exact Finset.mem_powerset.mpr (hKI.trans hIuniv)
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast Finset.card_le_card hsubset) hHT
    _ = (Sall.card : ℝ) * ((Sall.card : ℝ) * HT) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = boundedConvertedEvenNorm s HsigmaNorm Kfactor := by
      simp [boundedConvertedEvenNorm, conversionSubsetCount, Sall, HT]

/-- Coefficient budget for replacing the summed pure-theta terms by the
uniform theta multiple of the complete converted-even polynomial. -/
def boundedSharpThetaAbsorptionBudget
    (s : ℕ) (sigmaNormBound theta factorBound : ℝ) : ℝ :=
  conversionSubsetCount s *
      (sharpThetaCoefficient s theta *
        boundedConvertedTermNorm s sigmaNormBound factorBound) +
    sharpThetaCoefficient s theta *
      boundedConvertedEvenNorm s sigmaNormBound factorBound

/-- Bounded version of the global pure-theta absorption. -/
theorem bounded_sharpThetaSum_le_convertedEven_at
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    {d : ℕ} {G HsigmaNorm : ℝ}
    (hsigma : ∀ I, IsSOS (sigma I))
    (hsigmaDegree : ∀ I, (sigma I).totalDegree ≤ d)
    (hsigmaNorm : ∀ I, coeffL1Norm (sigma I) ≤ HsigmaNorm)
    (hHsigmaNorm : 0 ≤ HsigmaNorm)
    (haDegree : ∀ i, (a i).totalDegree ≤ d)
    (haNorm : ∀ i, coeffL1Norm (a i) ≤ G)
    (hG : 1 ≤ G) (hδ : 0 < δ) (htheta : 0 ≤ theta)
    (B' : ℝ) :
    Nonempty (BoundedModuleLEAt g
      (d + 3 * s * conversionFactorDegree pkg d)
      (boundedSharpThetaAbsorptionBudget s HsigmaNorm theta
        (conversionFactorCoefficientBound pkg B' G))
      (∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
        C (((I.powerset.filter (fun K => ¬ Even K.card)).card : ℝ) *
          theta) * zeroErrorTerm (fun _ => pkg) a sigma I)
      (C (sharpThetaCoefficient s theta) *
        convertedEven (fun _ => pkg) a sigma)) := by
  classical
  let R := d + 3 * s * conversionFactorDegree pkg d
  let Sall : Finset (Finset (Fin s)) :=
    (Finset.univ : Finset (Fin s)).powerset
  let T : Finset (Fin s) → Finset (Finset (Fin s)) :=
    fun I => I.powerset.filter (fun K => ¬ Even K.card)
  let Kfactor := conversionFactorCoefficientBound pkg B' G
  let HT := boundedConvertedTermNorm s HsigmaNorm Kfactor
  let alpha := sharpThetaCoefficient s theta
  let Heven := boundedConvertedEvenNorm s HsigmaNorm Kfactor
  have halpha : 0 ≤ alpha := by
    dsimp [alpha, sharpThetaCoefficient]
    positivity
  have hHT : 0 ≤ HT := by
    dsimp [HT, boundedConvertedTermNorm, Kfactor]
    have hk := conversionFactorCoefficientBound_nonneg pkg B' G
    positivity
  have hone : 1 ≤ (Sall.card : ℝ) := by
    have hempty : (∅ : Finset (Fin s)) ∈ Sall := by simp [Sall]
    exact_mod_cast Finset.one_le_card.mpr ⟨∅, hempty⟩
  have hterm (I : Finset (Fin s)) (hI : I ∈ Sall) :
      BoundedModuleLEAt g R (alpha * HT)
        (C (((T I).card : ℝ) * theta) *
          zeroErrorTerm (fun _ => pkg) a sigma I)
        (C alpha * zeroErrorTerm (fun _ => pkg) a sigma I) := by
    let Z := zeroErrorTerm (fun _ => pkg) a sigma I
    let gap := alpha - ((T I).card : ℝ) * theta
    have hgap : 0 ≤ gap := by
      dsimp [gap, alpha, T]
      exact sub_nonneg.mpr
        (odd_card_mul_theta_le_sharpThetaCoefficient htheta I (by
          simpa only [Sall, Finset.mem_univ] using hI))
    have hgapAlpha : gap ≤ alpha := by
      dsimp [gap]
      have hcardtheta : 0 ≤ ((T I).card : ℝ) * theta := by positivity
      linarith
    have hZSOS : IsSOS Z := by
      dsimp [Z, zeroErrorTerm]
      exact errorExpansionTerm_isSOS (fun _ => pkg) a sigma hsigma hδ I ∅
    have hZDegree : Z.totalDegree ≤ R := by
      dsimp [Z, zeroErrorTerm, R]
      exact errorExpansionTerm_totalDegree_le pkg a sigma
        hsigmaDegree haDegree I ∅
    have hZNorm : coeffL1Norm Z ≤ HT := by
      dsimp [Z, zeroErrorTerm, HT, Kfactor]
      exact errorExpansionTerm_coeffL1Norm_le pkg a sigma
        hsigmaNorm hHsigmaNorm haNorm hG B' I ∅
    have hdiffSOS : IsSOS (C gap * Z) :=
      IsSOS_mul (IsSOS_C_nonneg gap hgap) hZSOS
    have hdiffDegree : (C gap * Z).totalDegree ≤ R :=
      (mv_C_mul_totalDegree_le gap Z).trans hZDegree
    let cRaw := BoundedQuadraticModuleCertificate.ofSOS g
      (C gap * Z) hdiffSOS hdiffDegree
    have hdiffNorm : coeffL1Norm (C gap * Z) ≤ alpha * HT := by
      calc
        _ ≤ |gap| * coeffL1Norm Z := coeffL1Norm_C_mul_le _ _
        _ = gap * coeffL1Norm Z := by rw [abs_of_nonneg hgap]
        _ ≤ alpha * HT :=
          mul_le_mul hgapAlpha hZNorm (coeffL1Norm_nonneg Z) halpha
    exact (cRaw.weakenBound hdiffNorm).congr (by
      dsimp [gap, Z]
      rw [map_sub, map_mul, map_natCast]
      ring)
  obtain ⟨ctheta⟩ := BoundedModuleLEAt.sum_nonempty Sall
    (fun I => C (((T I).card : ℝ) * theta) *
      zeroErrorTerm (fun _ => pkg) a sigma I)
    (fun I => C alpha * zeroErrorTerm (fun _ => pkg) a sigma I)
    (fun I hI => ⟨hterm I hI⟩)
  have ctheta' : BoundedModuleLEAt g R
      ((Sall.card : ℝ) * (alpha * HT))
      (∑ I ∈ Sall, C (((T I).card : ℝ) * theta) *
        zeroErrorTerm (fun _ => pkg) a sigma I)
      (C alpha * convertedZero (fun _ => pkg) a sigma) := by
    have heq : C alpha * convertedZero (fun _ => pkg) a sigma =
        ∑ I ∈ Sall, C alpha * zeroErrorTerm (fun _ => pkg) a sigma I := by
      dsimp [convertedZero, Sall]
      rw [Finset.mul_sum]
    rw [heq]
    exact ctheta
  have hpositiveSOS := convertedPositiveEven_isSOS
    (fun _ => pkg) a sigma hsigma hδ
  have hpositiveDegree := convertedPositiveEven_totalDegree_le
    pkg a sigma hsigmaDegree haDegree
  have hpositiveNorm :
      coeffL1Norm (convertedPositiveEven (fun _ => pkg) a sigma) ≤
        Heven := by
    dsimp [Heven, Kfactor]
    exact convertedPositiveEven_coeffL1Norm_le pkg a sigma
      hsigmaNorm hHsigmaNorm haNorm hG B'
  have hscaledSOS : IsSOS
      (C alpha * convertedPositiveEven (fun _ => pkg) a sigma) :=
    IsSOS_mul (IsSOS_C_nonneg alpha halpha) hpositiveSOS
  have hscaledDegree :
      (C alpha * convertedPositiveEven (fun _ => pkg) a sigma).totalDegree ≤
        R := by
    exact (mv_C_mul_totalDegree_le alpha _).trans (by
      simpa [R] using hpositiveDegree)
  let cpositiveRaw := BoundedQuadraticModuleCertificate.ofSOS g
    (C alpha * convertedPositiveEven (fun _ => pkg) a sigma)
    hscaledSOS hscaledDegree
  have hscaledNorm :
      coeffL1Norm
          (C alpha * convertedPositiveEven (fun _ => pkg) a sigma) ≤
        alpha * Heven := by
    calc
      _ ≤ |alpha| * coeffL1Norm
          (convertedPositiveEven (fun _ => pkg) a sigma) :=
        coeffL1Norm_C_mul_le _ _
      _ = alpha * coeffL1Norm
          (convertedPositiveEven (fun _ => pkg) a sigma) := by
        rw [abs_of_nonneg halpha]
      _ ≤ alpha * Heven := mul_le_mul_of_nonneg_left hpositiveNorm halpha
  let cpositive := cpositiveRaw.weakenBound hscaledNorm
  have czeroEven : BoundedModuleLEAt g R (alpha * Heven)
      (C alpha * convertedZero (fun _ => pkg) a sigma)
      (C alpha * convertedEven (fun _ => pkg) a sigma) := by
    exact cpositive.congr (by
      rw [convertedEven_eq_zero_add_positive]
      ring)
  have cfinal := ctheta'.trans czeroEven
  exact ⟨by
    simpa [boundedSharpThetaAbsorptionBudget, R, Sall, T, Kfactor,
      HT, alpha, Heven, conversionSubsetCount] using cfinal⟩

/-- Budget for the complete global sharp odd comparison. -/
def boundedSharpConvertedOddBudget
    (s : ℕ) (sigmaNormBound theta factorBound oddTermBudget : ℝ) : ℝ :=
  boundedConvertedOddBudget s oddTermBudget +
    boundedSharpThetaAbsorptionBudget s sigmaNormBound theta factorBound

/-- The complete odd aggregate satisfies the sharp two-channel comparison,
with both truncation order and coefficient size tracked. -/
theorem bounded_convertedOdd_le_sharpAbsorption_at
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta H B' : ℝ} (pkg : Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    {d rSigma rA rB : ℕ}
    {Ha Hb G HsigmaNorm HsigmaCert : ℝ}
    (hsigma : ∀ I, IsSOS (sigma I))
    (hsigmaDegree : ∀ I, (sigma I).totalDegree ≤ d)
    (hsigmaNorm : ∀ I, coeffL1Norm (sigma I) ≤ HsigmaNorm)
    (hHsigmaNorm : 0 ≤ HsigmaNorm)
    (csigma : ∀ I, BoundedModuleLEAt g rSigma HsigmaCert
      (sigma I) (C H))
    (hHa : 0 ≤ Ha) (hHb : 0 ≤ Hb)
    (ca : ∀ i, BoundedQuadraticModuleCertificate g (a i) rA Ha)
    (cBa : ∀ i, BoundedQuadraticModuleCertificate g (C B - a i) rB Hb)
    (haDegree : ∀ i, (a i).totalDegree ≤ d)
    (haNorm : ∀ i, coeffL1Norm (a i) ≤ G)
    (hG : 1 ≤ G) (hδ : 0 < δ) (hB : 1 ≤ B)
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hB' : 0 ≤ B')
    (hBcondition : B + δ ≤ (1 - theta) * B') :
    Nonempty (BoundedModuleLEAt g
      (conversionSharpOddOrder pkg s d rSigma rA rB)
      (boundedSharpConvertedOddBudget s HsigmaNorm theta
        (conversionFactorCoefficientBound pkg B' G)
        (boundedSharpOddTermBudget s HsigmaCert HsigmaNorm theta
          (conversionIntervalCertificateBound pkg B' G Ha Hb)
          (conversionFactorCoefficientBound pkg B' G)))
      (convertedOdd (fun _ => pkg) a sigma)
      (C (sharpThetaCoefficient s theta) *
          convertedEven (fun _ => pkg) a sigma +
        C (sharpDeltaCoefficient s H B' theta δ) *
          denominatorProduct (fun _ => pkg) a)) := by
  classical
  let Rterm := conversionSharpOddTermOrder pkg s d rSigma rA rB
  let RE := d + 3 * s * conversionFactorDegree pkg d
  let Sall : Finset (Finset (Fin s)) :=
    (Finset.univ : Finset (Fin s)).powerset
  let T : Finset (Fin s) → Finset (Finset (Fin s)) :=
    fun I => I.powerset.filter (fun K => ¬ Even K.card)
  let D := denominatorProduct (fun _ => pkg) a
  let Hint := conversionIntervalCertificateBound pkg B' G Ha Hb
  let Kfactor := conversionFactorCoefficientBound pkg B' G
  let HT := boundedSharpOddTermBudget s HsigmaCert HsigmaNorm theta
    Hint Kfactor
  let Hraw := boundedConvertedOddBudget s HT
  let Htheta := boundedSharpThetaAbsorptionBudget s HsigmaNorm theta Kfactor
  have hHT : 0 ≤ HT := by
    have hc : 0 ≤ HsigmaCert := (csigma ∅).bound_nonneg
    have hk := conversionFactorCoefficientBound_nonneg pkg B' G
    have hi := conversionIntervalCertificateBound_nonneg
      pkg B' hB hG hHa hHb
    have hs : 0 ≤ HsigmaNorm := hHsigmaNorm
    have hp : 0 ≤ (Kfactor + 1) ^ s := pow_nonneg (by linarith) _
    have hexp : 0 ≤ boundedConversionExpansionBudget s HsigmaNorm Hint Kfactor := by
      dsimp [boundedConversionExpansionBudget, boundedConversionContextBound,
        boundedConversionProductBudget]
      positivity
    have hpure : 0 ≤ boundedSharpPureThetaBudget s HsigmaNorm Kfactor := by
      dsimp [boundedSharpPureThetaBudget, boundedConvertedTermNorm]
      positivity
    have hscalar : 0 ≤ boundedSharpScalarBudget s HsigmaCert HsigmaNorm
        theta Hint Kfactor := by
      dsimp [boundedSharpScalarBudget]
      positivity
    have hcount : 0 ≤ conversionSubsetCount s := by
      unfold conversionSubsetCount
      positivity
    change 0 ≤ boundedConversionExpansionBudget s HsigmaNorm Hint Kfactor +
      (boundedSharpPureThetaBudget s HsigmaNorm Kfactor +
        conversionSubsetCount s * boundedSharpScalarBudget s HsigmaCert
          HsigmaNorm theta Hint Kfactor)
    exact add_nonneg hexp (add_nonneg hpure (mul_nonneg hcount hscalar))
  have hinner (I : Finset (Fin s)) (hI : I ∈ Sall) :
      Nonempty (BoundedModuleLEAt g Rterm
        ((Sall.card : ℝ) * HT)
        (oddErrorSum (fun _ => pkg) a sigma I)
        (∑ K ∈ T I,
          (C theta * zeroErrorTerm (fun _ => pkg) a sigma I +
            ∑ L ∈ K.powerset.erase ∅,
              C (refinedRemainderCoefficient H B' theta δ I K L) * D))) := by
    obtain ⟨craw⟩ := BoundedModuleLEAt.sum_nonempty (T I)
      (fun K => errorExpansionTerm (fun _ => pkg) a sigma I K)
      (fun K => C theta * zeroErrorTerm (fun _ => pkg) a sigma I +
        ∑ L ∈ K.powerset.erase ∅,
          C (refinedRemainderCoefficient H B' theta δ I K L) * D)
      (fun K hK => by
        have hf := Finset.mem_filter.mp hK
        exact bounded_errorExpansionTerm_le_sharpPairBound_at
          pkg a sigma hsigma hsigmaDegree hsigmaNorm hHsigmaNorm
          csigma hHa hHb ca cBa haDegree haNorm hG hδ hB
          htheta htheta1 hB' hBcondition I K
          (Finset.mem_powerset.mp hf.1) hf.2)
    have hsubset : T I ⊆ Sall := by
      intro K hK
      have hKI := Finset.mem_powerset.mp (Finset.mem_filter.mp hK).1
      have hIuniv := Finset.mem_powerset.mp hI
      exact Finset.mem_powerset.mpr (hKI.trans hIuniv)
    have hcard : ((T I).card : ℝ) ≤ (Sall.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    change Nonempty (BoundedModuleLEAt g Rterm
      ((Sall.card : ℝ) * HT)
      (∑ K ∈ T I, errorExpansionTerm (fun _ => pkg) a sigma I K)
      (∑ K ∈ T I, (C theta * zeroErrorTerm (fun _ => pkg) a sigma I +
        ∑ L ∈ K.powerset.erase ∅,
          C (refinedRemainderCoefficient H B' theta δ I K L) * D)))
    exact ⟨craw.weakenBound (mul_le_mul_of_nonneg_right hcard hHT)⟩
  obtain ⟨couter⟩ := BoundedModuleLEAt.sum_nonempty Sall
    (fun I => oddErrorSum (fun _ => pkg) a sigma I)
    (fun I => ∑ K ∈ T I,
      (C theta * zeroErrorTerm (fun _ => pkg) a sigma I +
        ∑ L ∈ K.powerset.erase ∅,
          C (refinedRemainderCoefficient H B' theta δ I K L) * D))
    hinner
  have hrhs :
      (∑ I ∈ Sall, ∑ K ∈ T I,
        (C theta * zeroErrorTerm (fun _ => pkg) a sigma I +
          ∑ L ∈ K.powerset.erase ∅,
            C (refinedRemainderCoefficient H B' theta δ I K L) * D)) =
        (∑ I ∈ Sall, C (((T I).card : ℝ) * theta) *
          zeroErrorTerm (fun _ => pkg) a sigma I) +
        C (sharpDeltaCoefficient s H B' theta δ) * D := by
    dsimp [Sall, T, D]
    unfold sharpDeltaCoefficient
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      map_sum, Finset.sum_mul, map_mul, map_natCast]
    congr 1
    · apply Finset.sum_congr rfl
      intro I hI
      ring
  let cnormalized : BoundedModuleLEAt g Rterm Hraw
      (convertedOdd (fun _ => pkg) a sigma)
      ((∑ I ∈ Sall, C (((T I).card : ℝ) * theta) *
          zeroErrorTerm (fun _ => pkg) a sigma I) +
        C (sharpDeltaCoefficient s H B' theta δ) * D) := by
    rw [hrhs] at couter
    simpa [Hraw, boundedConvertedOddBudget, conversionSubsetCount,
      convertedOdd, oddErrorSum, Sall, T] using couter
  obtain ⟨ctheta⟩ := bounded_sharpThetaSum_le_convertedEven_at
    (g := g) pkg a sigma hsigma hsigmaDegree hsigmaNorm hHsigmaNorm
    haDegree haNorm hG hδ htheta B'
  have ctheta' : BoundedModuleLEAt g RE Htheta
      (∑ I ∈ Sall, C (((T I).card : ℝ) * theta) *
        zeroErrorTerm (fun _ => pkg) a sigma I)
      (C (sharpThetaCoefficient s theta) *
        convertedEven (fun _ => pkg) a sigma) := by
    simpa [RE, Htheta, Kfactor, Sall, T] using ctheta
  have cdelta := (BoundedModuleLEAt.refl g
    (C (sharpDeltaCoefficient s H B' theta δ) * D)).mono
      (Nat.zero_le RE)
  have ctoEven := ctheta'.add cdelta
  have cfinal := cnormalized.trans ctoEven
  exact ⟨by
    simpa [conversionSharpOddOrder, boundedSharpConvertedOddBudget,
      Rterm, RE, Hraw, Htheta, HT, Hint, Kfactor, D] using cfinal⟩

end OptimalConvergenceRates.GeneralArchimedean

end
