/-
  Coefficient-bounded Archimedean bridge for the sharp conversion.
-/
import OptimalConvergenceRates.GeneralArchimedean.BoundedQuantitativeBridge
import OptimalConvergenceRates.GeneralArchimedean.SharpBoundedFinalConversion
import OptimalConvergenceRates.GeneralArchimedean.SharpParameterBounds

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

variable {n s : ℕ}

/-- Coefficient budget produced by the complete bounded sharp bridge. -/
def boundedSharpBridgeRefutationBudget
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (s n d : ℕ) (R Hcoord G H Hconvert : ℝ) : ℝ :=
  let Bprime : ℝ := 2 * (B + 1)
  let Ha : ℝ := 1
  let Hb : ℝ := boundedBridgeGeneratorBudget n d R Hcoord G B
  let HsigmaCert : ℝ :=
    boundedBridgeSigmaBudget n d R Hcoord H Hconvert
  boundedSharpRefutationBudget
    (sharpDeltaCoefficient s Hconvert Bprime theta δ)
    (boundedSharpConvertedOddBudget s H theta
      (conversionFactorCoefficientBound pkg Bprime G)
      (boundedSharpOddTermBudget s HsigmaCert H theta
        (conversionIntervalCertificateBound pkg Bprime G Ha Hb)
        (conversionFactorCoefficientBound pkg Bprime G)))
    (boundedConvertedEvenNorm s H
      (conversionFactorCoefficientBound pkg Bprime G))
    (boundedDenominatorProductBudget pkg s Bprime G Ha)

/-- A bounded preordering refutation converts to a bounded ordinary-module
refutation using fixed theta and shrinking delta. -/
theorem bounded_certificate_preordering_refutation_to_sharp_module_at_of_coordinate_bounds
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    {R Hcoord : ℝ} {t : ℕ}
    (hR : 1 ≤ R) (hHcoord : 0 ≤ Hcoord)
    (hcoord : ∀ i : Fin n,
      BoundedQuadraticModuleCertificate a
        (C R - X i ^ 2) t Hcoord)
    {r d : ℕ} {H G : ℝ}
    (c : BoundedPreorderingCertificate a
      (-1 : MvPolynomial (Fin n) ℝ) r H)
    (hrd : r ≤ d) (hG : 1 ≤ G)
    (haDegree : ∀ i, (a i).totalDegree ≤ d)
    (haNorm : ∀ i, coeffL1Norm (a i) ≤ G) :
    ∃ (B Hconvert : ℝ),
      B = finiteFamilyEnvelopeBound s n d R G ∧
      Hconvert =
        finiteFamilyEnvelopeBound
          ((Finset.univ : Finset (Finset (Fin s))).card)
          n d R H ∧
      let Bprime : ℝ := 2 * (B + 1)
      let theta : ℝ := sharpThetaScale s
      let delta : ℝ := sharpDeltaScale s Hconvert Bprime
      ∃ pkg : Package delta B theta,
        (pkg.ell : ℝ) ≤
            Real.log (theta / 4) / Real.log (1 / 9) + 1 ∧
          (pkg.J : ℝ) ≤
            Real.log (Real.sqrt (B + delta) / Real.sqrt delta) /
              Real.log 2 ∧
          Nonempty (BoundedQuadraticModuleCertificate a
            (-1 : MvPolynomial (Fin n) ℝ)
            (sharpConversionRefutationOrder pkg s d
              (boundedCoeffEnvelopeOrder n t d) d
              (boundedCoeffEnvelopeOrder n t d))
            (boundedSharpBridgeRefutationBudget pkg s n d
              R Hcoord G H Hconvert)) := by
  classical
  let generatorSet : Finset (Fin s) := Finset.univ
  let sigmaSet : Finset (Finset (Fin s)) := Finset.univ
  let sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ :=
    activePreorderingCoefficient a c.certificate.sigma
  let B : ℝ := finiteFamilyEnvelopeBound s n d R G
  let Hconvert : ℝ := finiteFamilyEnvelopeBound sigmaSet.card n d R H
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hH : 0 ≤ H := c.bound_nonneg
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hsigmaDegree : ∀ I, (sigma I).totalDegree ≤ d := by
    intro I
    exact (activePreorderingCoefficient_totalDegree_le
      a c.certificate I).trans hrd
  have hsigmaSOS : ∀ I, IsSOS (sigma I) := by
    intro I
    exact activePreorderingCoefficient_isSOS
      a c.certificate.sigma c.certificate.isSOS I
  have hB : 1 ≤ B := by
    dsimp [B, finiteFamilyEnvelopeBound]
    exact le_add_of_nonneg_right <| mul_nonneg (Nat.cast_nonneg _) <| by
      unfold polynomialEnvelopeBound
      positivity
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hHconvert : 0 ≤ Hconvert := by
    dsimp [Hconvert, finiteFamilyEnvelopeBound, polynomialEnvelopeBound]
    positivity
  have ha : ∀ i,
      BoundedQuadraticModuleCertificate a (a i) d 1 := by
    intro i
    exact (BoundedQuadraticModuleCertificate.generator a i).mono
      (haDegree i)
  have hgeneratorFamily :
      finiteFamilyEnvelope R generatorSet a ≤ B := by
    have hbound := finiteFamilyEnvelope_le_finiteFamilyEnvelopeBound
      hR hG0 generatorSet a
      (fun i hi => haDegree i)
      (fun i hi => haNorm i)
    simpa [B, generatorSet] using hbound
  have hgeneratorEnvelope (i : Fin s) :
      weightedCoeffEnvelope R (a i) ≤ B := by
    have hsingle :
        weightedCoeffEnvelope R (a i) ≤
          ∑ j ∈ generatorSet, weightedCoeffEnvelope R (a j) :=
      Finset.single_le_sum
        (fun j _ => weightedCoeffEnvelope_nonneg hR0 (a j))
        (by simp [generatorSet])
    calc
      weightedCoeffEnvelope R (a i) ≤
          ∑ j ∈ generatorSet, weightedCoeffEnvelope R (a j) := hsingle
      _ ≤ finiteFamilyEnvelope R generatorSet a := by
        dsimp [finiteFamilyEnvelope]
        linarith
      _ ≤ B := hgeneratorFamily
  have hBa : ∀ i, BoundedQuadraticModuleCertificate a
      (C B - a i) (boundedCoeffEnvelopeOrder n t d)
      (boundedBridgeGeneratorBudget n d R Hcoord G B) := by
    intro i
    exact Classical.choice <| by
      simpa [boundedBridgeGeneratorBudget] using
        bounded_polynomial_le_constant_of_coordinate_bounds
          hR hHcoord hcoord (a i) (haDegree i) hG0 (haNorm i)
          (zero_le_one.trans hB) (hgeneratorEnvelope i)
  have hfamilyBound :
      finiteFamilyEnvelope R sigmaSet sigma ≤ Hconvert := by
    dsimp [Hconvert]
    exact finiteFamilyEnvelope_le_finiteFamilyEnvelopeBound
      hR hH sigmaSet sigma
      (fun I hI => hsigmaDegree I)
      (fun I hI => activePreorderingCoefficient_coeffL1Norm_le a c I)
  have hsigmaEnvelope (I : Finset (Fin s)) :
      weightedCoeffEnvelope R (sigma I) ≤ Hconvert := by
    have hsingle :
        weightedCoeffEnvelope R (sigma I) ≤
          ∑ J ∈ sigmaSet, weightedCoeffEnvelope R (sigma J) :=
      Finset.single_le_sum
        (fun J _ => weightedCoeffEnvelope_nonneg hR0 (sigma J))
        (by simp [sigmaSet])
    calc
      weightedCoeffEnvelope R (sigma I) ≤
          ∑ J ∈ sigmaSet, weightedCoeffEnvelope R (sigma J) := hsingle
      _ ≤ finiteFamilyEnvelope R sigmaSet sigma := by
        dsimp [finiteFamilyEnvelope]
        linarith
      _ ≤ Hconvert := hfamilyBound
  have hsigmaNorm : ∀ I, coeffL1Norm (sigma I) ≤ H := by
    intro I
    exact activePreorderingCoefficient_coeffL1Norm_le a c I
  have csigma : ∀ I, BoundedModuleLEAt a
      (boundedCoeffEnvelopeOrder n t d)
      (boundedBridgeSigmaBudget n d R Hcoord H Hconvert)
      (sigma I) (C Hconvert) := by
    intro I
    exact Classical.choice <| by
      simpa [BoundedModuleLEAt, boundedBridgeSigmaBudget] using
        bounded_polynomial_le_constant_of_coordinate_bounds
          hR hHcoord hcoord (sigma I) (hsigmaDegree I) hH
          (hsigmaNorm I) hHconvert (hsigmaEnvelope I)
  have hidentity :
      (-1 : MvPolynomial (Fin n) ℝ) =
        ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
          sigma I * ∏ i ∈ I, a i :=
    activePreorderingCoefficient_identity
      a c.certificate.sigma c.certificate.identity
  refine ⟨B, Hconvert, rfl, rfl, ?_⟩
  dsimp only
  let Bprime : ℝ := 2 * (B + 1)
  let theta : ℝ := sharpThetaScale s
  let delta : ℝ := sharpDeltaScale s Hconvert Bprime
  have hBprime : 0 ≤ Bprime := by
    dsimp [Bprime]
    positivity
  have htheta : 0 < theta := sharpThetaScale_pos s
  have hthetaHalf : theta ≤ 1 / 2 := sharpThetaScale_le_half s
  have hthetaOne : theta ≤ 1 := hthetaHalf.trans (by norm_num)
  have hthetaLtOne : theta < 1 :=
    lt_of_le_of_lt hthetaHalf (by norm_num)
  have hdelta : 0 < delta := sharpDeltaScale_pos hHconvert hBprime
  have hdeltaHalf : delta ≤ 1 / 2 :=
    sharpDeltaScale_le_half hHconvert hBprime
  have hcondition : B + delta ≤ (1 - theta) * Bprime := by
    have hfactor : 1 ≤ 2 * (1 - theta) := by linarith
    have hB1 : 0 ≤ B + 1 := by linarith
    calc
      B + delta ≤ B + 1 := by linarith
      _ = 1 * (B + 1) := by ring
      _ ≤ (2 * (1 - theta)) * (B + 1) :=
        mul_le_mul_of_nonneg_right hfactor hB1
      _ = (1 - theta) * Bprime := by dsimp [Bprime]; ring
  obtain ⟨pkg, hell, hJ⟩ :=
    RationalSquareRoot.package_nonempty_with_parameter_log_bounds
      hdelta hB0 htheta hthetaOne
  refine ⟨pkg, hell, hJ, ?_⟩
  simpa [boundedSharpBridgeRefutationBudget, boundedBridgeGeneratorBudget, Bprime, theta, delta] using
    bounded_refutation_of_sharpAbsorption_with_denominator_at
      pkg a sigma hsigmaSOS hsigmaDegree hsigmaNorm hH
      csigma (by norm_num : (0 : ℝ) ≤ 1)
      (add_nonneg hB0
        (boundedArchimedeanEnvelopeBudget_nonneg n d hR0 hHcoord hG0))
      ha hBa haDegree haNorm hG hdelta hB htheta.le hthetaLtOne
      hBprime hcondition hidentity
      (sharpThetaCoefficient_scale_lt_one s).le
      (sharpDeltaCoefficient_scale_lt_one hHconvert hBprime
        htheta.le hthetaOne)

end OptimalConvergenceRates.GeneralArchimedean

end
