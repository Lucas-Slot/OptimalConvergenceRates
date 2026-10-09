/-
  Final coefficient-bounded assembly for the sharp two-channel conversion.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpBoundedAggregation
import OptimalConvergenceRates.GeneralArchimedean.BoundedDenominatorCertificate

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

variable {n m : ℕ}

/-- Final coefficient budget for the sharp absorption argument and the
denominator telescoping certificate. -/
def boundedSharpRefutationBudget
    (beta oddBudget evenBudget denominatorBudget : ℝ) : ℝ :=
  (1 - beta)⁻¹ * (oddBudget + evenBudget) + denominatorBudget

/-- A coefficient-tracked two-channel absorption inequality gives a bounded
ordinary quadratic-module refutation. -/
theorem bounded_refutation_of_sharpAbsorption_at
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta H B' : ℝ} (pkg : Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    {d rSigma rA rB : ℕ}
    {Ha Hb G HsigmaNorm HsigmaCert Hden : ℝ}
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
    (hidentity : (-1 : MvPolynomial (Fin n) ℝ) =
      ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
        sigma I * ∏ i ∈ I, a i)
    (halpha : sharpThetaCoefficient s theta ≤ 1)
    (hbeta : sharpDeltaCoefficient s H B' theta δ < 1)
    (cden : BoundedQuadraticModuleCertificate g
      (denominatorProduct (fun _ : Fin s => pkg) a - 1)
      (s * ((rA + conversionFactorDegree pkg d) +
        conversionFactorDegree pkg d)) Hden) :
    Nonempty (BoundedQuadraticModuleCertificate g
      (-1 : MvPolynomial (Fin n) ℝ)
      (sharpConversionRefutationOrder pkg s d rSigma rA rB)
      (boundedSharpRefutationBudget
        (sharpDeltaCoefficient s H B' theta δ)
        (boundedSharpConvertedOddBudget s HsigmaNorm theta
          (conversionFactorCoefficientBound pkg B' G)
          (boundedSharpOddTermBudget s HsigmaCert HsigmaNorm theta
            (conversionIntervalCertificateBound pkg B' G Ha Hb)
            (conversionFactorCoefficientBound pkg B' G)))
        (boundedConvertedEvenNorm s HsigmaNorm
          (conversionFactorCoefficientBound pkg B' G)) Hden)) := by
  let D := denominatorProduct (fun _ : Fin s => pkg) a
  let E := convertedEven (fun _ : Fin s => pkg) a sigma
  let O := convertedOdd (fun _ : Fin s => pkg) a sigma
  let F := conversionFactorDegree pkg d
  let Rodd := conversionSharpOddOrder pkg s d rSigma rA rB
  let RE := d + 3 * s * F
  let Rden := s * ((rA + F) + F)
  let alpha := sharpThetaCoefficient s theta
  let beta := sharpDeltaCoefficient s H B' theta δ
  let Hint := conversionIntervalCertificateBound pkg B' G Ha Hb
  let Kfactor := conversionFactorCoefficientBound pkg B' G
  let Hodd := boundedSharpConvertedOddBudget s HsigmaNorm theta Kfactor
    (boundedSharpOddTermBudget s HsigmaCert HsigmaNorm theta Hint Kfactor)
  let Heven := boundedConvertedEvenNorm s HsigmaNorm Kfactor
  have hEO : -D = E - O := by
    exact multiplied_refutation_eq_even_sub_odd
      (fun _ : Fin s => pkg) a sigma hδ hidentity
  have hO : O = E + D := by
    linear_combination hEO
  obtain ⟨coddRaw⟩ := bounded_convertedOdd_le_sharpAbsorption_at
    pkg a sigma hsigma hsigmaDegree hsigmaNorm hHsigmaNorm
    csigma hHa hHb ca cBa haDegree haNorm hG hδ hB
    htheta htheta1 hB' hBcondition
  let codd : BoundedModuleLEAt g Rodd Hodd O
      (C alpha * E + C beta * D) := by
    simpa [Rodd, Hodd, alpha, beta, Hint, Kfactor, O, E, D]
      using coddRaw
  have hESOS : IsSOS E :=
    convertedEven_isSOS (fun _ : Fin s => pkg) a sigma hsigma hδ
  have hEDegree : E.totalDegree ≤ RE := by
    simpa [E, RE, F] using
      convertedEven_totalDegree_le pkg a sigma hsigmaDegree haDegree
  have hENorm : coeffL1Norm E ≤ Heven := by
    simpa [E, Heven, Kfactor] using
      convertedEven_coeffL1Norm_le pkg a sigma
        hsigmaNorm hHsigmaNorm haNorm hG B'
  have halpha0 : 0 ≤ alpha := by
    dsimp [alpha, sharpThetaCoefficient]
    positivity
  have hscaleESOS : IsSOS (C (1 - alpha) * E) :=
    IsSOS_mul (IsSOS_C_nonneg (1 - alpha) (sub_nonneg.mpr halpha)) hESOS
  have hscaleDegree : (C (1 - alpha) * E).totalDegree ≤ RE :=
    (mv_C_mul_totalDegree_le (1 - alpha) E).trans hEDegree
  let cscaleRaw := BoundedQuadraticModuleCertificate.ofSOS g
    (C (1 - alpha) * E) hscaleESOS hscaleDegree
  have hscaleNorm : coeffL1Norm (C (1 - alpha) * E) ≤ Heven := by
    have hgap0 : 0 ≤ 1 - alpha := sub_nonneg.mpr halpha
    have hgap1 : 1 - alpha ≤ 1 := by linarith
    calc
      _ ≤ |1 - alpha| * coeffL1Norm E := coeffL1Norm_C_mul_le _ _
      _ = (1 - alpha) * coeffL1Norm E := by rw [abs_of_nonneg hgap0]
      _ ≤ 1 * Heven :=
        mul_le_mul hgap1 hENorm (coeffL1Norm_nonneg E) (by positivity)
      _ = Heven := one_mul _
  let cscale : BoundedQuadraticModuleCertificate g
      (C (1 - alpha) * E) RE Heven :=
    cscaleRaw.weakenBound hscaleNorm
  have hRE : RE ≤ Rodd := by
    dsimp [Rodd, conversionSharpOddOrder, RE]
    exact le_max_right _ _
  have ccombined := BoundedQuadraticModuleCertificate.add codd
    (cscale.mono hRE)
  let gamma : ℝ := 1 - beta
  let cneg : BoundedQuadraticModuleCertificate g
      (-(C gamma * D)) Rodd (Hodd + Heven) := by
    simpa only [max_self] using ccombined.congr (by
      rw [hO]
      dsimp [gamma]
      simp only [map_sub, map_one]
      ring)
  have hgamma : 0 < gamma := by
    dsimp [gamma, beta]
    exact sub_pos.mpr hbeta
  have hinvSOS : IsSOS (C gamma⁻¹ : MvPolynomial (Fin n) ℝ) :=
    IsSOS_C_nonneg gamma⁻¹ (inv_nonneg.mpr hgamma.le)
  have hinvNorm :
      coeffL1Norm (C gamma⁻¹ : MvPolynomial (Fin n) ℝ) ≤ gamma⁻¹ := by
    simpa [abs_of_pos (inv_pos.mpr hgamma)] using
      (coeffL1Norm_C_le (n := n) gamma⁻¹)
  have cscaled := cneg.sosMulOfNormLe hinvSOS hinvNorm
  have heq :
      (C gamma⁻¹ : MvPolynomial (Fin n) ℝ) *
        (-(C gamma * D)) = -D := by
    calc
      C gamma⁻¹ * (-(C gamma * D)) =
          -(C gamma⁻¹ * C gamma) * D := by ring
      _ = -D := by
        rw [← map_mul, inv_mul_cancel₀ hgamma.ne', map_one]
        ring
  let cminusD : BoundedQuadraticModuleCertificate g (-D) Rodd
      (gamma⁻¹ * (Hodd + Heven)) := by
    simpa [MvPolynomial.totalDegree_C] using cscaled.congr heq
  have cfinalRaw := cminusD.add cden
  have cfinal : BoundedQuadraticModuleCertificate g
      (-1 : MvPolynomial (Fin n) ℝ) (max Rodd Rden)
      (gamma⁻¹ * (Hodd + Heven) + Hden) :=
    cfinalRaw.congr (by
      dsimp [D] at cfinalRaw ⊢
      ring)
  exact ⟨by
    simpa [sharpConversionRefutationOrder, boundedSharpRefutationBudget,
      Rodd, Rden, F, gamma, beta, Hodd, Heven, Hint, Kfactor]
      using cfinal⟩


/-- Final sharp bounded conversion with the denominator certificate built
from the bounded generator certificates. -/
theorem bounded_refutation_of_sharpAbsorption_with_denominator_at
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
    (hidentity : (-1 : MvPolynomial (Fin n) ℝ) =
      ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
        sigma I * ∏ i ∈ I, a i)
    (halpha : sharpThetaCoefficient s theta ≤ 1)
    (hbeta : sharpDeltaCoefficient s H B' theta δ < 1) :
    Nonempty (BoundedQuadraticModuleCertificate g
      (-1 : MvPolynomial (Fin n) ℝ)
      (sharpConversionRefutationOrder pkg s d rSigma rA rB)
      (boundedSharpRefutationBudget
        (sharpDeltaCoefficient s H B' theta δ)
        (boundedSharpConvertedOddBudget s HsigmaNorm theta
          (conversionFactorCoefficientBound pkg B' G)
          (boundedSharpOddTermBudget s HsigmaCert HsigmaNorm theta
            (conversionIntervalCertificateBound pkg B' G Ha Hb)
            (conversionFactorCoefficientBound pkg B' G)))
        (boundedConvertedEvenNorm s HsigmaNorm
          (conversionFactorCoefficientBound pkg B' G))
        (boundedDenominatorProductBudget pkg s B' G Ha))) := by
  obtain ⟨cden⟩ := bounded_one_le_denominatorProduct_const
    pkg a hHa ca haDegree haNorm hG hδ
  exact bounded_refutation_of_sharpAbsorption_at
    pkg a sigma hsigma hsigmaDegree hsigmaNorm hHsigmaNorm
    csigma hHa hHb ca cBa haDegree haNorm hG hδ hB
    htheta htheta1 hB' hBcondition hidentity halpha hbeta cden
end OptimalConvergenceRates.GeneralArchimedean

end
