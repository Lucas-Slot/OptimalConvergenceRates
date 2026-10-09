/-
  Final coefficient-bounded preordering-to-module conversion.
-/
import OptimalConvergenceRates.GeneralArchimedean.BoundedOddConversion

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

variable {n m : ℕ}

/-- Coefficient envelope for one even error-expansion term. -/
def boundedConvertedTermNorm
    (s : ℕ) (sigmaNormBound factorBound : ℝ) : ℝ :=
  sigmaNormBound * (factorBound + 1) ^ (3 * s)

/-- Coefficient envelope for the complete converted even aggregate. -/
def boundedConvertedEvenNorm
    (s : ℕ) (sigmaNormBound factorBound : ℝ) : ℝ :=
  conversionSubsetCount s *
    (conversionSubsetCount s *
      boundedConvertedTermNorm s sigmaNormBound factorBound)

theorem errorExpansionTerm_coeffL1Norm_le
    {s : ℕ} {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    {G HsigmaNorm : ℝ}
    (hsigmaNorm : ∀ I, coeffL1Norm (sigma I) ≤ HsigmaNorm)
    (hHsigmaNorm : 0 ≤ HsigmaNorm)
    (haNorm : ∀ i, coeffL1Norm (a i) ≤ G)
    (hG : 1 ≤ G) (B' : ℝ)
    (I K : Finset (Fin s)) :
    coeffL1Norm (errorExpansionTerm (fun _ => pkg) a sigma I K) ≤
      boundedConvertedTermNorm s HsigmaNorm
        (conversionFactorCoefficientBound pkg B' G) := by
  classical
  let Kfactor := conversionFactorCoefficientBound pkg B' G
  have hKfactor : 0 ≤ Kfactor := by
    dsimp [Kfactor]
    exact conversionFactorCoefficientBound_nonneg pkg B' G
  have hP :
      coeffL1Norm (∏ i ∈ I \ K, pkg.substP (a i) ^ 2) ≤
        (Kfactor + 1) ^ s :=
    coeffL1Norm_finset_prod_le_common_pow (I \ K)
      (fun i => pkg.substP (a i) ^ 2) hKfactor
      (finset_fin_card_le (I \ K))
      (fun i hi => by
        dsimp [Kfactor]
        exact substP_sq_coeffL1Norm_le_conversionFactor
          pkg B' (a i) hG (haNorm i))
  have hE :
      coeffL1Norm (∏ i ∈ K, pkg.substE (a i)) ≤
        (Kfactor + 1) ^ s :=
    coeffL1Norm_finset_prod_le_common_pow K
      (fun i => pkg.substE (a i)) hKfactor
      (finset_fin_card_le K)
      (fun i hi => by
        dsimp [Kfactor]
        exact substE_coeffL1Norm_le_conversionFactor
          pkg B' (a i) hG (haNorm i))
  have hV :
      coeffL1Norm (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2) ≤
        (Kfactor + 1) ^ s :=
    coeffL1Norm_finset_prod_le_common_pow Iᶜ
      (fun i => pkg.substV (a i) ^ 2) hKfactor
      (finset_fin_card_le Iᶜ)
      (fun i hi => by
        dsimp [Kfactor]
        exact substV_sq_coeffL1Norm_le_conversionFactor
          pkg B' (a i) hG (haNorm i))
  dsimp [errorExpansionTerm, boundedConvertedTermNorm]
  calc
    coeffL1Norm
        (sigma I * (∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
          (∏ i ∈ K, pkg.substE (a i)) *
          ∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2) ≤
        ((coeffL1Norm (sigma I) *
          coeffL1Norm (∏ i ∈ I \ K, pkg.substP (a i) ^ 2)) *
          coeffL1Norm (∏ i ∈ K, pkg.substE (a i))) *
          coeffL1Norm (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2) := by
      exact (coeffL1Norm_mul_le _ _).trans <|
        mul_le_mul_of_nonneg_right
          ((coeffL1Norm_mul_le _ _).trans <|
            mul_le_mul_of_nonneg_right (coeffL1Norm_mul_le _ _)
              (coeffL1Norm_nonneg _))
          (coeffL1Norm_nonneg _)
    _ ≤ ((HsigmaNorm * (Kfactor + 1) ^ s) *
        (Kfactor + 1) ^ s) * (Kfactor + 1) ^ s := by
      exact mul_le_mul
        (mul_le_mul
          (mul_le_mul (hsigmaNorm I) hP
            (coeffL1Norm_nonneg _) hHsigmaNorm)
          hE (coeffL1Norm_nonneg _)
          (mul_nonneg hHsigmaNorm (by positivity)))
        hV (coeffL1Norm_nonneg _)
        (mul_nonneg (mul_nonneg hHsigmaNorm (by positivity)) (by positivity))
    _ = HsigmaNorm * (Kfactor + 1) ^ (3 * s) := by
      rw [show 3 * s = s + s + s by omega, pow_add, pow_add]
      ring

theorem convertedEven_coeffL1Norm_le
    {s : ℕ} {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    {G HsigmaNorm : ℝ}
    (hsigmaNorm : ∀ I, coeffL1Norm (sigma I) ≤ HsigmaNorm)
    (hHsigmaNorm : 0 ≤ HsigmaNorm)
    (haNorm : ∀ i, coeffL1Norm (a i) ≤ G)
    (hG : 1 ≤ G) (B' : ℝ) :
    coeffL1Norm (convertedEven (fun _ => pkg) a sigma) ≤
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
  unfold convertedEven
  calc
    coeffL1Norm (∑ I ∈ Sall, evenErrorSum (fun _ => pkg) a sigma I) ≤
        ∑ I ∈ Sall, coeffL1Norm (evenErrorSum (fun _ => pkg) a sigma I) :=
      coeffL1Norm_sum_le Sall _
    _ ≤ ∑ _I ∈ Sall, (Sall.card : ℝ) * HT := by
      apply Finset.sum_le_sum
      intro I hI
      unfold evenErrorSum
      calc
        coeffL1Norm (∑ K ∈ I.powerset.filter (fun K => Even K.card),
            errorExpansionTerm (fun _ => pkg) a sigma I K) ≤
            ∑ K ∈ I.powerset.filter (fun K => Even K.card),
              coeffL1Norm (errorExpansionTerm (fun _ => pkg) a sigma I K) :=
          coeffL1Norm_sum_le _ _
        _ ≤ ∑ _K ∈ I.powerset.filter (fun K => Even K.card), HT :=
          Finset.sum_le_sum fun K hK =>
            errorExpansionTerm_coeffL1Norm_le pkg a sigma
              hsigmaNorm hHsigmaNorm haNorm hG B' I K
        _ ≤ (Sall.card : ℝ) * HT := by
          rw [Finset.sum_const, nsmul_eq_mul]
          have hsubset :
              I.powerset.filter (fun K => Even K.card) ⊆ Sall := by
            intro K hK
            have hKI := Finset.mem_powerset.mp (Finset.mem_filter.mp hK).1
            have hIuniv : I ⊆ (Finset.univ : Finset (Fin s)) :=
              Finset.mem_powerset.mp hI
            exact Finset.mem_powerset.mpr (hKI.trans hIuniv)
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast Finset.card_le_card hsubset) hHT
    _ = (Sall.card : ℝ) * ((Sall.card : ℝ) * HT) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = boundedConvertedEvenNorm s HsigmaNorm Kfactor := by
      simp [boundedConvertedEvenNorm, conversionSubsetCount, Sall, HT]

end OptimalConvergenceRates.GeneralArchimedean

end

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

variable {n m : ℕ}

/-- Final coefficient budget after absorption and the denominator
telescoping certificate. -/
def boundedConversionRefutationBudget
    (alpha oddBudget evenBudget denominatorBudget : ℝ) : ℝ :=
  (1 - alpha)⁻¹ * (oddBudget + evenBudget) + denominatorBudget

/-- Final bounded refutation assembly.  The denominator-product certificate
is kept as an explicit input, so its positive-coefficient construction can
be bounded independently. -/
theorem bounded_refutation_of_oddAbsorptionCoefficient_at
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
    (hsmall : oddAbsorptionCoefficient s H B' theta δ < 1)
    (cden : BoundedQuadraticModuleCertificate g
      (denominatorProduct (fun _ : Fin s => pkg) a - 1)
      (s * ((rA + conversionFactorDegree pkg d) +
        conversionFactorDegree pkg d)) Hden) :
    Nonempty (BoundedQuadraticModuleCertificate g
      (-1 : MvPolynomial (Fin n) ℝ)
      (conversionRefutationOrder pkg s d rSigma rA rB)
      (boundedConversionRefutationBudget
        (oddAbsorptionCoefficient s H B' theta δ)
        (boundedConvertedOddBudget s
          (boundedConversionOddTermBudget s HsigmaCert HsigmaNorm theta
            (conversionIntervalCertificateBound pkg B' G Ha Hb)
            (conversionFactorCoefficientBound pkg B' G)))
        (boundedConvertedEvenNorm s HsigmaNorm
          (conversionFactorCoefficientBound pkg B' G))
        Hden)) := by
  let D := denominatorProduct (fun _ : Fin s => pkg) a
  let E := convertedEven (fun _ : Fin s => pkg) a sigma
  let O := convertedOdd (fun _ : Fin s => pkg) a sigma
  let F := conversionFactorDegree pkg d
  let Rodd := conversionOddTermOrder pkg s d rSigma rA rB
  let RE := d + 3 * s * F
  let Rden := s * ((rA + F) + F)
  let alpha := oddAbsorptionCoefficient s H B' theta δ
  let Hint := conversionIntervalCertificateBound pkg B' G Ha Hb
  let Kfactor := conversionFactorCoefficientBound pkg B' G
  let Hodd := boundedConvertedOddBudget s
    (boundedConversionOddTermBudget s HsigmaCert HsigmaNorm theta
      Hint Kfactor)
  let Heven := boundedConvertedEvenNorm s HsigmaNorm Kfactor
  have hEO : -D = E - O := by
    exact multiplied_refutation_eq_even_sub_odd
      (fun _ : Fin s => pkg) a sigma hδ hidentity
  have hO : O = E + D := by
    linear_combination hEO
  obtain ⟨codd⟩ :=
    bounded_convertedOdd_le_oddAbsorptionCoefficient_at
      pkg a sigma hsigma hsigmaDegree hsigmaNorm hHsigmaNorm
      csigma hHa hHb ca cBa haDegree haNorm hG hδ hB
      htheta htheta1 hB' hBcondition
  have codd' : BoundedModuleLEAt g Rodd Hodd O (C alpha * D) := by
    simpa [Rodd, Hodd, alpha, Hint, Kfactor, O, D] using codd
  have hESOS : IsSOS E :=
    convertedEven_isSOS (fun _ : Fin s => pkg) a sigma hsigma hδ
  have hEDegree : E.totalDegree ≤ RE := by
    simpa [E, RE, F] using
      convertedEven_totalDegree_le pkg a sigma hsigmaDegree haDegree
  have hENorm : coeffL1Norm E ≤ Heven := by
    simpa [E, Heven, Kfactor] using
      convertedEven_coeffL1Norm_le pkg a sigma
        hsigmaNorm hHsigmaNorm haNorm hG B'
  let cE : BoundedQuadraticModuleCertificate g E RE Heven :=
    (BoundedQuadraticModuleCertificate.ofSOS g E hESOS hEDegree).weakenBound
      hENorm
  have ccombined :=
    BoundedQuadraticModuleCertificate.add codd' cE
  let gamma : ℝ := 1 - alpha
  have hgamma : 0 < gamma := by
    dsimp [gamma, alpha]
    exact sub_pos.mpr hsmall
  let cneg : BoundedQuadraticModuleCertificate g
      (-(C gamma * D)) (max Rodd RE) (Hodd + Heven) :=
    ccombined.congr (by
      rw [hO]
      dsimp [gamma]
      calc
        C alpha * D - (E + D) + E = (C alpha - 1) * D := by ring
        _ = -(C (1 - alpha) * D) := by
          rw [show (1 : MvPolynomial (Fin n) ℝ) = C 1 by simp]
          rw [← map_sub]
          rw [show alpha - 1 = -(1 - alpha) by ring, map_neg]
          ring)
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
  let cminusD : BoundedQuadraticModuleCertificate g (-D)
      (max Rodd RE) (gamma⁻¹ * (Hodd + Heven)) := by
    simpa [MvPolynomial.totalDegree_C] using cscaled.congr heq
  have cfinalRaw := cminusD.add cden
  have cfinal : BoundedQuadraticModuleCertificate g
      (-1 : MvPolynomial (Fin n) ℝ)
      (max (max Rodd RE) Rden)
      (gamma⁻¹ * (Hodd + Heven) + Hden) :=
    cfinalRaw.congr (by
      dsimp [D] at cfinalRaw ⊢
      ring)
  exact ⟨by
    simpa [conversionRefutationOrder, boundedConversionRefutationBudget,
      Rodd, RE, Rden, F, gamma, alpha, Hodd, Heven, Hint, Kfactor]
      using cfinal⟩

end OptimalConvergenceRates.GeneralArchimedean

end
