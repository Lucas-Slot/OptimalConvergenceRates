/-
  Coefficient-bounded certificates for the common rational denominator.
-/
import OptimalConvergenceRates.GeneralArchimedean.BoundedPositiveCoefficientCertificate
import OptimalConvergenceRates.GeneralArchimedean.BoundedFinalConversion

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

variable {n m : ℕ}

namespace RationalSquareRoot.Package

/-- Coefficient budget for the positive-coefficient certificate showing
`1 ≤ V(a)^2`. -/
def denominatorFactorCertificateBound
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (G Ha : ℝ) : ℝ :=
  positiveSubstitutionCertificateBound (pkg.V ^ 2 - 1) G Ha

theorem denominatorFactorCertificateBound_nonneg
    {δ B theta : ℝ} (pkg : Package δ B theta)
    {G Ha : ℝ} (hG : 1 ≤ G) (hHa : 0 ≤ Ha) :
    0 ≤ pkg.denominatorFactorCertificateBound G Ha := by
  unfold denominatorFactorCertificateBound
  unfold positiveSubstitutionCertificateBound
  unfold positiveSubstitutionTermBound
  have hK : 0 ≤ polynomialCoeffL1Norm (pkg.V ^ 2 - 1) :=
    polynomialCoeffL1Norm_nonneg _
  positivity

/-- Bounded version of the normalized denominator-square relation. -/
theorem bounded_one_le_substV_sq_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta : ℝ} (pkg : Package δ B theta)
    {a : MvPolynomial (Fin n) ℝ} {r : ℕ} {Ha G : ℝ}
    (ca : BoundedQuadraticModuleCertificate g a r Ha)
    (hδ : 0 < δ) (hG : 1 ≤ G)
    (haNorm : coeffL1Norm a ≤ G) :
    Nonempty (BoundedModuleLEAt g
      (r + pkg.degreeBound * a.totalDegree)
      (pkg.denominatorFactorCertificateBound G Ha)
      1 (pkg.substV a ^ 2)) := by
  obtain ⟨craw⟩ :=
    bounded_polynomialSubst_sq_sub_one_mem_at
      ca pkg.V (pkg.V_coeffNonneg hδ) (pkg.V_coeff_zero hδ)
        hG haNorm
  have hdegree : 2 * pkg.V.natDegree ≤ pkg.degreeBound := by
    calc
      2 * pkg.V.natDegree ≤ 2 * (2 * pkg.ell * (pkg.J + 1)) :=
        Nat.mul_le_mul_left 2 pkg.V_degree_le
      _ = pkg.degreeBound := by
        simp [degreeBound]
        ring
  have horder :
      r + 2 * pkg.V.natDegree * a.totalDegree ≤
        r + pkg.degreeBound * a.totalDegree :=
    Nat.add_le_add_left
      (Nat.mul_le_mul_right a.totalDegree hdegree) r
  exact ⟨by
    simpa [denominatorFactorCertificateBound] using craw.mono horder⟩

end RationalSquareRoot.Package

/-- Coefficient budget for telescoping all denominator-square relations. -/
def boundedDenominatorProductBudget
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (s : ℕ) (B' G Ha : ℝ) : ℝ :=
  (conversionFactorCoefficientBound pkg B' G + 1 + 1) ^ s *
    pkg.denominatorFactorCertificateBound G Ha

/-- The full common denominator is above one with explicit order and
coefficient budget. -/
theorem bounded_one_le_denominatorProduct_const
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta B' : ℝ} (pkg : Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    {rA d : ℕ} {Ha G : ℝ}
    (hHa : 0 ≤ Ha)
    (ca : ∀ i, BoundedQuadraticModuleCertificate g (a i) rA Ha)
    (haDegree : ∀ i, (a i).totalDegree ≤ d)
    (haNorm : ∀ i, coeffL1Norm (a i) ≤ G)
    (hG : 1 ≤ G) (hδ : 0 < δ) :
    Nonempty (BoundedQuadraticModuleCertificate g
      (denominatorProduct (fun _ : Fin s => pkg) a - 1)
      (s * ((rA + conversionFactorDegree pkg d) +
        conversionFactorDegree pkg d))
      (boundedDenominatorProductBudget pkg s B' G Ha)) := by
  classical
  let F := conversionFactorDegree pkg d
  let Kfactor := conversionFactorCoefficientBound pkg B' G
  let Hfactor := pkg.denominatorFactorCertificateBound G Ha
  have hKfactor : 0 ≤ Kfactor := by
    dsimp [Kfactor]
    exact conversionFactorCoefficientBound_nonneg pkg B' G
  have hHfactor : 0 ≤ Hfactor := by
    dsimp [Hfactor]
    exact pkg.denominatorFactorCertificateBound_nonneg hG hHa
  have hrel : ∀ i ∈ (Finset.univ : Finset (Fin s)),
      BoundedModuleLEAt g (rA + F) Hfactor
        1 (pkg.substV (a i) ^ 2) := by
    intro i hi
    exact Classical.choice <|
      Nonempty.map
        (fun c => c.mono <| Nat.add_le_add_left
          (Nat.mul_le_mul_left pkg.degreeBound (haDegree i)) rA)
        (pkg.bounded_one_le_substV_sq_at (ca i) hδ hG (haNorm i))
  obtain ⟨cprod⟩ := BoundedModuleLEAt.prod
    (Finset.univ : Finset (Fin s))
    (fun _ => (1 : MvPolynomial (Fin n) ℝ))
    (fun i => pkg.substV (a i) ^ 2)
    (rA + F) F hHfactor (by linarith : 0 ≤ Kfactor + 1)
    (fun _ _ => ModuleLE.sos_one)
    (fun i _ => pkg.substV_sq_isSOS (a i))
    (fun _ _ => by simp)
    (fun i _ => (pkg.substV_sq_totalDegree_le (a i)).trans
      (Nat.mul_le_mul_left pkg.degreeBound (haDegree i)))
    (fun _ _ => by
      change coeffL1Norm (C (1 : ℝ)) ≤ Kfactor + 1
      exact (coeffL1Norm_C_le (n := n) 1).trans (by
        simpa using (show (1 : ℝ) ≤ Kfactor + 1 by linarith)))
    (fun i _ => (substV_sq_coeffL1Norm_le_conversionFactor pkg
      B' (a i) hG (haNorm i)).trans (by linarith))
    hrel
  change Nonempty (BoundedModuleLEAt g
    (s * ((rA + conversionFactorDegree pkg d) +
      conversionFactorDegree pkg d))
    (boundedDenominatorProductBudget pkg s B' G Ha)
    1 (denominatorProduct (fun _ : Fin s => pkg) a))
  exact ⟨by
    simpa [denominatorProduct, boundedDenominatorProductBudget,
      F, Kfactor, Hfactor] using cprod⟩

/-- Final bounded conversion with the denominator certificate constructed
internally from the bounded certificates for the artificial generators. -/
theorem bounded_refutation_of_oddAbsorptionCoefficient_with_denominator_at
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
    (hsmall : oddAbsorptionCoefficient s H B' theta δ < 1) :
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
        (boundedDenominatorProductBudget pkg s B' G Ha))) := by
  obtain ⟨cden⟩ := bounded_one_le_denominatorProduct_const
    pkg a hHa ca haDegree haNorm hG hδ
  exact bounded_refutation_of_oddAbsorptionCoefficient_at
    pkg a sigma hsigma hsigmaDegree hsigmaNorm hHsigmaNorm
      csigma hHa hHb ca cBa haDegree haNorm hG hδ hB
      htheta htheta1 hB' hBcondition hidentity hsmall cden

end OptimalConvergenceRates.GeneralArchimedean

end
