/-
  Coefficient-bounded assembly of the odd conversion terms.
-/
import OptimalConvergenceRates.GeneralArchimedean.BoundedScalarConversion

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

variable {n m : ℕ}

/-- Common budget for one expanded odd term after both comparison stages. -/
def boundedConversionOddTermBudget
    (s : ℕ) (sigmaCertificateBound sigmaNormBound theta
      comparisonBound factorBound : ℝ) : ℝ :=
  boundedConversionExpansionBudget s sigmaNormBound
      comparisonBound factorBound +
    boundedConversionScalarBudget s sigmaCertificateBound sigmaNormBound
      theta comparisonBound factorBound

/-- One expanded odd term lies below its scalar common-denominator bound,
with explicit degree and coefficient budgets. -/
theorem bounded_errorExpansionTerm_le_scalarBoundTerm_at
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
    (I K : Finset (Fin s)) :
    Nonempty (BoundedModuleLEAt g
      (conversionOddTermOrder pkg s d rSigma rA rB)
      (boundedConversionOddTermBudget s HsigmaCert HsigmaNorm theta
        (conversionIntervalCertificateBound pkg B' G Ha Hb)
        (conversionFactorCoefficientBound pkg B' G))
      (errorExpansionTerm (fun _ => pkg) a sigma I K)
      (scalarBoundTerm (fun _ => pkg) a H B' I K)) := by
  obtain ⟨cexpansion⟩ :=
    bounded_errorExpansionTerm_le_errorBoundTerm_at pkg a sigma
      hsigma hsigmaDegree hsigmaNorm hHsigmaNorm hHa hHb ca cBa
      haDegree haNorm hG hδ hB htheta I K
  obtain ⟨cscalar⟩ :=
    bounded_errorBoundTerm_le_scalarBoundTerm_at pkg a sigma
      hsigma hsigmaDegree hsigmaNorm hHsigmaNorm csigma hHa hHb
      ca cBa haDegree haNorm hG hδ hB htheta htheta1 hB'
      hBcondition I K
  exact ⟨by
    simpa [conversionOddTermOrder, boundedConversionOddTermBudget] using
      cexpansion.trans cscalar⟩

/-- Number of squarefree subsets of an s-element index type. -/
def conversionSubsetCount (s : ℕ) : ℝ :=
  ((Finset.univ : Finset (Finset (Fin s))).card : ℝ)

/-- Budget after summing one common term budget over both subset indices. -/
def boundedConvertedOddBudget (s : ℕ) (termBudget : ℝ) : ℝ :=
  conversionSubsetCount s * (conversionSubsetCount s * termBudget)

end OptimalConvergenceRates.GeneralArchimedean

end

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

variable {n m : ℕ}

/-- The complete odd aggregate satisfies the scalar absorption comparison
with an explicit coefficient budget. -/
theorem bounded_convertedOdd_le_oddAbsorptionCoefficient_at
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
      (conversionOddTermOrder pkg s d rSigma rA rB)
      (boundedConvertedOddBudget s
        (boundedConversionOddTermBudget s HsigmaCert HsigmaNorm theta
          (conversionIntervalCertificateBound pkg B' G Ha Hb)
          (conversionFactorCoefficientBound pkg B' G)))
      (convertedOdd (fun _ => pkg) a sigma)
      (C (oddAbsorptionCoefficient s H B' theta δ) *
        denominatorProduct (fun _ => pkg) a)) := by
  classical
  let Sall : Finset (Finset (Fin s)) :=
    (Finset.univ : Finset (Fin s)).powerset
  let Hint := conversionIntervalCertificateBound pkg B' G Ha Hb
  let Kfactor := conversionFactorCoefficientBound pkg B' G
  let HT := boundedConversionOddTermBudget s HsigmaCert HsigmaNorm
    theta Hint Kfactor
  have hHint : 0 ≤ Hint := by
    dsimp [Hint]
    exact conversionIntervalCertificateBound_nonneg pkg B' hB hG hHa hHb
  have hKfactor : 0 ≤ Kfactor := by
    dsimp [Kfactor]
    exact conversionFactorCoefficientBound_nonneg pkg B' G
  have hHsigmaCert : 0 ≤ HsigmaCert :=
    (csigma ∅).bound_nonneg
  have hHT : 0 ≤ HT := by
    dsimp [HT, boundedConversionOddTermBudget,
      boundedConversionExpansionBudget, boundedConversionContextBound,
      boundedConversionProductBudget, boundedConversionScalarBudget,
      boundedConversionSecondScalarBudget,
      boundedConversionFirstScalarBudget,
      boundedConversionNumeratorProductBudget,
      boundedConversionErrorProductBudget]
    positivity
  have hterm (I K : Finset (Fin s)) :
      Nonempty (BoundedModuleLEAt g
        (conversionOddTermOrder pkg s d rSigma rA rB) HT
        (errorExpansionTerm (fun _ => pkg) a sigma I K)
        (scalarBoundTerm (fun _ => pkg) a H B' I K)) := by
    simpa [HT, Hint, Kfactor] using
      bounded_errorExpansionTerm_le_scalarBoundTerm_at pkg a sigma
        hsigma hsigmaDegree hsigmaNorm hHsigmaNorm csigma hHa hHb
        ca cBa haDegree haNorm hG hδ hB htheta htheta1 hB'
        hBcondition I K
  have hinner (I : Finset (Fin s)) (hI : I ∈ Sall) :
      Nonempty (BoundedModuleLEAt g
        (conversionOddTermOrder pkg s d rSigma rA rB)
        ((Sall.card : ℝ) * HT)
        (oddErrorSum (fun _ => pkg) a sigma I)
        (∑ K ∈ I.powerset.filter (fun K => ¬ Even K.card),
          C (scalarErrorCoefficient H B' theta δ I K) *
            denominatorProduct (fun _ => pkg) a)) := by
    let T := I.powerset.filter (fun K => ¬ Even K.card)
    obtain ⟨craw⟩ := BoundedModuleLEAt.sum_nonempty T
      (fun K => errorExpansionTerm (fun _ => pkg) a sigma I K)
      (fun K => C (scalarErrorCoefficient H B' theta δ I K) *
        denominatorProduct (fun _ => pkg) a)
      (fun K hK => by
        have hKI : K ⊆ I :=
          Finset.mem_powerset.mp (Finset.mem_filter.mp hK).1
        obtain ⟨c⟩ := hterm I K
        rw [scalarBoundTerm_eq_coefficient_mul_denominator
          (fun _ => pkg) a H B' I K hKI] at c
        exact ⟨c⟩)
    have hsubset : T ⊆ Sall := by
      intro K hK
      have hKI : K ⊆ I :=
        Finset.mem_powerset.mp (Finset.mem_filter.mp hK).1
      have hIuniv : I ⊆ (Finset.univ : Finset (Fin s)) :=
        Finset.mem_powerset.mp hI
      exact Finset.mem_powerset.mpr (hKI.trans hIuniv)
    have hcardNat : T.card ≤ Sall.card :=
      Finset.card_le_card hsubset
    have hcard : (T.card : ℝ) ≤ (Sall.card : ℝ) := by
      exact_mod_cast hcardNat
    have cbounded := craw.weakenBound
      (mul_le_mul_of_nonneg_right hcard hHT)
    exact ⟨by simpa [T, oddErrorSum] using cbounded⟩
  obtain ⟨couter⟩ := BoundedModuleLEAt.sum_nonempty Sall
    (fun I => oddErrorSum (fun _ => pkg) a sigma I)
    (fun I =>
      ∑ K ∈ I.powerset.filter (fun K => ¬ Even K.card),
        C (scalarErrorCoefficient H B' theta δ I K) *
          denominatorProduct (fun _ => pkg) a)
    hinner
  have cfinal : BoundedModuleLEAt g
      (conversionOddTermOrder pkg s d rSigma rA rB)
      ((Sall.card : ℝ) * ((Sall.card : ℝ) * HT))
      (convertedOdd (fun _ => pkg) a sigma)
      (C (oddAbsorptionCoefficient s H B' theta δ) *
        denominatorProduct (fun _ => pkg) a) := by
    simpa only [convertedOdd, oddAbsorptionCoefficient,
      map_sum, Finset.sum_mul, Sall] using couter
  exact ⟨by
    simpa [boundedConvertedOddBudget, conversionSubsetCount, Sall,
      HT, Hint, Kfactor] using cfinal⟩

end OptimalConvergenceRates.GeneralArchimedean

end
