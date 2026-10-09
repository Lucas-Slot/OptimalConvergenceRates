/-
  Coefficient-bounded Archimedean bridge for the quantitative conversion.
-/
import OptimalConvergenceRates.GeneralArchimedean.QuantitativeBridge
import OptimalConvergenceRates.GeneralArchimedean.BoundedArchimedeanEnvelope
import OptimalConvergenceRates.GeneralArchimedean.BoundedDenominatorCertificate

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

variable {n m s : ℕ}

/-- An Archimedean module has a common bounded certificate for all coordinate
square bounds.  Its numerical budget is fixed by the module. -/
theorem IsArchimedean.exists_bounded_truncated_coordinate_square_bound
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (harch : IsArchimedean g) :
    ∃ B t Hcoord, 1 ≤ B ∧ 0 ≤ Hcoord ∧
      ∀ i : Fin n,
        Nonempty (BoundedQuadraticModuleCertificate g
          (C B - X i ^ 2) t Hcoord) := by
  classical
  obtain ⟨B, t, hB, hcoord⟩ :=
    harch.exists_truncated_coordinate_square_bound
  have hexists (i : Fin n) :
      ∃ Hi, Nonempty (BoundedQuadraticModuleCertificate g
        (C B - X i ^ 2) t Hi) :=
    BoundedQuadraticModuleCertificate.exists_of_mem (hcoord i)
  choose Hi cHi using hexists
  let ci (i : Fin n) := Classical.choice (cHi i)
  let Hcoord : ℝ := ∑ i : Fin n, Hi i
  have hHi (i : Fin n) : 0 ≤ Hi i := (ci i).bound_nonneg
  have hHcoord : 0 ≤ Hcoord := by
    dsimp [Hcoord]
    exact Finset.sum_nonneg fun i _ => hHi i
  refine ⟨B, t, Hcoord, hB, hHcoord, fun i => ?_⟩
  exact ⟨(ci i).weakenBound <| by
    dsimp [Hcoord]
    exact Finset.single_le_sum
      (fun j _ => hHi j) (Finset.mem_univ i)⟩

/-- Uniform bounded-envelope budget for polynomials of degree at most `d`
and coefficient norm at most `H`. -/
def boundedArchimedeanEnvelopeBudget
    (n d : ℕ) (B Hcoord H : ℝ) : ℝ :=
  boundedCoeffEnvelopeBudgetUpper
    (boundedMonomialCount n d) n d B Hcoord H

theorem boundedArchimedeanEnvelopeBudget_nonneg
    (n d : ℕ) {B Hcoord H : ℝ}
    (hB : 0 ≤ B) (hHcoord : 0 ≤ Hcoord) (hH : 0 ≤ H) :
    0 ≤ boundedArchimedeanEnvelopeBudget n d B Hcoord H := by
  unfold boundedArchimedeanEnvelopeBudget
  unfold boundedCoeffEnvelopeBudgetUpper
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    (by
      have hQ := boundedMonomialSquareBudget_nonneg n d hB hHcoord
      linarith)

theorem boundedWeightedCoeffMinusBudget_le_uniform
    {B Hcoord H : ℝ} {d : ℕ}
    (hB : 0 ≤ B) (hHcoord : 0 ≤ Hcoord) (hH : 0 ≤ H)
    (q : MvPolynomial (Fin n) ℝ)
    (hqDegree : q.totalDegree ≤ d)
    (hqNorm : coeffL1Norm q ≤ H) :
    boundedWeightedCoeffMinusBudget n d B Hcoord q ≤
      boundedArchimedeanEnvelopeBudget n d B Hcoord H := by
  have hbase :=
    boundedWeightedCoeffMinusBudget_le n d hB hHcoord hH q hqNorm
  apply hbase.trans
  unfold boundedCoeffEnvelopeBudgetUpper
  unfold boundedArchimedeanEnvelopeBudget
  unfold boundedCoeffEnvelopeBudgetUpper
  have hcardNat := support_card_le_boundedMonomialCount q hqDegree
  have hcard :
      (q.support.card : ℝ) ≤ (boundedMonomialCount n d : ℝ) := by
    exact_mod_cast hcardNat
  have hfactor :
      0 ≤ (H + 1) ^ 2 *
        (boundedMonomialSquareBudget n d B Hcoord + 1) := by
    exact mul_nonneg (sq_nonneg _) (by
      have hQ := boundedMonomialSquareBudget_nonneg n d hB hHcoord
      linarith)
  nlinarith

/-- A scalar upper bound above the weighted envelope gives a bounded
quadratic-module certificate for the corresponding polynomial inequality. -/
theorem bounded_polynomial_le_constant_of_coordinate_bounds
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B Hcoord U H : ℝ} {t d : ℕ}
    (hB : 1 ≤ B) (hHcoord : 0 ≤ Hcoord)
    (hcoord : ∀ i : Fin n,
      BoundedQuadraticModuleCertificate g (C B - X i ^ 2) t Hcoord)
    (q : MvPolynomial (Fin n) ℝ)
    (hqDegree : q.totalDegree ≤ d)
    (hH : 0 ≤ H) (hqNorm : coeffL1Norm q ≤ H)
    (hU : 0 ≤ U)
    (henv : weightedCoeffEnvelope B q ≤ U) :
    Nonempty (BoundedQuadraticModuleCertificate g
      (C U - q)
      (boundedCoeffEnvelopeOrder n t d)
      (U + boundedArchimedeanEnvelopeBudget n d B Hcoord H)) := by
  obtain ⟨cenvRaw⟩ := bounded_weightedCoeffEnvelope_minus_mem_at
    hB hHcoord hcoord q hqDegree
  let Henv := boundedArchimedeanEnvelopeBudget n d B Hcoord H
  have cenv : BoundedQuadraticModuleCertificate g
      (C (weightedCoeffEnvelope B q) - q)
      (boundedCoeffEnvelopeOrder n t d) Henv :=
    cenvRaw.weakenBound <|
      boundedWeightedCoeffMinusBudget_le_uniform
        (zero_le_one.trans hB) hHcoord hH q hqDegree hqNorm
  have hgap : 0 ≤ U - weightedCoeffEnvelope B q :=
    sub_nonneg.mpr henv
  let cgapRaw := BoundedQuadraticModuleCertificate.ofSOS g
    (C (U - weightedCoeffEnvelope B q))
    (IsSOS_C_nonneg _ hgap)
    (show (C (U - weightedCoeffEnvelope B q) :
      MvPolynomial (Fin n) ℝ).totalDegree ≤
        boundedCoeffEnvelopeOrder n t d by
      exact (MvPolynomial.totalDegree_C _).le.trans (Nat.zero_le _))
  have hgapBudget :
      coeffL1Norm (C (U - weightedCoeffEnvelope B q) :
        MvPolynomial (Fin n) ℝ) ≤ U := by
    calc
      _ ≤ |U - weightedCoeffEnvelope B q| :=
        coeffL1Norm_C_le _
      _ = U - weightedCoeffEnvelope B q := abs_of_nonneg hgap
      _ ≤ U := by
        exact sub_le_self _ (weightedCoeffEnvelope_nonneg
          (zero_le_one.trans hB) q)
  let cgap := cgapRaw.weakenBound hgapBudget
  exact ⟨by
    simpa [Henv, max_self] using (cgap.add cenv).congr (by
      rw [map_sub]
      ring)⟩


/-- Coefficient budget used to certify that every generator is below the
common scalar envelope. -/
def boundedBridgeGeneratorBudget
    (n d : ℕ) (R Hcoord G B : ℝ) : ℝ :=
  B + boundedArchimedeanEnvelopeBudget n d R Hcoord G

/-- Coefficient budget used to certify that every active preordering
coefficient is below its common scalar envelope. -/
def boundedBridgeSigmaBudget
    (n d : ℕ) (R Hcoord H Hconvert : ℝ) : ℝ :=
  Hconvert + boundedArchimedeanEnvelopeBudget n d R Hcoord H

/-- The coefficient budget produced by the complete bounded conversion. -/
def boundedBridgeRefutationBudget
    {eta B : ℝ} (pkg : RationalSquareRoot.Package eta B eta)
    (s n d : ℕ) (R Hcoord G H Hconvert : ℝ) : ℝ :=
  let Bprime : ℝ := 2 * (B + 1)
  let Ha : ℝ := 1
  let Hb : ℝ := boundedBridgeGeneratorBudget n d R Hcoord G B
  let HsigmaCert : ℝ :=
    boundedBridgeSigmaBudget n d R Hcoord H Hconvert
  boundedConversionRefutationBudget
    (oddAbsorptionCoefficient s Hconvert Bprime eta eta)
    (boundedConvertedOddBudget s
      (boundedConversionOddTermBudget s HsigmaCert H eta
        (conversionIntervalCertificateBound pkg Bprime G Ha Hb)
        (conversionFactorCoefficientBound pkg Bprime G)))
    (boundedConvertedEvenNorm s H
      (conversionFactorCoefficientBound pkg Bprime G))
    (boundedDenominatorProductBudget pkg s Bprime G Ha)

/-- A bounded preordering refutation converts to a bounded quadratic-module
refutation when bounded coordinate-square certificates and uniform bounds on
the generators are supplied. -/
theorem bounded_certificate_preordering_refutation_to_module_at_of_coordinate_bounds
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
      let eta : ℝ := absorptionScale s Hconvert Bprime
      ∃ pkg : RationalSquareRoot.Package eta B eta,
        (pkg.ell : ℝ) ≤
            Real.log (eta / 4) / Real.log (1 / 9) + 1 ∧
          (pkg.J : ℝ) ≤
            Real.log (Real.sqrt (B + eta) / Real.sqrt eta) /
              Real.log 2 ∧
          Nonempty (BoundedQuadraticModuleCertificate a
            (-1 : MvPolynomial (Fin n) ℝ)
            (conversionRefutationOrder pkg s d
              (boundedCoeffEnvelopeOrder n t d) d
              (boundedCoeffEnvelopeOrder n t d))
            (boundedBridgeRefutationBudget pkg s n d
              R Hcoord G H Hconvert)) := by
  classical
  let generatorSet : Finset (Fin s) := Finset.univ
  let sigmaSet : Finset (Finset (Fin s)) := Finset.univ
  let sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ :=
    activePreorderingCoefficient a c.certificate.sigma
  let B : ℝ := finiteFamilyEnvelopeBound s n d R G
  let Hconvert : ℝ :=
    finiteFamilyEnvelopeBound sigmaSet.card n d R H
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
      (fun I hI =>
        activePreorderingCoefficient_coeffL1Norm_le a c I)
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
  have hBprime : 0 ≤ Bprime := by
    dsimp [Bprime]
    positivity
  let eta : ℝ := absorptionScale s Hconvert Bprime
  have heta : 0 < eta := absorptionScale_pos hHconvert hBprime
  have hetahalf : eta ≤ 1 / 2 :=
    absorptionScale_le_half hHconvert hBprime
  have hetaone : eta ≤ 1 := hetahalf.trans (by norm_num)
  have htheta1 : eta < 1 := lt_of_le_of_lt hetahalf (by norm_num)
  have hcondition : B + eta ≤ (1 - eta) * Bprime := by
    have hfactor : 1 ≤ 2 * (1 - eta) := by linarith
    have hB1 : 0 ≤ B + 1 := by linarith
    calc
      B + eta ≤ B + 1 := by linarith
      _ = 1 * (B + 1) := by ring
      _ ≤ (2 * (1 - eta)) * (B + 1) :=
        mul_le_mul_of_nonneg_right hfactor hB1
      _ = (1 - eta) * Bprime := by dsimp [Bprime]; ring
  obtain ⟨pkg, hell, hJ⟩ :=
    RationalSquareRoot.package_nonempty_with_parameter_log_bounds
      heta hB0 heta hetaone
  refine ⟨pkg, hell, hJ, ?_⟩
  simpa [boundedBridgeRefutationBudget, Bprime] using
    bounded_refutation_of_oddAbsorptionCoefficient_with_denominator_at
      pkg a sigma hsigmaSOS hsigmaDegree hsigmaNorm hH
      csigma (by norm_num : (0 : ℝ) ≤ 1)
      (add_nonneg hB0
        (boundedArchimedeanEnvelopeBudget_nonneg n d hR0 hHcoord hG0))
      ha hBa haDegree haNorm hG heta hB heta.le htheta1 hBprime
      hcondition hidentity
      (oddAbsorptionCoefficient_scale_lt_one hHconvert hBprime)

end OptimalConvergenceRates.GeneralArchimedean

end
