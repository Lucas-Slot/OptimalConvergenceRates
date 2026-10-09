/-
  Coefficient-bounded scalar replacement for one expanded conversion term.
-/
import OptimalConvergenceRates.GeneralArchimedean.BoundedConversion

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

variable {n m : ℕ}

/-- Scaling the numerator-square comparison and adding the unchanged
denominator-square term gives the bounded comparison used for error
factors. -/
theorem bounded_errorUpper_comparison_common
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta B' : ℝ} (pkg : Package δ B theta)
    (hδ : 0 < δ) (hB : 1 ≤ B)
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hBcondition : B + δ ≤ (1 - theta) * B')
    {a : MvPolynomial (Fin n) ℝ} {r s : ℕ} {Ha Hb G : ℝ}
    (ca : BoundedQuadraticModuleCertificate g a r Ha)
    (cBa : BoundedQuadraticModuleCertificate g (C B - a) s Hb)
    (hG : 1 ≤ G) (haNorm : coeffL1Norm a ≤ G) :
    Nonempty (BoundedModuleLEAt g
      (max r s + (pkg.degreeBound + 3) * a.totalDegree)
      (theta * conversionIntervalCertificateBound pkg B' G Ha Hb)
      (C theta * pkg.substP a ^ 2 + C δ * pkg.substV a ^ 2)
      (C (theta * B' + δ) * pkg.substV a ^ 2)) := by
  let R := max r s + (pkg.degreeBound + 3) * a.totalDegree
  let Hint := conversionIntervalCertificateBound pkg B' G Ha Hb
  obtain ⟨cP⟩ := bounded_substP_sq_comparison_common pkg hδ hB
    htheta1 hBcondition ca cBa hG haNorm
  have hthetaNorm :
      coeffL1Norm (C theta : MvPolynomial (Fin n) ℝ) ≤ theta := by
    simpa [abs_of_nonneg htheta] using
      (coeffL1Norm_C_le (n := n) theta)
  have cscaled := cP.sosMulLeftOfNormLe
    (IsSOS_C_nonneg theta htheta) hthetaNorm
  have cscaled' : BoundedModuleLEAt g R (theta * Hint)
      (C theta * pkg.substP a ^ 2)
      (C theta * (C B' * pkg.substV a ^ 2)) := by
    simpa [R, Hint, MvPolynomial.totalDegree_C] using cscaled
  have crefl : BoundedModuleLEAt g R 0
      (C δ * pkg.substV a ^ 2)
      (C δ * pkg.substV a ^ 2) :=
    (BoundedModuleLEAt.refl g
      (C δ * pkg.substV a ^ 2)).mono (Nat.zero_le R)
  have cadd := cscaled'.add crefl
  let cfinal : BoundedModuleLEAt g R (theta * Hint)
      (C theta * pkg.substP a ^ 2 + C δ * pkg.substV a ^ 2)
      (C (theta * B' + δ) * pkg.substV a ^ 2) :=
    (by
      simpa [R, Hint] using cadd.congr (by ring))
  exact ⟨by simpa [R, Hint] using cfinal⟩

end OptimalConvergenceRates.GeneralArchimedean

end

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

variable {n m : ℕ}

/-- The fully expanded error upper bound lies below its scalar denominator
bound with both the truncation order and the certificate coefficient budget
made explicit. -/
theorem bounded_errorBoundTerm_le_scalarBoundTerm_at
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
      (conversionScalarTermOrder pkg s d rSigma rA rB)
      (boundedConversionScalarBudget s HsigmaCert HsigmaNorm theta
        (conversionIntervalCertificateBound pkg B' G Ha Hb)
        (conversionFactorCoefficientBound pkg B' G))
      (errorBoundTerm (fun _ => pkg) a sigma I K)
      (scalarBoundTerm (fun _ => pkg) a H B' I K)) := by
  classical
  let F := conversionFactorDegree pkg d
  let Rint := conversionIntervalOrder pkg d rA rB
  let Rprod := conversionProductOrder pkg s d rA rB
  let R₁ := max (rSigma + s * F) (Rprod + d)
  let R₂ := max (R₁ + s * F) (Rprod + (d + s * F))
  let Hint := conversionIntervalCertificateBound pkg B' G Ha Hb
  let Kfactor := conversionFactorCoefficientBound pkg B' G
  let HPP := boundedConversionNumeratorProductBudget s Hint Kfactor
  let HEP := boundedConversionErrorProductBudget s theta Hint Kfactor
  let H₁ := boundedConversionFirstScalarBudget s HsigmaCert
    HsigmaNorm Hint Kfactor
  let H₂ := boundedConversionSecondScalarBudget s HsigmaCert
    HsigmaNorm theta Hint Kfactor
  have hKfactor : 0 ≤ Kfactor := by
    dsimp [Kfactor]
    exact conversionFactorCoefficientBound_nonneg pkg B' G
  have hbase : 1 ≤ Kfactor + 1 := by linarith
  have hHint : 0 ≤ Hint := by
    dsimp [Hint]
    exact conversionIntervalCertificateBound_nonneg pkg B' hB hG hHa hHb
  have hThetaHint : 0 ≤ theta * Hint :=
    mul_nonneg htheta hHint
  have hP (i : Fin s) : Nonempty (BoundedModuleLEAt g Rint Hint
      (pkg.substP (a i) ^ 2)
      (C B' * pkg.substV (a i) ^ 2)) := by
    obtain ⟨c⟩ := bounded_substP_sq_comparison_common pkg hδ hB
      htheta1 hBcondition (ca i) (cBa i) hG (haNorm i)
    refine ⟨c.mono ?_⟩
    simpa [Rint, conversionIntervalOrder] using
      Nat.add_le_add_left
        (Nat.mul_le_mul_left (pkg.degreeBound + 3) (haDegree i))
        (max rA rB)
  have herror (i : Fin s) :
      Nonempty (BoundedModuleLEAt g Rint (theta * Hint)
        (C theta * pkg.substP (a i) ^ 2 +
          C δ * pkg.substV (a i) ^ 2)
        (C (theta * B' + δ) * pkg.substV (a i) ^ 2)) := by
    obtain ⟨c⟩ := bounded_errorUpper_comparison_common pkg hδ hB
      htheta htheta1 hBcondition (ca i) (cBa i) hG (haNorm i)
    refine ⟨c.mono ?_⟩
    simpa [Rint, Hint, conversionIntervalOrder] using
      Nat.add_le_add_left
        (Nat.mul_le_mul_left (pkg.degreeBound + 3) (haDegree i))
        (max rA rB)
  have hPDegree (i : Fin s) :
      (pkg.substP (a i) ^ 2).totalDegree ≤ F :=
    (pkg.substP_sq_totalDegree_le (a i)).trans
      (Nat.mul_le_mul_left pkg.degreeBound (haDegree i))
  have hVDegree (i : Fin s) :
      (pkg.substV (a i) ^ 2).totalDegree ≤ F :=
    (pkg.substV_sq_totalDegree_le (a i)).trans
      (Nat.mul_le_mul_left pkg.degreeBound (haDegree i))
  have hPUpperDegree (i : Fin s) :
      (C B' * pkg.substV (a i) ^ 2).totalDegree ≤ F :=
    (mv_C_mul_totalDegree_le B' _).trans (hVDegree i)
  have hErrorDegree (i : Fin s) :
      (C theta * pkg.substP (a i) ^ 2 +
        C δ * pkg.substV (a i) ^ 2).totalDegree ≤ F := by
    exact (MvPolynomial.totalDegree_add _ _).trans <| max_le
      ((mv_C_mul_totalDegree_le theta _).trans (hPDegree i))
      ((mv_C_mul_totalDegree_le δ _).trans (hVDegree i))
  have hErrorUpperDegree (i : Fin s) :
      (C (theta * B' + δ) * pkg.substV (a i) ^ 2).totalDegree ≤ F :=
    (mv_C_mul_totalDegree_le (theta * B' + δ) _).trans (hVDegree i)
  have hPNorm (i : Fin s) :
      coeffL1Norm (pkg.substP (a i) ^ 2) ≤ Kfactor := by
    dsimp [Kfactor]
    exact substP_sq_coeffL1Norm_le_conversionFactor
      pkg B' (a i) hG (haNorm i)
  have hVNorm (i : Fin s) :
      coeffL1Norm (pkg.substV (a i) ^ 2) ≤ Kfactor := by
    dsimp [Kfactor]
    exact substV_sq_coeffL1Norm_le_conversionFactor
      pkg B' (a i) hG (haNorm i)
  have hPUpperNorm (i : Fin s) :
      coeffL1Norm (C B' * pkg.substV (a i) ^ 2) ≤ Kfactor := by
    dsimp [Kfactor]
    exact numeratorUpper_coeffL1Norm_le_conversionFactor
      pkg B' (a i) hG (haNorm i)
  have hErrorNorm (i : Fin s) :
      coeffL1Norm
        (C theta * pkg.substP (a i) ^ 2 +
          C δ * pkg.substV (a i) ^ 2) ≤ Kfactor := by
    dsimp [Kfactor]
    exact errorUpper_coeffL1Norm_le_conversionFactor
      pkg B' (a i) hG (haNorm i)
  have hErrorUpperNorm (i : Fin s) :
      coeffL1Norm
        (C (theta * B' + δ) * pkg.substV (a i) ^ 2) ≤ Kfactor := by
    dsimp [Kfactor]
    exact errorScalarUpper_coeffL1Norm_le_conversionFactor
      pkg B' (a i) hG (haNorm i)
  obtain ⟨cPprodRaw⟩ := BoundedModuleLEAt.prod (I \ K)
    (fun i => pkg.substP (a i) ^ 2)
    (fun i => C B' * pkg.substV (a i) ^ 2)
    Rint F hHint hKfactor
    (fun i hi => IsSOS_sq _)
    (fun i hi => IsSOS_mul (IsSOS_C_nonneg B' hB') (IsSOS_sq _))
    (fun i hi => hPDegree i) (fun i hi => hPUpperDegree i)
    (fun i hi => hPNorm i) (fun i hi => hPUpperNorm i)
    (fun i hi => (hP i).some)
  have hPprodOrder : (I \ K).card * (Rint + F) ≤ Rprod := by
    dsimp [Rprod, conversionProductOrder]
    exact Nat.mul_le_mul_right (Rint + F) (finset_fin_card_le (I \ K))
  have hPprodBudget :
      (Kfactor + 1) ^ (I \ K).card * Hint ≤ HPP := by
    dsimp [HPP, boundedConversionNumeratorProductBudget]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hbase (finset_fin_card_le (I \ K))) hHint
  let cPprod : BoundedModuleLEAt g Rprod HPP
      (∏ i ∈ I \ K, pkg.substP (a i) ^ 2)
      (∏ i ∈ I \ K, C B' * pkg.substV (a i) ^ 2) :=
    (cPprodRaw.mono hPprodOrder).weakenBound hPprodBudget
  obtain ⟨cEprodRaw⟩ := BoundedModuleLEAt.prod K
    (fun i => C theta * pkg.substP (a i) ^ 2 +
      C δ * pkg.substV (a i) ^ 2)
    (fun i => C (theta * B' + δ) * pkg.substV (a i) ^ 2)
    Rint F hThetaHint hKfactor
    (fun i hi => IsSOS_add
      (IsSOS_mul (IsSOS_C_nonneg theta htheta) (IsSOS_sq _))
      (IsSOS_mul (IsSOS_C_nonneg δ hδ.le) (IsSOS_sq _)))
    (fun i hi => IsSOS_mul
      (IsSOS_C_nonneg (theta * B' + δ)
        (add_nonneg (mul_nonneg htheta hB') hδ.le))
      (IsSOS_sq _))
    (fun i hi => hErrorDegree i) (fun i hi => hErrorUpperDegree i)
    (fun i hi => hErrorNorm i) (fun i hi => hErrorUpperNorm i)
    (fun i hi => (herror i).some)
  have hEprodOrder : K.card * (Rint + F) ≤ Rprod := by
    dsimp [Rprod, conversionProductOrder]
    exact Nat.mul_le_mul_right (Rint + F) (finset_fin_card_le K)
  have hEprodBudget :
      (Kfactor + 1) ^ K.card * (theta * Hint) ≤ HEP := by
    dsimp [HEP, boundedConversionErrorProductBudget]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hbase (finset_fin_card_le K)) hThetaHint
  let cEprod : BoundedModuleLEAt g Rprod HEP
      (∏ i ∈ K,
        (C theta * pkg.substP (a i) ^ 2 +
          C δ * pkg.substV (a i) ^ 2))
      (∏ i ∈ K,
        C (theta * B' + δ) * pkg.substV (a i) ^ 2) :=
    (cEprodRaw.mono hEprodOrder).weakenBound hEprodBudget
  have hPUpperSOS : IsSOS
      (∏ i ∈ I \ K, C B' * pkg.substV (a i) ^ 2) :=
    IsSOS_finset_prod fun i hi =>
      IsSOS_mul (IsSOS_C_nonneg B' hB') (IsSOS_sq _)
  have hPLowerSOS : IsSOS
      (∏ i ∈ I \ K, pkg.substP (a i) ^ 2) :=
    IsSOS_finset_prod fun i hi => IsSOS_sq _
  have hEUpperSOS : IsSOS
      (∏ i ∈ K,
        C (theta * B' + δ) * pkg.substV (a i) ^ 2) :=
    IsSOS_finset_prod fun i hi => IsSOS_mul
      (IsSOS_C_nonneg (theta * B' + δ)
        (add_nonneg (mul_nonneg htheta hB') hδ.le))
      (IsSOS_sq _)
  have hVSOS : IsSOS (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2) :=
    IsSOS_finset_prod fun i hi => IsSOS_sq _
  have hPProdNorm :
      coeffL1Norm (∏ i ∈ I \ K, pkg.substP (a i) ^ 2) ≤
        (Kfactor + 1) ^ s :=
    coeffL1Norm_finset_prod_le_common_pow (I \ K)
      (fun i => pkg.substP (a i) ^ 2) hKfactor
      (finset_fin_card_le (I \ K)) (fun i hi => hPNorm i)
  have hPUpperProdNorm :
      coeffL1Norm
        (∏ i ∈ I \ K, C B' * pkg.substV (a i) ^ 2) ≤
          (Kfactor + 1) ^ s :=
    coeffL1Norm_finset_prod_le_common_pow (I \ K)
      (fun i => C B' * pkg.substV (a i) ^ 2) hKfactor
      (finset_fin_card_le (I \ K)) (fun i hi => hPUpperNorm i)
  have hEUpperProdNorm :
      coeffL1Norm
        (∏ i ∈ K,
          C (theta * B' + δ) * pkg.substV (a i) ^ 2) ≤
          (Kfactor + 1) ^ s :=
    coeffL1Norm_finset_prod_le_common_pow K
      (fun i => C (theta * B' + δ) * pkg.substV (a i) ^ 2)
      hKfactor (finset_fin_card_le K) (fun i hi => hErrorUpperNorm i)
  have hVProdNorm :
      coeffL1Norm (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2) ≤
        (Kfactor + 1) ^ s :=
    coeffL1Norm_finset_prod_le_common_pow Iᶜ
      (fun i => pkg.substV (a i) ^ 2) hKfactor
      (finset_fin_card_le Iᶜ) (fun i hi => hVNorm i)
  have hPLowerDegree :
      (∏ i ∈ I \ K, pkg.substP (a i) ^ 2).totalDegree ≤ s * F :=
    (totalDegree_finset_prod_le_card_mul (I \ K) _ F
      (fun i hi => hPDegree i)).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le (I \ K)))
  have hPUpperProdDegree :
      (∏ i ∈ I \ K, C B' * pkg.substV (a i) ^ 2).totalDegree ≤
        s * F :=
    (totalDegree_finset_prod_le_card_mul (I \ K) _ F
      (fun i hi => hPUpperDegree i)).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le (I \ K)))
  have hEUpperProdDegree :
      (∏ i ∈ K,
        C (theta * B' + δ) * pkg.substV (a i) ^ 2).totalDegree ≤
          s * F :=
    (totalDegree_finset_prod_le_card_mul K _ F
      (fun i hi => hErrorUpperDegree i)).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le K))
  have hVProdDegree :
      (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2).totalDegree ≤ s * F :=
    (totalDegree_finset_prod_le_card_mul Iᶜ _ F
      (fun i hi => hVDegree i)).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le Iᶜ))
  have hfirstRaw := BoundedModuleLEAt.mulOfNormLe
    (csigma I) cPprod (hsigma I) hPUpperSOS
    (hsigmaNorm I) hPUpperProdNorm
  have hfirstOrder :
      max
        ((∏ i ∈ I \ K,
          C B' * pkg.substV (a i) ^ 2).totalDegree + rSigma)
        ((sigma I).totalDegree + Rprod) ≤ R₁ := by
    apply max_le
    · calc
        _ ≤ s * F + rSigma :=
          Nat.add_le_add_right hPUpperProdDegree rSigma
        _ = rSigma + s * F := by omega
        _ ≤ R₁ := le_max_left _ _
    · calc
        _ ≤ d + Rprod :=
          Nat.add_le_add_right (hsigmaDegree I) Rprod
        _ = Rprod + d := by omega
        _ ≤ R₁ := le_max_right _ _
  let cfirst : BoundedModuleLEAt g R₁ H₁
      (sigma I * ∏ i ∈ I \ K, pkg.substP (a i) ^ 2)
      (C H * ∏ i ∈ I \ K,
        C B' * pkg.substV (a i) ^ 2) := by
    simpa [H₁, boundedConversionFirstScalarBudget] using
      hfirstRaw.mono hfirstOrder
  have hLowerPrefixNorm :
      coeffL1Norm
        (sigma I * ∏ i ∈ I \ K, pkg.substP (a i) ^ 2) ≤
          HsigmaNorm * (Kfactor + 1) ^ s := by
    exact (coeffL1Norm_mul_le _ _).trans
      (mul_le_mul (hsigmaNorm I) hPProdNorm
        (coeffL1Norm_nonneg _) hHsigmaNorm)
  have hLowerPrefixDegree :
      (sigma I * ∏ i ∈ I \ K,
        pkg.substP (a i) ^ 2).totalDegree ≤ d + s * F :=
    (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add (hsigmaDegree I) hPLowerDegree)
  have hsecondRaw := BoundedModuleLEAt.mulOfNormLe cfirst cEprod
    (IsSOS_mul (hsigma I) hPLowerSOS) hEUpperSOS
    hLowerPrefixNorm hEUpperProdNorm
  have hsecondOrder :
      max
        ((∏ i ∈ K,
          C (theta * B' + δ) * pkg.substV (a i) ^ 2).totalDegree + R₁)
        ((sigma I * ∏ i ∈ I \ K,
          pkg.substP (a i) ^ 2).totalDegree + Rprod) ≤ R₂ := by
    apply max_le
    · calc
        _ ≤ s * F + R₁ :=
          Nat.add_le_add_right hEUpperProdDegree R₁
        _ = R₁ + s * F := by omega
        _ ≤ R₂ := le_max_left _ _
    · calc
        _ ≤ (d + s * F) + Rprod :=
          Nat.add_le_add_right hLowerPrefixDegree Rprod
        _ = Rprod + (d + s * F) := by omega
        _ ≤ R₂ := le_max_right _ _
  let csecond : BoundedModuleLEAt g R₂ H₂
      ((sigma I * ∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
        ∏ i ∈ K,
          (C theta * pkg.substP (a i) ^ 2 +
            C δ * pkg.substV (a i) ^ 2))
      ((C H * ∏ i ∈ I \ K,
          C B' * pkg.substV (a i) ^ 2) *
        ∏ i ∈ K,
          C (theta * B' + δ) * pkg.substV (a i) ^ 2) := by
    simpa [H₂, boundedConversionSecondScalarBudget] using
      hsecondRaw.mono hsecondOrder
  have hthirdRaw := csecond.sosMulLeftOfNormLe hVSOS hVProdNorm
  have hthirdOrder :
      (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2).totalDegree + R₂ ≤
        R₂ + s * F := by
    calc
      _ ≤ s * F + R₂ := Nat.add_le_add_right hVProdDegree R₂
      _ = R₂ + s * F := by omega
  have hthird := hthirdRaw.mono hthirdOrder
  let cfinal : BoundedModuleLEAt g
      (conversionScalarTermOrder pkg s d rSigma rA rB)
      ((Kfactor + 1) ^ s * H₂)
      (errorBoundTerm (fun _ => pkg) a sigma I K)
      (scalarBoundTerm (fun _ => pkg) a H B' I K) := by
    simpa only [conversionScalarTermOrder, R₁, R₂, Rprod, Rint, F] using
      hthird.congr (by
        dsimp [errorBoundTerm, scalarBoundTerm]
        ring)
  exact ⟨by
    simpa [boundedConversionScalarBudget, H₂, Kfactor, Hint] using cfinal⟩

end OptimalConvergenceRates.GeneralArchimedean

end
