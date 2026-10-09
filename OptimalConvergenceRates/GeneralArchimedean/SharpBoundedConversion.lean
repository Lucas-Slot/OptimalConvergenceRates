/-
  Coefficient-tracked form of the sharp two-channel conversion.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpQuantitativeConversion
import OptimalConvergenceRates.GeneralArchimedean.BoundedFinalConversion

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

variable {n m : ℕ}

theorem theta_substP_sq_coeffL1Norm_le_conversionFactor
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (B' : ℝ) (a : MvPolynomial (Fin n) ℝ) {G : ℝ}
    (hG : 1 ≤ G) (ha : coeffL1Norm a ≤ G) :
    coeffL1Norm (C theta * pkg.substP a ^ 2) ≤
      conversionFactorCoefficientBound pkg B' G := by
  let S := pkg.substitutionCoefficientBound G
  have hP := pkg.substP_sq_coeffL1Norm_le a hG ha
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact zero_le_one.trans (pkg.one_le_substitutionCoefficientBound hG)
  calc
    coeffL1Norm (C theta * pkg.substP a ^ 2) ≤
        |theta| * coeffL1Norm (pkg.substP a ^ 2) :=
      coeffL1Norm_C_mul_le _ _
    _ ≤ |theta| * S ^ 2 :=
      mul_le_mul_of_nonneg_left hP (abs_nonneg theta)
    _ ≤ (|theta| + |δ| + |B'| + |theta * B' + δ| + 2) *
          (S + 1) ^ 2 := by
      have hc : |theta| ≤
          |theta| + |δ| + |B'| + |theta * B' + δ| + 2 := by
        have := abs_nonneg δ
        have := abs_nonneg B'
        have := abs_nonneg (theta * B' + δ)
        linarith
      have hp : S ^ 2 ≤ (S + 1) ^ 2 :=
        pow_le_pow_left₀ hS0 (by linarith) 2
      exact mul_le_mul hc hp (sq_nonneg S) (by positivity)

theorem delta_substV_sq_coeffL1Norm_le_conversionFactor
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (B' : ℝ) (a : MvPolynomial (Fin n) ℝ) {G : ℝ}
    (hG : 1 ≤ G) (ha : coeffL1Norm a ≤ G) :
    coeffL1Norm (C δ * pkg.substV a ^ 2) ≤
      conversionFactorCoefficientBound pkg B' G := by
  let S := pkg.substitutionCoefficientBound G
  have hV := pkg.substV_sq_coeffL1Norm_le a hG ha
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact zero_le_one.trans (pkg.one_le_substitutionCoefficientBound hG)
  calc
    coeffL1Norm (C δ * pkg.substV a ^ 2) ≤
        |δ| * coeffL1Norm (pkg.substV a ^ 2) :=
      coeffL1Norm_C_mul_le _ _
    _ ≤ |δ| * S ^ 2 :=
      mul_le_mul_of_nonneg_left hV (abs_nonneg δ)
    _ ≤ (|theta| + |δ| + |B'| + |theta * B' + δ| + 2) *
          (S + 1) ^ 2 := by
      have hc : |δ| ≤
          |theta| + |δ| + |B'| + |theta * B' + δ| + 2 := by
        have := abs_nonneg theta
        have := abs_nonneg B'
        have := abs_nonneg (theta * B' + δ)
        linarith
      have hp : S ^ 2 ≤ (S + 1) ^ 2 :=
        pow_le_pow_left₀ hS0 (by linarith) 2
      exact mul_le_mul hc hp (sq_nonneg S) (by positivity)

theorem thetaNumeratorUpper_coeffL1Norm_le_conversionFactor
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (B' : ℝ) (a : MvPolynomial (Fin n) ℝ) {G : ℝ}
    (hG : 1 ≤ G) (ha : coeffL1Norm a ≤ G) :
    coeffL1Norm (C (theta * B') * pkg.substV a ^ 2) ≤
      conversionFactorCoefficientBound pkg B' G := by
  let S := pkg.substitutionCoefficientBound G
  have hV := pkg.substV_sq_coeffL1Norm_le a hG ha
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact zero_le_one.trans (pkg.one_le_substitutionCoefficientBound hG)
  calc
    coeffL1Norm (C (theta * B') * pkg.substV a ^ 2) ≤
        |theta * B'| * coeffL1Norm (pkg.substV a ^ 2) :=
      coeffL1Norm_C_mul_le _ _
    _ ≤ |theta * B'| * S ^ 2 :=
      mul_le_mul_of_nonneg_left hV (abs_nonneg _)
    _ ≤ (|theta| + |δ| + |B'| + |theta * B' + δ| + 2) *
          (S + 1) ^ 2 := by
      have htri : |theta * B'| ≤ |theta * B' + δ| + |δ| := by
        calc
          |theta * B'| = |(theta * B' + δ) - δ| := by ring_nf
          _ ≤ |theta * B' + δ| + |δ| := abs_sub _ _
      have hc : |theta * B'| ≤
          |theta| + |δ| + |B'| + |theta * B' + δ| + 2 := by
        have := abs_nonneg theta
        have := abs_nonneg B'
        linarith
      have hp : S ^ 2 ≤ (S + 1) ^ 2 :=
        pow_le_pow_left₀ hS0 (by linarith) 2
      exact mul_le_mul hc hp (sq_nonneg S) (by positivity)

/-- A scaled numerator comparison with the same common interval budget. -/
theorem bounded_theta_substP_sq_comparison_common
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
      (C theta * pkg.substP a ^ 2)
      (C (theta * B') * pkg.substV a ^ 2)) := by
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
  exact ⟨by
    simpa [R, Hint, MvPolynomial.totalDegree_C] using
      cscaled.congr (by ring)⟩

/-- Coarse but explicit budget for one refined scalar comparison. -/
def boundedSharpScalarBudget
    (s : ℕ) (sigmaCertificateBound sigmaNormBound theta
      comparisonBound factorBound : ℝ) : ℝ :=
  let P := (factorBound + 1) ^ s
  let HP := P * comparisonBound
  let HT := P * (theta * comparisonBound)
  let H1 := P * sigmaCertificateBound + sigmaNormBound * HP
  let H2 := P * H1
  let H3 := P * H2 + (sigmaNormBound * P ^ 2) * HT
  P * H3

/-- The refined scalar comparison with an explicit coefficient budget. -/
theorem bounded_refinedErrorBoundTerm_le_refinedScalarBoundTerm_at
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
    (I K L : Finset (Fin s)) :
    Nonempty (BoundedModuleLEAt g
      (conversionSharpScalarTermOrder pkg s d rSigma rA rB)
      (boundedSharpScalarBudget s HsigmaCert HsigmaNorm theta
        (conversionIntervalCertificateBound pkg B' G Ha Hb)
        (conversionFactorCoefficientBound pkg B' G))
      (refinedErrorBoundTerm (fun _ => pkg) a sigma I K L)
      (refinedScalarBoundTerm (fun _ => pkg) a H B' I K L)) := by
  classical
  let F := conversionFactorDegree pkg d
  let Rint := conversionIntervalOrder pkg d rA rB
  let Rprod := conversionProductOrder pkg s d rA rB
  let R1 := max (rSigma + s * F) (Rprod + d)
  let R2 := max (R1 + s * F) (d + s * F)
  let R3 := max (R2 + s * F) (Rprod + (d + 2 * s * F))
  let R4 := max (R3 + s * F) (d + 3 * s * F)
  let Hint := conversionIntervalCertificateBound pkg B' G Ha Hb
  let Kfactor := conversionFactorCoefficientBound pkg B' G
  let P := (Kfactor + 1) ^ s
  let HP := P * Hint
  let HT := P * (theta * Hint)
  let H1 := P * HsigmaCert + HsigmaNorm * HP
  let H2 := P * H1
  let H3 := P * H2 + (HsigmaNorm * P ^ 2) * HT
  have hKfactor : 0 ≤ Kfactor := by
    dsimp [Kfactor]
    exact conversionFactorCoefficientBound_nonneg pkg B' G
  have hPnonneg : 0 ≤ P := by dsimp [P]; positivity
  have hHint : 0 ≤ Hint := by
    dsimp [Hint]
    exact conversionIntervalCertificateBound_nonneg pkg B' hB hG hHa hHb
  have hThetaHint : 0 ≤ theta * Hint := mul_nonneg htheta hHint
  have hcomp (i : Fin s) : Nonempty (BoundedModuleLEAt g Rint Hint
      (pkg.substP (a i) ^ 2)
      (C B' * pkg.substV (a i) ^ 2)) := by
    obtain ⟨c⟩ := bounded_substP_sq_comparison_common pkg hδ hB
      htheta1 hBcondition (ca i) (cBa i) hG (haNorm i)
    refine ⟨c.mono ?_⟩
    simpa [Rint, conversionIntervalOrder] using
      Nat.add_le_add_left
        (Nat.mul_le_mul_left (pkg.degreeBound + 3) (haDegree i))
        (max rA rB)
  have hthetaComp (i : Fin s) :
      Nonempty (BoundedModuleLEAt g Rint (theta * Hint)
        (C theta * pkg.substP (a i) ^ 2)
        (C (theta * B') * pkg.substV (a i) ^ 2)) := by
    obtain ⟨c⟩ := bounded_theta_substP_sq_comparison_common pkg hδ hB
      htheta htheta1 hBcondition (ca i) (cBa i) hG (haNorm i)
    refine ⟨c.mono ?_⟩
    simpa [Rint, Hint, conversionIntervalOrder] using
      Nat.add_le_add_left
        (Nat.mul_le_mul_left (pkg.degreeBound + 3) (haDegree i))
        (max rA rB)
  have hPDegree (i : Fin s) : (pkg.substP (a i) ^ 2).totalDegree ≤ F :=
    (pkg.substP_sq_totalDegree_le (a i)).trans
      (Nat.mul_le_mul_left pkg.degreeBound (haDegree i))
  have hVDegree (i : Fin s) : (pkg.substV (a i) ^ 2).totalDegree ≤ F :=
    (pkg.substV_sq_totalDegree_le (a i)).trans
      (Nat.mul_le_mul_left pkg.degreeBound (haDegree i))
  have hPUpperDegree (i : Fin s) :
      (C B' * pkg.substV (a i) ^ 2).totalDegree ≤ F :=
    (mv_C_mul_totalDegree_le B' _).trans (hVDegree i)
  have hDeltaDegree (i : Fin s) :
      (C δ * pkg.substV (a i) ^ 2).totalDegree ≤ F :=
    (mv_C_mul_totalDegree_le δ _).trans (hVDegree i)
  have hThetaDegree (i : Fin s) :
      (C theta * pkg.substP (a i) ^ 2).totalDegree ≤ F :=
    (mv_C_mul_totalDegree_le theta _).trans (hPDegree i)
  have hThetaUpperDegree (i : Fin s) :
      (C (theta * B') * pkg.substV (a i) ^ 2).totalDegree ≤ F :=
    (mv_C_mul_totalDegree_le (theta * B') _).trans (hVDegree i)
  have hPNorm (i : Fin s) :
      coeffL1Norm (pkg.substP (a i) ^ 2) ≤ Kfactor := by
    dsimp [Kfactor]
    exact substP_sq_coeffL1Norm_le_conversionFactor pkg B' (a i) hG (haNorm i)
  have hVNorm (i : Fin s) :
      coeffL1Norm (pkg.substV (a i) ^ 2) ≤ Kfactor := by
    dsimp [Kfactor]
    exact substV_sq_coeffL1Norm_le_conversionFactor pkg B' (a i) hG (haNorm i)
  have hPUpperNorm (i : Fin s) :
      coeffL1Norm (C B' * pkg.substV (a i) ^ 2) ≤ Kfactor := by
    dsimp [Kfactor]
    exact numeratorUpper_coeffL1Norm_le_conversionFactor pkg B' (a i) hG (haNorm i)
  have hDeltaNorm (i : Fin s) :
      coeffL1Norm (C δ * pkg.substV (a i) ^ 2) ≤ Kfactor := by
    dsimp [Kfactor]
    exact delta_substV_sq_coeffL1Norm_le_conversionFactor pkg B' (a i) hG (haNorm i)
  have hThetaNorm (i : Fin s) :
      coeffL1Norm (C theta * pkg.substP (a i) ^ 2) ≤ Kfactor := by
    dsimp [Kfactor]
    exact theta_substP_sq_coeffL1Norm_le_conversionFactor pkg B' (a i) hG (haNorm i)
  have hThetaUpperNorm (i : Fin s) :
      coeffL1Norm (C (theta * B') * pkg.substV (a i) ^ 2) ≤ Kfactor := by
    dsimp [Kfactor]
    exact thetaNumeratorUpper_coeffL1Norm_le_conversionFactor pkg B' (a i) hG (haNorm i)
  obtain ⟨cPraw⟩ := BoundedModuleLEAt.prod (I \ K)
    (fun i => pkg.substP (a i) ^ 2)
    (fun i => C B' * pkg.substV (a i) ^ 2)
    Rint F hHint hKfactor
    (fun i hi => IsSOS_sq _)
    (fun i hi => IsSOS_mul (IsSOS_C_nonneg B' hB') (IsSOS_sq _))
    (fun i hi => hPDegree i) (fun i hi => hPUpperDegree i)
    (fun i hi => hPNorm i) (fun i hi => hPUpperNorm i)
    (fun i hi => (hcomp i).some)
  have hPorder : (I \ K).card * (Rint + F) ≤ Rprod := by
    dsimp [Rprod, conversionProductOrder]
    exact Nat.mul_le_mul_right (Rint + F) (finset_fin_card_le (I \ K))
  have hPbudget : (Kfactor + 1) ^ (I \ K).card * Hint ≤ HP := by
    dsimp [HP, P]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by linarith : 1 ≤ Kfactor + 1)
        (finset_fin_card_le (I \ K))) hHint
  let cP : BoundedModuleLEAt g Rprod HP
      (∏ i ∈ I \ K, pkg.substP (a i) ^ 2)
      (∏ i ∈ I \ K, C B' * pkg.substV (a i) ^ 2) :=
    (cPraw.mono hPorder).weakenBound hPbudget
  obtain ⟨cThetaRaw⟩ := BoundedModuleLEAt.prod (K \ L)
    (fun i => C theta * pkg.substP (a i) ^ 2)
    (fun i => C (theta * B') * pkg.substV (a i) ^ 2)
    Rint F hThetaHint hKfactor
    (fun i hi => IsSOS_mul (IsSOS_C_nonneg theta htheta) (IsSOS_sq _))
    (fun i hi => IsSOS_mul
      (IsSOS_C_nonneg (theta * B') (mul_nonneg htheta hB')) (IsSOS_sq _))
    (fun i hi => hThetaDegree i) (fun i hi => hThetaUpperDegree i)
    (fun i hi => hThetaNorm i) (fun i hi => hThetaUpperNorm i)
    (fun i hi => (hthetaComp i).some)
  have hThetaOrder : (K \ L).card * (Rint + F) ≤ Rprod := by
    dsimp [Rprod, conversionProductOrder]
    exact Nat.mul_le_mul_right (Rint + F) (finset_fin_card_le (K \ L))
  have hThetaBudget :
      (Kfactor + 1) ^ (K \ L).card * (theta * Hint) ≤ HT := by
    dsimp [HT, P]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by linarith : 1 ≤ Kfactor + 1)
        (finset_fin_card_le (K \ L))) hThetaHint
  let cTheta : BoundedModuleLEAt g Rprod HT
      (∏ i ∈ K \ L, C theta * pkg.substP (a i) ^ 2)
      (∏ i ∈ K \ L, C (theta * B') * pkg.substV (a i) ^ 2) :=
    (cThetaRaw.mono hThetaOrder).weakenBound hThetaBudget
  have prodNorm (S : Finset (Fin s))
      (q : Fin s → MvPolynomial (Fin n) ℝ)
      (hq : ∀ i ∈ S, coeffL1Norm (q i) ≤ Kfactor) :
      coeffL1Norm (∏ i ∈ S, q i) ≤ P := by
    exact coeffL1Norm_finset_prod_le_common_pow S q hKfactor
      (finset_fin_card_le S) hq
  have hPloNorm := prodNorm (I \ K) (fun i => pkg.substP (a i) ^ 2)
    (fun i hi => hPNorm i)
  have hPupNorm := prodNorm (I \ K)
    (fun i => C B' * pkg.substV (a i) ^ 2) (fun i hi => hPUpperNorm i)
  have hDeltaNorm' := prodNorm L
    (fun i => C δ * pkg.substV (a i) ^ 2) (fun i hi => hDeltaNorm i)
  have hThetaUpNorm := prodNorm (K \ L)
    (fun i => C (theta * B') * pkg.substV (a i) ^ 2)
    (fun i hi => hThetaUpperNorm i)
  have hVprodNorm := prodNorm Iᶜ (fun i => pkg.substV (a i) ^ 2)
    (fun i hi => hVNorm i)
  have prodDegree (S : Finset (Fin s))
      (q : Fin s → MvPolynomial (Fin n) ℝ)
      (hq : ∀ i ∈ S, (q i).totalDegree ≤ F) :
      (∏ i ∈ S, q i).totalDegree ≤ s * F :=
    (totalDegree_finset_prod_le_card_mul S q F hq).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le S))
  have hPloDegree := prodDegree (I \ K) (fun i => pkg.substP (a i) ^ 2)
    (fun i hi => hPDegree i)
  have hPupDegree := prodDegree (I \ K)
    (fun i => C B' * pkg.substV (a i) ^ 2) (fun i hi => hPUpperDegree i)
  have hDeltaDegree' := prodDegree L
    (fun i => C δ * pkg.substV (a i) ^ 2) (fun i hi => hDeltaDegree i)
  have hThetaUpDegree := prodDegree (K \ L)
    (fun i => C (theta * B') * pkg.substV (a i) ^ 2)
    (fun i hi => hThetaUpperDegree i)
  have hVDegree' := prodDegree Iᶜ (fun i => pkg.substV (a i) ^ 2)
    (fun i hi => hVDegree i)
  have hPloSOS : IsSOS (∏ i ∈ I \ K, pkg.substP (a i) ^ 2) :=
    IsSOS_finset_prod fun i hi => IsSOS_sq _
  have hPupSOS : IsSOS (∏ i ∈ I \ K, C B' * pkg.substV (a i) ^ 2) :=
    IsSOS_finset_prod fun i hi =>
      IsSOS_mul (IsSOS_C_nonneg B' hB') (IsSOS_sq _)
  have hDeltaSOS : IsSOS (∏ i ∈ L, C δ * pkg.substV (a i) ^ 2) :=
    IsSOS_finset_prod fun i hi =>
      IsSOS_mul (IsSOS_C_nonneg δ hδ.le) (IsSOS_sq _)
  have hThetaUpSOS : IsSOS
      (∏ i ∈ K \ L, C (theta * B') * pkg.substV (a i) ^ 2) :=
    IsSOS_finset_prod fun i hi => IsSOS_mul
      (IsSOS_C_nonneg (theta * B') (mul_nonneg htheta hB')) (IsSOS_sq _)
  have hVSOS : IsSOS (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2) :=
    IsSOS_finset_prod fun i hi => IsSOS_sq _
  have cfirstRaw := BoundedModuleLEAt.mulOfNormLe
    (csigma I) cP (hsigma I) hPupSOS (hsigmaNorm I) hPupNorm
  have hfirstOrder :
      max ((∏ i ∈ I \ K, C B' * pkg.substV (a i) ^ 2).totalDegree + rSigma)
        ((sigma I).totalDegree + Rprod) ≤ R1 := by
    apply max_le
    · calc
        _ ≤ s * F + rSigma := Nat.add_le_add_right hPupDegree rSigma
        _ = rSigma + s * F := by omega
        _ ≤ R1 := by dsimp [R1]; exact le_max_left _ _
    · calc
        _ ≤ d + Rprod := Nat.add_le_add_right (hsigmaDegree I) Rprod
        _ = Rprod + d := by omega
        _ ≤ R1 := by dsimp [R1]; exact le_max_right _ _
  let cfirst : BoundedModuleLEAt g R1 H1
      (sigma I * ∏ i ∈ I \ K, pkg.substP (a i) ^ 2)
      (C H * ∏ i ∈ I \ K, C B' * pkg.substV (a i) ^ 2) := by
    simpa [H1, HP] using cfirstRaw.mono hfirstOrder
  have csecondRaw := cfirst.sosMulLeftOfNormLe hDeltaSOS hDeltaNorm'
  have hsecondOrder :
      (∏ i ∈ L, C δ * pkg.substV (a i) ^ 2).totalDegree + R1 ≤ R2 := by
    calc
      _ ≤ s * F + R1 := Nat.add_le_add_right hDeltaDegree' R1
      _ = R1 + s * F := by omega
      _ ≤ R2 := by dsimp [R2]; exact le_max_left _ _
  let csecond : BoundedModuleLEAt g R2 H2
      ((sigma I * ∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
        ∏ i ∈ L, C δ * pkg.substV (a i) ^ 2)
      ((C H * ∏ i ∈ I \ K, C B' * pkg.substV (a i) ^ 2) *
        ∏ i ∈ L, C δ * pkg.substV (a i) ^ 2) := by
    simpa [H2] using (csecondRaw.mono hsecondOrder).congr (by ring)
  have hprefixNorm : coeffL1Norm
      ((sigma I * ∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
        ∏ i ∈ L, C δ * pkg.substV (a i) ^ 2) ≤
      HsigmaNorm * P ^ 2 := by
    calc
      _ ≤ (coeffL1Norm (sigma I) *
          coeffL1Norm (∏ i ∈ I \ K, pkg.substP (a i) ^ 2)) *
          coeffL1Norm (∏ i ∈ L, C δ * pkg.substV (a i) ^ 2) := by
        exact (coeffL1Norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (coeffL1Norm_mul_le _ _)
            (coeffL1Norm_nonneg _))
      _ ≤ (HsigmaNorm * P) * P := by
        exact mul_le_mul
          (mul_le_mul (hsigmaNorm I) hPloNorm
            (coeffL1Norm_nonneg _) hHsigmaNorm)
          hDeltaNorm' (coeffL1Norm_nonneg _)
          (mul_nonneg hHsigmaNorm hPnonneg)
      _ = HsigmaNorm * P ^ 2 := by ring
  have hprefixDegree :
      ((sigma I * ∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
        ∏ i ∈ L, C δ * pkg.substV (a i) ^ 2).totalDegree ≤
        d + 2 * s * F := by
    calc
      _ ≤ (sigma I * ∏ i ∈ I \ K,
          pkg.substP (a i) ^ 2).totalDegree +
          (∏ i ∈ L, C δ * pkg.substV (a i) ^ 2).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ (d + s * F) + s * F := by
        exact Nat.add_le_add
          ((MvPolynomial.totalDegree_mul _ _).trans
            (Nat.add_le_add (hsigmaDegree I) hPloDegree))
          hDeltaDegree'
      _ = d + 2 * s * F := by ring
  have cthirdRaw := BoundedModuleLEAt.mulOfNormLe csecond cTheta
    (IsSOS_mul (IsSOS_mul (hsigma I) hPloSOS) hDeltaSOS)
    hThetaUpSOS hprefixNorm hThetaUpNorm
  have hthirdOrder :
      max
        ((∏ i ∈ K \ L, C (theta * B') * pkg.substV (a i) ^ 2).totalDegree + R2)
        (((sigma I * ∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
          ∏ i ∈ L, C δ * pkg.substV (a i) ^ 2).totalDegree + Rprod) ≤ R3 := by
    apply max_le
    · calc
        _ ≤ s * F + R2 := Nat.add_le_add_right hThetaUpDegree R2
        _ = R2 + s * F := by omega
        _ ≤ R3 := by dsimp [R3]; exact le_max_left _ _
    · calc
        _ ≤ (d + 2 * s * F) + Rprod :=
          Nat.add_le_add_right hprefixDegree Rprod
        _ = Rprod + (d + 2 * s * F) := by omega
        _ ≤ R3 := by dsimp [R3]; exact le_max_right _ _
  let cthird : BoundedModuleLEAt g R3 H3
      (((sigma I * ∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
          ∏ i ∈ L, C δ * pkg.substV (a i) ^ 2) *
        ∏ i ∈ K \ L, C theta * pkg.substP (a i) ^ 2)
      (((C H * ∏ i ∈ I \ K, C B' * pkg.substV (a i) ^ 2) *
          ∏ i ∈ L, C δ * pkg.substV (a i) ^ 2) *
        ∏ i ∈ K \ L, C (theta * B') * pkg.substV (a i) ^ 2) := by
    simpa [H3] using cthirdRaw.mono hthirdOrder
  have cfourthRaw := cthird.sosMulLeftOfNormLe hVSOS hVprodNorm
  have hfourthOrder :
      (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2).totalDegree + R3 ≤ R4 := by
    calc
      _ ≤ s * F + R3 := Nat.add_le_add_right hVDegree' R3
      _ = R3 + s * F := by omega
      _ ≤ R4 := by dsimp [R4]; exact le_max_left _ _
  have hthetaProd :
      (∏ i ∈ K \ L, C (theta * B') * pkg.substV (a i) ^ 2) =
        ∏ i ∈ K \ L, C theta * C B' * pkg.substV (a i) ^ 2 := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [← map_mul]
  let cfinal : BoundedModuleLEAt g R4 (P * H3)
      (refinedErrorBoundTerm (fun _ => pkg) a sigma I K L)
      (refinedScalarBoundTerm (fun _ => pkg) a H B' I K L) := by
    simpa [refinedErrorBoundTerm, refinedScalarBoundTerm] using
      (cfourthRaw.mono hfourthOrder).congr (by
        rw [hthetaProd]
        ring)
  exact ⟨by
    simpa [conversionSharpScalarTermOrder, boundedSharpScalarBudget,
      R1, R2, R3, R4, Rprod, Rint, F, Hint, Kfactor, P, HP, HT,
      H1, H2, H3] using cfinal⟩

end OptimalConvergenceRates.GeneralArchimedean

end
