/-
  Degree-tracked version of the sharp two-channel absorption argument.

  The approximation parameter `theta` is absorbed by the converted even
  part, whereas the terms carrying at least one factor of `delta` are
  absorbed by the common denominator.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpAbsorption
import OptimalConvergenceRates.GeneralArchimedean.QuantitativeConversion

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

variable {n m : ℕ}

/-- Common order for the refined scalar comparison.  The four successive
products correspond to the numerator factors, the genuine `delta` factors,
the remaining `theta` factors, and the complementary denominator factors. -/
def conversionSharpScalarTermOrder
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (s d rSigma rA rB : ℕ) : ℕ :=
  let F := conversionFactorDegree pkg d
  let Rprod := conversionProductOrder pkg s d rA rB
  let R₁ := max (rSigma + s * F) (Rprod + d)
  let R₂ := max (R₁ + s * F) (d + s * F)
  let R₃ := max (R₂ + s * F) (Rprod + (d + 2 * s * F))
  max (R₃ + s * F) (d + 3 * s * F)

/-- Degree-tracked form of the refined interval comparison. -/
theorem refinedErrorBoundTerm_le_refinedScalarBoundTerm_at
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta H Bprime : ℝ} (pkg : Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    {d rSigma rA rB : ℕ}
    (hsigma : ∀ I, IsSOS (sigma I))
    (hsigmaDegree : ∀ I, (sigma I).totalDegree ≤ d)
    (hsigmaBound : ∀ I, ModuleLEAt g rSigma (sigma I) (C H))
    (ha : ∀ i, a i ∈ GenQuadraticModule g rA)
    (hBa : ∀ i, C B - a i ∈ GenQuadraticModule g rB)
    (haDegree : ∀ i, (a i).totalDegree ≤ d)
    (hδ : 0 < δ) (hB : 0 < B)
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hBprime : 0 ≤ Bprime)
    (hBcondition : B + δ ≤ (1 - theta) * Bprime)
    (I K L : Finset (Fin s)) :
    ModuleLEAt g
      (conversionSharpScalarTermOrder pkg s d rSigma rA rB)
      (refinedErrorBoundTerm (fun _ => pkg) a sigma I K L)
      (refinedScalarBoundTerm (fun _ => pkg) a H Bprime I K L) := by
  classical
  let F := conversionFactorDegree pkg d
  let Rint := conversionIntervalOrder pkg d rA rB
  let Rprod := conversionProductOrder pkg s d rA rB
  let R₁ := max (rSigma + s * F) (Rprod + d)
  let R₂ := max (R₁ + s * F) (d + s * F)
  let R₃ := max (R₂ + s * F) (Rprod + (d + 2 * s * F))
  let R₄ := max (R₃ + s * F) (d + 3 * s * F)
  have hP (i : Fin s) :
      ModuleLEAt g Rint (pkg.substP (a i) ^ 2)
        (C Bprime * pkg.substV (a i) ^ 2) := by
    have hbase := pkg.substP_sq_le_B_mul_substV_sq_at hδ hB htheta1
      hBcondition (ha i) (hBa i)
    apply hbase.mono
    simpa [Rint, conversionIntervalOrder] using
      Nat.add_le_add_left
        (Nat.mul_le_mul_left (pkg.degreeBound + 3) (haDegree i))
        (max rA rB)
  have hthetaP (i : Fin s) :
      ModuleLEAt g Rint
        (C theta * pkg.substP (a i) ^ 2)
        (C (theta * Bprime) * pkg.substV (a i) ^ 2) := by
    have hscaled := (hP i).sos_mul_left
      (IsSOS_C_nonneg theta htheta)
    convert hscaled using 1
    all_goals
      simp only [map_mul, MvPolynomial.totalDegree_C, Nat.add_zero]
    all_goals ring
  have hPDegree (i : Fin s) :
      (pkg.substP (a i) ^ 2).totalDegree ≤ F :=
    (pkg.substP_sq_totalDegree_le (a i)).trans
      (Nat.mul_le_mul_left pkg.degreeBound (haDegree i))
  have hVDegree (i : Fin s) :
      (pkg.substV (a i) ^ 2).totalDegree ≤ F :=
    (pkg.substV_sq_totalDegree_le (a i)).trans
      (Nat.mul_le_mul_left pkg.degreeBound (haDegree i))
  have hPUpperDegree (i : Fin s) :
      (C Bprime * pkg.substV (a i) ^ 2).totalDegree ≤ F :=
    (mv_C_mul_totalDegree_le Bprime _).trans (hVDegree i)
  have hDeltaDegree (i : Fin s) :
      (C δ * pkg.substV (a i) ^ 2).totalDegree ≤ F :=
    (mv_C_mul_totalDegree_le δ _).trans (hVDegree i)
  have hThetaDegree (i : Fin s) :
      (C theta * pkg.substP (a i) ^ 2).totalDegree ≤ F :=
    (mv_C_mul_totalDegree_le theta _).trans (hPDegree i)
  have hThetaUpperDegree (i : Fin s) :
      (C (theta * Bprime) * pkg.substV (a i) ^ 2).totalDegree ≤ F :=
    (mv_C_mul_totalDegree_le (theta * Bprime) _).trans (hVDegree i)
  have hPprodRaw := ModuleLEAt.prod (I \ K)
    (fun i => pkg.substP (a i) ^ 2)
    (fun i => C Bprime * pkg.substV (a i) ^ 2)
    Rint F
    (fun i hi => IsSOS_sq _)
    (fun i hi => IsSOS_mul (IsSOS_C_nonneg Bprime hBprime) (IsSOS_sq _))
    (fun i hi => hPDegree i) (fun i hi => hPUpperDegree i)
    (fun i hi => hP i)
  have hPprod : ModuleLEAt g Rprod
      (∏ i ∈ I \ K, pkg.substP (a i) ^ 2)
      (∏ i ∈ I \ K, C Bprime * pkg.substV (a i) ^ 2) := by
    apply hPprodRaw.mono
    exact Nat.mul_le_mul_right (Rint + F) (finset_fin_card_le (I \ K))
  have hThetaProdRaw := ModuleLEAt.prod (K \ L)
    (fun i => C theta * pkg.substP (a i) ^ 2)
    (fun i => C (theta * Bprime) * pkg.substV (a i) ^ 2)
    Rint F
    (fun i hi => IsSOS_mul (IsSOS_C_nonneg theta htheta) (IsSOS_sq _))
    (fun i hi => IsSOS_mul
      (IsSOS_C_nonneg (theta * Bprime) (mul_nonneg htheta hBprime))
      (IsSOS_sq _))
    (fun i hi => hThetaDegree i) (fun i hi => hThetaUpperDegree i)
    (fun i hi => hthetaP i)
  have hThetaProd : ModuleLEAt g Rprod
      (∏ i ∈ K \ L, C theta * pkg.substP (a i) ^ 2)
      (∏ i ∈ K \ L,
        C (theta * Bprime) * pkg.substV (a i) ^ 2) := by
    apply hThetaProdRaw.mono
    exact Nat.mul_le_mul_right (Rint + F) (finset_fin_card_le (K \ L))
  have hPloSOS : IsSOS
      (∏ i ∈ I \ K, pkg.substP (a i) ^ 2) :=
    IsSOS_finset_prod fun i hi => IsSOS_sq _
  have hPupSOS : IsSOS
      (∏ i ∈ I \ K, C Bprime * pkg.substV (a i) ^ 2) :=
    IsSOS_finset_prod fun i hi =>
      IsSOS_mul (IsSOS_C_nonneg Bprime hBprime) (IsSOS_sq _)
  have hDeltaSOS : IsSOS
      (∏ i ∈ L, C δ * pkg.substV (a i) ^ 2) :=
    IsSOS_finset_prod fun i hi =>
      IsSOS_mul (IsSOS_C_nonneg δ hδ.le) (IsSOS_sq _)
  have hThetaLoSOS : IsSOS
      (∏ i ∈ K \ L, C theta * pkg.substP (a i) ^ 2) :=
    IsSOS_finset_prod fun i hi =>
      IsSOS_mul (IsSOS_C_nonneg theta htheta) (IsSOS_sq _)
  have hThetaUpSOS : IsSOS
      (∏ i ∈ K \ L,
        C (theta * Bprime) * pkg.substV (a i) ^ 2) :=
    IsSOS_finset_prod fun i hi => IsSOS_mul
      (IsSOS_C_nonneg (theta * Bprime) (mul_nonneg htheta hBprime))
      (IsSOS_sq _)
  have hVSOS : IsSOS (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2) :=
    IsSOS_finset_prod fun i hi => IsSOS_sq _
  have hPloProdDegree :
      (∏ i ∈ I \ K, pkg.substP (a i) ^ 2).totalDegree ≤ s * F :=
    (totalDegree_finset_prod_le_card_mul (I \ K) _ F
      (fun i hi => hPDegree i)).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le (I \ K)))
  have hPupProdDegree :
      (∏ i ∈ I \ K,
        C Bprime * pkg.substV (a i) ^ 2).totalDegree ≤ s * F :=
    (totalDegree_finset_prod_le_card_mul (I \ K) _ F
      (fun i hi => hPUpperDegree i)).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le (I \ K)))
  have hDeltaProdDegree :
      (∏ i ∈ L, C δ * pkg.substV (a i) ^ 2).totalDegree ≤ s * F :=
    (totalDegree_finset_prod_le_card_mul L _ F
      (fun i hi => hDeltaDegree i)).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le L))
  have hThetaLoProdDegree :
      (∏ i ∈ K \ L,
        C theta * pkg.substP (a i) ^ 2).totalDegree ≤ s * F :=
    (totalDegree_finset_prod_le_card_mul (K \ L) _ F
      (fun i hi => hThetaDegree i)).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le (K \ L)))
  have hThetaUpProdDegree :
      (∏ i ∈ K \ L,
        C (theta * Bprime) * pkg.substV (a i) ^ 2).totalDegree ≤ s * F :=
    (totalDegree_finset_prod_le_card_mul (K \ L) _ F
      (fun i hi => hThetaUpperDegree i)).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le (K \ L)))
  have hVProdDegree :
      (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2).totalDegree ≤ s * F :=
    (totalDegree_finset_prod_le_card_mul Iᶜ _ F
      (fun i hi => hVDegree i)).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le Iᶜ))
  have hfirstRaw := ModuleLEAt.mul (hsigma I) hPupSOS
    (hsigmaBound I) hPprod
  have hfirst : ModuleLEAt g R₁
      (sigma I * ∏ i ∈ I \ K, pkg.substP (a i) ^ 2)
      (C H * ∏ i ∈ I \ K,
        C Bprime * pkg.substV (a i) ^ 2) := by
    apply hfirstRaw.mono
    apply max_le
    · exact (Nat.add_le_add_left hPupProdDegree rSigma).trans
        (le_max_left _ _)
    · exact (Nat.add_le_add_left (hsigmaDegree I) Rprod).trans
        (le_max_right _ _)
  have hPrefixOneDegree :
      (sigma I * ∏ i ∈ I \ K,
        pkg.substP (a i) ^ 2).totalDegree ≤ d + s * F :=
    (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add (hsigmaDegree I) hPloProdDegree)
  have hdeltaRefl := ModuleLEAt.refl g
    (∏ i ∈ L, C δ * pkg.substV (a i) ^ 2)
  have hsecondRaw := ModuleLEAt.mul
    (IsSOS_mul (hsigma I) hPloSOS) hDeltaSOS hfirst hdeltaRefl
  have hsecond : ModuleLEAt g R₂
      ((sigma I * ∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
        ∏ i ∈ L, C δ * pkg.substV (a i) ^ 2)
      ((C H * ∏ i ∈ I \ K,
          C Bprime * pkg.substV (a i) ^ 2) *
        ∏ i ∈ L, C δ * pkg.substV (a i) ^ 2) := by
    apply hsecondRaw.mono
    apply max_le
    · exact (Nat.add_le_add_left hDeltaProdDegree R₁).trans
        (le_max_left _ _)
    · calc
        0 + (sigma I * ∏ i ∈ I \ K,
            pkg.substP (a i) ^ 2).totalDegree ≤ d + s * F := by
          simpa using hPrefixOneDegree
        _ ≤ R₂ := le_max_right _ _
  have hPrefixTwoDegree :
      ((sigma I * ∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
        ∏ i ∈ L, C δ * pkg.substV (a i) ^ 2).totalDegree ≤
        d + 2 * s * F := by
    exact (MvPolynomial.totalDegree_mul _ _).trans
      ((Nat.add_le_add hPrefixOneDegree hDeltaProdDegree).trans_eq (by ring))
  have hthirdRaw := ModuleLEAt.mul
    (IsSOS_mul (IsSOS_mul (hsigma I) hPloSOS) hDeltaSOS)
    hThetaUpSOS hsecond hThetaProd
  have hthird : ModuleLEAt g R₃
      (((sigma I * ∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
          ∏ i ∈ L, C δ * pkg.substV (a i) ^ 2) *
        ∏ i ∈ K \ L, C theta * pkg.substP (a i) ^ 2)
      (((C H * ∏ i ∈ I \ K,
          C Bprime * pkg.substV (a i) ^ 2) *
          ∏ i ∈ L, C δ * pkg.substV (a i) ^ 2) *
        ∏ i ∈ K \ L,
          C (theta * Bprime) * pkg.substV (a i) ^ 2) := by
    apply hthirdRaw.mono
    apply max_le
    · exact (Nat.add_le_add_left hThetaUpProdDegree R₂).trans
        (le_max_left _ _)
    · exact (Nat.add_le_add_left hPrefixTwoDegree Rprod).trans
        (le_max_right _ _)
  have hPrefixThreeDegree :
      (((sigma I * ∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
          ∏ i ∈ L, C δ * pkg.substV (a i) ^ 2) *
        ∏ i ∈ K \ L,
          C theta * pkg.substP (a i) ^ 2).totalDegree ≤
        d + 3 * s * F := by
    exact (MvPolynomial.totalDegree_mul _ _).trans
      ((Nat.add_le_add hPrefixTwoDegree hThetaLoProdDegree).trans_eq (by ring))
  have hfourthRaw := ModuleLEAt.mul
    (IsSOS_mul
      (IsSOS_mul (IsSOS_mul (hsigma I) hPloSOS) hDeltaSOS)
      hThetaLoSOS)
    hVSOS hthird (ModuleLEAt.refl g _)
  have hfourth : ModuleLEAt g R₄
      ((((sigma I * ∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
        ∏ i ∈ L, C δ * pkg.substV (a i) ^ 2) *
        ∏ i ∈ K \ L, C theta * pkg.substP (a i) ^ 2) *
        ∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2)
      ((((C H * ∏ i ∈ I \ K,
        C Bprime * pkg.substV (a i) ^ 2) *
        ∏ i ∈ L, C δ * pkg.substV (a i) ^ 2) *
        ∏ i ∈ K \ L,
          C (theta * Bprime) * pkg.substV (a i) ^ 2) *
        ∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2) := by
    apply hfourthRaw.mono
    apply max_le
    · exact (Nat.add_le_add_left hVProdDegree R₃).trans
        (le_max_left _ _)
    · calc
        0 + (((sigma I * ∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
            ∏ i ∈ L, C δ * pkg.substV (a i) ^ 2) *
            ∏ i ∈ K \ L,
              C theta * pkg.substP (a i) ^ 2).totalDegree ≤
            d + 3 * s * F := by simpa using hPrefixThreeDegree
        _ ≤ R₄ := le_max_right _ _
  change ModuleLEAt g R₄ _ _
  unfold refinedErrorBoundTerm refinedScalarBoundTerm
  convert hfourth using 1

/-- Common order for a sharp odd summand. -/
def conversionSharpOddTermOrder
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (s d rSigma rA rB : ℕ) : ℕ :=
  max (conversionExpansionOrder pkg s d rA rB)
    (max (d + 3 * s * conversionFactorDegree pkg d)
      (conversionSharpScalarTermOrder pkg s d rSigma rA rB))

/-- One odd expansion term satisfies the two-channel estimate at an
explicit common order. -/
theorem errorExpansionTerm_le_sharpPairBound_at
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta H Bprime : ℝ} (pkg : Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    {d rSigma rA rB : ℕ}
    (hsigma : ∀ I, IsSOS (sigma I))
    (hsigmaDegree : ∀ I, (sigma I).totalDegree ≤ d)
    (hsigmaBound : ∀ I, ModuleLEAt g rSigma (sigma I) (C H))
    (ha : ∀ i, a i ∈ GenQuadraticModule g rA)
    (hBa : ∀ i, C B - a i ∈ GenQuadraticModule g rB)
    (haDegree : ∀ i, (a i).totalDegree ≤ d)
    (hδ : 0 < δ) (hB : 0 < B)
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hBprime : 0 ≤ Bprime)
    (hBcondition : B + δ ≤ (1 - theta) * Bprime)
    (I K : Finset (Fin s)) (hKI : K ⊆ I)
    (hKodd : ¬ Even K.card) :
    ModuleLEAt g
      (conversionSharpOddTermOrder pkg s d rSigma rA rB)
      (errorExpansionTerm (fun _ => pkg) a sigma I K)
      (C theta * zeroErrorTerm (fun _ => pkg) a sigma I +
        ∑ L ∈ K.powerset.erase ∅,
          C (refinedRemainderCoefficient H Bprime theta δ I K L) *
            denominatorProduct (fun _ => pkg) a) := by
  classical
  let RE := d + 3 * s * conversionFactorDegree pkg d
  let RS := conversionSharpScalarTermOrder pkg s d rSigma rA rB
  have htheta_le_one : theta ≤ 1 := le_of_lt htheta1
  have hodd : Odd K.card := Nat.not_even_iff_odd.mp hKodd
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hodd.pos.ne'
  have hthetaPow : theta ^ K.card ≤ theta := by
    rw [hj, pow_succ']
    exact (mul_le_mul_of_nonneg_left
      (pow_le_one₀ htheta htheta_le_one) htheta).trans_eq (mul_one theta)
  have hzeroSOS : IsSOS (zeroErrorTerm (fun _ => pkg) a sigma I) :=
    errorExpansionTerm_isSOS (fun _ => pkg) a sigma hsigma hδ I ∅
  have hzeroDegree :
      (zeroErrorTerm (fun _ => pkg) a sigma I).totalDegree ≤ RE := by
    simpa [zeroErrorTerm, RE] using
      errorExpansionTerm_totalDegree_le pkg a sigma
        hsigmaDegree haDegree I ∅
  have hpureRaw := (ModuleLEAt.constant (g := g) hthetaPow).sos_mul_right
    hzeroSOS
  have hpure : ModuleLEAt g RE
      (refinedErrorBoundTerm (fun _ => pkg) a sigma I K ∅)
      (C theta * zeroErrorTerm (fun _ => pkg) a sigma I) := by
    rw [refinedErrorBoundTerm_empty (fun _ => pkg) a sigma I K hKI]
    apply hpureRaw.mono
    simpa using hzeroDegree
  have hrem : ModuleLEAt g RS
      (∑ L ∈ K.powerset.erase ∅,
        refinedErrorBoundTerm (fun _ => pkg) a sigma I K L)
      (∑ L ∈ K.powerset.erase ∅,
        C (refinedRemainderCoefficient H Bprime theta δ I K L) *
          denominatorProduct (fun _ => pkg) a) := by
    apply ModuleLEAt.sum
    intro L hL
    have hLK : L ⊆ K :=
      Finset.mem_powerset.mp (Finset.mem_erase.mp hL).2
    have hcmp := refinedErrorBoundTerm_le_refinedScalarBoundTerm_at
      pkg a sigma hsigma hsigmaDegree hsigmaBound ha hBa haDegree
      hδ hB htheta htheta1 hBprime hBcondition I K L
    rw [refinedScalarBoundTerm_eq_coefficient_mul_denominator
      (fun _ => pkg) a H Bprime I K L hKI hLK] at hcmp
    exact hcmp
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
  have hbound : ModuleLEAt g (max RE RS)
      (errorBoundTerm (fun _ => pkg) a sigma I K)
      (C theta * zeroErrorTerm (fun _ => pkg) a sigma I +
        ∑ L ∈ K.powerset.erase ∅,
          C (refinedRemainderCoefficient H Bprime theta δ I K L) *
            denominatorProduct (fun _ => pkg) a) := by
    rw [hsplit]
    exact ModuleLEAt.add hpure hrem
  have hexp := errorExpansionTerm_le_errorBoundTerm_at pkg a sigma
    hsigma hsigmaDegree ha hBa haDegree hδ hB htheta I K
  have htrans := ModuleLEAt.trans hexp hbound
  simpa [conversionSharpOddTermOrder, RE, RS] using htrans

/-- Degree of the positive-even remainder. -/
theorem convertedPositiveEven_totalDegree_le
    {s : ℕ} {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    {d : ℕ}
    (hsigmaDegree : ∀ I, (sigma I).totalDegree ≤ d)
    (haDegree : ∀ i, (a i).totalDegree ≤ d) :
    (convertedPositiveEven (fun _ => pkg) a sigma).totalDegree ≤
      d + 3 * s * conversionFactorDegree pkg d := by
  classical
  dsimp [convertedPositiveEven, positiveEvenErrorSum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro I hI
  apply MvPolynomial.totalDegree_finsetSum_le
  intro K hK
  exact errorExpansionTerm_totalDegree_le pkg a sigma
    hsigmaDegree haDegree I K

/-- Tracked zero-error-to-even comparison. -/
theorem convertedZero_le_convertedEven_at
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    {d : ℕ}
    (hsigma : ∀ I, IsSOS (sigma I))
    (hsigmaDegree : ∀ I, (sigma I).totalDegree ≤ d)
    (haDegree : ∀ i, (a i).totalDegree ≤ d)
    (hδ : 0 < δ) :
    ModuleLEAt g (d + 3 * s * conversionFactorDegree pkg d)
      (convertedZero (fun _ => pkg) a sigma)
      (convertedEven (fun _ => pkg) a sigma) := by
  have hrestSOS := convertedPositiveEven_isSOS
    (fun _ => pkg) a sigma hsigma hδ
  have hrestDegree := convertedPositiveEven_totalDegree_le
    pkg a sigma hsigmaDegree haDegree
  change convertedEven (fun _ => pkg) a sigma -
      convertedZero (fun _ => pkg) a sigma ∈
    GenQuadraticModule g (d + 3 * s * conversionFactorDegree pkg d)
  rw [convertedEven_eq_zero_add_positive]
  convert genQuadraticModule_sos g hrestSOS hrestDegree using 1; ring

/-- Common order of the global sharp odd comparison. -/
def conversionSharpOddOrder
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (s d rSigma rA rB : ℕ) : ℕ :=
  max (conversionSharpOddTermOrder pkg s d rSigma rA rB)
    (d + 3 * s * conversionFactorDegree pkg d)

/-- Global tracked two-channel absorption. -/
theorem convertedOdd_le_sharpAbsorption_at
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta H Bprime : ℝ} (pkg : Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    {d rSigma rA rB : ℕ}
    (hsigma : ∀ I, IsSOS (sigma I))
    (hsigmaDegree : ∀ I, (sigma I).totalDegree ≤ d)
    (hsigmaBound : ∀ I, ModuleLEAt g rSigma (sigma I) (C H))
    (ha : ∀ i, a i ∈ GenQuadraticModule g rA)
    (hBa : ∀ i, C B - a i ∈ GenQuadraticModule g rB)
    (haDegree : ∀ i, (a i).totalDegree ≤ d)
    (hδ : 0 < δ) (hB : 0 < B)
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hBprime : 0 ≤ Bprime)
    (hBcondition : B + δ ≤ (1 - theta) * Bprime) :
    ModuleLEAt g (conversionSharpOddOrder pkg s d rSigma rA rB)
      (convertedOdd (fun _ => pkg) a sigma)
      (C (sharpThetaCoefficient s theta) *
          convertedEven (fun _ => pkg) a sigma +
        C (sharpDeltaCoefficient s H Bprime theta δ) *
          denominatorProduct (fun _ => pkg) a) := by
  classical
  let Rterm := conversionSharpOddTermOrder pkg s d rSigma rA rB
  let RE := d + 3 * s * conversionFactorDegree pkg d
  let Sall : Finset (Finset (Fin s)) :=
    (Finset.univ : Finset (Fin s)).powerset
  let T : Finset (Fin s) → Finset (Finset (Fin s)) :=
    fun I => I.powerset.filter (fun K => ¬ Even K.card)
  let D := denominatorProduct (fun _ => pkg) a
  have hraw := ModuleLEAt.sum
    (s := Sall)
    (p := fun I => oddErrorSum (fun _ => pkg) a sigma I)
    (q := fun I =>
      ∑ K ∈ T I,
        (C theta * zeroErrorTerm (fun _ => pkg) a sigma I +
          ∑ L ∈ K.powerset.erase ∅,
            C (refinedRemainderCoefficient H Bprime theta δ I K L) * D))
    (fun I hI => by
      apply ModuleLEAt.sum
      intro K hK
      have hfilter := Finset.mem_filter.mp hK
      exact errorExpansionTerm_le_sharpPairBound_at
        pkg a sigma hsigma hsigmaDegree hsigmaBound ha hBa haDegree
        hδ hB htheta htheta1 hBprime hBcondition I K
        (Finset.mem_powerset.mp hfilter.1) hfilter.2)
  have hrhs :
      (∑ I ∈ Sall,
        ∑ K ∈ T I,
          (C theta * zeroErrorTerm (fun _ => pkg) a sigma I +
            ∑ L ∈ K.powerset.erase ∅,
              C (refinedRemainderCoefficient H Bprime theta δ I K L) * D)) =
        (∑ I ∈ Sall,
          C (((T I).card : ℝ) * theta) *
            zeroErrorTerm (fun _ => pkg) a sigma I) +
          C (sharpDeltaCoefficient s H Bprime theta δ) * D := by
    dsimp [Sall, T, D]
    unfold sharpDeltaCoefficient
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      map_sum, Finset.sum_mul, map_mul, map_natCast]
    congr 1
    · apply Finset.sum_congr rfl
      intro I hI
      ring
  have hnormalized : ModuleLEAt g Rterm
      (convertedOdd (fun _ => pkg) a sigma)
      ((∑ I ∈ Sall,
          C (((T I).card : ℝ) * theta) *
            zeroErrorTerm (fun _ => pkg) a sigma I) +
        C (sharpDeltaCoefficient s H Bprime theta δ) * D) := by
    rw [hrhs] at hraw
    simpa [convertedOdd, oddErrorSum, Sall, T, Rterm] using hraw
  have hthetaSum : ModuleLEAt g RE
      (∑ I ∈ Sall,
        C (((T I).card : ℝ) * theta) *
          zeroErrorTerm (fun _ => pkg) a sigma I)
      (C (sharpThetaCoefficient s theta) *
        convertedZero (fun _ => pkg) a sigma) := by
    have hsum := ModuleLEAt.sum
      (s := Sall)
      (p := fun I =>
        C (((T I).card : ℝ) * theta) *
          zeroErrorTerm (fun _ => pkg) a sigma I)
      (q := fun I =>
        C (sharpThetaCoefficient s theta) *
          zeroErrorTerm (fun _ => pkg) a sigma I)
      (fun I hI => by
        have hconst := ModuleLEAt.constant (g := g)
          (odd_card_mul_theta_le_sharpThetaCoefficient htheta I (by
            simpa only [Sall, Finset.mem_univ] using hI))
        have hzeroSOS := errorExpansionTerm_isSOS
          (fun _ => pkg) a sigma hsigma hδ I ∅
        have hzeroDegree :
            (zeroErrorTerm (fun _ => pkg) a sigma I).totalDegree ≤ RE := by
          simpa [zeroErrorTerm, RE] using
            errorExpansionTerm_totalDegree_le pkg a sigma
              hsigmaDegree haDegree I ∅
        have hmul := hconst.sos_mul_right hzeroSOS
        exact hmul.mono (by simpa [zeroErrorTerm] using hzeroDegree))
    simpa [convertedZero, Sall, T, Finset.mul_sum] using hsum
  have hzeroEven := convertedZero_le_convertedEven_at
    (g := g) pkg a sigma hsigma hsigmaDegree haDegree hδ
  have halpha : 0 ≤ sharpThetaCoefficient s theta := by
    unfold sharpThetaCoefficient
    positivity
  have hscaledZeroEven := hzeroEven.sos_mul_left
    (IsSOS_C_nonneg (sharpThetaCoefficient s theta) halpha)
  have hthetaEven : ModuleLEAt g RE
      (∑ I ∈ Sall,
        C (((T I).card : ℝ) * theta) *
          zeroErrorTerm (fun _ => pkg) a sigma I)
      (C (sharpThetaCoefficient s theta) *
        convertedEven (fun _ => pkg) a sigma) := by
    have htrans := ModuleLEAt.trans hthetaSum hscaledZeroEven
    simpa [RE] using htrans
  have htoEven := ModuleLEAt.add hthetaEven
    ((ModuleLEAt.refl g
      (C (sharpDeltaCoefficient s H Bprime theta δ) * D)).mono
        (Nat.zero_le RE))
  have hfinal := ModuleLEAt.trans hnormalized htoEven
  simpa [conversionSharpOddOrder, Rterm, RE, D] using hfinal

/-- Final order of the sharp tracked conversion. -/
def sharpConversionRefutationOrder
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (s d rSigma rA rB : ℕ) : ℕ :=
  let F := conversionFactorDegree pkg d
  max
    (conversionSharpOddOrder pkg s d rSigma rA rB)
    (s * ((rA + F) + F))

/-- A two-channel absorption inequality gives a degree-tracked ordinary
quadratic-module refutation. -/
theorem refutation_of_sharpAbsorption_at
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta H Bprime : ℝ} (pkg : Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    {d rSigma rA rB : ℕ}
    (hsigma : ∀ I, IsSOS (sigma I))
    (hsigmaDegree : ∀ I, (sigma I).totalDegree ≤ d)
    (hsigmaBound : ∀ I, ModuleLEAt g rSigma (sigma I) (C H))
    (ha : ∀ i, a i ∈ GenQuadraticModule g rA)
    (hBa : ∀ i, C B - a i ∈ GenQuadraticModule g rB)
    (haDegree : ∀ i, (a i).totalDegree ≤ d)
    (hδ : 0 < δ) (hB : 0 < B)
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hBprime : 0 ≤ Bprime)
    (hBcondition : B + δ ≤ (1 - theta) * Bprime)
    (hidentity : (-1 : MvPolynomial (Fin n) ℝ) =
      ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
        sigma I * ∏ i ∈ I, a i)
    (halpha : sharpThetaCoefficient s theta ≤ 1)
    (hbeta : sharpDeltaCoefficient s H Bprime theta δ < 1) :
    (-1 : MvPolynomial (Fin n) ℝ) ∈ GenQuadraticModule g
      (sharpConversionRefutationOrder pkg s d rSigma rA rB) := by
  let D := denominatorProduct (fun _ : Fin s => pkg) a
  let E := convertedEven (fun _ : Fin s => pkg) a sigma
  let O := convertedOdd (fun _ : Fin s => pkg) a sigma
  let F := conversionFactorDegree pkg d
  let Rodd := conversionSharpOddOrder pkg s d rSigma rA rB
  let RE := d + 3 * s * F
  let Rden := s * ((rA + F) + F)
  let alpha := sharpThetaCoefficient s theta
  let beta := sharpDeltaCoefficient s H Bprime theta δ
  have hEO : -D = E - O := by
    exact multiplied_refutation_eq_even_sub_odd
      (fun _ : Fin s => pkg) a sigma hδ hidentity
  have hO : O = E + D := by
    linear_combination hEO
  have hodd : ModuleLEAt g Rodd O
      (C alpha * E + C beta * D) := by
    simpa [Rodd, O, E, D, alpha, beta] using
      convertedOdd_le_sharpAbsorption_at
        pkg a sigma hsigma hsigmaDegree hsigmaBound ha hBa haDegree
        hδ hB htheta htheta1 hBprime hBcondition
  have hESOS : IsSOS E :=
    convertedEven_isSOS (fun _ : Fin s => pkg) a sigma hsigma hδ
  have hEDegree : E.totalDegree ≤ RE := by
    simpa [E, RE, F] using
      convertedEven_totalDegree_le pkg a sigma hsigmaDegree haDegree
  have hscaleESOS : IsSOS (C (1 - alpha) * E) :=
    IsSOS_mul (IsSOS_C_nonneg (1 - alpha) (sub_nonneg.mpr halpha)) hESOS
  have hscaleEDegree : (C (1 - alpha) * E).totalDegree ≤ RE :=
    (mv_C_mul_totalDegree_le (1 - alpha) E).trans hEDegree
  have hscaleEmem : C (1 - alpha) * E ∈ GenQuadraticModule g RE :=
    genQuadraticModule_sos g hscaleESOS hscaleEDegree
  have hcombined := genQuadraticModule_add hodd hscaleEmem
  have hRE : RE ≤ Rodd := by
    dsimp [Rodd, conversionSharpOddOrder, RE]
    exact le_max_right _ _
  have hnegScaled : -(C (1 - beta) * D) ∈
      GenQuadraticModule g Rodd := by
    rw [← max_eq_left hRE]
    convert hcombined using 1
    rw [hO]
    simp only [map_sub, map_one]
    ring
  let gamma : ℝ := 1 - beta
  have hgamma : 0 < gamma := sub_pos.mpr hbeta
  have hinvSOS : IsSOS (C gamma⁻¹ : MvPolynomial (Fin n) ℝ) :=
    IsSOS_C_nonneg gamma⁻¹ (inv_nonneg.mpr hgamma.le)
  have hscaled := genQuadraticModule_sos_mul hinvSOS hnegScaled
  have hminusD : -D ∈ GenQuadraticModule g Rodd := by
    have heq :
        (C gamma⁻¹ : MvPolynomial (Fin n) ℝ) *
          (-(C gamma * D)) = -D := by
      calc
        C gamma⁻¹ * (-(C gamma * D)) =
            -(C gamma⁻¹ * C gamma) * D := by ring
        _ = -D := by
          rw [← map_mul, inv_mul_cancel₀ hgamma.ne', map_one]
          ring
    rw [← heq]
    simpa [gamma, beta, MvPolynomial.totalDegree_C] using hscaled
  have hDminusOne : D - 1 ∈ GenQuadraticModule g Rden := by
    have hden := one_le_denominatorProduct_const pkg a ha haDegree hδ
    simpa [ModuleLEAt, D, Rden, F, conversionFactorDegree] using hden
  have hfinal := genQuadraticModule_add hminusD hDminusOne
  have hpoly : -D + (D - 1) = (-1 : MvPolynomial (Fin n) ℝ) := by ring
  change (-1 : MvPolynomial (Fin n) ℝ) ∈
    GenQuadraticModule g
      (sharpConversionRefutationOrder pkg s d rSigma rA rB)
  rw [← hpoly]
  simpa [sharpConversionRefutationOrder, Rodd, Rden, F] using hfinal

end OptimalConvergenceRates.GeneralArchimedean

end
