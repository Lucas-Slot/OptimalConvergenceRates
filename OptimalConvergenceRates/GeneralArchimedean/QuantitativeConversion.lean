/-
  Degree-tracked conversion of bounded preordering refutations to ordinary
  quadratic-module refutations.
-/
import OptimalConvergenceRates.GeneralArchimedean.RefutationConversion

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

variable {n m : ℕ}

/-- Common degree of every substituted numerator, denominator, or error
factor when the artificial generators have degree at most `d`. -/
def conversionFactorDegree
    {δ B theta : ℝ} (pkg : Package δ B theta) (d : ℕ) : ℕ :=
  pkg.degreeBound * d

/-- Common order of the two interval comparisons for one factor. -/
def conversionIntervalOrder
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (d rA rB : ℕ) : ℕ :=
  max rA rB + (pkg.degreeBound + 3) * d

/-- Common order after comparing a product of at most `s` factors. -/
def conversionProductOrder
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (s d rA rB : ℕ) : ℕ :=
  s * (conversionIntervalOrder pkg d rA rB +
    conversionFactorDegree pkg d)

/-- Common order for one error-bound term after all scalar replacements. -/
def conversionScalarTermOrder
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (s d rSigma rA rB : ℕ) : ℕ :=
  let F := conversionFactorDegree pkg d
  let Rp := conversionProductOrder pkg s d rA rB
  let R₁ := max (rSigma + s * F) (Rp + d)
  let R₂ := max (R₁ + s * F) (Rp + (d + s * F))
  R₂ + s * F

theorem mv_C_mul_totalDegree_le
    (c : ℝ) (q : MvPolynomial (Fin n) ℝ) :
    (C c * q).totalDegree ≤ q.totalDegree := by
  calc
    (C c * q).totalDegree ≤
        (C c : MvPolynomial (Fin n) ℝ).totalDegree + q.totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + q.totalDegree :=
      Nat.add_le_add_right (MvPolynomial.totalDegree_C c).le _
    _ = q.totalDegree := by simp

theorem finset_fin_card_le (S : Finset (Fin s)) : S.card ≤ s := by
  simpa using Finset.card_le_univ S

/-- The fully expanded bounded error term lies below its scalar denominator
bound at one explicit common order. -/
theorem errorBoundTerm_le_scalarBoundTerm_at
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
    (I K : Finset (Fin s)) :
    ModuleLEAt g
      (conversionScalarTermOrder pkg s d rSigma rA rB)
      (errorBoundTerm (fun _ => pkg) a sigma I K)
      (scalarBoundTerm (fun _ => pkg) a H Bprime I K) := by
  classical
  let F := conversionFactorDegree pkg d
  let Rint := conversionIntervalOrder pkg d rA rB
  let Rprod := conversionProductOrder pkg s d rA rB
  let R₁ := max (rSigma + s * F) (Rprod + d)
  let R₂ := max (R₁ + s * F) (Rprod + (d + s * F))
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
  have herror (i : Fin s) :
      ModuleLEAt g Rint
        (C theta * pkg.substP (a i) ^ 2 +
          C δ * pkg.substV (a i) ^ 2)
        (C (theta * Bprime + δ) * pkg.substV (a i) ^ 2) := by
    have hscaled := (hP i).sos_mul_left
      (IsSOS_C_nonneg theta htheta)
    have hrefl := (ModuleLEAt.refl g
      (C δ * pkg.substV (a i) ^ 2)).mono (Nat.zero_le Rint)
    have hadd := hscaled.add hrefl
    convert hadd using 1
    all_goals
      simp only [map_add, map_mul, MvPolynomial.totalDegree_C,
        Nat.add_zero, max_self]
    all_goals ring
  have hPDegree (i : Fin s) :
      (pkg.substP (a i) ^ 2).totalDegree ≤ F := by
    exact (pkg.substP_sq_totalDegree_le (a i)).trans
      (Nat.mul_le_mul_left pkg.degreeBound (haDegree i))
  have hVDegree (i : Fin s) :
      (pkg.substV (a i) ^ 2).totalDegree ≤ F := by
    exact (pkg.substV_sq_totalDegree_le (a i)).trans
      (Nat.mul_le_mul_left pkg.degreeBound (haDegree i))
  have hPUpperDegree (i : Fin s) :
      (C Bprime * pkg.substV (a i) ^ 2).totalDegree ≤ F :=
    (mv_C_mul_totalDegree_le Bprime _).trans (hVDegree i)
  have hErrorDegree (i : Fin s) :
      (C theta * pkg.substP (a i) ^ 2 +
        C δ * pkg.substV (a i) ^ 2).totalDegree ≤ F := by
    exact (MvPolynomial.totalDegree_add _ _).trans <| max_le
      ((mv_C_mul_totalDegree_le theta _).trans (hPDegree i))
      ((mv_C_mul_totalDegree_le δ _).trans (hVDegree i))
  have hErrorUpperDegree (i : Fin s) :
      (C (theta * Bprime + δ) * pkg.substV (a i) ^ 2).totalDegree ≤ F :=
    (mv_C_mul_totalDegree_le (theta * Bprime + δ) _).trans (hVDegree i)
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
  have hEprodRaw := ModuleLEAt.prod K
    (fun i => C theta * pkg.substP (a i) ^ 2 +
      C δ * pkg.substV (a i) ^ 2)
    (fun i => C (theta * Bprime + δ) * pkg.substV (a i) ^ 2)
    Rint F
    (fun i hi => IsSOS_add
      (IsSOS_mul (IsSOS_C_nonneg theta htheta) (IsSOS_sq _))
      (IsSOS_mul (IsSOS_C_nonneg δ hδ.le) (IsSOS_sq _)))
    (fun i hi => IsSOS_mul
      (IsSOS_C_nonneg (theta * Bprime + δ)
        (add_nonneg (mul_nonneg htheta hBprime) hδ.le))
      (IsSOS_sq _))
    (fun i hi => hErrorDegree i) (fun i hi => hErrorUpperDegree i)
    (fun i hi => herror i)
  have hEprod : ModuleLEAt g Rprod
      (∏ i ∈ K,
        (C theta * pkg.substP (a i) ^ 2 +
          C δ * pkg.substV (a i) ^ 2))
      (∏ i ∈ K,
        C (theta * Bprime + δ) * pkg.substV (a i) ^ 2) := by
    apply hEprodRaw.mono
    exact Nat.mul_le_mul_right (Rint + F) (finset_fin_card_le K)
  have hPUpperSOS : IsSOS
      (∏ i ∈ I \ K, C Bprime * pkg.substV (a i) ^ 2) :=
    IsSOS_finset_prod fun i hi =>
      IsSOS_mul (IsSOS_C_nonneg Bprime hBprime) (IsSOS_sq _)
  have hPLowerSOS : IsSOS
      (∏ i ∈ I \ K, pkg.substP (a i) ^ 2) :=
    IsSOS_finset_prod fun i hi => IsSOS_sq _
  have hEUpperSOS : IsSOS
      (∏ i ∈ K,
        C (theta * Bprime + δ) * pkg.substV (a i) ^ 2) :=
    IsSOS_finset_prod fun i hi => IsSOS_mul
      (IsSOS_C_nonneg (theta * Bprime + δ)
        (add_nonneg (mul_nonneg htheta hBprime) hδ.le))
      (IsSOS_sq _)
  have hELowerSOS : IsSOS
      (∏ i ∈ K,
        (C theta * pkg.substP (a i) ^ 2 +
          C δ * pkg.substV (a i) ^ 2)) :=
    IsSOS_finset_prod fun i hi => IsSOS_add
      (IsSOS_mul (IsSOS_C_nonneg theta htheta) (IsSOS_sq _))
      (IsSOS_mul (IsSOS_C_nonneg δ hδ.le) (IsSOS_sq _))
  have hVSOS : IsSOS (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2) :=
    IsSOS_finset_prod fun i hi => IsSOS_sq _
  have hPLowerDegree :
      (∏ i ∈ I \ K, pkg.substP (a i) ^ 2).totalDegree ≤ s * F :=
    (totalDegree_finset_prod_le_card_mul (I \ K) _ F
      (fun i hi => hPDegree i)).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le (I \ K)))
  have hPUpperProdDegree :
      (∏ i ∈ I \ K, C Bprime * pkg.substV (a i) ^ 2).totalDegree ≤
        s * F :=
    (totalDegree_finset_prod_le_card_mul (I \ K) _ F
      (fun i hi => hPUpperDegree i)).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le (I \ K)))
  have hELowerDegree :
      (∏ i ∈ K,
        (C theta * pkg.substP (a i) ^ 2 +
          C δ * pkg.substV (a i) ^ 2)).totalDegree ≤ s * F :=
    (totalDegree_finset_prod_le_card_mul K _ F
      (fun i hi => hErrorDegree i)).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le K))
  have hEUpperProdDegree :
      (∏ i ∈ K,
        C (theta * Bprime + δ) * pkg.substV (a i) ^ 2).totalDegree ≤
          s * F :=
    (totalDegree_finset_prod_le_card_mul K _ F
      (fun i hi => hErrorUpperDegree i)).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le K))
  have hVProdDegree :
      (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2).totalDegree ≤ s * F :=
    (totalDegree_finset_prod_le_card_mul Iᶜ _ F
      (fun i hi => hVDegree i)).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le Iᶜ))
  have hfirstRaw := ModuleLEAt.mul (hsigma I) hPUpperSOS
    (hsigmaBound I) hPprod
  have hfirst : ModuleLEAt g R₁
      (sigma I * ∏ i ∈ I \ K, pkg.substP (a i) ^ 2)
      (C H * ∏ i ∈ I \ K,
        C Bprime * pkg.substV (a i) ^ 2) := by
    apply hfirstRaw.mono
    apply max_le
    · exact (Nat.add_le_add_left hPUpperProdDegree rSigma).trans
        (le_max_left _ _)
    · exact (Nat.add_le_add_left (hsigmaDegree I) Rprod).trans
        (le_max_right _ _)
  have hLowerPrefixDegree :
      (sigma I * ∏ i ∈ I \ K,
        pkg.substP (a i) ^ 2).totalDegree ≤ d + s * F := by
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add (hsigmaDegree I) hPLowerDegree)
  have hsecondRaw := ModuleLEAt.mul
    (IsSOS_mul (hsigma I) hPLowerSOS) hEUpperSOS hfirst hEprod
  have hsecond : ModuleLEAt g R₂
      ((sigma I * ∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
        ∏ i ∈ K,
          (C theta * pkg.substP (a i) ^ 2 +
            C δ * pkg.substV (a i) ^ 2))
      ((C H * ∏ i ∈ I \ K,
          C Bprime * pkg.substV (a i) ^ 2) *
        ∏ i ∈ K,
          C (theta * Bprime + δ) * pkg.substV (a i) ^ 2) := by
    apply hsecondRaw.mono
    apply max_le
    · exact (Nat.add_le_add_left hEUpperProdDegree R₁).trans
        (le_max_left _ _)
    · exact (Nat.add_le_add_left hLowerPrefixDegree Rprod).trans
        (le_max_right _ _)
  have hthirdRaw := hsecond.sos_mul_right hVSOS
  have hthird := hthirdRaw.mono
    (Nat.add_le_add_left hVProdDegree R₂)
  simpa only [conversionScalarTermOrder, R₂, R₁, Rprod, F,
    errorBoundTerm, scalarBoundTerm] using hthird


/-- Order used to replace every genuine error factor by its interval bound. -/
def conversionExpansionOrder
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (s d rA rB : ℕ) : ℕ :=
  conversionProductOrder pkg s d rA rB +
    (d + 2 * s * conversionFactorDegree pkg d)

/-- Common order for one expanded odd term all the way to its scalar bound. -/
def conversionOddTermOrder
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (s d rSigma rA rB : ℕ) : ℕ :=
  max (conversionExpansionOrder pkg s d rA rB)
    (conversionScalarTermOrder pkg s d rSigma rA rB)

/-- Replacing all genuine error factors by their interval upper bounds,
with a completely explicit truncation order. -/
theorem errorExpansionTerm_le_errorBoundTerm_at
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    {d rA rB : ℕ}
    (hsigma : ∀ I, IsSOS (sigma I))
    (hsigmaDegree : ∀ I, (sigma I).totalDegree ≤ d)
    (ha : ∀ i, a i ∈ GenQuadraticModule g rA)
    (hBa : ∀ i, C B - a i ∈ GenQuadraticModule g rB)
    (haDegree : ∀ i, (a i).totalDegree ≤ d)
    (hδ : 0 < δ) (hB : 0 < B) (htheta : 0 ≤ theta)
    (I K : Finset (Fin s)) :
    ModuleLEAt g (conversionExpansionOrder pkg s d rA rB)
      (errorExpansionTerm (fun _ => pkg) a sigma I K)
      (errorBoundTerm (fun _ => pkg) a sigma I K) := by
  classical
  let F := conversionFactorDegree pkg d
  let Rint := conversionIntervalOrder pkg d rA rB
  let Rprod := conversionProductOrder pkg s d rA rB
  have hE (i : Fin s) :
      ModuleLEAt g Rint (pkg.substE (a i))
        (C theta * pkg.substP (a i) ^ 2 +
          C δ * pkg.substV (a i) ^ 2) := by
    have hbase := pkg.substE_le_thetaP_sq_add_deltaV_sq_at
      hδ hB (ha i) (hBa i)
    apply hbase.mono
    simpa [Rint, conversionIntervalOrder] using
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
  have hEDegree (i : Fin s) :
      (pkg.substE (a i)).totalDegree ≤ F :=
    (pkg.substE_totalDegree_le (a i)).trans
      (Nat.mul_le_mul_left pkg.degreeBound (haDegree i))
  have hErrorDegree (i : Fin s) :
      (C theta * pkg.substP (a i) ^ 2 +
        C δ * pkg.substV (a i) ^ 2).totalDegree ≤ F := by
    exact (MvPolynomial.totalDegree_add _ _).trans <| max_le
      ((mv_C_mul_totalDegree_le theta _).trans (hPDegree i))
      ((mv_C_mul_totalDegree_le δ _).trans (hVDegree i))
  have hEprodRaw := ModuleLEAt.prod K
    (fun i => pkg.substE (a i))
    (fun i => C theta * pkg.substP (a i) ^ 2 +
      C δ * pkg.substV (a i) ^ 2)
    Rint F
    (fun i hi => pkg.substE_isSOS (a i) hδ)
    (fun i hi => IsSOS_add
      (IsSOS_mul (IsSOS_C_nonneg theta htheta) (IsSOS_sq _))
      (IsSOS_mul (IsSOS_C_nonneg δ hδ.le) (IsSOS_sq _)))
    (fun i hi => hEDegree i) (fun i hi => hErrorDegree i)
    (fun i hi => hE i)
  have hEprod : ModuleLEAt g Rprod
      (∏ i ∈ K, pkg.substE (a i))
      (∏ i ∈ K,
        (C theta * pkg.substP (a i) ^ 2 +
          C δ * pkg.substV (a i) ^ 2)) := by
    apply hEprodRaw.mono
    exact Nat.mul_le_mul_right (Rint + F) (finset_fin_card_le K)
  have hPprodSOS : IsSOS
      (∏ i ∈ I \ K, pkg.substP (a i) ^ 2) :=
    IsSOS_finset_prod fun i hi => IsSOS_sq _
  have hVprodSOS : IsSOS
      (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2) :=
    IsSOS_finset_prod fun i hi => IsSOS_sq _
  have hcontext : IsSOS
      (sigma I * (∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
        ∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2) :=
    IsSOS_mul (IsSOS_mul (hsigma I) hPprodSOS) hVprodSOS
  have hPprodDegree :
      (∏ i ∈ I \ K, pkg.substP (a i) ^ 2).totalDegree ≤ s * F :=
    (totalDegree_finset_prod_le_card_mul (I \ K) _ F
      (fun i hi => hPDegree i)).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le (I \ K)))
  have hVprodDegree :
      (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2).totalDegree ≤ s * F :=
    (totalDegree_finset_prod_le_card_mul Iᶜ _ F
      (fun i hi => hVDegree i)).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le Iᶜ))
  have hcontextDegree :
      (sigma I * (∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
        ∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2).totalDegree ≤
        d + 2 * s * F := by
    calc
      (sigma I * (∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
          ∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2).totalDegree ≤
          (sigma I * ∏ i ∈ I \ K, pkg.substP (a i) ^ 2).totalDegree +
            (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ ((sigma I).totalDegree +
            (∏ i ∈ I \ K, pkg.substP (a i) ^ 2).totalDegree) +
          (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2).totalDegree :=
        Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _) _
      _ ≤ (d + s * F) + s * F :=
        Nat.add_le_add (Nat.add_le_add (hsigmaDegree I) hPprodDegree)
          hVprodDegree
      _ = d + 2 * s * F := by ring
  have hmul := hEprod.sos_mul_left hcontext
  have hmono := hmul.mono
    (Nat.add_le_add_left hcontextDegree Rprod)
  change ModuleLEAt g (conversionExpansionOrder pkg s d rA rB)
    _ _ at hmono
  convert hmono using 1 <;>
    dsimp [errorExpansionTerm, errorBoundTerm] <;> ring

/-- One odd expansion term lies below its scalar common-denominator bound. -/
theorem errorExpansionTerm_le_scalarBoundTerm_at
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
    (I K : Finset (Fin s)) :
    ModuleLEAt g
      (conversionOddTermOrder pkg s d rSigma rA rB)
      (errorExpansionTerm (fun _ => pkg) a sigma I K)
      (scalarBoundTerm (fun _ => pkg) a H Bprime I K) := by
  exact (errorExpansionTerm_le_errorBoundTerm_at pkg a sigma
    hsigma hsigmaDegree ha hBa haDegree hδ hB htheta I K).trans
      (errorBoundTerm_le_scalarBoundTerm_at pkg a sigma
        hsigma hsigmaDegree hsigmaBound ha hBa haDegree hδ hB
        htheta htheta1 hBprime hBcondition I K)


/-- The complete odd aggregate satisfies the scalar absorption inequality at
the same common order as each summand. -/
theorem convertedOdd_le_oddAbsorptionCoefficient_at
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
    ModuleLEAt g
      (conversionOddTermOrder pkg s d rSigma rA rB)
      (convertedOdd (fun _ => pkg) a sigma)
      (C (oddAbsorptionCoefficient s H Bprime theta δ) *
        denominatorProduct (fun _ => pkg) a) := by
  classical
  have houter := ModuleLEAt.sum
    (s := (Finset.univ : Finset (Fin s)).powerset)
    (p := fun I => oddErrorSum (fun _ => pkg) a sigma I)
    (q := fun I =>
      ∑ K ∈ I.powerset.filter (fun K => ¬ Even K.card),
        C (scalarErrorCoefficient H Bprime theta δ I K) *
          denominatorProduct (fun _ => pkg) a)
    (fun I hI => by
      apply ModuleLEAt.sum
      intro K hK
      have hKI : K ⊆ I :=
        Finset.mem_powerset.mp (Finset.mem_filter.mp hK).1
      have hterm := errorExpansionTerm_le_scalarBoundTerm_at
        pkg a sigma hsigma hsigmaDegree hsigmaBound ha hBa haDegree
        hδ hB htheta htheta1 hBprime hBcondition I K
      rw [scalarBoundTerm_eq_coefficient_mul_denominator
        (fun _ => pkg) a H Bprime I K hKI] at hterm
      exact hterm)
  simpa only [convertedOdd, oddAbsorptionCoefficient,
    map_sum, Finset.sum_mul] using houter

/-- Degree of one expanded term under common input and package bounds. -/
theorem errorExpansionTerm_totalDegree_le
    {s : ℕ} {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    {d : ℕ}
    (hsigmaDegree : ∀ I, (sigma I).totalDegree ≤ d)
    (haDegree : ∀ i, (a i).totalDegree ≤ d)
    (I K : Finset (Fin s)) :
    (errorExpansionTerm (fun _ => pkg) a sigma I K).totalDegree ≤
      d + 3 * s * conversionFactorDegree pkg d := by
  classical
  let F := conversionFactorDegree pkg d
  have hPDegree (i : Fin s) :
      (pkg.substP (a i) ^ 2).totalDegree ≤ F :=
    (pkg.substP_sq_totalDegree_le (a i)).trans
      (Nat.mul_le_mul_left pkg.degreeBound (haDegree i))
  have hEDegree (i : Fin s) :
      (pkg.substE (a i)).totalDegree ≤ F :=
    (pkg.substE_totalDegree_le (a i)).trans
      (Nat.mul_le_mul_left pkg.degreeBound (haDegree i))
  have hVDegree (i : Fin s) :
      (pkg.substV (a i) ^ 2).totalDegree ≤ F :=
    (pkg.substV_sq_totalDegree_le (a i)).trans
      (Nat.mul_le_mul_left pkg.degreeBound (haDegree i))
  have hPprod :
      (∏ i ∈ I \ K, pkg.substP (a i) ^ 2).totalDegree ≤ s * F :=
    (totalDegree_finset_prod_le_card_mul (I \ K) _ F
      (fun i hi => hPDegree i)).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le (I \ K)))
  have hEprod :
      (∏ i ∈ K, pkg.substE (a i)).totalDegree ≤ s * F :=
    (totalDegree_finset_prod_le_card_mul K _ F
      (fun i hi => hEDegree i)).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le K))
  have hVprod :
      (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2).totalDegree ≤ s * F :=
    (totalDegree_finset_prod_le_card_mul Iᶜ _ F
      (fun i hi => hVDegree i)).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le Iᶜ))
  dsimp [errorExpansionTerm]
  calc
    (sigma I * (∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
        (∏ i ∈ K, pkg.substE (a i)) *
        ∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2).totalDegree ≤
      (sigma I * (∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
        ∏ i ∈ K, pkg.substE (a i)).totalDegree +
        (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ ((sigma I *
          (∏ i ∈ I \ K, pkg.substP (a i) ^ 2)).totalDegree +
        (∏ i ∈ K, pkg.substE (a i)).totalDegree) +
        (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2).totalDegree :=
      Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _) _
    _ ≤ (((sigma I).totalDegree +
          (∏ i ∈ I \ K, pkg.substP (a i) ^ 2).totalDegree) +
        (∏ i ∈ K, pkg.substE (a i)).totalDegree) +
        (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2).totalDegree :=
      Nat.add_le_add_right
        (Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _) _) _
    _ ≤ ((d + s * F) + s * F) + s * F :=
      Nat.add_le_add
        (Nat.add_le_add (Nat.add_le_add (hsigmaDegree I) hPprod) hEprod)
        hVprod
    _ = d + 3 * s * F := by ring

theorem convertedEven_totalDegree_le
    {s : ℕ} {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    {d : ℕ}
    (hsigmaDegree : ∀ I, (sigma I).totalDegree ≤ d)
    (haDegree : ∀ i, (a i).totalDegree ≤ d) :
    (convertedEven (fun _ => pkg) a sigma).totalDegree ≤
      d + 3 * s * conversionFactorDegree pkg d := by
  classical
  dsimp [convertedEven]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro I hI
  dsimp [evenErrorSum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro K hK
  exact errorExpansionTerm_totalDegree_le pkg a sigma
    hsigmaDegree haDegree I K


/-- Final order of the tracked absorption argument. -/
def conversionRefutationOrder
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (s d rSigma rA rB : ℕ) : ℕ :=
  let F := conversionFactorDegree pkg d
  max
    (max (conversionOddTermOrder pkg s d rSigma rA rB)
      (d + 3 * s * F))
    (s * ((rA + F) + F))

/-- A bounded preordering refutation, together with finite-order module
bounds on its artificial generators and multipliers, converts to a
finite-order ordinary quadratic-module refutation. -/
theorem refutation_of_oddAbsorptionCoefficient_at
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
    (hsmall : oddAbsorptionCoefficient s H Bprime theta δ < 1) :
    (-1 : MvPolynomial (Fin n) ℝ) ∈ GenQuadraticModule g
      (conversionRefutationOrder pkg s d rSigma rA rB) := by
  let D := denominatorProduct (fun _ : Fin s => pkg) a
  let E := convertedEven (fun _ : Fin s => pkg) a sigma
  let O := convertedOdd (fun _ : Fin s => pkg) a sigma
  let F := conversionFactorDegree pkg d
  let Rodd := conversionOddTermOrder pkg s d rSigma rA rB
  let RE := d + 3 * s * F
  let Rden := s * ((rA + F) + F)
  have hEO : -D = E - O := by
    exact multiplied_refutation_eq_even_sub_odd
      (fun _ : Fin s => pkg) a sigma hδ hidentity
  have hO : O = E + D := by
    linear_combination hEO
  have hodd : ModuleLEAt g Rodd O
      (C (oddAbsorptionCoefficient s H Bprime theta δ) * D) := by
    simpa [Rodd, O, D] using
      convertedOdd_le_oddAbsorptionCoefficient_at
        pkg a sigma hsigma hsigmaDegree hsigmaBound ha hBa haDegree
        hδ hB htheta htheta1 hBprime hBcondition
  have hESOS : IsSOS E :=
    convertedEven_isSOS (fun _ : Fin s => pkg) a sigma hsigma hδ
  have hEDegree : E.totalDegree ≤ RE := by
    simpa [E, RE, F] using
      convertedEven_totalDegree_le pkg a sigma hsigmaDegree haDegree
  have hEmem : E ∈ GenQuadraticModule g RE :=
    genQuadraticModule_sos g hESOS hEDegree
  have hcombined := genQuadraticModule_add hodd hEmem
  have hnegScaled :
      -(C (1 - oddAbsorptionCoefficient s H Bprime theta δ) * D) ∈
        GenQuadraticModule g (max Rodd RE) := by
    convert hcombined using 1
    rw [hO]
    simp only [map_sub, map_one]
    ring
  let gamma : ℝ := 1 - oddAbsorptionCoefficient s H Bprime theta δ
  have hgamma : 0 < gamma := sub_pos.mpr hsmall
  have hinvSOS : IsSOS (C gamma⁻¹ : MvPolynomial (Fin n) ℝ) :=
    IsSOS_C_nonneg gamma⁻¹ (inv_nonneg.mpr hgamma.le)
  have hscaled := genQuadraticModule_sos_mul hinvSOS hnegScaled
  have hminusD : -D ∈ GenQuadraticModule g (max Rodd RE) := by
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
    simpa [gamma] using hscaled
  have hDminusOne : D - 1 ∈ GenQuadraticModule g Rden := by
    have hden := one_le_denominatorProduct_const pkg a ha haDegree hδ
    simpa [ModuleLEAt, D, Rden, F, conversionFactorDegree] using hden
  have hfinal := genQuadraticModule_add hminusD hDminusOne
  have hpoly : -D + (D - 1) = (-1 : MvPolynomial (Fin n) ℝ) := by
    ring
  change (-1 : MvPolynomial (Fin n) ℝ) ∈
    GenQuadraticModule g (conversionRefutationOrder pkg s d rSigma rA rB)
  rw [← hpoly]
  simpa [conversionRefutationOrder, Rodd, RE, Rden, F] using hfinal
/-- Select the rational-square-root package in the tracked conversion.  In
addition to the resulting finite-order module refutation, this records the
two logarithmic parameter bounds used by the final asymptotic estimate. -/
theorem bounded_preordering_refutation_to_module_at
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (B H : ℝ) {d rSigma rA rB : ℕ}
    (hB : 0 < B) (hH : 0 ≤ H)
    (hsigma : ∀ I, IsSOS (sigma I))
    (hsigmaDegree : ∀ I, (sigma I).totalDegree ≤ d)
    (hsigmaBound : ∀ I, ModuleLEAt g rSigma (sigma I) (C H))
    (ha : ∀ i, a i ∈ GenQuadraticModule g rA)
    (hBa : ∀ i, C B - a i ∈ GenQuadraticModule g rB)
    (haDegree : ∀ i, (a i).totalDegree ≤ d)
    (hidentity : (-1 : MvPolynomial (Fin n) ℝ) =
      ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
        sigma I * ∏ i ∈ I, a i) :
    let Bprime : ℝ := 2 * (B + 1)
    let eta : ℝ := absorptionScale s H Bprime
    ∃ pkg : Package eta B eta,
      (pkg.ell : ℝ) ≤
          Real.log (eta / 4) / Real.log (1 / 9) + 1 ∧
        (pkg.J : ℝ) ≤
          Real.log (Real.sqrt (B + eta) / Real.sqrt eta) /
            Real.log 2 ∧
        (-1 : MvPolynomial (Fin n) ℝ) ∈ GenQuadraticModule g
          (conversionRefutationOrder pkg s d rSigma rA rB) := by
  dsimp only
  let Bprime : ℝ := 2 * (B + 1)
  have hBprime : 0 ≤ Bprime := by
    dsimp [Bprime]
    positivity
  let eta : ℝ := absorptionScale s H Bprime
  have heta : 0 < eta := absorptionScale_pos hH hBprime
  have hetahalf : eta ≤ 1 / 2 := absorptionScale_le_half hH hBprime
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
      heta hB.le heta hetaone
  refine ⟨pkg, hell, hJ, ?_⟩
  exact refutation_of_oddAbsorptionCoefficient_at
    pkg a sigma hsigma hsigmaDegree hsigmaBound ha hBa haDegree
    heta hB heta.le htheta1 hBprime hcondition hidentity
    (oddAbsorptionCoefficient_scale_lt_one hH hBprime)


end OptimalConvergenceRates.GeneralArchimedean

end
