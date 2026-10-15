/-
  Common coefficient envelopes for the bounded preordering-to-module
  conversion.
-/
import OptimalConvergenceRates.GeneralArchimedean.QuantitativeConversion
import OptimalConvergenceRates.GeneralArchimedean.BoundedModuleOrder

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

variable {n m : ℕ}

/-- A common certificate budget for the two interval comparisons attached to
one substituted artificial generator. -/
def conversionIntervalCertificateBound
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (B' G Ha Hb : ℝ) : ℝ :=
  max
    (pkg.errorComparisonCoefficientBound G +
      (pkg.errorComparisonCoefficientBound G * Ha +
        pkg.errorComparisonCoefficientBound G * Hb))
    (pkg.numeratorComparisonCoefficientBound B' G +
      (pkg.numeratorComparisonCoefficientBound B' G * Ha +
        pkg.numeratorComparisonCoefficientBound B' G * Hb))

theorem conversionIntervalCertificateBound_nonneg
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (B' : ℝ) {G Ha Hb : ℝ} (hB : 1 ≤ B) (hG : 1 ≤ G)
    (hHa : 0 ≤ Ha) (hHb : 0 ≤ Hb) :
    0 ≤ conversionIntervalCertificateBound pkg B' G Ha Hb := by
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hError : 0 ≤ pkg.errorComparisonCoefficientBound G := by
    unfold RationalSquareRoot.Package.errorComparisonCoefficientBound
    exact mul_nonneg
      (intervalCertificateCoefficientBound_nonneg hB pkg.errorGap)
      (pow_nonneg hG0 _)
  have hNumerator : 0 ≤ pkg.numeratorComparisonCoefficientBound B' G := by
    unfold RationalSquareRoot.Package.numeratorComparisonCoefficientBound
    exact mul_nonneg
      (intervalCertificateCoefficientBound_nonneg hB (pkg.numeratorGap B'))
      (pow_nonneg hG0 _)
  unfold conversionIntervalCertificateBound
  exact (add_nonneg hError
    (add_nonneg (mul_nonneg hError hHa) (mul_nonneg hError hHb))).trans
      (le_max_left _ _)

theorem conversionIntervalCertificateBound_nonneg_of_certificates
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (B' : ℝ) {G Ha Hb : ℝ} (hB : 1 ≤ B) (hG : 1 ≤ G)
    {a : MvPolynomial (Fin n) ℝ} {r s : ℕ}
    (ca : BoundedQuadraticModuleCertificate g a r Ha)
    (cBa : BoundedQuadraticModuleCertificate g (C B - a) s Hb) :
    0 ≤ conversionIntervalCertificateBound pkg B' G Ha Hb :=
  conversionIntervalCertificateBound_nonneg pkg B' hB hG
    ca.bound_nonneg cBa.bound_nonneg

/-- Both squares, the normalized error, and their scalar combinations have
coefficient norm below this single factor envelope. -/
def conversionFactorCoefficientBound
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (B' G : ℝ) : ℝ :=
  (|theta| + |δ| + |B'| + |theta * B' + δ| + 2) *
    (pkg.substitutionCoefficientBound G + 1) ^ 2

theorem conversionFactorCoefficientBound_nonneg
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (B' G : ℝ) : 0 ≤ conversionFactorCoefficientBound pkg B' G := by
  unfold conversionFactorCoefficientBound
  positivity

theorem substP_sq_coeffL1Norm_le_conversionFactor
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (B' : ℝ) (a : MvPolynomial (Fin n) ℝ) {G : ℝ}
    (hG : 1 ≤ G) (ha : coeffL1Norm a ≤ G) :
    coeffL1Norm (pkg.substP a ^ 2) ≤
      conversionFactorCoefficientBound pkg B' G := by
  have hS := pkg.substP_sq_coeffL1Norm_le a hG ha
  have hS0 : 0 ≤ pkg.substitutionCoefficientBound G :=
    zero_le_one.trans (pkg.one_le_substitutionCoefficientBound hG)
  have hpow : pkg.substitutionCoefficientBound G ^ 2 ≤
      (pkg.substitutionCoefficientBound G + 1) ^ 2 :=
    pow_le_pow_left₀ hS0 (by linarith) 2
  have hscalar : 1 ≤ |theta| + |δ| + |B'| + |theta * B' + δ| + 2 := by
    have := abs_nonneg theta
    have := abs_nonneg δ
    have := abs_nonneg B'
    have := abs_nonneg (theta * B' + δ)
    linarith
  calc
    coeffL1Norm (pkg.substP a ^ 2) ≤
        pkg.substitutionCoefficientBound G ^ 2 := hS
    _ ≤ (pkg.substitutionCoefficientBound G + 1) ^ 2 := hpow
    _ ≤ (|theta| + |δ| + |B'| + |theta * B' + δ| + 2) *
        (pkg.substitutionCoefficientBound G + 1) ^ 2 := by
      exact le_mul_of_one_le_left (sq_nonneg _) hscalar

theorem substV_sq_coeffL1Norm_le_conversionFactor
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (B' : ℝ) (a : MvPolynomial (Fin n) ℝ) {G : ℝ}
    (hG : 1 ≤ G) (ha : coeffL1Norm a ≤ G) :
    coeffL1Norm (pkg.substV a ^ 2) ≤
      conversionFactorCoefficientBound pkg B' G := by
  have hS := pkg.substV_sq_coeffL1Norm_le a hG ha
  have hS0 : 0 ≤ pkg.substitutionCoefficientBound G :=
    zero_le_one.trans (pkg.one_le_substitutionCoefficientBound hG)
  have hpow : pkg.substitutionCoefficientBound G ^ 2 ≤
      (pkg.substitutionCoefficientBound G + 1) ^ 2 :=
    pow_le_pow_left₀ hS0 (by linarith) 2
  have hscalar : 1 ≤ |theta| + |δ| + |B'| + |theta * B' + δ| + 2 := by
    have := abs_nonneg theta
    have := abs_nonneg δ
    have := abs_nonneg B'
    have := abs_nonneg (theta * B' + δ)
    linarith
  exact hS.trans <| hpow.trans <|
    le_mul_of_one_le_left (sq_nonneg _) hscalar

theorem substE_coeffL1Norm_le_conversionFactor
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (B' : ℝ) (a : MvPolynomial (Fin n) ℝ) {G : ℝ}
    (hG : 1 ≤ G) (ha : coeffL1Norm a ≤ G) :
    coeffL1Norm (pkg.substE a) ≤
      conversionFactorCoefficientBound pkg B' G := by
  have hE := pkg.substE_coeffL1Norm_le a hG ha
  have hS : 1 ≤ pkg.substitutionCoefficientBound G :=
    pkg.one_le_substitutionCoefficientBound hG
  have hsquare : pkg.substitutionCoefficientBound G ≤
      (pkg.substitutionCoefficientBound G + 1) ^ 2 := by
    nlinarith [sq_nonneg (pkg.substitutionCoefficientBound G)]
  have hscalar : 1 ≤ |theta| + |δ| + |B'| + |theta * B' + δ| + 2 := by
    have := abs_nonneg theta
    have := abs_nonneg δ
    have := abs_nonneg B'
    have := abs_nonneg (theta * B' + δ)
    linarith
  exact hE.trans <| hsquare.trans <|
    le_mul_of_one_le_left (sq_nonneg _) hscalar

theorem errorUpper_coeffL1Norm_le_conversionFactor
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (B' : ℝ) (a : MvPolynomial (Fin n) ℝ) {G : ℝ}
    (hG : 1 ≤ G) (ha : coeffL1Norm a ≤ G) :
    coeffL1Norm
        (C theta * pkg.substP a ^ 2 + C δ * pkg.substV a ^ 2) ≤
      conversionFactorCoefficientBound pkg B' G := by
  let S := pkg.substitutionCoefficientBound G
  have hP := pkg.substP_sq_coeffL1Norm_le a hG ha
  have hV := pkg.substV_sq_coeffL1Norm_le a hG ha
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact zero_le_one.trans (pkg.one_le_substitutionCoefficientBound hG)
  have hbase : coeffL1Norm
      (C theta * pkg.substP a ^ 2 + C δ * pkg.substV a ^ 2) ≤
      (|theta| + |δ|) * S ^ 2 := by
    calc
      coeffL1Norm
          (C theta * pkg.substP a ^ 2 + C δ * pkg.substV a ^ 2) ≤
          coeffL1Norm (C theta * pkg.substP a ^ 2) +
            coeffL1Norm (C δ * pkg.substV a ^ 2) :=
        coeffL1Norm_add_le _ _
      _ ≤ |theta| * coeffL1Norm (pkg.substP a ^ 2) +
          |δ| * coeffL1Norm (pkg.substV a ^ 2) :=
        add_le_add (coeffL1Norm_C_mul_le _ _) (coeffL1Norm_C_mul_le _ _)
      _ ≤ |theta| * S ^ 2 + |δ| * S ^ 2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hP (abs_nonneg theta))
          (mul_le_mul_of_nonneg_left hV (abs_nonneg δ))
      _ = (|theta| + |δ|) * S ^ 2 := by ring
  calc
    coeffL1Norm
        (C theta * pkg.substP a ^ 2 + C δ * pkg.substV a ^ 2) ≤
        (|theta| + |δ|) * S ^ 2 := hbase
    _ ≤ (|theta| + |δ| + |B'| + |theta * B' + δ| + 2) * (S + 1) ^ 2 := by
      have hcoef : |theta| + |δ| ≤
          |theta| + |δ| + |B'| + |theta * B' + δ| + 2 := by
        have := abs_nonneg B'
        have := abs_nonneg (theta * B' + δ)
        linarith
      have hpow : S ^ 2 ≤ (S + 1) ^ 2 :=
        pow_le_pow_left₀ hS0 (by linarith) 2
      exact mul_le_mul hcoef hpow (sq_nonneg S)
        (add_nonneg
          (add_nonneg (add_nonneg (add_nonneg (abs_nonneg theta)
            (abs_nonneg δ)) (abs_nonneg B')) (abs_nonneg (theta * B' + δ))) (by norm_num))

theorem numeratorUpper_coeffL1Norm_le_conversionFactor
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (B' : ℝ) (a : MvPolynomial (Fin n) ℝ) {G : ℝ}
    (hG : 1 ≤ G) (ha : coeffL1Norm a ≤ G) :
    coeffL1Norm (C B' * pkg.substV a ^ 2) ≤
      conversionFactorCoefficientBound pkg B' G := by
  let S := pkg.substitutionCoefficientBound G
  have hV := pkg.substV_sq_coeffL1Norm_le a hG ha
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact zero_le_one.trans (pkg.one_le_substitutionCoefficientBound hG)
  calc
    coeffL1Norm (C B' * pkg.substV a ^ 2) ≤
        |B'| * coeffL1Norm (pkg.substV a ^ 2) :=
      coeffL1Norm_C_mul_le _ _
    _ ≤ |B'| * S ^ 2 :=
      mul_le_mul_of_nonneg_left hV (abs_nonneg B')
    _ ≤ (|theta| + |δ| + |B'| + |theta * B' + δ| + 2) * (S + 1) ^ 2 := by
      have hcoef : |B'| ≤
          |theta| + |δ| + |B'| + |theta * B' + δ| + 2 := by
        have := abs_nonneg theta
        have := abs_nonneg δ
        have := abs_nonneg (theta * B' + δ)
        linarith
      have hpow : S ^ 2 ≤ (S + 1) ^ 2 :=
        pow_le_pow_left₀ hS0 (by linarith) 2
      exact mul_le_mul hcoef hpow (sq_nonneg S)
        (add_nonneg
          (add_nonneg (add_nonneg (add_nonneg (abs_nonneg theta)
            (abs_nonneg δ)) (abs_nonneg B')) (abs_nonneg (theta * B' + δ))) (by norm_num))

theorem errorScalarUpper_coeffL1Norm_le_conversionFactor
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (B' : ℝ) (a : MvPolynomial (Fin n) ℝ) {G : ℝ}
    (hG : 1 ≤ G) (ha : coeffL1Norm a ≤ G) :
    coeffL1Norm (C (theta * B' + δ) * pkg.substV a ^ 2) ≤
      conversionFactorCoefficientBound pkg B' G := by
  let S := pkg.substitutionCoefficientBound G
  have hV := pkg.substV_sq_coeffL1Norm_le a hG ha
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact zero_le_one.trans (pkg.one_le_substitutionCoefficientBound hG)
  calc
    coeffL1Norm (C (theta * B' + δ) * pkg.substV a ^ 2) ≤
        |theta * B' + δ| * coeffL1Norm (pkg.substV a ^ 2) :=
      coeffL1Norm_C_mul_le _ _
    _ ≤ |theta * B' + δ| * S ^ 2 :=
      mul_le_mul_of_nonneg_left hV (abs_nonneg _)
    _ ≤
        (|theta| + |δ| + |B'| + |theta * B' + δ| + 2) * (S + 1) ^ 2 := by
      have hcoef :
          |theta * B' + δ| ≤
            |theta| + |δ| + |B'| + |theta * B' + δ| + 2 := by
        have h0 : 0 ≤ |theta| + |δ| + |B'| + 2 := by positivity
        linarith
      have hpow : S ^ 2 ≤ (S + 1) ^ 2 := by
        nlinarith [sq_nonneg S, sq_nonneg (S + 1)]
      exact mul_le_mul hcoef hpow (sq_nonneg S) (by positivity)

theorem bounded_substE_comparison_common
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta B' : ℝ} (pkg : Package δ B theta)
    (hδ : 0 < δ) (hB : 1 ≤ B)
    {a : MvPolynomial (Fin n) ℝ} {r s : ℕ} {Ha Hb G : ℝ}
    (ca : BoundedQuadraticModuleCertificate g a r Ha)
    (cBa : BoundedQuadraticModuleCertificate g (C B - a) s Hb)
    (hG : 1 ≤ G) (haNorm : coeffL1Norm a ≤ G) :
    Nonempty (BoundedModuleLEAt g
      (max r s + (pkg.degreeBound + 3) * a.totalDegree)
      (conversionIntervalCertificateBound pkg B' G Ha Hb)
      (pkg.substE a)
      (C theta * pkg.substP a ^ 2 + C δ * pkg.substV a ^ 2)) := by
  obtain ⟨c⟩ := pkg.bounded_substE_comparison hδ hB ca cBa hG haNorm
  exact ⟨c.weakenBound (le_max_left _ _)⟩

theorem bounded_substP_sq_comparison_common
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta B' : ℝ} (pkg : Package δ B theta)
    (hδ : 0 < δ) (hB : 1 ≤ B)
    (htheta1 : theta < 1)
    (hBcondition : B + δ ≤ (1 - theta) * B')
    {a : MvPolynomial (Fin n) ℝ} {r s : ℕ} {Ha Hb G : ℝ}
    (ca : BoundedQuadraticModuleCertificate g a r Ha)
    (cBa : BoundedQuadraticModuleCertificate g (C B - a) s Hb)
    (hG : 1 ≤ G) (haNorm : coeffL1Norm a ≤ G) :
    Nonempty (BoundedModuleLEAt g
      (max r s + (pkg.degreeBound + 3) * a.totalDegree)
      (conversionIntervalCertificateBound pkg B' G Ha Hb)
      (pkg.substP a ^ 2) (C B' * pkg.substV a ^ 2)) := by
  obtain ⟨c⟩ := pkg.bounded_substP_sq_comparison hδ hB htheta1
    hBcondition ca cBa hG haNorm
  exact ⟨c.weakenBound (le_max_right _ _)⟩

theorem conversionIntervalCertificateBound_nonneg_of_error
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta B' : ℝ} (pkg : Package δ B theta)
    (hδ : 0 < δ) (hB : 1 ≤ B)
    {a : MvPolynomial (Fin n) ℝ} {r s : ℕ} {Ha Hb G : ℝ}
    (ca : BoundedQuadraticModuleCertificate g a r Ha)
    (cBa : BoundedQuadraticModuleCertificate g (C B - a) s Hb)
    (hG : 1 ≤ G) (haNorm : coeffL1Norm a ≤ G) :
    0 ≤ conversionIntervalCertificateBound pkg B' G Ha Hb := by
  obtain ⟨c⟩ := bounded_substE_comparison_common pkg
    (B' := B') hδ hB ca cBa hG haNorm
  exact c.bound_nonneg

/-- Coefficient budget for a product of at most `s` interval comparisons. -/
def boundedConversionProductBudget
    (s : ℕ) (comparisonBound factorBound : ℝ) : ℝ :=
  (factorBound + 1) ^ s * comparisonBound

/-- Coefficient norm envelope for the SOS context multiplying a product of
error comparisons. -/
def boundedConversionContextBound
    (s : ℕ) (sigmaBound factorBound : ℝ) : ℝ :=
  sigmaBound * (factorBound + 1) ^ (2 * s)

/-- Certificate budget for replacing every genuine error factor in one
expanded term. -/
def boundedConversionExpansionBudget
    (s : ℕ) (sigmaBound comparisonBound factorBound : ℝ) : ℝ :=
  boundedConversionContextBound s sigmaBound factorBound *
    boundedConversionProductBudget s comparisonBound factorBound

/-- Replacing all genuine error factors by their interval upper bounds,
while tracking an explicit coefficient budget for the resulting quadratic-
module certificate. -/
theorem bounded_errorExpansionTerm_le_errorBoundTerm_at
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta B' : ℝ} (pkg : Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    {d rA rB : ℕ} {Ha Hb G Hsigma : ℝ}
    (hsigma : ∀ I, IsSOS (sigma I))
    (hsigmaDegree : ∀ I, (sigma I).totalDegree ≤ d)
    (hsigmaNorm : ∀ I, coeffL1Norm (sigma I) ≤ Hsigma)
    (hHsigma : 0 ≤ Hsigma)
    (hHa : 0 ≤ Ha) (hHb : 0 ≤ Hb)
    (ca : ∀ i, BoundedQuadraticModuleCertificate g (a i) rA Ha)
    (cBa : ∀ i, BoundedQuadraticModuleCertificate g (C B - a i) rB Hb)
    (haDegree : ∀ i, (a i).totalDegree ≤ d)
    (haNorm : ∀ i, coeffL1Norm (a i) ≤ G)
    (hG : 1 ≤ G) (hδ : 0 < δ) (hB : 1 ≤ B)
    (htheta : 0 ≤ theta)
    (I K : Finset (Fin s)) :
    Nonempty (BoundedModuleLEAt g
      (conversionExpansionOrder pkg s d rA rB)
      (boundedConversionExpansionBudget s Hsigma
        (conversionIntervalCertificateBound pkg B' G Ha Hb)
        (conversionFactorCoefficientBound pkg B' G))
      (errorExpansionTerm (fun _ => pkg) a sigma I K)
      (errorBoundTerm (fun _ => pkg) a sigma I K)) := by
  classical
  let F := conversionFactorDegree pkg d
  let Rint := conversionIntervalOrder pkg d rA rB
  let Rprod := conversionProductOrder pkg s d rA rB
  let Hint := conversionIntervalCertificateBound pkg B' G Ha Hb
  let Kfactor := conversionFactorCoefficientBound pkg B' G
  let Hprod := boundedConversionProductBudget s Hint Kfactor
  let Hcontext := boundedConversionContextBound s Hsigma Kfactor
  have hKfactor : 0 ≤ Kfactor := by
    dsimp [Kfactor]
    exact conversionFactorCoefficientBound_nonneg pkg B' G
  have hbase : 1 ≤ Kfactor + 1 := by linarith
  have hHint : 0 ≤ Hint := by
    dsimp [Hint]
    exact conversionIntervalCertificateBound_nonneg pkg B' hB hG hHa hHb
  have hE (i : Fin s) : Nonempty (BoundedModuleLEAt g Rint Hint
      (pkg.substE (a i))
      (C theta * pkg.substP (a i) ^ 2 +
        C δ * pkg.substV (a i) ^ 2)) := by
    obtain ⟨c⟩ := bounded_substE_comparison_common pkg
      (B' := B') hδ hB (ca i) (cBa i) hG (haNorm i)
    refine ⟨c.mono ?_⟩
    simpa [Rint, conversionIntervalOrder] using
      Nat.add_le_add_left
        (Nat.mul_le_mul_left (pkg.degreeBound + 3) (haDegree i))
        (max rA rB)
  have hEDegree (i : Fin s) : (pkg.substE (a i)).totalDegree ≤ F :=
    (pkg.substE_totalDegree_le (a i)).trans
      (Nat.mul_le_mul_left pkg.degreeBound (haDegree i))
  have hErrorDegree (i : Fin s) :
      (C theta * pkg.substP (a i) ^ 2 +
        C δ * pkg.substV (a i) ^ 2).totalDegree ≤ F := by
    exact (MvPolynomial.totalDegree_add _ _).trans <| max_le
      ((mv_C_mul_totalDegree_le theta _).trans
        ((pkg.substP_sq_totalDegree_le (a i)).trans
          (Nat.mul_le_mul_left pkg.degreeBound (haDegree i))))
      ((mv_C_mul_totalDegree_le δ _).trans
        ((pkg.substV_sq_totalDegree_le (a i)).trans
          (Nat.mul_le_mul_left pkg.degreeBound (haDegree i))))
  have hENorm (i : Fin s) : coeffL1Norm (pkg.substE (a i)) ≤ Kfactor := by
    dsimp [Kfactor]
    exact substE_coeffL1Norm_le_conversionFactor pkg B' (a i) hG (haNorm i)
  have hErrorNorm (i : Fin s) : coeffL1Norm
      (C theta * pkg.substP (a i) ^ 2 +
        C δ * pkg.substV (a i) ^ 2) ≤ Kfactor := by
    dsimp [Kfactor]
    exact errorUpper_coeffL1Norm_le_conversionFactor
      pkg B' (a i) hG (haNorm i)
  obtain ⟨cprodRaw⟩ := BoundedModuleLEAt.prod K
    (fun i => pkg.substE (a i))
    (fun i => C theta * pkg.substP (a i) ^ 2 +
      C δ * pkg.substV (a i) ^ 2)
    Rint F hHint hKfactor
    (fun i hi => pkg.substE_isSOS (a i) hδ)
    (fun i hi => IsSOS_add
      (IsSOS_mul (IsSOS_C_nonneg theta htheta) (IsSOS_sq _))
      (IsSOS_mul (IsSOS_C_nonneg δ hδ.le) (IsSOS_sq _)))
    (fun i hi => hEDegree i) (fun i hi => hErrorDegree i)
    (fun i hi => hENorm i) (fun i hi => hErrorNorm i)
    (fun i hi => (hE i).some)
  have hprodOrder : K.card * (Rint + F) ≤ Rprod := by
    dsimp [Rprod, conversionProductOrder]
    exact Nat.mul_le_mul_right (Rint + F) (finset_fin_card_le K)
  have hprodBudget : (Kfactor + 1) ^ K.card * Hint ≤ Hprod := by
    dsimp [Hprod, boundedConversionProductBudget]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hbase (finset_fin_card_le K)) hHint
  let cprod : BoundedModuleLEAt g Rprod Hprod
      (∏ i ∈ K, pkg.substE (a i))
      (∏ i ∈ K, (C theta * pkg.substP (a i) ^ 2 +
        C δ * pkg.substV (a i) ^ 2)) :=
    (cprodRaw.mono hprodOrder).weakenBound hprodBudget
  have hPprodNorm : coeffL1Norm
      (∏ i ∈ I \ K, pkg.substP (a i) ^ 2) ≤
      (Kfactor + 1) ^ s := by
    calc
      coeffL1Norm (∏ i ∈ I \ K, pkg.substP (a i) ^ 2) ≤
          ∏ i ∈ I \ K, coeffL1Norm (pkg.substP (a i) ^ 2) :=
        coeffL1Norm_prod_le _ _
      _ ≤ ∏ _i ∈ I \ K, Kfactor := by
        exact Finset.prod_le_prod₀
          (fun _ _ => coeffL1Norm_nonneg _)
          (fun i hi => substP_sq_coeffL1Norm_le_conversionFactor
            pkg B' (a i) hG (haNorm i))
      _ = Kfactor ^ (I \ K).card := by simp
      _ ≤ (Kfactor + 1) ^ (I \ K).card :=
        pow_le_pow_left₀ hKfactor (by linarith) _
      _ ≤ (Kfactor + 1) ^ s :=
        pow_le_pow_right₀ hbase (finset_fin_card_le (I \ K))
  have hVprodNorm : coeffL1Norm
      (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2) ≤
      (Kfactor + 1) ^ s := by
    calc
      coeffL1Norm (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2) ≤
          ∏ i ∈ Iᶜ, coeffL1Norm (pkg.substV (a i) ^ 2) :=
        coeffL1Norm_prod_le _ _
      _ ≤ ∏ _i ∈ Iᶜ, Kfactor := by
        exact Finset.prod_le_prod₀
          (fun _ _ => coeffL1Norm_nonneg _)
          (fun i hi => substV_sq_coeffL1Norm_le_conversionFactor
            pkg B' (a i) hG (haNorm i))
      _ = Kfactor ^ Iᶜ.card := by simp
      _ ≤ (Kfactor + 1) ^ Iᶜ.card :=
        pow_le_pow_left₀ hKfactor (by linarith) _
      _ ≤ (Kfactor + 1) ^ s :=
        pow_le_pow_right₀ hbase (finset_fin_card_le Iᶜ)
  have hcontextNorm : coeffL1Norm
      (sigma I * (∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
        ∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2) ≤ Hcontext := by
    calc
      coeffL1Norm
          (sigma I * (∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
            ∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2) ≤
          (coeffL1Norm (sigma I) *
            coeffL1Norm (∏ i ∈ I \ K, pkg.substP (a i) ^ 2)) *
              coeffL1Norm (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2) :=
        (coeffL1Norm_mul_le _ _).trans <|
          mul_le_mul_of_nonneg_right (coeffL1Norm_mul_le _ _)
            (coeffL1Norm_nonneg _)
      _ ≤ (Hsigma * (Kfactor + 1) ^ s) *
          (Kfactor + 1) ^ s := by
        exact mul_le_mul
          (mul_le_mul (hsigmaNorm I) hPprodNorm
            (coeffL1Norm_nonneg _) hHsigma)
          hVprodNorm (coeffL1Norm_nonneg _)
          (mul_nonneg hHsigma (by positivity))
      _ = Hcontext := by
        dsimp [Hcontext, boundedConversionContextBound]
        rw [show 2 * s = s + s by omega, pow_add]
        ring
  have hcontextSOS : IsSOS
      (sigma I * (∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
        ∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2) :=
    IsSOS_mul
      (IsSOS_mul (hsigma I)
        (IsSOS_finset_prod fun i hi => IsSOS_sq _))
      (IsSOS_finset_prod fun i hi => IsSOS_sq _)
  have hPprodDegree :
      (∏ i ∈ I \ K, pkg.substP (a i) ^ 2).totalDegree ≤ s * F :=
    (totalDegree_finset_prod_le_card_mul (I \ K) _ F
      (fun i hi => (pkg.substP_sq_totalDegree_le (a i)).trans
        (Nat.mul_le_mul_left pkg.degreeBound (haDegree i)))).trans
      (Nat.mul_le_mul_right F (finset_fin_card_le (I \ K)))
  have hVprodDegree :
      (∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2).totalDegree ≤ s * F :=
    (totalDegree_finset_prod_le_card_mul Iᶜ _ F
      (fun i hi => (pkg.substV_sq_totalDegree_le (a i)).trans
        (Nat.mul_le_mul_left pkg.degreeBound (haDegree i)))).trans
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
        Nat.add_le_add
          (Nat.add_le_add (hsigmaDegree I) hPprodDegree) hVprodDegree
      _ = d + 2 * s * F := by ring
  have hmul := cprod.sosMulLeftOfNormLe hcontextSOS hcontextNorm
  have horder :
      (sigma I * (∏ i ∈ I \ K, pkg.substP (a i) ^ 2) *
          ∏ i ∈ Iᶜ, pkg.substV (a i) ^ 2).totalDegree + Rprod ≤
        conversionExpansionOrder pkg s d rA rB := by
    calc
      _ ≤ (d + 2 * s * F) + Rprod :=
        Nat.add_le_add_right hcontextDegree Rprod
      _ = Rprod + (d + 2 * s * F) := by omega
      _ = conversionExpansionOrder pkg s d rA rB := by
        simp [conversionExpansionOrder, Rprod, F]
  have cfinal : BoundedModuleLEAt g
      (conversionExpansionOrder pkg s d rA rB) (Hcontext * Hprod)
      (errorExpansionTerm (fun _ => pkg) a sigma I K)
      (errorBoundTerm (fun _ => pkg) a sigma I K) :=
    (hmul.mono horder).congr (by
    dsimp [errorExpansionTerm, errorBoundTerm]
    ring)
  refine ⟨?_⟩
  simpa [boundedConversionExpansionBudget, Hcontext, Hprod,
    Kfactor, Hint] using cfinal

end OptimalConvergenceRates.GeneralArchimedean

end

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

variable {n m : ℕ}

/-- A common coefficient envelope for a product of a bounded number of
factors. -/
theorem coeffL1Norm_finset_prod_le_common_pow
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (q : ι → MvPolynomial (Fin n) ℝ)
    {K : ℝ} {s : ℕ} (hK : 0 ≤ K) (hcard : S.card ≤ s)
    (hq : ∀ i ∈ S, coeffL1Norm (q i) ≤ K) :
    coeffL1Norm (∏ i ∈ S, q i) ≤ (K + 1) ^ s := by
  have hbase : 1 ≤ K + 1 := by linarith
  calc
    coeffL1Norm (∏ i ∈ S, q i) ≤
        ∏ i ∈ S, coeffL1Norm (q i) :=
      coeffL1Norm_prod_le S q
    _ ≤ ∏ _i ∈ S, K := by
      exact Finset.prod_le_prod₀
        (fun _ _ => coeffL1Norm_nonneg _)
        hq
    _ = K ^ S.card := by simp
    _ ≤ (K + 1) ^ S.card :=
      pow_le_pow_left₀ hK (by linarith) _
    _ ≤ (K + 1) ^ s :=
      pow_le_pow_right₀ hbase hcard

/-- Budget for a product of numerator comparisons. -/
def boundedConversionNumeratorProductBudget
    (s : ℕ) (comparisonBound factorBound : ℝ) : ℝ :=
  (factorBound + 1) ^ s * comparisonBound

/-- Budget for a product of scaled error comparisons. -/
def boundedConversionErrorProductBudget
    (s : ℕ) (theta comparisonBound factorBound : ℝ) : ℝ :=
  (factorBound + 1) ^ s * (theta * comparisonBound)

/-- Budget after adjoining the numerator comparison product to the
coefficient comparison for the preordering multiplier. -/
def boundedConversionFirstScalarBudget
    (s : ℕ) (sigmaCertificateBound sigmaNormBound
      comparisonBound factorBound : ℝ) : ℝ :=
  (factorBound + 1) ^ s * sigmaCertificateBound +
    sigmaNormBound *
      boundedConversionNumeratorProductBudget s comparisonBound factorBound

/-- Budget after adjoining the scaled-error comparison product. -/
def boundedConversionSecondScalarBudget
    (s : ℕ) (sigmaCertificateBound sigmaNormBound theta
      comparisonBound factorBound : ℝ) : ℝ :=
  (factorBound + 1) ^ s *
      boundedConversionFirstScalarBudget s sigmaCertificateBound
        sigmaNormBound comparisonBound factorBound +
    (sigmaNormBound * (factorBound + 1) ^ s) *
      boundedConversionErrorProductBudget s theta comparisonBound factorBound

/-- Final budget for replacing all numerator and error factors by scalar
multiples of denominator squares in one expanded term. -/
def boundedConversionScalarBudget
    (s : ℕ) (sigmaCertificateBound sigmaNormBound theta
      comparisonBound factorBound : ℝ) : ℝ :=
  (factorBound + 1) ^ s *
    boundedConversionSecondScalarBudget s sigmaCertificateBound
      sigmaNormBound theta comparisonBound factorBound

end OptimalConvergenceRates.GeneralArchimedean

end
