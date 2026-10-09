/-
  Linear logarithmic parameter bounds for the sharp two-channel
  preordering-to-quadratic-module conversion.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpQuantitativeConversion
import OptimalConvergenceRates.GeneralArchimedean.ConversionParameterBounds

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

/-- The fixed part of the reciprocal `delta` scale. -/
def sharpDeltaScaleConstant (s : ℕ) (Bprime : ℝ) : ℝ :=
  2 * ((sharpTripleCount s : ℝ) + 1) * (Bprime + 1) ^ s

theorem sharpDeltaScale_eq_constant_mul_inv
    (s : ℕ) (H Bprime : ℝ) :
    sharpDeltaScale s H Bprime =
      (sharpDeltaScaleConstant s Bprime * (H + 1))⁻¹ := by
  unfold sharpDeltaScale sharpDeltaScaleConstant
  congr 1
  ring

theorem sharpDeltaScaleConstant_pos
    {s : ℕ} {Bprime : ℝ} (hBprime : 0 ≤ Bprime) :
    0 < sharpDeltaScaleConstant s Bprime := by
  unfold sharpDeltaScaleConstant
  positivity

theorem one_le_sharpDeltaScaleConstant
    {s : ℕ} {Bprime : ℝ} (hBprime : 0 ≤ Bprime) :
    1 ≤ sharpDeltaScaleConstant s Bprime := by
  let count : ℝ := sharpTripleCount s
  let M : ℝ := Bprime + 1
  have hcount : 0 ≤ count := by positivity
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hpow : 1 ≤ M ^ s := one_le_pow₀ hM
  dsimp [sharpDeltaScaleConstant, count, M]
  nlinarith [mul_nonneg hcount (pow_nonneg (zero_le_one.trans hM) s)]

/-- Fixed coefficient in the linear logarithmic package-degree estimate. -/
def sharpPackageDegreeConstant (s : ℕ) (B Bprime : ℝ) : ℝ :=
  4 *
    (Real.log (sharpThetaScale s / 4) / Real.log (1 / 9) + 1) *
    (dyadicLinearConstant B (sharpDeltaScaleConstant s Bprime) + 1)

/-- With `theta` fixed and only `delta` shrinking, the rational package
degree is linear, rather than quadratic, in `1 + log x`. -/
theorem package_degreeBound_le_log_linear
    {s : ℕ} {δ B Bprime x : ℝ}
    (pkg : Package δ B (sharpThetaScale s))
    (hB : 0 ≤ B) (hBprime : 0 ≤ Bprime) (hx : 1 ≤ x)
    (hδ : δ = (sharpDeltaScaleConstant s Bprime * x)⁻¹)
    (hell : (pkg.ell : ℝ) ≤
      Real.log (sharpThetaScale s / 4) / Real.log (1 / 9) + 1)
    (hJ : (pkg.J : ℝ) ≤
      Real.log
          (Real.sqrt (B + δ) / Real.sqrt δ) /
        Real.log 2) :
    (pkg.degreeBound : ℝ) ≤
      sharpPackageDegreeConstant s B Bprime * (1 + Real.log x) := by
  subst δ
  let C₀ := sharpDeltaScaleConstant s Bprime
  let L : ℝ := 1 + Real.log x
  let Etheta : ℝ :=
    Real.log (sharpThetaScale s / 4) / Real.log (1 / 9) + 1
  have hC : 1 ≤ C₀ := one_le_sharpDeltaScaleConstant hBprime
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hEtheta : 0 ≤ Etheta := by
    have hellNonneg : 0 ≤ (pkg.ell : ℝ) := by positivity
    exact hellNonneg.trans hell
  have hJ' : (pkg.J : ℝ) ≤ dyadicLinearConstant B C₀ * L := by
    apply hJ.trans
    simpa [C₀, L] using dyadicLogExpression_le_linear hB hC hx
  have hJone :
      (pkg.J : ℝ) + 1 ≤ (dyadicLinearConstant B C₀ + 1) * L := by
    calc
      (pkg.J : ℝ) + 1 ≤ dyadicLinearConstant B C₀ * L + L :=
        add_le_add hJ' hL
      _ = (dyadicLinearConstant B C₀ + 1) * L := by ring
  have hmul :
      (pkg.ell : ℝ) * ((pkg.J : ℝ) + 1) ≤
        Etheta * ((dyadicLinearConstant B C₀ + 1) * L) := by
    exact mul_le_mul hell hJone (by positivity) hEtheta
  calc
    (pkg.degreeBound : ℝ) =
        4 * (pkg.ell : ℝ) * ((pkg.J : ℝ) + 1) := by
      simp [RationalSquareRoot.Package.degreeBound]
    _ ≤ 4 * (Etheta *
          ((dyadicLinearConstant B C₀ + 1) * L)) := by nlinarith
    _ = sharpPackageDegreeConstant s B Bprime *
          (1 + Real.log x) := by
      unfold sharpPackageDegreeConstant
      dsimp [C₀, Etheta, L]
      ring

/-- Specialization to the sharp scale `delta = C⁻¹(H+1)⁻¹`. -/
theorem package_degreeBound_le_of_sharpDeltaScale
    {s : ℕ} {H B Bprime : ℝ}
    (hH : 0 ≤ H) (hB : 0 ≤ B) (hBprime : 0 ≤ Bprime)
    (pkg : Package (sharpDeltaScale s H Bprime) B (sharpThetaScale s))
    (hell : (pkg.ell : ℝ) ≤
      Real.log (sharpThetaScale s / 4) / Real.log (1 / 9) + 1)
    (hJ : (pkg.J : ℝ) ≤
      Real.log
          (Real.sqrt (B + sharpDeltaScale s H Bprime) /
            Real.sqrt (sharpDeltaScale s H Bprime)) /
        Real.log 2) :
    (pkg.degreeBound : ℝ) ≤
      sharpPackageDegreeConstant s B Bprime *
        (1 + Real.log (H + 1)) := by
  exact package_degreeBound_le_log_linear pkg hB hBprime (by linarith)
    (sharpDeltaScale_eq_constant_mul_inv s H Bprime) hell hJ

/-- Sharp conversion order expressed only through the common package
degree. -/
def sharpConversionRefutationOrderOfDegree
    (L s d rSigma rA rB : ℕ) : ℕ :=
  let F := L * d
  let Rint := max rA rB + (L + 3) * d
  let Rprod := s * (Rint + F)
  let R₁ := max (rSigma + s * F) (Rprod + d)
  let R₂ := max (R₁ + s * F) (d + s * F)
  let R₃ := max (R₂ + s * F) (Rprod + (d + 2 * s * F))
  let R₄ := max (R₃ + s * F) (d + 3 * s * F)
  let Rexpansion := Rprod + (d + 2 * s * F)
  let RE := d + 3 * s * F
  let Rterm := max Rexpansion (max RE R₄)
  let Rodd := max Rterm RE
  max Rodd (s * ((rA + F) + F))

theorem sharpConversionRefutationOrder_eq_ofDegree
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (s d rSigma rA rB : ℕ) :
    sharpConversionRefutationOrder pkg s d rSigma rA rB =
      sharpConversionRefutationOrderOfDegree
        pkg.degreeBound s d rSigma rA rB := by
  simp only [sharpConversionRefutationOrder, conversionSharpOddOrder,
    conversionSharpOddTermOrder, conversionExpansionOrder,
    conversionSharpScalarTermOrder, conversionProductOrder,
    conversionIntervalOrder, conversionFactorDegree,
    sharpConversionRefutationOrderOfDegree]

set_option maxHeartbeats 800000 in
-- Nested maxima require a larger budget for the direct monotonicity proof.
theorem sharpConversionRefutationOrderOfDegree_mono
    {L M s d rSigma rA rB : ℕ} (hLM : L ≤ M) :
    sharpConversionRefutationOrderOfDegree L s d rSigma rA rB ≤
      sharpConversionRefutationOrderOfDegree M s d rSigma rA rB := by
  let FL := L * d
  let FM := M * d
  let RintL := max rA rB + (L + 3) * d
  let RintM := max rA rB + (M + 3) * d
  let RprodL := s * (RintL + FL)
  let RprodM := s * (RintM + FM)
  let R₁L := max (rSigma + s * FL) (RprodL + d)
  let R₁M := max (rSigma + s * FM) (RprodM + d)
  let R₂L := max (R₁L + s * FL) (d + s * FL)
  let R₂M := max (R₁M + s * FM) (d + s * FM)
  let R₃L := max (R₂L + s * FL) (RprodL + (d + 2 * s * FL))
  let R₃M := max (R₂M + s * FM) (RprodM + (d + 2 * s * FM))
  let R₄L := max (R₃L + s * FL) (d + 3 * s * FL)
  let R₄M := max (R₃M + s * FM) (d + 3 * s * FM)
  have hF : FL ≤ FM := by
    dsimp [FL, FM]
    exact Nat.mul_le_mul_right d hLM
  have hRint : RintL ≤ RintM := by
    dsimp [RintL, RintM]
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_right d (Nat.add_le_add_right hLM 3)) _
  have hRprod : RprodL ≤ RprodM :=
    Nat.mul_le_mul_left s (Nat.add_le_add hRint hF)
  have hsF : s * FL ≤ s * FM := Nat.mul_le_mul_left s hF
  have hR₁ : R₁L ≤ R₁M :=
    max_le_max (Nat.add_le_add_left hsF rSigma)
      (Nat.add_le_add_right hRprod d)
  have hR₂ : R₂L ≤ R₂M :=
    max_le_max (Nat.add_le_add hR₁ hsF)
      (Nat.add_le_add_left hsF d)
  have htwo : 2 * s * FL ≤ 2 * s * FM := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hsF
  have hR₃ : R₃L ≤ R₃M :=
    max_le_max (Nat.add_le_add hR₂ hsF)
      (Nat.add_le_add hRprod (Nat.add_le_add_left htwo d))
  have hthree : 3 * s * FL ≤ 3 * s * FM := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 3 hsF
  have hRE : d + 3 * s * FL ≤ d + 3 * s * FM :=
    Nat.add_le_add_left hthree d
  have hR₄ : R₄L ≤ R₄M :=
    max_le_max (Nat.add_le_add hR₃ hsF) hRE
  have hExpansion :
      RprodL + (d + 2 * s * FL) ≤
        RprodM + (d + 2 * s * FM) :=
    Nat.add_le_add hRprod (Nat.add_le_add_left htwo d)
  have hTerm :
      max (RprodL + (d + 2 * s * FL)) (max (d + 3 * s * FL) R₄L) ≤
        max (RprodM + (d + 2 * s * FM))
          (max (d + 3 * s * FM) R₄M) :=
    max_le_max hExpansion (max_le_max hRE hR₄)
  have hOdd := max_le_max hTerm hRE
  have hDen :
      s * ((rA + FL) + FL) ≤ s * ((rA + FM) + FM) :=
    Nat.mul_le_mul_left s
      (Nat.add_le_add (Nat.add_le_add_left hF rA) hF)
  simpa [sharpConversionRefutationOrderOfDegree, FL, FM, RintL, RintM,
    RprodL, RprodM, R₁L, R₁M, R₂L, R₂M, R₃L, R₃M, R₄L, R₄M]
    using max_le_max hOdd hDen

/-- Package-dependent sharp conversion orders are bounded by the explicit
linear-logarithmic ceiling. -/
theorem sharpConversionRefutationOrder_le_log_ceiling
    {s : ℕ} {H B Bprime : ℝ}
    (hH : 0 ≤ H) (hB : 0 ≤ B) (hBprime : 0 ≤ Bprime)
    (pkg : Package (sharpDeltaScale s H Bprime) B (sharpThetaScale s))
    (hell : (pkg.ell : ℝ) ≤
      Real.log (sharpThetaScale s / 4) / Real.log (1 / 9) + 1)
    (hJ : (pkg.J : ℝ) ≤
      Real.log
          (Real.sqrt (B + sharpDeltaScale s H Bprime) /
            Real.sqrt (sharpDeltaScale s H Bprime)) /
        Real.log 2)
    (d rSigma rA rB : ℕ) :
    sharpConversionRefutationOrder pkg s d rSigma rA rB ≤
      sharpConversionRefutationOrderOfDegree
        (Nat.ceil (sharpPackageDegreeConstant s B Bprime *
          (1 + Real.log (H + 1)))) s d rSigma rA rB := by
  rw [sharpConversionRefutationOrder_eq_ofDegree]
  apply sharpConversionRefutationOrderOfDegree_mono
  have hreal := package_degreeBound_le_of_sharpDeltaScale
    hH hB hBprime pkg hell hJ
  have hceil := Nat.le_ceil
    (sharpPackageDegreeConstant s B Bprime * (1 + Real.log (H + 1)))
  exact_mod_cast hreal.trans hceil

/-- Select the package with fixed `theta` and shrinking `delta`, and perform
the complete degree-tracked sharp conversion. -/
theorem sharp_bounded_preordering_refutation_to_module_at
    {s m n : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
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
    let theta : ℝ := sharpThetaScale s
    let delta : ℝ := sharpDeltaScale s H Bprime
    ∃ pkg : Package delta B theta,
      (pkg.ell : ℝ) ≤
          Real.log (theta / 4) / Real.log (1 / 9) + 1 ∧
        (pkg.J : ℝ) ≤
          Real.log (Real.sqrt (B + delta) / Real.sqrt delta) /
            Real.log 2 ∧
        (-1 : MvPolynomial (Fin n) ℝ) ∈ GenQuadraticModule g
          (sharpConversionRefutationOrder pkg s d rSigma rA rB) := by
  dsimp only
  let Bprime : ℝ := 2 * (B + 1)
  let theta : ℝ := sharpThetaScale s
  let delta : ℝ := sharpDeltaScale s H Bprime
  have hBprime : 0 ≤ Bprime := by dsimp [Bprime]; positivity
  have htheta : 0 < theta := sharpThetaScale_pos s
  have hthetaHalf : theta ≤ 1 / 2 := sharpThetaScale_le_half s
  have hthetaOne : theta ≤ 1 := hthetaHalf.trans (by norm_num)
  have hthetaLtOne : theta < 1 :=
    lt_of_le_of_lt hthetaHalf (by norm_num)
  have hdelta : 0 < delta := sharpDeltaScale_pos hH hBprime
  have hdeltaHalf : delta ≤ 1 / 2 := sharpDeltaScale_le_half hH hBprime
  have hcondition : B + delta ≤ (1 - theta) * Bprime := by
    have hfactor : 1 ≤ 2 * (1 - theta) := by linarith
    have hB1 : 0 ≤ B + 1 := by linarith
    calc
      B + delta ≤ B + 1 := by linarith
      _ = 1 * (B + 1) := by ring
      _ ≤ (2 * (1 - theta)) * (B + 1) :=
        mul_le_mul_of_nonneg_right hfactor hB1
      _ = (1 - theta) * Bprime := by dsimp [Bprime]; ring
  obtain ⟨pkg, hell, hJ⟩ :=
    RationalSquareRoot.package_nonempty_with_parameter_log_bounds
      hdelta hB.le htheta hthetaOne
  refine ⟨pkg, hell, hJ, ?_⟩
  exact refutation_of_sharpAbsorption_at
    pkg a sigma hsigma hsigmaDegree hsigmaBound ha hBa haDegree
    hdelta hB htheta.le hthetaLtOne hBprime hcondition hidentity
    (sharpThetaCoefficient_scale_lt_one s).le
    (sharpDeltaCoefficient_scale_lt_one hH hBprime htheta.le hthetaOne)

/-- The selected sharp conversion, with no package-dependent degree left in
the conclusion. -/
theorem sharp_preordering_refutation_mem_log_ceiling
    {s m n : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
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
    (-1 : MvPolynomial (Fin n) ℝ) ∈ GenQuadraticModule g
      (sharpConversionRefutationOrderOfDegree
        (Nat.ceil (sharpPackageDegreeConstant s B Bprime *
          (1 + Real.log (H + 1)))) s d rSigma rA rB) := by
  dsimp only
  let Bprime : ℝ := 2 * (B + 1)
  obtain ⟨pkg, hell, hJ, hmem⟩ :=
    sharp_bounded_preordering_refutation_to_module_at
      a sigma B H hB hH hsigma hsigmaDegree hsigmaBound ha hBa
      haDegree hidentity
  have hBprime : 0 ≤ Bprime := by dsimp [Bprime]; positivity
  exact GenQuadraticModule_mono
    (sharpConversionRefutationOrder_le_log_ceiling
      hH hB.le hBprime pkg hell hJ d rSigma rA rB) hmem

end OptimalConvergenceRates.GeneralArchimedean

end
