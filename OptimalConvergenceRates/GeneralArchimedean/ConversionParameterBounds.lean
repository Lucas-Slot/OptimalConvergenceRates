/-
  Logarithmic bounds for the rational-square-root parameters selected by the
  quantitative preordering-to-module conversion.
-/
import OptimalConvergenceRates.GeneralArchimedean.QuantitativeBridge

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

/-- The part of the reciprocal absorption scale independent of the
preordering multiplier bound. -/
def absorptionScaleConstant (s : ℕ) (Bprime : ℝ) : ℝ :=
  2 * ((oddPairCount s : ℝ) + 1) * (Bprime + 1) ^ (s + 1)

theorem absorptionScale_eq_constant_mul_inv
    (s : ℕ) (H Bprime : ℝ) :
    absorptionScale s H Bprime =
      (absorptionScaleConstant s Bprime * (H + 1))⁻¹ := by
  unfold absorptionScale absorptionScaleConstant
  congr 1
  ring

theorem absorptionScaleConstant_pos
    {s : ℕ} {Bprime : ℝ} (hBprime : 0 ≤ Bprime) :
    0 < absorptionScaleConstant s Bprime := by
  unfold absorptionScaleConstant
  positivity

theorem one_le_absorptionScaleConstant
    {s : ℕ} {Bprime : ℝ} (hBprime : 0 ≤ Bprime) :
    1 ≤ absorptionScaleConstant s Bprime := by
  let count : ℝ := oddPairCount s
  let M : ℝ := Bprime + 1
  have hcount : 0 ≤ count := by positivity
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hpow : 1 ≤ M ^ (s + 1) := one_le_pow₀ hM
  dsimp [absorptionScaleConstant, count, M]
  nlinarith [mul_nonneg hcount (pow_nonneg (zero_le_one.trans hM) (s + 1))]

theorem ellLogExpression_eq
    {C x : ℝ} (hC : 0 < C) (hx : 0 < x) :
    Real.log ((C * x)⁻¹ / 4) / Real.log (1 / 9) + 1 =
      (Real.log C + Real.log x + Real.log 4) / Real.log 9 + 1 := by
  rw [Real.log_div (inv_ne_zero (mul_ne_zero hC.ne' hx.ne')) (by norm_num)]
  rw [Real.log_inv]
  rw [Real.log_mul hC.ne' hx.ne']
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (9 : ℝ) ≠ 0)]
  norm_num only [Real.log_one]
  ring

theorem absorptionScale_pos_le_one
    {s : ℕ} {H Bprime : ℝ} (hH : 0 ≤ H) (hBprime : 0 ≤ Bprime) :
    0 < absorptionScale s H Bprime ∧
      absorptionScale s H Bprime ≤ 1 := by
  rw [absorptionScale_eq_constant_mul_inv]
  have hC := one_le_absorptionScaleConstant (s := s) hBprime
  have hx : 1 ≤ H + 1 := by linarith
  have hprod : 0 < absorptionScaleConstant s Bprime * (H + 1) := by
    positivity
  constructor
  · exact inv_pos.mpr hprod
  · exact (inv_le_one₀ hprod).mpr (one_le_mul_of_one_le_of_one_le hC hx)

theorem log_sqrt_div_sqrt_eq
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (Real.sqrt x / Real.sqrt y) =
      (Real.log x - Real.log y) / 2 := by
  rw [Real.log_div (Real.sqrt_pos.2 hx).ne' (Real.sqrt_pos.2 hy).ne']
  rw [Real.log_sqrt hx.le, Real.log_sqrt hy.le]
  ring

theorem log_inv_mul_eq
    {C x : ℝ} (hC : 0 < C) (hx : 0 < x) :
    Real.log (C * x)⁻¹ = -(Real.log C + Real.log x) := by
  rw [Real.log_inv, Real.log_mul hC.ne' hx.ne']

/-- A coarse logarithmic bound for the dyadic covering parameter.  Its
form is chosen so that the right-hand side separates the fixed data from
the varying multiplier bound. -/
theorem dyadicLogExpression_le
    {B C x : ℝ} (hB : 0 ≤ B) (hC : 1 ≤ C) (hx : 1 ≤ x) :
    Real.log
          (Real.sqrt (B + (C * x)⁻¹) /
            Real.sqrt (C * x)⁻¹) /
        Real.log 2 ≤
      (Real.log (B + 1) + Real.log C + Real.log x) /
        (2 * Real.log 2) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hprod : 0 < C * x := mul_pos hCpos hxpos
  have heta : 0 < (C * x)⁻¹ := inv_pos.mpr hprod
  have heta1 : (C * x)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ hprod).mpr (one_le_mul_of_one_le_of_one_le hC hx)
  have hsumPos : 0 < B + (C * x)⁻¹ := by positivity
  have hsum : B + (C * x)⁻¹ ≤ B + 1 := by linarith
  have hlogsum : Real.log (B + (C * x)⁻¹) ≤ Real.log (B + 1) :=
    Real.log_le_log hsumPos hsum
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [log_sqrt_div_sqrt_eq hsumPos heta]
  rw [log_inv_mul_eq hCpos hxpos]
  calc
    (Real.log (B + (C * x)⁻¹) -
          -(Real.log C + Real.log x)) / 2 / Real.log 2 =
        (Real.log (B + (C * x)⁻¹) -
          -(Real.log C + Real.log x)) / (2 * Real.log 2) := by ring
    _ ≤ (Real.log (B + 1) + Real.log C + Real.log x) /
          (2 * Real.log 2) := by
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- Fixed coefficient in the linear logarithmic bound for `Package.ell`. -/
def ellLinearConstant (C : ℝ) : ℝ :=
  1 + (Real.log C + Real.log 4) / Real.log 9 + 1 / Real.log 9

/-- Fixed coefficient in the linear logarithmic bound for `Package.J`. -/
def dyadicLinearConstant (B C : ℝ) : ℝ :=
  (Real.log (B + 1) + Real.log C) / (2 * Real.log 2) +
    1 / (2 * Real.log 2)

theorem ellLinearConstant_nonneg
    {C : ℝ} (hC : 1 ≤ C) : 0 ≤ ellLinearConstant C := by
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  unfold ellLinearConstant
  positivity

theorem dyadicLinearConstant_nonneg
    {B C : ℝ} (hB : 0 ≤ B) (hC : 1 ≤ C) :
    0 ≤ dyadicLinearConstant B C := by
  have hlogB : 0 ≤ Real.log (B + 1) :=
    Real.log_nonneg (by linarith)
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold dyadicLinearConstant
  positivity

theorem ellLogExpression_le_linear
    {C x : ℝ} (hC : 1 ≤ C) (hx : 1 ≤ x) :
    Real.log ((C * x)⁻¹ / 4) / Real.log (1 / 9) + 1 ≤
      ellLinearConstant C * (1 + Real.log x) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  rw [ellLogExpression_eq hCpos hxpos]
  unfold ellLinearConstant
  have hbase :
      0 ≤ 1 + (Real.log C + Real.log 4) / Real.log 9 := by
    positivity
  have hslope : 0 ≤ 1 / Real.log 9 := by positivity
  calc
    (Real.log C + Real.log x + Real.log 4) / Real.log 9 + 1 =
        (1 + (Real.log C + Real.log 4) / Real.log 9) +
          (1 / Real.log 9) * Real.log x := by ring
    _ ≤ (1 + (Real.log C + Real.log 4) / Real.log 9) *
          (1 + Real.log x) +
        (1 / Real.log 9) * (1 + Real.log x) := by
      gcongr
      · exact le_mul_of_one_le_right hbase (by linarith)
      · linarith
    _ = (1 + (Real.log C + Real.log 4) / Real.log 9 +
          1 / Real.log 9) * (1 + Real.log x) := by ring

theorem dyadicLogExpression_le_linear
    {B C x : ℝ} (hB : 0 ≤ B) (hC : 1 ≤ C) (hx : 1 ≤ x) :
    Real.log
          (Real.sqrt (B + (C * x)⁻¹) /
            Real.sqrt (C * x)⁻¹) /
        Real.log 2 ≤
      dyadicLinearConstant B C * (1 + Real.log x) := by
  have hraw := dyadicLogExpression_le hB hC hx
  have hlogB : 0 ≤ Real.log (B + 1) :=
    Real.log_nonneg (by linarith)
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold dyadicLinearConstant
  have hbase :
      0 ≤ (Real.log (B + 1) + Real.log C) /
        (2 * Real.log 2) := by positivity
  have hslope : 0 ≤ 1 / (2 * Real.log 2) := by positivity
  apply hraw.trans
  calc
    (Real.log (B + 1) + Real.log C + Real.log x) /
          (2 * Real.log 2) =
        (Real.log (B + 1) + Real.log C) / (2 * Real.log 2) +
          (1 / (2 * Real.log 2)) * Real.log x := by ring
    _ ≤ (Real.log (B + 1) + Real.log C) / (2 * Real.log 2) *
          (1 + Real.log x) +
        (1 / (2 * Real.log 2)) * (1 + Real.log x) := by
      gcongr
      · exact le_mul_of_one_le_right hbase (by linarith)
      · linarith
    _ = ((Real.log (B + 1) + Real.log C) / (2 * Real.log 2) +
          1 / (2 * Real.log 2)) * (1 + Real.log x) := by ring


/-- Fixed coefficient in the quadratic logarithmic bound for the common
degree of the numerator, denominator, and error polynomials. -/
def packageDegreeConstant (B C : ℝ) : ℝ :=
  4 * ellLinearConstant C * (dyadicLinearConstant B C + 1)

theorem packageDegreeConstant_nonneg
    {B C : ℝ} (hB : 0 ≤ B) (hC : 1 ≤ C) :
    0 ≤ packageDegreeConstant B C := by
  unfold packageDegreeConstant
  exact mul_nonneg
    (mul_nonneg (by norm_num) (ellLinearConstant_nonneg hC))
    (by linarith [dyadicLinearConstant_nonneg hB hC])

/-- If the package shift is the reciprocal of `C*x` and the two package
parameters satisfy their standard logarithmic estimates, then its common
polynomial degree is quadratic in `1 + log x`. -/
theorem package_degreeBound_le_log_sq
    {δ B theta C x : ℝ} (pkg : Package δ B theta)
    (hB : 0 ≤ B) (hC : 1 ≤ C) (hx : 1 ≤ x)
    (hδ : δ = (C * x)⁻¹)
    (hell : (pkg.ell : ℝ) ≤
      Real.log (δ / 4) / Real.log (1 / 9) + 1)
    (hJ : (pkg.J : ℝ) ≤
      Real.log (Real.sqrt (B + δ) / Real.sqrt δ) / Real.log 2) :
    (pkg.degreeBound : ℝ) ≤
      packageDegreeConstant B C * (1 + Real.log x) ^ 2 := by
  subst δ
  let L : ℝ := 1 + Real.log x
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hell' : (pkg.ell : ℝ) ≤ ellLinearConstant C * L := by
    exact hell.trans (by
      simpa [L] using ellLogExpression_le_linear hC hx)
  have hJ' : (pkg.J : ℝ) ≤ dyadicLinearConstant B C * L := by
    exact hJ.trans (by
      simpa [L] using dyadicLogExpression_le_linear hB hC hx)
  have hJone :
      (pkg.J : ℝ) + 1 ≤ (dyadicLinearConstant B C + 1) * L := by
    calc
      (pkg.J : ℝ) + 1 ≤ dyadicLinearConstant B C * L + L :=
        add_le_add hJ' hL
      _ = (dyadicLinearConstant B C + 1) * L := by ring
  have hmul :
      (pkg.ell : ℝ) * ((pkg.J : ℝ) + 1) ≤
        (ellLinearConstant C * L) *
          ((dyadicLinearConstant B C + 1) * L) := by
    exact mul_le_mul hell' hJone (by positivity)
      (mul_nonneg (ellLinearConstant_nonneg hC) hL0)
  calc
    (pkg.degreeBound : ℝ) =
        4 * (pkg.ell : ℝ) * ((pkg.J : ℝ) + 1) := by
      simp [RationalSquareRoot.Package.degreeBound]
    _ ≤ 4 * ((ellLinearConstant C * L) *
          ((dyadicLinearConstant B C + 1) * L)) := by
      nlinarith
    _ = packageDegreeConstant B C * L ^ 2 := by
      unfold packageDegreeConstant
      ring
    _ = packageDegreeConstant B C * (1 + Real.log x) ^ 2 := rfl

/-- Specialization to the reciprocal absorption scale used by the
preordering-to-module conversion. -/
theorem package_degreeBound_le_of_absorptionScale
    {s : ℕ} {H B Bprime : ℝ}
    (hH : 0 ≤ H) (hB : 0 ≤ B) (hBprime : 0 ≤ Bprime)
    (pkg : Package (absorptionScale s H Bprime) B
      (absorptionScale s H Bprime))
    (hell : (pkg.ell : ℝ) ≤
      Real.log (absorptionScale s H Bprime / 4) /
        Real.log (1 / 9) + 1)
    (hJ : (pkg.J : ℝ) ≤
      Real.log
          (Real.sqrt (B + absorptionScale s H Bprime) /
            Real.sqrt (absorptionScale s H Bprime)) /
        Real.log 2) :
    (pkg.degreeBound : ℝ) ≤
      packageDegreeConstant B (absorptionScaleConstant s Bprime) *
        (1 + Real.log (H + 1)) ^ 2 := by
  apply package_degreeBound_le_log_sq pkg hB
    (one_le_absorptionScaleConstant hBprime) (by linarith)
    (absorptionScale_eq_constant_mul_inv s H Bprime) hell hJ


/-- The tracked conversion order written solely as a function of the common
rational-package degree. -/
def conversionRefutationOrderOfDegree
    (L s d rSigma rA rB : ℕ) : ℕ :=
  let F := L * d
  let Rint := max rA rB + (L + 3) * d
  let Rprod := s * (Rint + F)
  let R₁ := max (rSigma + s * F) (Rprod + d)
  let R₂ := max (R₁ + s * F) (Rprod + (d + s * F))
  let Rscalar := R₂ + s * F
  let Rexpansion := Rprod + (d + 2 * s * F)
  let Rodd := max Rexpansion Rscalar
  max (max Rodd (d + 3 * s * F))
    (s * ((rA + F) + F))

theorem conversionRefutationOrder_eq_ofDegree
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (s d rSigma rA rB : ℕ) :
    conversionRefutationOrder pkg s d rSigma rA rB =
      conversionRefutationOrderOfDegree
        pkg.degreeBound s d rSigma rA rB := by
  simp only [conversionRefutationOrder,
    conversionOddTermOrder, conversionExpansionOrder,
    conversionScalarTermOrder, conversionProductOrder,
    conversionIntervalOrder, conversionFactorDegree,
    conversionRefutationOrderOfDegree]

set_option maxHeartbeats 800000 in
-- The expanded order expression contains several nested maxima; allowing a
-- larger heartbeat budget keeps its monotonicity proof transparent.
theorem conversionRefutationOrderOfDegree_mono
    {L M s d rSigma rA rB : ℕ} (hLM : L ≤ M) :
    conversionRefutationOrderOfDegree L s d rSigma rA rB ≤
      conversionRefutationOrderOfDegree M s d rSigma rA rB := by
  let FL := L * d
  let FM := M * d
  let RintL := max rA rB + (L + 3) * d
  let RintM := max rA rB + (M + 3) * d
  let RprodL := s * (RintL + FL)
  let RprodM := s * (RintM + FM)
  let R₁L := max (rSigma + s * FL) (RprodL + d)
  let R₁M := max (rSigma + s * FM) (RprodM + d)
  let R₂L := max (R₁L + s * FL) (RprodL + (d + s * FL))
  let R₂M := max (R₁M + s * FM) (RprodM + (d + s * FM))
  have hF : FL ≤ FM := by
    dsimp [FL, FM]
    exact Nat.mul_le_mul_right d hLM
  have hRint : RintL ≤ RintM := by
    dsimp [RintL, RintM]
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_right d (Nat.add_le_add_right hLM 3))
      (max rA rB)
  have hRprod : RprodL ≤ RprodM := by
    dsimp [RprodL, RprodM]
    exact Nat.mul_le_mul_left s (Nat.add_le_add hRint hF)
  have hsF : s * FL ≤ s * FM := Nat.mul_le_mul_left s hF
  have hR₁ : R₁L ≤ R₁M := by
    dsimp [R₁L, R₁M]
    exact max_le_max
      (Nat.add_le_add_left hsF rSigma)
      (Nat.add_le_add_right hRprod d)
  have hR₂ : R₂L ≤ R₂M := by
    dsimp [R₂L, R₂M]
    exact max_le_max
      (Nat.add_le_add hR₁ hsF)
      (Nat.add_le_add hRprod (Nat.add_le_add_left hsF d))
  have hscalar : R₂L + s * FL ≤ R₂M + s * FM :=
    Nat.add_le_add hR₂ hsF
  have htwoSF : 2 * s * FL ≤ 2 * s * FM := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hsF
  have hexpansion :
      RprodL + (d + 2 * s * FL) ≤
        RprodM + (d + 2 * s * FM) :=
    Nat.add_le_add hRprod (Nat.add_le_add_left htwoSF d)
  have hodd :
      max (RprodL + (d + 2 * s * FL)) (R₂L + s * FL) ≤
        max (RprodM + (d + 2 * s * FM)) (R₂M + s * FM) :=
    max_le_max hexpansion hscalar
  have hthreeSF : 3 * s * FL ≤ 3 * s * FM := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 3 hsF
  have heven : d + 3 * s * FL ≤ d + 3 * s * FM :=
    Nat.add_le_add_left hthreeSF d
  have hden :
      s * ((rA + FL) + FL) ≤ s * ((rA + FM) + FM) := by
    exact Nat.mul_le_mul_left s
      (Nat.add_le_add (Nat.add_le_add_left hF rA) hF)
  simpa [conversionRefutationOrderOfDegree, FL, FM, RintL, RintM,
    RprodL, RprodM, R₁L, R₁M, R₂L, R₂M] using
    max_le_max (max_le_max hodd heven) hden
/-- Combine the quadratic real-valued package-degree estimate with monotonicity
of the fully expanded natural-number conversion order. -/
theorem conversionRefutationOrder_le_log_sq_ceiling
    {s : ℕ} {H B Bprime : ℝ}
    (hH : 0 ≤ H) (hB : 0 ≤ B) (hBprime : 0 ≤ Bprime)
    (pkg : Package (absorptionScale s H Bprime) B
      (absorptionScale s H Bprime))
    (hell : (pkg.ell : ℝ) ≤
      Real.log (absorptionScale s H Bprime / 4) /
        Real.log (1 / 9) + 1)
    (hJ : (pkg.J : ℝ) ≤
      Real.log
          (Real.sqrt (B + absorptionScale s H Bprime) /
            Real.sqrt (absorptionScale s H Bprime)) /
        Real.log 2)
    (d rSigma rA rB : ℕ) :
    conversionRefutationOrder pkg s d rSigma rA rB ≤
      conversionRefutationOrderOfDegree
        (Nat.ceil
          (packageDegreeConstant B
              (absorptionScaleConstant s Bprime) *
            (1 + Real.log (H + 1)) ^ 2))
        s d rSigma rA rB := by
  rw [conversionRefutationOrder_eq_ofDegree]
  apply conversionRefutationOrderOfDegree_mono
  have hreal := package_degreeBound_le_of_absorptionScale
    hH hB hBprime pkg hell hJ
  have hceil := Nat.le_ceil
    (packageDegreeConstant B (absorptionScaleConstant s Bprime) *
      (1 + Real.log (H + 1)) ^ 2)
  exact_mod_cast hreal.trans hceil


/-- Upgrade a converted refutation from its package-dependent order to the
explicit quadratic logarithmic degree envelope.  This is the form consumed by
the perturbation bridge: no rational-square-root parameter remains in the
truncation order. -/
theorem converted_refutation_mem_log_sq_ceiling
    {s m n : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {H B Bprime : ℝ}
    (hH : 0 ≤ H) (hB : 0 ≤ B) (hBprime : 0 ≤ Bprime)
    (pkg : Package (absorptionScale s H Bprime) B
      (absorptionScale s H Bprime))
    (hell : (pkg.ell : ℝ) ≤
      Real.log (absorptionScale s H Bprime / 4) /
        Real.log (1 / 9) + 1)
    (hJ : (pkg.J : ℝ) ≤
      Real.log
          (Real.sqrt (B + absorptionScale s H Bprime) /
            Real.sqrt (absorptionScale s H Bprime)) /
        Real.log 2)
    (d rSigma rA rB : ℕ)
    (hmem : (-1 : MvPolynomial (Fin n) ℝ) ∈
      GenQuadraticModule g
        (conversionRefutationOrder pkg s d rSigma rA rB)) :
    (-1 : MvPolynomial (Fin n) ℝ) ∈
      GenQuadraticModule g
        (conversionRefutationOrderOfDegree
          (Nat.ceil
            (packageDegreeConstant B (absorptionScaleConstant s Bprime) *
              (1 + Real.log (H + 1)) ^ 2))
          s d rSigma rA rB) :=
  GenQuadraticModule_mono
    (conversionRefutationOrder_le_log_sq_ceiling
      hH hB hBprime pkg hell hJ d rSigma rA rB) hmem


end OptimalConvergenceRates.GeneralArchimedean

end
