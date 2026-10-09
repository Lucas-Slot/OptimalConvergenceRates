/-
  Exponential-log-squared coefficient bounds for the sharp rational
  square-root package.
-/
import OptimalConvergenceRates.GeneralArchimedean.RationalSquareRootCoefficientBounds
import OptimalConvergenceRates.GeneralArchimedean.SharpParameterBounds
import OptimalConvergenceRates.GeneralArchimedean.LogSquareBounds

noncomputable section

namespace OptimalConvergenceRates.GeneralArchimedean
namespace RationalSquareRoot

/-- A fixed upper bound for every dyadic affine coefficient when the
interval endpoint is `B` and the shift is at most one. -/
def sharpDyadicCoefficientBaseBound (B : ℝ) : ℝ :=
  4 + B + Real.sqrt (B + 1)

theorem one_le_sharpDyadicCoefficientBaseBound
    {B : ℝ} (hB : 0 ≤ B) :
    1 ≤ sharpDyadicCoefficientBaseBound B := by
  unfold sharpDyadicCoefficientBaseBound
  have hsqrt : 0 ≤ Real.sqrt (B + 1) := Real.sqrt_nonneg _
  linarith

/-- The logarithmic upper bound on the last dyadic grid point really puts
that point below the prescribed right endpoint. -/
theorem gridPoint_le_sqrt_endpoint
    {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) {J : ℕ}
    (hJ : (J : ℝ) ≤
      Real.log (Real.sqrt (B + δ) / Real.sqrt δ) / Real.log 2) :
    gridPoint δ J ≤ Real.sqrt (B + δ) := by
  have hsqrtδ : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hBδ : 0 < B + δ := add_pos_of_nonneg_of_pos hB hδ
  have hsqrtBδ : 0 < Real.sqrt (B + δ) := Real.sqrt_pos.2 hBδ
  have hratio : 0 < Real.sqrt (B + δ) / Real.sqrt δ :=
    div_pos hsqrtBδ hsqrtδ
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog : Real.log ((2 : ℝ) ^ J) ≤
      Real.log (Real.sqrt (B + δ) / Real.sqrt δ) := by
    rw [Real.log_pow]
    exact (le_div_iff₀ hlog2).mp hJ
  have hpow : (2 : ℝ) ^ J ≤ Real.sqrt (B + δ) / Real.sqrt δ :=
    (Real.log_le_log_iff (pow_pos (by norm_num) J) hratio).mp hlog
  unfold gridPoint
  have hmul := mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg δ)
  calc
    (2 : ℝ) ^ J * Real.sqrt δ =
        Real.sqrt δ * (2 : ℝ) ^ J := mul_comm _ _
    _ ≤ Real.sqrt δ * (Real.sqrt (B + δ) / Real.sqrt δ) := hmul
    _ = Real.sqrt (B + δ) := by field_simp

theorem dyadicCoefficientBase_le_sharp
    {δ B : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B)
    {J : ℕ}
    (hJ : (J : ℝ) ≤
      Real.log (Real.sqrt (B + δ) / Real.sqrt δ) / Real.log 2) :
    dyadicCoefficientBase δ J ≤ sharpDyadicCoefficientBaseBound B := by
  have hgrid := gridPoint_le_sqrt_endpoint hδ hB hJ
  have hgrid0 := gridPoint_nonneg hδ.le J
  have hsum : 0 ≤ B + δ := by positivity
  have hsquare : gridPoint δ J ^ 2 ≤ B + δ := by
    have hprod : 0 ≤
        (Real.sqrt (B + δ) - gridPoint δ J) *
          (Real.sqrt (B + δ) + gridPoint δ J) :=
      mul_nonneg (sub_nonneg.mpr hgrid)
        (add_nonneg (Real.sqrt_nonneg _) hgrid0)
    nlinarith [Real.sq_sqrt hsum]
  have hsqrt : Real.sqrt (B + δ) ≤ Real.sqrt (B + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  unfold dyadicCoefficientBase sharpDyadicCoefficientBaseBound
  linarith

/-- A generic conversion from a logarithmic exponent bound to an
`exp(O(log^2 x))` estimate. -/
theorem pow_mul_pow_le_exp_log_sq
    {C x Q D : ℝ} (hC : 1 ≤ C) (hx : 1 ≤ x)
    (hQ : 1 ≤ Q) (hD : 0 ≤ D) {N : ℕ}
    (hN : (N : ℝ) ≤ D * (1 + Real.log x)) :
    (C * x) ^ (N + 1) * Q ^ (2 * N) ≤
      Real.exp (((D + 1) * (Real.log C + 1) +
        2 * D * Real.log Q) * (1 + Real.log x) ^ 2) := by
  let L : ℝ := 1 + Real.log x
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hL : 1 ≤ L := by
    dsimp [L]
    linarith [Real.log_nonneg hx]
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hlogCx : Real.log (C * x) ≤ (Real.log C + 1) * L := by
    rw [Real.log_mul hCpos.ne' hxpos.ne']
    dsimp [L]
    nlinarith [mul_nonneg hlogC hlogx]
  have hlogCx0 : 0 ≤ Real.log (C * x) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hC hx)
  have hN1 : ((N + 1 : ℕ) : ℝ) ≤ (D + 1) * L := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    dsimp [L] at hN ⊢
    nlinarith
  have hterm1 :
      ((N + 1 : ℕ) : ℝ) * Real.log (C * x) ≤
        (D + 1) * (Real.log C + 1) * L ^ 2 := by
    calc
      ((N + 1 : ℕ) : ℝ) * Real.log (C * x) ≤
          ((D + 1) * L) * ((Real.log C + 1) * L) :=
        mul_le_mul hN1 hlogCx hlogCx0 (by positivity)
      _ = (D + 1) * (Real.log C + 1) * L ^ 2 := by ring
  have hterm2 :
      ((2 * N : ℕ) : ℝ) * Real.log Q ≤
        2 * D * Real.log Q * L ^ 2 := by
    have hN' : ((2 * N : ℕ) : ℝ) ≤ 2 * D * L := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      nlinarith
    calc
      ((2 * N : ℕ) : ℝ) * Real.log Q ≤
          (2 * D * L) * Real.log Q :=
        mul_le_mul_of_nonneg_right hN' hlogQ
      _ ≤ (2 * D * L) * (Real.log Q * L) :=
        mul_le_mul_of_nonneg_left
          (le_mul_of_one_le_right hlogQ hL) (by positivity)
      _ = 2 * D * Real.log Q * L ^ 2 := by ring
  apply (Real.log_le_iff_le_exp (by positivity)).mp
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow]
  dsimp [L] at hterm1 hterm2 ⊢
  nlinarith

end RationalSquareRoot

open RationalSquareRoot RationalSquareRoot.Package

/-- Fixed exponent constant in the coefficient estimate for the sharp
package. -/
def sharpPackageCoefficientExponentConstant
    (s : ℕ) (B Bprime : ℝ) : ℝ :=
  let D := sharpPackageDegreeConstant s B Bprime
  let C₀ := sharpDeltaScaleConstant s Bprime
  let Q₀ := sharpDyadicCoefficientBaseBound B
  (D + 1) * (Real.log C₀ + 1) + 2 * D * Real.log Q₀

/-- Explicit `exp(O(log^2(H+1)))` envelope for the coefficients of the
sharp rational-square-root package. -/
def sharpPackageCoefficientBound
    (s : ℕ) (B Bprime H : ℝ) : ℝ :=
  let E := Real.exp
    (sharpPackageCoefficientExponentConstant s B Bprime *
      (1 + Real.log (H + 1)) ^ 2)
  5 * E ^ 2

theorem RationalSquareRoot.Package.coefficientBound_le_sharpPackageCoefficientBound
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
    pkg.coefficientBound ≤
      sharpPackageCoefficientBound s B Bprime H := by
  let δ := sharpDeltaScale s H Bprime
  let x : ℝ := H + 1
  let C₀ := sharpDeltaScaleConstant s Bprime
  let D := sharpPackageDegreeConstant s B Bprime
  let Q₀ := sharpDyadicCoefficientBaseBound B
  let N : ℕ := 2 * pkg.ell * (pkg.J + 1)
  let L : ℝ := 1 + Real.log x
  let E := Real.exp
    (sharpPackageCoefficientExponentConstant s B Bprime * L ^ 2)
  have hx : 1 ≤ x := by dsimp [x]; linarith
  have hC : 1 ≤ C₀ := by
    dsimp [C₀]
    exact one_le_sharpDeltaScaleConstant hBprime
  have hδ : 0 < δ := by
    dsimp [δ]
    exact sharpDeltaScale_pos hH hBprime
  have hδ1 : δ ≤ 1 :=
    (sharpDeltaScale_le_half hH hBprime).trans (by norm_num)
  have hQ₀ : 1 ≤ Q₀ := by
    dsimp [Q₀]
    exact one_le_sharpDyadicCoefficientBaseBound hB
  have hdegree : (pkg.degreeBound : ℝ) ≤ D * L := by
    simpa [δ, x, D, L] using
      package_degreeBound_le_of_sharpDeltaScale
        hH hB hBprime pkg hell hJ
  have hD : 0 ≤ D := by
    have hprod : 0 ≤ D * L :=
      (Nat.cast_nonneg pkg.degreeBound).trans hdegree
    have hL : 1 ≤ L := by
      dsimp [L, x]
      linarith [Real.log_nonneg hx]
    nlinarith
  have hNdegree : N ≤ pkg.degreeBound := by
    unfold Package.degreeBound
    dsimp [N]
    gcongr
    norm_num
  have hNcast : (N : ℝ) ≤ (pkg.degreeBound : ℝ) := by
    exact_mod_cast hNdegree
  have hN : (N : ℝ) ≤ D * L := hNcast.trans hdegree
  have hbase : dyadicCoefficientBase δ pkg.J ≤ Q₀ := by
    dsimp [δ, Q₀]
    exact dyadicCoefficientBase_le_sharp
      (sharpDeltaScale_pos hH hBprime)
      ((sharpDeltaScale_le_half hH hBprime).trans (by norm_num)) hB hJ
  have hrawRewrite : dyadicRawNorm δ pkg.ell pkg.J =
      (C₀ * x) ^ (N + 1) *
        dyadicCoefficientBase δ pkg.J ^ (2 * N) := by
    dsimp [dyadicRawNorm, N]
    rw [show δ = (C₀ * x)⁻¹ by
      simpa [δ, C₀, x] using
        sharpDeltaScale_eq_constant_mul_inv s H Bprime]
    simp only [inv_pow, inv_inv]
  have hraw : dyadicRawNorm δ pkg.ell pkg.J ≤ E := by
    rw [hrawRewrite]
    calc
      (C₀ * x) ^ (N + 1) *
          dyadicCoefficientBase δ pkg.J ^ (2 * N) ≤
          (C₀ * x) ^ (N + 1) * Q₀ ^ (2 * N) := by
        apply mul_le_mul_of_nonneg_left
        · exact pow_le_pow_left₀
            (zero_le_one.trans
              (one_le_dyadicCoefficientBase hδ.le pkg.J))
            hbase _
        · positivity
      _ ≤ E := by
        simpa [E, L, sharpPackageCoefficientExponentConstant, C₀, D, Q₀]
          using pow_mul_pow_le_exp_log_sq hC hx hQ₀ hD hN
  have hZ0 : 0 ≤ dyadicRawNorm δ pkg.ell pkg.J := by
    unfold dyadicRawNorm
    exact mul_nonneg
      (inv_nonneg.mpr (pow_nonneg hδ.le _))
      (pow_nonneg
        (zero_le_one.trans (one_le_dyadicCoefficientBase hδ.le pkg.J)) _)
  have hEone : 1 ≤ E := by
    apply Real.one_le_exp
    have hlogC : 0 ≤ Real.log C₀ := Real.log_nonneg hC
    have hlogQ : 0 ≤ Real.log Q₀ := Real.log_nonneg hQ₀
    have hK : 0 ≤ sharpPackageCoefficientExponentConstant s B Bprime := by
      dsimp [sharpPackageCoefficientExponentConstant, C₀, D, Q₀]
      exact add_nonneg
        (mul_nonneg (by linarith) (by linarith))
        (mul_nonneg (mul_nonneg (by norm_num) hD) hlogQ)
    exact mul_nonneg hK (sq_nonneg L)
  have hpackage := pkg.coefficientBound_le_dyadicPackageCoefficientBound
    hδ hδ1
  dsimp [dyadicPackageCoefficientBound] at hpackage
  apply hpackage.trans
  dsimp [sharpPackageCoefficientBound]
  change 1 + 2 * dyadicRawNorm δ pkg.ell pkg.J +
      2 * dyadicRawNorm δ pkg.ell pkg.J ^ 2 ≤ 5 * E ^ 2
  have hrawSq : dyadicRawNorm δ pkg.ell pkg.J ^ 2 ≤ E ^ 2 :=
    pow_le_pow_left₀ hZ0 hraw 2
  nlinarith [sq_nonneg E]
/-- Pure exponential-log-squared form of the package coefficient estimate.
The exponent constant is independent of `H` and of the selected package. -/
theorem RationalSquareRoot.Package.coefficientBound_le_logSquareEnvelope
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
    pkg.coefficientBound ≤
      logSquareEnvelope
        (Real.log 6 + 2 *
          sharpPackageCoefficientExponentConstant s B Bprime)
        (H + 1) := by
  let K := sharpPackageCoefficientExponentConstant s B Bprime
  let x : ℝ := H + 1
  let E := logSquareEnvelope K x
  have hx : 1 ≤ x := by dsimp [x]; linarith
  have hpackage :=
    pkg.coefficientBound_le_sharpPackageCoefficientBound
      hH hB hBprime hell hJ
  have hpackage' : pkg.coefficientBound ≤ 5 * E ^ 2 := by
    simpa [sharpPackageCoefficientBound, E, K, x,
      logSquareEnvelope, logSquareScale] using hpackage
  have hfive : (5 : ℝ) ≤ logSquareEnvelope (Real.log 6) x := by
    have heq : Real.log ((5 : ℝ) + 1) = Real.log 6 := by norm_num
    rw [← heq]
    exact le_logSquareEnvelope_log_add_one (by norm_num) hx
  calc
    pkg.coefficientBound ≤ 5 * E ^ 2 := hpackage'
    _ ≤ logSquareEnvelope (Real.log 6) x * E ^ 2 := by
      exact mul_le_mul_of_nonneg_right hfive (sq_nonneg E)
    _ = logSquareEnvelope (Real.log 6) x *
        logSquareEnvelope (2 * K) x := by
      rw [logSquareEnvelope_pow]
      norm_num
    _ = logSquareEnvelope (Real.log 6 + 2 * K) x :=
      logSquareEnvelope_mul _ _ _
    _ = logSquareEnvelope
        (Real.log 6 + 2 *
          sharpPackageCoefficientExponentConstant s B Bprime)
        (H + 1) := rfl

end OptimalConvergenceRates.GeneralArchimedean

end
