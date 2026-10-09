/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Analysis/BoundedUniformSplit.lean

  Reduction of a bounded-base positive-curvature split to the global-slab construction.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.CurvatureParentPatch
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.ScaleCover
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.SplitAtomAssembly
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.ExplicitSplitRootJetBounds
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.RawSquareCoefficientJetBounds
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.ImplicitGraphFiveJet
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.SplitPathJetBounds

open Set
open scoped Topology

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- A tangential cutoff which is one on the half-radius ball and supported in the full
tangential ball of a bounded split input. -/
def boundedSplitTangentialCutoff {n : ℕ} (input : BoundedNormalizedLocalSplitInput n) :
    (Fin n → ℝ) → ℝ :=
  rescaledUnitBump 0 (input.tangentialRadius / 2)

/-- The fixed comparison quadratic has normal curvature exactly `1 / 4`. -/
def boundedSplitComparisonQuadratic {n : ℕ} (z : ℝ × (Fin n → ℝ)) : ℝ :=
  z.1 ^ 2 / 8

/-- Blend the bounded input with a fixed nonnegative quadratic outside its tangential base.
The blend is independent of the normal variable, so it preserves strict normal curvature. -/
def globalizedBoundedSplitFunction {n : ℕ} (input : BoundedNormalizedLocalSplitInput n)
    (z : ℝ × (Fin n → ℝ)) : ℝ :=
  let χ := boundedSplitTangentialCutoff input z.2
  χ * input.function z + (1 - χ) * boundedSplitComparisonQuadratic z

theorem boundedSplitTangentialCutoff_contDiff {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) :
    ContDiff ℝ 6 (boundedSplitTangentialCutoff input) := by
  exact rescaledUnitBump_contDiff 0 (input.tangentialRadius / 2)

theorem boundedSplitTangentialCutoff_mem_Icc {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) (y : Fin n → ℝ) :
    0 ≤ boundedSplitTangentialCutoff input y ∧
      boundedSplitTangentialCutoff input y ≤ 1 := by
  exact rescaledUnitBump_mem_Icc 0 (input.tangentialRadius / 2) y

theorem boundedSplitTangentialCutoff_eq_one {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) {y : Fin n → ℝ}
    (hy : ‖y‖ ≤ input.tangentialRadius / 2) :
    boundedSplitTangentialCutoff input y = 1 := by
  apply rescaledUnitBump_eq_one 0 (div_pos input.tangentialRadius_pos (by norm_num))
  simpa [Metric.mem_closedBall, dist_eq_norm] using hy

theorem norm_lt_tangentialRadius_of_boundedSplitTangentialCutoff_ne_zero {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) {y : Fin n → ℝ}
    (hy : boundedSplitTangentialCutoff input y ≠ 0) :
    ‖y‖ < input.tangentialRadius := by
  have hsupp : y ∈ Function.support (boundedSplitTangentialCutoff input) := by
    simpa [Function.mem_support] using hy
  rw [boundedSplitTangentialCutoff, support_rescaledUnitBump 0
    (div_pos input.tangentialRadius_pos (by norm_num))] at hsupp
  have hnorm : ‖y‖ < 2 * (input.tangentialRadius / 2) := by
    simpa [Metric.mem_ball, dist_eq_norm] using hsupp
  linarith

theorem boundedSplitComparisonQuadratic_contDiff {n : ℕ} :
    ContDiff ℝ 6 (boundedSplitComparisonQuadratic (n := n)) := by
  unfold boundedSplitComparisonQuadratic
  fun_prop

theorem globalizedBoundedSplitFunction_contDiff {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) :
    ContDiff ℝ 6 (globalizedBoundedSplitFunction input) := by
  have hχ : ContDiff ℝ 6
      (fun z : ℝ × (Fin n → ℝ) ↦ boundedSplitTangentialCutoff input z.2) :=
    (boundedSplitTangentialCutoff_contDiff input).comp contDiff_snd
  have hq : ContDiff ℝ 6 (boundedSplitComparisonQuadratic (n := n)) :=
    boundedSplitComparisonQuadratic_contDiff
  exact (hχ.mul input.contDiff).add ((contDiff_const.sub hχ).mul hq)

theorem globalizedBoundedSplitFunction_nonnegative {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) (z : ℝ × (Fin n → ℝ)) :
    0 ≤ globalizedBoundedSplitFunction input z := by
  have hχ := boundedSplitTangentialCutoff_mem_Icc input z.2
  exact add_nonneg (mul_nonneg hχ.1 (input.nonnegative z))
    (mul_nonneg (sub_nonneg.mpr hχ.2) (div_nonneg (sq_nonneg z.1) (by norm_num)))

/-- On the inner tangential ball the globalized function is exactly the original input. -/
theorem globalizedBoundedSplitFunction_eq {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) {z : ℝ × (Fin n → ℝ)}
    (hz : ‖z.2‖ ≤ input.tangentialRadius / 2) :
    globalizedBoundedSplitFunction input z = input.function z := by
  rw [globalizedBoundedSplitFunction, boundedSplitTangentialCutoff_eq_one input hz]
  ring


theorem fderiv_globalizedBoundedSplitFunction_normal {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) (z : ℝ × (Fin n → ℝ)) :
    fderiv ℝ (globalizedBoundedSplitFunction input) z (splitNormalDirection n) =
      boundedSplitTangentialCutoff input z.2 *
          fderiv ℝ input.function z (splitNormalDirection n) +
        (1 - boundedSplitTangentialCutoff input z.2) * (z.1 / 4) := by
  let χ : (ℝ × (Fin n → ℝ)) → ℝ := fun w ↦ boundedSplitTangentialCutoff input w.2
  let q : (ℝ × (Fin n → ℝ)) → ℝ := fun w ↦ w.1 ^ 2 / 8
  have hχcd : ContDiff ℝ 1 χ :=
    (boundedSplitTangentialCutoff_contDiff input).of_le (by norm_num) |>.comp contDiff_snd
  have hχ : DifferentiableAt ℝ χ z := hχcd.differentiable (by norm_num) z
  have hF : DifferentiableAt ℝ input.function z :=
    input.contDiff.differentiable (by norm_num) z
  have hq : DifferentiableAt ℝ q z := by
    dsimp [q]
    fun_prop
  have honeSub : DifferentiableAt ℝ (1 - χ) z := by fun_prop
  rw [show globalizedBoundedSplitFunction input = χ * input.function + (1 - χ) * q by
    funext w
    rfl]
  rw [fderiv_add (hχ.mul hF) (honeSub.mul hq)]
  rw [fderiv_mul hχ hF, fderiv_mul honeSub hq]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Pi.one_apply, Pi.sub_apply]
  have hχnormal : fderiv ℝ χ z (splitNormalDirection n) = 0 := by
    have hcut : HasFDerivAt (boundedSplitTangentialCutoff input)
        (fderiv ℝ (boundedSplitTangentialCutoff input) z.2) z.2 :=
      ((boundedSplitTangentialCutoff_contDiff input).differentiable (by norm_num) z.2).hasFDerivAt
    have hcomp := hcut.comp z (hasFDerivAt_snd (p := z))
    rw [show fderiv ℝ χ z =
        (fderiv ℝ (boundedSplitTangentialCutoff input) z.2).comp
          (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)) by
      exact hcomp.fderiv]
    simp [splitNormalDirection]
  have hqnormal : fderiv ℝ q z (splitNormalDirection n) = z.1 / 4 := by
    have hfst : HasFDerivAt (fun w : ℝ × (Fin n → ℝ) ↦ w.1)
        (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)) z := hasFDerivAt_fst
    have hpow := hfst.pow 2
    have hmul := hpow.mul_const ((8 : ℝ)⁻¹)
    have hmul' : HasFDerivAt q
        (((8 : ℝ)⁻¹) •
          ((2 : ℕ) • z.1 ^ (2 - 1)) •
            ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)) z := by
      simpa [q, div_eq_mul_inv] using hmul
    rw [hmul'.fderiv]
    simp [splitNormalDirection]
    ring
  have honeNormal : fderiv ℝ (1 - χ) z (splitNormalDirection n) = 0 := by
    change fderiv ℝ (fun w ↦ 1 - χ w) z (splitNormalDirection n) = 0
    rw [fderiv_const_sub]
    simp [hχnormal]
  rw [hχnormal, hqnormal, honeNormal]
  simp [χ, q]

theorem fderiv_second_globalizedBoundedSplitFunction_normal {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) (z : ℝ × (Fin n → ℝ)) :
    fderiv ℝ
        (fun w ↦ fderiv ℝ (globalizedBoundedSplitFunction input) w
          (splitNormalDirection n)) z (splitNormalDirection n) =
      boundedSplitTangentialCutoff input z.2 *
          fderiv ℝ (fun w ↦ fderiv ℝ input.function w (splitNormalDirection n)) z
            (splitNormalDirection n) +
        (1 - boundedSplitTangentialCutoff input z.2) * (1 / 4) := by
  let χ : (ℝ × (Fin n → ℝ)) → ℝ := fun w ↦ boundedSplitTangentialCutoff input w.2
  let N : (ℝ × (Fin n → ℝ)) → ℝ :=
    fun w ↦ fderiv ℝ input.function w (splitNormalDirection n)
  let l : (ℝ × (Fin n → ℝ)) → ℝ := fun w ↦ w.1 / 4
  have hχcd : ContDiff ℝ 1 χ :=
    (boundedSplitTangentialCutoff_contDiff input).of_le (by norm_num) |>.comp contDiff_snd
  have hχ : DifferentiableAt ℝ χ z := hχcd.differentiable (by norm_num) z
  have hNcd : ContDiff ℝ 1 N := by
    exact ((input.contDiff.fderiv_right (m := 5) (by norm_num)).clm_apply contDiff_const).of_le
      (by norm_num)
  have hN : DifferentiableAt ℝ N z := hNcd.differentiable (by norm_num) z
  have hl : DifferentiableAt ℝ l z := by
    dsimp [l]
    fun_prop
  have honeSub : DifferentiableAt ℝ (1 - χ) z := by fun_prop
  rw [show (fun w ↦ fderiv ℝ (globalizedBoundedSplitFunction input) w
      (splitNormalDirection n)) = χ * N + (1 - χ) * l by
    funext w
    exact fderiv_globalizedBoundedSplitFunction_normal input w]
  rw [fderiv_add (hχ.mul hN) (honeSub.mul hl)]
  rw [fderiv_mul hχ hN, fderiv_mul honeSub hl]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Pi.one_apply, Pi.sub_apply]
  have hχnormal : fderiv ℝ χ z (splitNormalDirection n) = 0 := by
    have hcut : HasFDerivAt (boundedSplitTangentialCutoff input)
        (fderiv ℝ (boundedSplitTangentialCutoff input) z.2) z.2 :=
      ((boundedSplitTangentialCutoff_contDiff input).differentiable
        (by norm_num) z.2).hasFDerivAt
    have hcomp := hcut.comp z (hasFDerivAt_snd (p := z))
    rw [show fderiv ℝ χ z =
        (fderiv ℝ (boundedSplitTangentialCutoff input) z.2).comp
          (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)) by
      exact hcomp.fderiv]
    simp [splitNormalDirection]
  have hlnormal : fderiv ℝ l z (splitNormalDirection n) = 1 / 4 := by
    have hfst : HasFDerivAt (fun w : ℝ × (Fin n → ℝ) ↦ w.1)
        (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)) z := hasFDerivAt_fst
    have hmul := hfst.mul_const ((4 : ℝ)⁻¹)
    have hmul' : HasFDerivAt l
        (((4 : ℝ)⁻¹) • ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)) z := by
      simpa [l, div_eq_mul_inv] using hmul
    rw [hmul'.fderiv]
    simp [splitNormalDirection]
  have honeNormal : fderiv ℝ (1 - χ) z (splitNormalDirection n) = 0 := by
    change fderiv ℝ (fun w ↦ 1 - χ w) z (splitNormalDirection n) = 0
    rw [fderiv_const_sub]
    simp [hχnormal]
  rw [hχnormal, hlnormal, honeNormal]
  simp [χ, N, l]

noncomputable def globalizedBoundedSplitInput {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) : NormalizedLocalSplitInput n where
  function := globalizedBoundedSplitFunction input
  cylinder := {z | -input.normalRadius ≤ z.1 ∧ z.1 ≤ input.normalRadius}
  tLeft := -input.normalRadius
  tRight := input.normalRadius
  left_lt_right := by linarith [input.normalRadius_pos]
  cylinder_eq := rfl
  nonnegative_on := fun z _ ↦ globalizedBoundedSplitFunction_nonnegative input z
  contDiff := globalizedBoundedSplitFunction_contDiff input
  normal_derivative_left_nonpos := by
    intro y
    rw [fderiv_globalizedBoundedSplitFunction_normal]
    let χ := boundedSplitTangentialCutoff input y
    have hχ := boundedSplitTangentialCutoff_mem_Icc input y
    by_cases hzero : χ = 0
    · simp only [hzero, zero_mul, sub_zero, one_mul, zero_add, ge_iff_le, χ]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr input.normalRadius_pos.le)
        (by norm_num)
    · have hy : ‖y‖ ≤ input.tangentialRadius :=
        (norm_lt_tangentialRadius_of_boundedSplitTangentialCutoff_ne_zero input hzero).le
      have hF := input.normal_derivative_left_nonpos y hy
      dsimp [χ] at hzero hχ ⊢
      have hfirst : boundedSplitTangentialCutoff input y *
          fderiv ℝ input.function (-input.normalRadius, y) (splitNormalDirection n) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hχ.1 hF
      have hsecond : (1 - boundedSplitTangentialCutoff input y) *
          (-input.normalRadius / 4) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hχ.2) (by
          exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr input.normalRadius_pos.le)
            (by norm_num))
      linarith
  normal_derivative_right_nonneg := by
    intro y
    rw [fderiv_globalizedBoundedSplitFunction_normal]
    let χ := boundedSplitTangentialCutoff input y
    have hχ := boundedSplitTangentialCutoff_mem_Icc input y
    by_cases hzero : χ = 0
    · simp only [hzero, zero_mul, sub_zero, one_mul, zero_add, ge_iff_le, χ]
      exact div_nonneg input.normalRadius_pos.le (by norm_num)
    · have hy : ‖y‖ ≤ input.tangentialRadius :=
        (norm_lt_tangentialRadius_of_boundedSplitTangentialCutoff_ne_zero input hzero).le
      have hF := input.normal_derivative_right_nonneg y hy
      dsimp [χ] at hzero hχ ⊢
      have hfirst : 0 ≤ boundedSplitTangentialCutoff input y *
          fderiv ℝ input.function (input.normalRadius, y) (splitNormalDirection n) :=
        mul_nonneg hχ.1 hF
      have hsecond : 0 ≤ (1 - boundedSplitTangentialCutoff input y) *
          (input.normalRadius / 4) :=
        mul_nonneg (sub_nonneg.mpr hχ.2) (div_nonneg input.normalRadius_pos.le (by norm_num))
      linarith
  normal_curvature := by
    intro z hz
    rw [fderiv_second_globalizedBoundedSplitFunction_normal]
    let χ := boundedSplitTangentialCutoff input z.2
    have hχ := boundedSplitTangentialCutoff_mem_Icc input z.2
    by_cases hzero : χ = 0
    · simp [χ, hzero]
    · have hy : ‖z.2‖ ≤ input.tangentialRadius :=
        (norm_lt_tangentialRadius_of_boundedSplitTangentialCutoff_ne_zero input hzero).le
      have ht : |z.1| ≤ input.normalRadius := (abs_le).2 hz
      have hF := input.normal_curvature z ⟨ht, hy⟩
      dsimp [χ] at hzero hχ ⊢
      have hmul : boundedSplitTangentialCutoff input z.2 * (1 / 4 : ℝ) ≤
          boundedSplitTangentialCutoff input z.2 *
            fderiv ℝ (fun w ↦ fderiv ℝ input.function w (splitNormalDirection n)) z
              (splitNormalDirection n) := mul_le_mul_of_nonneg_left hF hχ.1
      nlinarith


structure BoundedUniformLocalSplitData {n : ℕ} (input : BoundedNormalizedLocalSplitInput n) where
  graph : MinimizingGraphData (globalizedBoundedSplitInput input)
  root : (ℝ × (Fin n → ℝ)) → ℝ
  residual : (Fin n → ℝ) → ℝ
  root_contDiff : ContDiff ℝ 4 root
  residual_contDiff : ContDiff ℝ 6 residual
  residual_eq_envelope :
    residual = localSplitEnvelope (globalizedBoundedSplitInput input) graph
  residual_nonnegative : ∀ y, 0 ≤ residual y
  residual_le_center : ∀ y, residual y ≤ input.function (0, y)
  residual_eq_zero_of_tangentialCutoff_eq_zero : ∀ y,
    boundedSplitTangentialCutoff input y = 0 → residual y = 0
  exact_square : ∀ z ∈ boundedSplitCylinder input.normalRadius
      (input.tangentialRadius / 2), input.function z = root z ^ 2 + residual z.2

theorem boundedUniformLocalSplit (n : ℕ) (input : BoundedNormalizedLocalSplitInput n) :
    Nonempty (BoundedUniformLocalSplitData input) := by
  rcases uniformLocalSplit n with ⟨C, hC, hsplit⟩
  let globalInput := globalizedBoundedSplitInput input
  let data := Classical.choice (hsplit globalInput)
  have hresidualNonnegative : ∀ y, 0 ≤ data.residual y := by
    intro y
    rw [data.residual_eq_envelope]
    exact globalInput.nonnegative_on (data.graph.graph y, y) (data.graph.graph_point_mem y)
  refine ⟨{
    graph := data.graph
    root := data.root
    residual := data.residual
    root_contDiff := data.root_contDiff
    residual_contDiff := data.residual_contDiff
    residual_eq_envelope := data.residual_eq_envelope
    residual_nonnegative := hresidualNonnegative
    residual_le_center := ?_
    residual_eq_zero_of_tangentialCutoff_eq_zero := ?_
    exact_square := ?_ }⟩
  · intro y
    have hmem : ((0 : ℝ), y) ∈ globalInput.cylinder := by
      rw [globalInput.cylinder_eq]
      change -input.normalRadius ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ input.normalRadius
      constructor <;> linarith [input.normalRadius_pos]
    have hsquare := data.exact_square (0, y) hmem
    have hleGlobal : data.residual y ≤ globalInput.function (0, y) := by
      nlinarith [sq_nonneg (data.root (0, y))]
    have hglobal : globalInput.function (0, y) =
        boundedSplitTangentialCutoff input y * input.function (0, y) := by
      change globalizedBoundedSplitFunction input (0, y) = _
      simp [globalizedBoundedSplitFunction, boundedSplitComparisonQuadratic]
    rw [hglobal] at hleGlobal
    exact hleGlobal.trans (mul_le_of_le_one_left (input.nonnegative (0, y))
      (boundedSplitTangentialCutoff_mem_Icc input y).2)
  · intro y hy
    have hmem : ((0 : ℝ), y) ∈ globalInput.cylinder := by
      rw [globalInput.cylinder_eq]
      change -input.normalRadius ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ input.normalRadius
      constructor <;> linarith [input.normalRadius_pos]
    have hsquare := data.exact_square (0, y) hmem
    have hzero : globalInput.function (0, y) = 0 := by
      change globalizedBoundedSplitFunction input (0, y) = 0
      simp [globalizedBoundedSplitFunction, boundedSplitComparisonQuadratic, hy]
    rw [hzero] at hsquare
    nlinarith [sq_nonneg (data.root (0, y)), hresidualNonnegative y]
  · intro z hz
    have hzGlobal : z ∈ globalInput.cylinder := by
      rw [globalInput.cylinder_eq]
      exact abs_le.mp hz.1
    have hsquare := data.exact_square z hzGlobal
    change globalizedBoundedSplitFunction input z = _ at hsquare
    rw [globalizedBoundedSplitFunction_eq input hz.2] at hsquare
    exact hsquare


/-- The canonical minimizing graph used by the explicit bounded split. -/
noncomputable def boundedUniformMinimizingGraph {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) :
    MinimizingGraphData (globalizedBoundedSplitInput input) :=
  Classical.choice (uniformMinimizingGraph (globalizedBoundedSplitInput input))

/-- The raw integral Taylor coefficient around the canonical minimizing graph. -/
noncomputable def boundedUniformRawSquareCoefficient {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) (z : ℝ × (Fin n → ℝ)) : ℝ :=
  localRawSquareCoefficientFn (globalizedBoundedSplitInput input)
    (boundedUniformMinimizingGraph input) z

/-- The explicit positive regularization of the raw integral Taylor coefficient. -/
noncomputable def boundedUniformSquareCoefficientFn {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) (z : ℝ × (Fin n → ℝ)) : ℝ :=
  positiveIdentityRegularization (1 / 8) (boundedUniformRawSquareCoefficient input z)

/-- The canonical positive Taylor coefficient around the canonical minimizing graph, constructed
directly from the integral remainder and positive identity regularization. -/
noncomputable def boundedUniformSquareCoefficient {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) :
    LocalSquareCoefficientData (globalizedBoundedSplitInput input)
      (boundedUniformMinimizingGraph input) where
  coefficient := boundedUniformSquareCoefficientFn input
  coefficient_contDiff := by
    exact (positiveIdentityRegularization_contDiff (1 / 8)).comp
      (localRawSquareCoefficientFn_contDiff (globalizedBoundedSplitInput input)
        (boundedUniformMinimizingGraph input))
  coefficient_pos := fun _ ↦ positiveIdentityRegularization_pos (by norm_num)
  factorization := by
    intro z hz
    have heq : boundedUniformSquareCoefficientFn input z =
        boundedUniformRawSquareCoefficient input z := by
      exact positiveIdentityRegularization_eq_self (by norm_num)
        (localSquareCoefficient_lower_of_factorization
          (boundedUniformRawSquareCoefficient input)
          (localRawSquareCoefficientFn_contDiff (globalizedBoundedSplitInput input)
            (boundedUniformMinimizingGraph input)).continuous
          (fun w _ ↦ localRawSquareCoefficientFn_factorization
            (globalizedBoundedSplitInput input) (boundedUniformMinimizingGraph input) w)
          z hz)
    rw [heq]
    exact localRawSquareCoefficientFn_factorization (globalizedBoundedSplitInput input)
      (boundedUniformMinimizingGraph input) z

@[simp] theorem boundedUniformSquareCoefficient_coefficient {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) :
    (boundedUniformSquareCoefficient input).coefficient =
      boundedUniformSquareCoefficientFn input := rfl

@[simp] theorem boundedUniformSquareCoefficientFn_formula {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) (z : ℝ × (Fin n → ℝ)) :
    boundedUniformSquareCoefficientFn input z =
      positiveIdentityRegularization (1 / 8)
        (localRawSquareCoefficientFn (globalizedBoundedSplitInput input)
          (boundedUniformMinimizingGraph input) z) := rfl

/-- The explicit square root of the normal Taylor remainder. -/
noncomputable def explicitBoundedUniformRoot {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) (z : ℝ × (Fin n → ℝ)) : ℝ :=
  (z.1 - (boundedUniformMinimizingGraph input).graph z.2) *
    Real.sqrt ((boundedUniformSquareCoefficient input).coefficient z)

/-- The explicit residual is the restriction of the globalized function to its minimizing
graph. -/
noncomputable def explicitBoundedUniformResidual {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) (y : Fin n → ℝ) : ℝ :=
  localSplitEnvelope (globalizedBoundedSplitInput input)
    (boundedUniformMinimizingGraph input) y

theorem explicitBoundedUniformRoot_contDiff {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) :
    ContDiff ℝ 4 (explicitBoundedUniformRoot input) := by
  let graph := boundedUniformMinimizingGraph input
  let coeff := boundedUniformSquareCoefficient input
  have hlinear : ContDiff ℝ 4 (fun z : ℝ × (Fin n → ℝ) ↦
      z.1 - graph.graph z.2) := by
    exact contDiff_fst.sub ((graph.graph_contDiff.of_le (by norm_num)).comp contDiff_snd)
  have hsqrt : ContDiff ℝ 4 (fun z ↦ Real.sqrt (coeff.coefficient z)) :=
    coeff.coefficient_contDiff.sqrt (fun z ↦ ne_of_gt (coeff.coefficient_pos z))
  change ContDiff ℝ 4 (fun z ↦
    (z.1 - graph.graph z.2) * Real.sqrt (coeff.coefficient z))
  exact hlinear.mul hsqrt

theorem explicitBoundedUniformResidual_contDiff {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) :
    ContDiff ℝ 6 (explicitBoundedUniformResidual input) := by
  exact localSplitEnvelope_contDiff_six (globalizedBoundedSplitInput input)
    (boundedUniformMinimizingGraph input)

/-- Exact Taylor square identity throughout the full normal slab of the globalized input. -/
theorem explicitBoundedUniform_exact_square_global {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n)
    (z : ℝ × (Fin n → ℝ)) (hz : z ∈ (globalizedBoundedSplitInput input).cylinder) :
    (globalizedBoundedSplitInput input).function z =
      explicitBoundedUniformRoot input z ^ 2 + explicitBoundedUniformResidual input z.2 := by
  let graph := boundedUniformMinimizingGraph input
  let coeff := boundedUniformSquareCoefficient input
  have hcoeff0 : 0 ≤ coeff.coefficient z :=
    (coeff.coefficient_lower z hz).trans' (by norm_num)
  have hfac := coeff.factorization z hz
  change (globalizedBoundedSplitInput input).function z =
    ((z.1 - graph.graph z.2) * Real.sqrt (coeff.coefficient z)) ^ 2 +
      localSplitEnvelope (globalizedBoundedSplitInput input) graph z.2
  rw [mul_pow, Real.sq_sqrt hcoeff0]
  nlinarith

theorem explicitBoundedUniformResidual_nonnegative {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) (y : Fin n → ℝ) :
    0 ≤ explicitBoundedUniformResidual input y := by
  exact (globalizedBoundedSplitInput input).nonnegative_on
    ((boundedUniformMinimizingGraph input).graph y, y)
    ((boundedUniformMinimizingGraph input).graph_point_mem y)

theorem explicitBoundedUniformResidual_le_center {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) (y : Fin n → ℝ) :
    explicitBoundedUniformResidual input y ≤ input.function (0, y) := by
  let globalInput := globalizedBoundedSplitInput input
  have hmem : ((0 : ℝ), y) ∈ globalInput.cylinder := by
    rw [globalInput.cylinder_eq]
    change -input.normalRadius ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ input.normalRadius
    constructor <;> linarith [input.normalRadius_pos]
  have hsquare := explicitBoundedUniform_exact_square_global input (0, y) hmem
  have hleGlobal : explicitBoundedUniformResidual input y ≤ globalInput.function (0, y) := by
    nlinarith [sq_nonneg (explicitBoundedUniformRoot input (0, y))]
  have hglobal : globalInput.function (0, y) =
      boundedSplitTangentialCutoff input y * input.function (0, y) := by
    change globalizedBoundedSplitFunction input (0, y) = _
    simp [globalizedBoundedSplitFunction, boundedSplitComparisonQuadratic]
  rw [hglobal] at hleGlobal
  exact hleGlobal.trans (mul_le_of_le_one_left (input.nonnegative (0, y))
    (boundedSplitTangentialCutoff_mem_Icc input y).2)

theorem explicitBoundedUniformResidual_eq_zero_of_tangentialCutoff_eq_zero
    {n : ℕ} (input : BoundedNormalizedLocalSplitInput n) (y : Fin n → ℝ)
    (hy : boundedSplitTangentialCutoff input y = 0) :
    explicitBoundedUniformResidual input y = 0 := by
  let globalInput := globalizedBoundedSplitInput input
  have hmem : ((0 : ℝ), y) ∈ globalInput.cylinder := by
    rw [globalInput.cylinder_eq]
    change -input.normalRadius ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ input.normalRadius
    constructor <;> linarith [input.normalRadius_pos]
  have hsquare := explicitBoundedUniform_exact_square_global input (0, y) hmem
  have hzero : globalInput.function (0, y) = 0 := by
    change globalizedBoundedSplitFunction input (0, y) = 0
    simp [globalizedBoundedSplitFunction, boundedSplitComparisonQuadratic, hy]
  rw [hzero] at hsquare
  nlinarith [sq_nonneg (explicitBoundedUniformRoot input (0, y)),
    explicitBoundedUniformResidual_nonnegative input y]

theorem explicitBoundedUniform_exact_square {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n)
    (z : ℝ × (Fin n → ℝ))
    (hz : z ∈ boundedSplitCylinder input.normalRadius (input.tangentialRadius / 2)) :
    input.function z =
      explicitBoundedUniformRoot input z ^ 2 + explicitBoundedUniformResidual input z.2 := by
  have hzGlobal : z ∈ (globalizedBoundedSplitInput input).cylinder := by
    rw [(globalizedBoundedSplitInput input).cylinder_eq]
    exact abs_le.mp hz.1
  have hsquare := explicitBoundedUniform_exact_square_global input z hzGlobal
  change globalizedBoundedSplitFunction input z = _ at hsquare
  rw [globalizedBoundedSplitFunction_eq input hz.2] at hsquare
  exact hsquare

/-- Fully explicit canonical witness for the bounded local split. -/
noncomputable def explicitBoundedUniformLocalSplitData {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) : BoundedUniformLocalSplitData input where
  graph := boundedUniformMinimizingGraph input
  root := explicitBoundedUniformRoot input
  residual := explicitBoundedUniformResidual input
  root_contDiff := explicitBoundedUniformRoot_contDiff input
  residual_contDiff := explicitBoundedUniformResidual_contDiff input
  residual_eq_envelope := rfl
  residual_nonnegative := explicitBoundedUniformResidual_nonnegative input
  residual_le_center := explicitBoundedUniformResidual_le_center input
  residual_eq_zero_of_tangentialCutoff_eq_zero :=
    explicitBoundedUniformResidual_eq_zero_of_tangentialCutoff_eq_zero input
  exact_square := explicitBoundedUniform_exact_square input

@[simp] theorem explicitBoundedUniformLocalSplitData_graph {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) :
    (explicitBoundedUniformLocalSplitData input).graph = boundedUniformMinimizingGraph input := rfl

@[simp] theorem explicitBoundedUniformLocalSplitData_root {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) :
    (explicitBoundedUniformLocalSplitData input).root = explicitBoundedUniformRoot input := rfl

@[simp] theorem explicitBoundedUniformLocalSplitData_residual {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) :
    (explicitBoundedUniformLocalSplitData input).residual =
      explicitBoundedUniformResidual input := rfl
/-- The canonical choice of the proved bounded exact split. -/
noncomputable def boundedUniformLocalSplitData {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) : BoundedUniformLocalSplitData input :=
  explicitBoundedUniformLocalSplitData input

@[simp] theorem boundedUniformLocalSplitData_graph {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) :
    (boundedUniformLocalSplitData input).graph = boundedUniformMinimizingGraph input := rfl

@[simp] theorem boundedUniformLocalSplitData_root {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) :
    (boundedUniformLocalSplitData input).root = explicitBoundedUniformRoot input := rfl

@[simp] theorem boundedUniformLocalSplitData_residual {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) :
    (boundedUniformLocalSplitData input).residual = explicitBoundedUniformResidual input := rfl

@[simp] theorem boundedUniformLocalSplitData_root_formula {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) :
    (boundedUniformLocalSplitData input).root = fun z ↦
      (z.1 - (boundedUniformMinimizingGraph input).graph z.2) *
        regularizedPositiveSqrt (1 / 8) (boundedUniformRawSquareCoefficient input) z := rfl
/-- Stationarity of the minimizing graph removes its derivative from the first derivative of
the residual envelope. -/
theorem BoundedUniformLocalSplitData.fderiv_residual_eq_tangential
    {n : ℕ} {input : BoundedNormalizedLocalSplitInput n}
    (data : BoundedUniformLocalSplitData input) (y : Fin n → ℝ) :
    fderiv ℝ data.residual y =
      (fderiv ℝ (globalizedBoundedSplitInput input).function
        (data.graph.graph y, y)).comp
          (ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)) := by
  let globalInput := globalizedBoundedSplitInput input
  let G : (Fin n → ℝ) → (ℝ × (Fin n → ℝ)) :=
    fun w ↦ (data.graph.graph w, w)
  let T : (Fin n → ℝ) →L[ℝ] (ℝ × (Fin n → ℝ)) :=
    ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)
  have hG : ContDiff ℝ 5 G := data.graph.graph_contDiff.prodMk contDiff_id
  have hfDiff : DifferentiableAt ℝ globalInput.function (G y) :=
    globalInput.contDiff.differentiable (by norm_num) (G y)
  have hgraphDiff : DifferentiableAt ℝ data.graph.graph y :=
    data.graph.graph_contDiff.differentiable (by norm_num) y
  have hGDiff : DifferentiableAt ℝ G y := hG.differentiable (by norm_num) y
  rw [data.residual_eq_envelope]
  change fderiv ℝ (globalInput.function ∘ G) y = _
  rw [fderiv_comp y hfDiff hGDiff]
  rw [show fderiv ℝ G y = (fderiv ℝ data.graph.graph y).prod
      (ContinuousLinearMap.id ℝ (Fin n → ℝ)) by
    simpa [G, fderiv_id'] using hgraphDiff.fderiv_prodMk differentiableAt_id]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply]
  let L := fderiv ℝ globalInput.function (G y)
  change L (fderiv ℝ data.graph.graph y v, v) = L (T v)
  have hdecomp : (fderiv ℝ data.graph.graph y v, v) =
      (fderiv ℝ data.graph.graph y v, 0) + T v := by
    simp [T]
  rw [hdecomp, map_add]
  have hnormal : L (fderiv ℝ data.graph.graph y v, 0) = 0 := by
    have hsmul : (fderiv ℝ data.graph.graph y v, 0) =
        (fderiv ℝ data.graph.graph y v) • splitNormalDirection n := by
      ext <;> simp [splitNormalDirection]
    rw [hsmul, map_smul, data.graph.first_derivative_zero y]
    simp
  rw [hnormal, zero_add]
theorem BoundedUniformLocalSplitData.residual_compactSupport {n : ℕ}
    {input : BoundedNormalizedLocalSplitInput n} (data : BoundedUniformLocalSplitData input) :
    HasCompactSupport data.residual := by
  have hsubset : Function.support data.residual ⊆
      Function.support (boundedSplitTangentialCutoff input) := by
    intro y hy hcut
    exact hy (data.residual_eq_zero_of_tangentialCutoff_eq_zero y hcut)
  have hr : 0 < input.tangentialRadius / 2 :=
    div_pos input.tangentialRadius_pos (by norm_num)
  have hcompact : HasCompactSupport (boundedSplitTangentialCutoff input) := by
    rw [boundedSplitTangentialCutoff, ← centeredScaleBump_eq_rescaledUnitBump 0 hr]
    exact (centeredScaleBump 0 (input.tangentialRadius / 2) hr).hasCompactSupport
  exact hcompact.mono hsubset
theorem MinimizingGraphData.norm_fderiv_graph_le_of_second_deriv_bound
    {n : ℕ} {input : NormalizedLocalSplitInput n}
    (graph : MinimizingGraphData input) (y : Fin n → ℝ) {M : ℝ}
    (hsecond :
      ‖iteratedFDeriv ℝ 2 input.function (graph.graph y, y)‖ ≤ M) :
    ‖fderiv ℝ graph.graph y‖ ≤ 4 * M := by
  let N : (ℝ × (Fin n → ℝ)) → ℝ := fun z ↦
    fderiv ℝ input.function z (splitNormalDirection n)
  let G : (Fin n → ℝ) → (ℝ × (Fin n → ℝ)) := fun w ↦ (graph.graph w, w)
  let T : (Fin n → ℝ) →L[ℝ] (ℝ × (Fin n → ℝ)) :=
    ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)
  have hN : ContDiff ℝ 5 N := by
    exact (input.contDiff.fderiv_right (m := 5) (by norm_num)).clm_apply contDiff_const
  have hG : ContDiff ℝ 5 G := graph.graph_contDiff.prodMk contDiff_id
  have hgraphDiff : DifferentiableAt ℝ graph.graph y :=
    graph.graph_contDiff.differentiable (by norm_num) y
  have hGDiff : DifferentiableAt ℝ G y := hG.differentiable (by norm_num) y
  have hNdiff : DifferentiableAt ℝ N (G y) := hN.differentiable (by norm_num) (G y)
  have hstationary : N ∘ G = fun _ ↦ 0 := by
    funext w
    exact graph.first_derivative_zero w
  have hstationaryDeriv :
      (fderiv ℝ N (G y)).comp (fderiv ℝ G y) = 0 := by
    have h := congrArg (fun f ↦ fderiv ℝ f y) hstationary
    change fderiv ℝ (N ∘ G) y = fderiv ℝ (fun _ ↦ (0 : ℝ)) y at h
    rw [fderiv_comp y hNdiff hGDiff] at h
    simpa using h
  have hGderiv : fderiv ℝ G y =
      (fderiv ℝ graph.graph y).prod
        (ContinuousLinearMap.id ℝ (Fin n → ℝ)) := by
    simpa [G, fderiv_id'] using hgraphDiff.fderiv_prodMk differentiableAt_id
  have hcurvature : (1 / 4 : ℝ) ≤
      fderiv ℝ N (G y) (splitNormalDirection n) := by
    simpa [N, G] using input.normal_curvature (graph.graph y, y)
      (graph.graph_point_mem y)
  have hHnorm : ‖fderiv ℝ N (G y)‖ ≤
      ‖iteratedFDeriv ℝ 2 input.function (G y)‖ := by
    have h := norm_iteratedFDeriv_clm_apply_const
      (f := fun z ↦ fderiv ℝ input.function z)
      (c := splitNormalDirection n) (x := G y) (n := 1)
      ((input.contDiff.fderiv_right (m := 5) (by norm_num)).contDiffAt)
      (by norm_num : (1 : ℕ) ≤ (5 : WithTop ℕ∞))
    rw [norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv] at h
    simpa [N, splitNormalDirection, Prod.norm_def] using h
  have hTnorm : ‖T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    change ‖((0 : ℝ), v)‖ ≤ 1 * ‖v‖
    simp [Prod.norm_def]
  have hM : 0 ≤ M := (norm_nonneg _).trans hsecond
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) hM)
  intro v
  have hzero : fderiv ℝ N (G y) (fderiv ℝ graph.graph y v, v) = 0 := by
    have happ := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ ↦ L v) hstationaryDeriv
    rw [hGderiv] at happ
    simpa using happ
  have hdecomp : (fderiv ℝ graph.graph y v, v) =
      (fderiv ℝ graph.graph y v) • splitNormalDirection n + T v := by
    ext <;> simp [splitNormalDirection, T]
  have hscalar :
      fderiv ℝ graph.graph y v *
          fderiv ℝ N (G y) (splitNormalDirection n) =
        -fderiv ℝ N (G y) (T v) := by
    rw [hdecomp, map_add, map_smul] at hzero
    simpa [smul_eq_mul] using eq_neg_of_add_eq_zero_left hzero
  have hnormalNonneg : 0 ≤ fderiv ℝ N (G y) (splitNormalDirection n) :=
    (by norm_num : (0 : ℝ) ≤ 1 / 4).trans hcurvature
  have hnormEq : ‖fderiv ℝ graph.graph y v‖ *
      fderiv ℝ N (G y) (splitNormalDirection n) =
        ‖fderiv ℝ N (G y) (T v)‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, ← abs_of_nonneg hnormalNonneg,
      ← abs_mul, hscalar, abs_neg]
  have hpointSecond : ‖iteratedFDeriv ℝ 2 input.function (G y)‖ ≤ M := by
    simpa [G] using hsecond
  have hnormalPart : ‖fderiv ℝ N (G y) (T v)‖ ≤ M * ‖v‖ := by
    calc
      ‖fderiv ℝ N (G y) (T v)‖ ≤ ‖fderiv ℝ N (G y)‖ * ‖T v‖ :=
        (fderiv ℝ N (G y)).le_opNorm (T v)
      _ ≤ ‖iteratedFDeriv ℝ 2 input.function (G y)‖ * (‖T‖ * ‖v‖) := by
        gcongr
        exact T.le_opNorm v
      _ ≤ M * (1 * ‖v‖) := by gcongr
      _ = M * ‖v‖ := by ring
  have hlower : (1 / 4 : ℝ) * ‖fderiv ℝ graph.graph y v‖ ≤
      ‖fderiv ℝ N (G y) (T v)‖ := by
    calc
      (1 / 4 : ℝ) * ‖fderiv ℝ graph.graph y v‖ ≤
          fderiv ℝ N (G y) (splitNormalDirection n) *
            ‖fderiv ℝ graph.graph y v‖ := by gcongr
      _ = ‖fderiv ℝ N (G y) (T v)‖ := by rw [mul_comm, hnormEq]
  nlinarith

/-- The scalar normal derivative of the normal critical equation along a minimizing graph. -/
def minimizingGraphNormalCurvature {n : ℕ} {input : NormalizedLocalSplitInput n}
    (graph : MinimizingGraphData input) (y : Fin n → ℝ) : ℝ :=
  fderiv ℝ (fun z ↦ fderiv ℝ input.function z (splitNormalDirection n))
    (graph.graph y, y) (splitNormalDirection n)

/-- The tangential derivative of the normal critical equation along a minimizing graph. -/
def minimizingGraphNormalTangentialDerivative {n : ℕ}
    {input : NormalizedLocalSplitInput n} (graph : MinimizingGraphData input)
    (y : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  (fderiv ℝ (fun z ↦ fderiv ℝ input.function z (splitNormalDirection n))
    (graph.graph y, y)).comp (ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ))

/-- Quantitative implicit differentiation in the one-dimensional normal variable. -/
theorem MinimizingGraphData.fderiv_graph_eq_normalCurvature_inv_smul
    {n : ℕ} {input : NormalizedLocalSplitInput n}
    (graph : MinimizingGraphData input) (y : Fin n → ℝ) :
    fderiv ℝ graph.graph y =
      (-(minimizingGraphNormalCurvature graph y)⁻¹) •
        minimizingGraphNormalTangentialDerivative graph y := by
  let N : (ℝ × (Fin n → ℝ)) → ℝ := fun z ↦
    fderiv ℝ input.function z (splitNormalDirection n)
  let G : (Fin n → ℝ) → (ℝ × (Fin n → ℝ)) := fun w ↦ (graph.graph w, w)
  let T : (Fin n → ℝ) →L[ℝ] (ℝ × (Fin n → ℝ)) :=
    ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)
  have hN : ContDiff ℝ 5 N := by
    exact (input.contDiff.fderiv_right (m := 5) (by norm_num)).clm_apply contDiff_const
  have hG : ContDiff ℝ 5 G := graph.graph_contDiff.prodMk contDiff_id
  have hgraphDiff : DifferentiableAt ℝ graph.graph y :=
    graph.graph_contDiff.differentiable (by norm_num) y
  have hGDiff : DifferentiableAt ℝ G y := hG.differentiable (by norm_num) y
  have hNdiff : DifferentiableAt ℝ N (G y) := hN.differentiable (by norm_num) (G y)
  have hstationary : N ∘ G = fun _ ↦ 0 := by
    funext w
    exact graph.first_derivative_zero w
  have hstationaryDeriv :
      (fderiv ℝ N (G y)).comp (fderiv ℝ G y) = 0 := by
    have h := congrArg (fun f ↦ fderiv ℝ f y) hstationary
    change fderiv ℝ (N ∘ G) y = fderiv ℝ (fun _ ↦ (0 : ℝ)) y at h
    rw [fderiv_comp y hNdiff hGDiff] at h
    simpa using h
  have hGderiv : fderiv ℝ G y =
      (fderiv ℝ graph.graph y).prod
        (ContinuousLinearMap.id ℝ (Fin n → ℝ)) := by
    simpa [G, fderiv_id'] using hgraphDiff.fderiv_prodMk differentiableAt_id
  have hcurvature : (1 / 4 : ℝ) ≤ minimizingGraphNormalCurvature graph y := by
    exact input.normal_curvature (graph.graph y, y) (graph.graph_point_mem y)
  have hcurvatureNe : minimizingGraphNormalCurvature graph y ≠ 0 :=
    ne_of_gt ((by norm_num : (0 : ℝ) < 1 / 4).trans_le hcurvature)
  ext v
  have hzero : fderiv ℝ N (G y) (fderiv ℝ graph.graph y v, v) = 0 := by
    have happ := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ ↦ L v) hstationaryDeriv
    rw [hGderiv] at happ
    simpa using happ
  have hdecomp : (fderiv ℝ graph.graph y v, v) =
      (fderiv ℝ graph.graph y v) • splitNormalDirection n + T v := by
    ext <;> simp [splitNormalDirection, T]
  rw [hdecomp, map_add, map_smul] at hzero
  have heq : minimizingGraphNormalCurvature graph y * fderiv ℝ graph.graph y v =
      -minimizingGraphNormalTangentialDerivative graph y v := by
    simpa [minimizingGraphNormalCurvature, minimizingGraphNormalTangentialDerivative,
      N, G, T, mul_comm] using eq_neg_of_add_eq_zero_left hzero
  change fderiv ℝ graph.graph y v =
    (-(minimizingGraphNormalCurvature graph y)⁻¹) *
      minimizingGraphNormalTangentialDerivative graph y v
  calc
    fderiv ℝ graph.graph y v =
        (minimizingGraphNormalCurvature graph y)⁻¹ *
          (minimizingGraphNormalCurvature graph y * fderiv ℝ graph.graph y v) := by
      field_simp
    _ = (minimizingGraphNormalCurvature graph y)⁻¹ *
          (-minimizingGraphNormalTangentialDerivative graph y v) := by rw [heq]
    _ = (-(minimizingGraphNormalCurvature graph y)⁻¹) *
          minimizingGraphNormalTangentialDerivative graph y v := by ring

set_option maxHeartbeats 400000 in
-- Differentiating the stationary equation twice requires expensive nested operator-norm bounds.
theorem MinimizingGraphData.norm_fderiv_fderiv_graph_le_of_third_deriv_bound
    {n : ℕ} {input : NormalizedLocalSplitInput n}
    (graph : MinimizingGraphData input) (y : Fin n → ℝ) {A C : ℝ}
    (hsecond : ‖iteratedFDeriv ℝ 2 input.function (graph.graph y, y)‖ ≤ A)
    (hthird : ‖iteratedFDeriv ℝ 3 input.function (graph.graph y, y)‖ ≤ C) :
    ‖fderiv ℝ (fderiv ℝ graph.graph) y‖ ≤
      4 * C * (max (4 * A) 1) ^ 2 := by
  let N : (ℝ × (Fin n → ℝ)) → ℝ := fun z ↦
    fderiv ℝ input.function z (splitNormalDirection n)
  let G : (Fin n → ℝ) → (ℝ × (Fin n → ℝ)) := fun w ↦ (graph.graph w, w)
  have hN : ContDiff ℝ 5 N := by
    exact (input.contDiff.fderiv_right (m := 5) (by norm_num)).clm_apply contDiff_const
  have hG : ContDiff ℝ 5 G := graph.graph_contDiff.prodMk contDiff_id
  have hgraphFirst := graph.norm_fderiv_graph_le_of_second_deriv_bound y hsecond
  have hGderiv (w : Fin n → ℝ) : fderiv ℝ G w =
      (fderiv ℝ graph.graph w).prod
        (ContinuousLinearMap.id ℝ (Fin n → ℝ)) := by
    have hgdiff : DifferentiableAt ℝ graph.graph w :=
      graph.graph_contDiff.differentiable (by norm_num) w
    simpa [G, fderiv_id'] using hgdiff.fderiv_prodMk differentiableAt_id
  have hGnorm : ‖fderiv ℝ G y‖ ≤ max (4 * A) 1 := by
    rw [hGderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (le_max_right _ _))
    intro v
    change ‖(fderiv ℝ graph.graph y v, v)‖ ≤ max (4 * A) 1 * ‖v‖
    rw [Prod.norm_def]
    apply max_le
    · calc
        ‖fderiv ℝ graph.graph y v‖ ≤ ‖fderiv ℝ graph.graph y‖ * ‖v‖ :=
          (fderiv ℝ graph.graph y).le_opNorm v
        _ ≤ (4 * A) * ‖v‖ := mul_le_mul_of_nonneg_right hgraphFirst (norm_nonneg v)
        _ ≤ max (4 * A) 1 * ‖v‖ := by gcongr; exact le_max_left _ _
    · calc
        ‖v‖ = 1 * ‖v‖ := by ring
        _ ≤ max (4 * A) 1 * ‖v‖ := by gcongr; exact le_max_right _ _
  have hD2N : ‖fderiv ℝ (fderiv ℝ N) (G y)‖ ≤
      ‖iteratedFDeriv ℝ 3 input.function (G y)‖ := by
    have happ := norm_iteratedFDeriv_clm_apply_const
      (f := fun z ↦ fderiv ℝ input.function z)
      (c := splitNormalDirection n) (x := G y) (n := 2)
      ((input.contDiff.fderiv_right (m := 5) (by norm_num)).contDiffAt)
      (by norm_num : (2 : ℕ) ≤ (5 : WithTop ℕ∞))
    calc
      ‖fderiv ℝ (fderiv ℝ N) (G y)‖ =
          ‖iteratedFDeriv ℝ 2 N (G y)‖ := by
        rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
      _ ≤ ‖splitNormalDirection n‖ *
          ‖iteratedFDeriv ℝ 2 (fderiv ℝ input.function) (G y)‖ := happ
      _ = ‖iteratedFDeriv ℝ 3 input.function (G y)‖ := by
        rw [norm_iteratedFDeriv_fderiv]
        simp [splitNormalDirection, Prod.norm_def]
  have hthirdPoint : ‖iteratedFDeriv ℝ 3 input.function (G y)‖ ≤ C := by
    simpa [G] using hthird
  have hcurvature : (1 / 4 : ℝ) ≤
      fderiv ℝ N (G y) (splitNormalDirection n) := by
    simpa [N, G] using input.normal_curvature (graph.graph y, y)
      (graph.graph_point_mem y)
  have hnormalNonneg : 0 ≤ fderiv ℝ N (G y) (splitNormalDirection n) :=
    (by norm_num : (0 : ℝ) ≤ 1 / 4).trans hcurvature
  have hstationary : N ∘ G = fun _ ↦ 0 := by
    funext w
    exact graph.first_derivative_zero w
  have hfirstStationary :
      (fun w ↦ (fderiv ℝ N (G w)).comp (fderiv ℝ G w)) = fun _ ↦ 0 := by
    funext w
    have h := congrArg (fun f ↦ fderiv ℝ f w) hstationary
    change fderiv ℝ (N ∘ G) w = fderiv ℝ (fun _ ↦ (0 : ℝ)) w at h
    rw [fderiv_comp w (hN.differentiable (by norm_num) (G w))
      (hG.differentiable (by norm_num) w)] at h
    simpa using h
  let K := fderiv ℝ (fderiv ℝ graph.graph) y
  have hC : 0 ≤ C := (norm_nonneg _).trans hthird
  have hboundNonneg : 0 ≤ 4 * C * (max (4 * A) 1) ^ 2 := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hboundNonneg
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hboundNonneg (norm_nonneg u))
  intro v
  let c : (Fin n → ℝ) → ((ℝ × (Fin n → ℝ)) →L[ℝ] ℝ) :=
    fun w ↦ fderiv ℝ N (G w)
  let q : (Fin n → ℝ) → (ℝ × (Fin n → ℝ)) :=
    fun w ↦ fderiv ℝ G w v
  let S : (Fin n → ℝ) → ℝ := fun w ↦ c w (q w)
  have hcDiff : DifferentiableAt ℝ c y := by
    exact ((hN.fderiv_right (m := 4) (by norm_num)).differentiable
      (by norm_num) (G y)).comp y (hG.differentiable (by norm_num) y)
  have hqDiff : DifferentiableAt ℝ q y := by
    exact ((hG.fderiv_right (m := 4) (by norm_num)).differentiable
      (by norm_num) y).clm_apply (differentiableAt_const (c := v))
  have hSzero : S = fun _ ↦ 0 := by
    funext w
    have hw := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ ↦ L v)
      (congrFun hfirstStationary w)
    simpa [S, c, q] using hw
  have hzeroDeriv : fderiv ℝ S y = 0 := by
    have h := congrArg (fun f ↦ fderiv ℝ f y) hSzero
    change fderiv ℝ S y = fderiv ℝ (fun _ ↦ (0 : ℝ)) y at h
    simpa using h
  have hproductDeriv : fderiv ℝ S y =
      (c y).comp (fderiv ℝ q y) + (fderiv ℝ c y).flip (q y) := by
    exact fderiv_clm_apply hcDiff hqDiff
  have hcDeriv : fderiv ℝ c y =
      (fderiv ℝ (fderiv ℝ N) (G y)).comp (fderiv ℝ G y) := by
    exact fderiv_comp y
      ((hN.fderiv_right (m := 4) (by norm_num)).differentiable (by norm_num) (G y))
      (hG.differentiable (by norm_num) y)
  have hqDeriv : fderiv ℝ q y u =
      (fderiv ℝ (fderiv ℝ graph.graph) y u v, 0) := by
    have hqEq : q = fun w ↦ (fderiv ℝ graph.graph w v, v) := by
      funext w
      rw [show q w = fderiv ℝ G w v by rfl, hGderiv]
      simp
    have h := congrArg (fun f ↦ fderiv ℝ f y) hqEq
    change fderiv ℝ q y = fderiv ℝ (fun w ↦ (fderiv ℝ graph.graph w v, v)) y at h
    have hfirstDiff : DifferentiableAt ℝ (fun w ↦ fderiv ℝ graph.graph w v) y :=
      ((graph.graph_contDiff.fderiv_right (m := 4) (by norm_num)).differentiable
        (by norm_num) y).clm_apply (differentiableAt_const (c := v))
    rw [show fderiv ℝ (fun w ↦ (fderiv ℝ graph.graph w v, v)) y =
        (fderiv ℝ (fun w ↦ fderiv ℝ graph.graph w v) y).prod 0 by
      simpa using hfirstDiff.fderiv_prodMk (differentiableAt_const (c := v))] at h
    have happ := congrArg
      (fun L : (Fin n → ℝ) →L[ℝ] (ℝ × (Fin n → ℝ)) ↦ L u) h
    have hscalar := fderiv_clm_apply
      ((graph.graph_contDiff.fderiv_right (m := 4) (by norm_num)).differentiable
        (by norm_num) y) (differentiableAt_const (c := v))
    have hscalarApply := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ ↦ L u) hscalar
    simpa [q] using happ.trans (by
      simpa using congrArg (fun a ↦ (a, (0 : Fin n → ℝ))) hscalarApply)
  have hqValue : q y = fderiv ℝ G y v := rfl
  have heq0 :
      fderiv ℝ N (G y) (fderiv ℝ (fderiv ℝ graph.graph) y u v, 0) +
        fderiv ℝ (fderiv ℝ N) (G y) (fderiv ℝ G y u)
          (fderiv ℝ G y v) = 0 := by
    have hmap :
        (c y).comp (fderiv ℝ q y) + (fderiv ℝ c y).flip (q y) = 0 := by
      rw [← hproductDeriv, hzeroDeriv]
    have happ := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ ↦ L u) hmap
    rw [hcDeriv] at happ
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply] at happ
    rw [hqDeriv, hqValue] at happ
    exact happ
  have hnormalTerm :
      fderiv ℝ N (G y) (fderiv ℝ (fderiv ℝ graph.graph) y u v, 0) =
        fderiv ℝ (fderiv ℝ graph.graph) y u v *
          fderiv ℝ N (G y) (splitNormalDirection n) := by
    have hv : (fderiv ℝ (fderiv ℝ graph.graph) y u v, 0) =
        fderiv ℝ (fderiv ℝ graph.graph) y u v • splitNormalDirection n := by
      ext <;> simp [splitNormalDirection]
    rw [hv, map_smul]
    simp [smul_eq_mul]
  have hscalar :
      fderiv ℝ (fderiv ℝ graph.graph) y u v *
          fderiv ℝ N (G y) (splitNormalDirection n) =
        -fderiv ℝ (fderiv ℝ N) (G y) (fderiv ℝ G y u)
          (fderiv ℝ G y v) := by
    rw [hnormalTerm] at heq0
    linarith
  have hnormEq :
      ‖fderiv ℝ (fderiv ℝ graph.graph) y u v‖ *
          fderiv ℝ N (G y) (splitNormalDirection n) =
        ‖fderiv ℝ (fderiv ℝ N) (G y) (fderiv ℝ G y u)
          (fderiv ℝ G y v)‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, ← abs_of_nonneg hnormalNonneg,
      ← abs_mul, hscalar, abs_neg]
  have hrhs :
      ‖fderiv ℝ (fderiv ℝ N) (G y) (fderiv ℝ G y u)
          (fderiv ℝ G y v)‖ ≤
        C * (max (4 * A) 1) ^ 2 * ‖u‖ * ‖v‖ := by
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ N) (G y) (fderiv ℝ G y u)‖ *
          ‖fderiv ℝ G y v‖ :=
        (fderiv ℝ (fderiv ℝ N) (G y) (fderiv ℝ G y u)).le_opNorm _
      _ ≤ (‖fderiv ℝ (fderiv ℝ N) (G y)‖ * ‖fderiv ℝ G y u‖) *
          ‖fderiv ℝ G y v‖ := by
        gcongr
        exact (fderiv ℝ (fderiv ℝ N) (G y)).le_opNorm _
      _ ≤ C * (max (4 * A) 1 * ‖u‖) * (max (4 * A) 1 * ‖v‖) := by
        gcongr
        · exact hD2N.trans hthirdPoint
        · exact (fderiv ℝ G y).le_opNorm u |>.trans
            (mul_le_mul_of_nonneg_right hGnorm (norm_nonneg u))
        · exact (fderiv ℝ G y).le_opNorm v |>.trans
            (mul_le_mul_of_nonneg_right hGnorm (norm_nonneg v))
      _ = C * (max (4 * A) 1) ^ 2 * ‖u‖ * ‖v‖ := by ring
  have hlower : (1 / 4 : ℝ) *
      ‖fderiv ℝ (fderiv ℝ graph.graph) y u v‖ ≤
        ‖fderiv ℝ (fderiv ℝ N) (G y) (fderiv ℝ G y u)
          (fderiv ℝ G y v)‖ := by
    calc
      (1 / 4 : ℝ) * ‖fderiv ℝ (fderiv ℝ graph.graph) y u v‖ ≤
          fderiv ℝ N (G y) (splitNormalDirection n) *
            ‖fderiv ℝ (fderiv ℝ graph.graph) y u v‖ := by gcongr
      _ = _ := by rw [mul_comm, hnormEq]
  nlinarith

/-- Iterated-derivative form of the quantitative graph Hessian estimate. -/
theorem MinimizingGraphData.norm_iteratedFDeriv_two_graph_le_of_third_deriv_bound
    {n : ℕ} {input : NormalizedLocalSplitInput n}
    (graph : MinimizingGraphData input) (y : Fin n → ℝ) {A C : ℝ}
    (hsecond : ‖iteratedFDeriv ℝ 2 input.function (graph.graph y, y)‖ ≤ A)
    (hthird : ‖iteratedFDeriv ℝ 3 input.function (graph.graph y, y)‖ ≤ C) :
    ‖iteratedFDeriv ℝ 2 graph.graph y‖ ≤ 4 * C * (max (4 * A) 1) ^ 2 := by
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
  exact graph.norm_fderiv_fderiv_graph_le_of_third_deriv_bound y hsecond hthird
/-- The Hessian bound on the globalized input controls the residual Hessian on the bounded
tangential base. -/
theorem BoundedUniformLocalSplitData.norm_iteratedFDeriv_two_residual_le
    {n : ℕ} {input : BoundedNormalizedLocalSplitInput n}
    (data : BoundedUniformLocalSplitData input) {A : ℝ} (hA : 0 ≤ A)
    (hsecond : ∀ z ∈ boundedSplitCylinder input.normalRadius input.tangentialRadius,
      ‖iteratedFDeriv ℝ 2 (globalizedBoundedSplitFunction input) z‖ ≤ A)
    {y : Fin n → ℝ} (hy : ‖y‖ ≤ input.tangentialRadius) :
    ‖iteratedFDeriv ℝ 2 data.residual y‖ ≤ A * max (4 * A) 1 := by
  let F := (globalizedBoundedSplitInput input).function
  let G : (Fin n → ℝ) → (ℝ × (Fin n → ℝ)) :=
    fun w ↦ (data.graph.graph w, w)
  let T : (Fin n → ℝ) →L[ℝ] (ℝ × (Fin n → ℝ)) :=
    ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)
  let P : (((ℝ × (Fin n → ℝ)) →L[ℝ] ℝ) →L[ℝ]
      ((Fin n → ℝ) →L[ℝ] ℝ)) :=
    (ContinuousLinearMap.compL ℝ (Fin n → ℝ)
      (ℝ × (Fin n → ℝ)) ℝ).flip T
  let R : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] ℝ) :=
    fun w ↦ P (fderiv ℝ F (G w))
  have hgraphPoint := data.graph.graph_point_mem y
  have hnormal : |data.graph.graph y| ≤ input.normalRadius := by
    rw [(globalizedBoundedSplitInput input).cylinder_eq] at hgraphPoint
    exact abs_le.mpr hgraphPoint
  have hpoint : (data.graph.graph y, y) ∈
      boundedSplitCylinder input.normalRadius input.tangentialRadius := ⟨hnormal, hy⟩
  have hsecondPoint :
      ‖iteratedFDeriv ℝ 2 F (G y)‖ ≤ A := by
    simpa [F, G] using hsecond (data.graph.graph y, y) hpoint
  have hgraphBound : ‖fderiv ℝ data.graph.graph y‖ ≤ 4 * A :=
    data.graph.norm_fderiv_graph_le_of_second_deriv_bound y hsecondPoint
  have hgraphDiff : DifferentiableAt ℝ data.graph.graph y :=
    data.graph.graph_contDiff.differentiable (by norm_num) y
  have hGDiff : DifferentiableAt ℝ G y :=
    (data.graph.graph_contDiff.prodMk contDiff_id).differentiable (by norm_num) y
  have hGderiv : fderiv ℝ G y =
      (fderiv ℝ data.graph.graph y).prod
        (ContinuousLinearMap.id ℝ (Fin n → ℝ)) := by
    simpa [G, fderiv_id'] using hgraphDiff.fderiv_prodMk differentiableAt_id
  have hGnorm : ‖fderiv ℝ G y‖ ≤ max (4 * A) 1 := by
    rw [hGderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (le_max_right _ _))
    intro v
    change ‖(fderiv ℝ data.graph.graph y v, v)‖ ≤ max (4 * A) 1 * ‖v‖
    rw [Prod.norm_def]
    apply max_le
    · calc
        ‖fderiv ℝ data.graph.graph y v‖ ≤
            ‖fderiv ℝ data.graph.graph y‖ * ‖v‖ :=
          (fderiv ℝ data.graph.graph y).le_opNorm v
        _ ≤ (4 * A) * ‖v‖ := mul_le_mul_of_nonneg_right hgraphBound (norm_nonneg v)
        _ ≤ max (4 * A) 1 * ‖v‖ := by gcongr; exact le_max_left _ _
    · calc
        ‖v‖ = 1 * ‖v‖ := by ring
        _ ≤ max (4 * A) 1 * ‖v‖ := by gcongr; exact le_max_right _ _
  have hTnorm : ‖T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    change ‖((0 : ℝ), v)‖ ≤ 1 * ‖v‖
    simp [Prod.norm_def]
  have hPnorm : ‖P‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro L
    change ‖L.comp T‖ ≤ 1 * ‖L‖
    calc
      ‖L.comp T‖ ≤ ‖L‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le L T
      _ ≤ ‖L‖ * 1 := mul_le_mul_of_nonneg_left hTnorm (norm_nonneg L)
      _ = 1 * ‖L‖ := by ring
  have hFderivDiff : DifferentiableAt ℝ (fderiv ℝ F) (G y) := by
    exact ((globalizedBoundedSplitInput input).contDiff.fderiv_right
      (m := 5) (by norm_num)).differentiable (by norm_num) (G y)
  have hRderiv : fderiv ℝ R y =
      P.comp ((fderiv ℝ (fderiv ℝ F) (G y)).comp (fderiv ℝ G y)) := by
    have hinner := hFderivDiff.hasFDerivAt.comp y hGDiff.hasFDerivAt
    simpa [R, Function.comp_def] using (P.hasFDerivAt.comp y hinner).fderiv
  have hresidualFirst : fderiv ℝ data.residual = R := by
    funext w
    simpa [R, P, F, G, T] using data.fderiv_residual_eq_tangential w
  have hresidualSecond : fderiv ℝ (fderiv ℝ data.residual) y =
      P.comp ((fderiv ℝ (fderiv ℝ F) (G y)).comp (fderiv ℝ G y)) := by
    rw [hresidualFirst, hRderiv]
  have hHnorm : ‖fderiv ℝ (fderiv ℝ F) (G y)‖ =
      ‖iteratedFDeriv ℝ 2 F (G y)‖ := by
    rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one,
    hresidualSecond]
  calc
    ‖P.comp ((fderiv ℝ (fderiv ℝ F) (G y)).comp (fderiv ℝ G y))‖ ≤
        ‖P‖ * ‖(fderiv ℝ (fderiv ℝ F) (G y)).comp (fderiv ℝ G y)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖fderiv ℝ (fderiv ℝ F) (G y)‖ * ‖fderiv ℝ G y‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (A * max (4 * A) 1) := by rw [hHnorm]; gcongr
    _ = A * max (4 * A) 1 := one_mul _

/-- The same Hessian estimate is global because the residual is supported in the bounded
tangential base. -/
theorem BoundedUniformLocalSplitData.norm_iteratedFDeriv_two_residual_le_global
    {n : ℕ} {input : BoundedNormalizedLocalSplitInput n}
    (data : BoundedUniformLocalSplitData input) {A : ℝ} (hA : 0 ≤ A)
    (hsecond : ∀ z ∈ boundedSplitCylinder input.normalRadius input.tangentialRadius,
      ‖iteratedFDeriv ℝ 2 (globalizedBoundedSplitFunction input) z‖ ≤ A)
    (y : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ 2 data.residual y‖ ≤ A * max (4 * A) 1 := by
  by_cases hy : ‖y‖ ≤ input.tangentialRadius
  · exact data.norm_iteratedFDeriv_two_residual_le hA hsecond hy
  · have hresidualSupport : Function.support data.residual ⊆
        Function.support (boundedSplitTangentialCutoff input) := by
      intro w hw hcut
      exact hw (data.residual_eq_zero_of_tangentialCutoff_eq_zero w hcut)
    have hcutoffSupport : Function.support (boundedSplitTangentialCutoff input) =
        Metric.ball (0 : Fin n → ℝ) input.tangentialRadius := by
      rw [boundedSplitTangentialCutoff,
        support_rescaledUnitBump 0 (div_pos input.tangentialRadius_pos (by norm_num))]
      congr 1
      ring
    have hresidualTopologicalSupport : tsupport data.residual ⊆
        Metric.closedBall (0 : Fin n → ℝ) input.tangentialRadius := by
      apply closure_minimal
      · intro w hw
        exact Metric.ball_subset_closedBall (hcutoffSupport ▸ hresidualSupport hw)
      · exact Metric.isClosed_closedBall
    have hyBall : y ∉ Metric.closedBall (0 : Fin n → ℝ) input.tangentialRadius := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hy
    have hyTopological : y ∉ tsupport data.residual :=
      fun hmem ↦ hyBall (hresidualTopologicalSupport hmem)
    have hyDeriv : y ∉ Function.support (iteratedFDeriv ℝ 2 data.residual) :=
      fun hmem ↦ hyTopological (support_iteratedFDeriv_subset 2 hmem)
    have hzero : iteratedFDeriv ℝ 2 data.residual y = 0 := by
      simpa [Function.mem_support] using hyDeriv
    rw [hzero, norm_zero]
    positivity
def boundedSplitResidualCutoff {n : ℕ} (input : BoundedNormalizedLocalSplitInput n) :
    (Fin n → ℝ) → ℝ :=
  rescaledUnitBump 0 (input.tangentialRadius / 4)

theorem boundedSplitResidualCutoff_contDiff {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) :
    ContDiff ℝ 6 (boundedSplitResidualCutoff input) := by
  exact rescaledUnitBump_contDiff 0 (input.tangentialRadius / 4)

theorem boundedSplitResidualCutoff_compactSupport {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) :
    HasCompactSupport (boundedSplitResidualCutoff input) := by
  have hr : 0 < input.tangentialRadius / 4 := div_pos input.tangentialRadius_pos (by norm_num)
  rw [boundedSplitResidualCutoff, ← centeredScaleBump_eq_rescaledUnitBump 0 hr]
  exact (centeredScaleBump 0 (input.tangentialRadius / 4) hr).hasCompactSupport

theorem boundedSplitResidualCutoff_support {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) :
    Function.support (boundedSplitResidualCutoff input) =
      Metric.ball 0 (input.tangentialRadius / 2) := by
  rw [boundedSplitResidualCutoff, support_rescaledUnitBump 0
    (div_pos input.tangentialRadius_pos (by norm_num))]
  rw [show 2 * (input.tangentialRadius / 4) = input.tangentialRadius / 2 by ring]

theorem boundedSplitResidualCutoff_eq_one {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) {y : Fin n → ℝ}
    (hy : ‖y‖ ≤ input.tangentialRadius / 4) :
    boundedSplitResidualCutoff input y = 1 := by
  apply rescaledUnitBump_eq_one 0 (div_pos input.tangentialRadius_pos (by norm_num))
  simpa [Metric.mem_closedBall, dist_eq_norm] using hy

theorem boundedSplitResidualCutoff_mem_Icc {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) (y : Fin n → ℝ) :
    0 ≤ boundedSplitResidualCutoff input y ∧ boundedSplitResidualCutoff input y ≤ 1 := by
  exact rescaledUnitBump_mem_Icc 0 (input.tangentialRadius / 4) y

theorem exists_boundedSplitResidualCutoff_deriv_bound {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ j, j ≤ 6 → ∀ y,
      ‖iteratedFDeriv ℝ j (boundedSplitResidualCutoff input) y‖ ≤ A := by
  obtain ⟨A, hA, hunit⟩ := unitScaleBump_uniform_deriv_bound n
  let r := input.tangentialRadius / 4
  have hr : 0 < r := div_pos input.tangentialRadius_pos (by norm_num)
  let M : ℕ → ℝ := fun j ↦ A / r ^ j
  let Aout := max (((Finset.range 7).image M).max' (by simp)) 0
  refine ⟨Aout, le_max_right _ _, ?_⟩
  intro j hj y
  have hscaled :
      ‖iteratedFDeriv ℝ j (boundedSplitResidualCutoff input) y‖ * r ^ j ≤ A := by
    simpa [boundedSplitResidualCutoff, r] using
      rescaledUnitBump_scaled_deriv_bound hunit 0 hr j hj y
  have hdiv : ‖iteratedFDeriv ℝ j (boundedSplitResidualCutoff input) y‖ ≤ M j := by
    dsimp [M]
    exact (le_div_iff₀ (pow_pos hr j)).2 hscaled
  exact hdiv.trans ((Finset.le_max' ((Finset.range 7).image M) (M j)
    (Finset.mem_image_of_mem M (by simpa using Nat.lt_succ_of_le hj))).trans
      (le_max_left _ _))
theorem exists_global_iteratedFDeriv_bound_of_compactSupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} {f : E → ℝ} (hf : ContDiff ℝ m f) (hcompact : HasCompactSupport f) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ j, j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A := by
  have hbound (j : ℕ) (hj : j ≤ m) :
      ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ M := by
    have hsmooth : ContDiff ℝ j f := hf.of_le (by exact_mod_cast hj)
    have hbdd : BddAbove (Set.range fun x ↦ ‖iteratedFDeriv ℝ j f x‖) := by
      apply (hsmooth.continuous_iteratedFDeriv (by exact_mod_cast le_rfl)).norm
        |>.bddAbove_range_of_hasCompactSupport
      apply HasCompactSupport.comp_left _ norm_zero
      exact hcompact.iteratedFDeriv j
    rcases hbdd with ⟨M, hM⟩
    exact ⟨M, fun x ↦ hM (Set.mem_range_self x)⟩
  let M : ℕ → ℝ := fun j ↦ if hj : j ≤ m then Classical.choose (hbound j hj) else 0
  have hM : ∀ j, j ≤ m → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ M j := by
    intro j hj x
    dsimp only [M]
    rw [dif_pos hj]
    exact Classical.choose_spec (hbound j hj) x
  let A := max (((Finset.range (m + 1)).image M).max' (by simp)) 0
  refine ⟨A, le_max_right _ _, ?_⟩
  intro j hj x
  exact (hM j hj x).trans <| (Finset.le_max' ((Finset.range (m + 1)).image M) (M j)
    (Finset.mem_image_of_mem M (by simpa using Nat.lt_succ_of_le hj))).trans
      (le_max_left _ _)

theorem exists_scaled_global_iteratedFDeriv_bound_of_compactSupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} {f : E → ℝ} (hf : ContDiff ℝ m f) (hcompact : HasCompactSupport f)
    {r : ℝ} (hr : 0 < r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j, j ≤ m → ∀ x,
      ‖iteratedFDeriv ℝ j f x‖ * r ^ j ≤ M * r ^ 2 := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_global_iteratedFDeriv_bound_of_compactSupport hf hcompact
  let T : ℕ → ℝ := fun j ↦ A * r ^ j / r ^ 2
  let M := max (((Finset.range (m + 1)).image T).max' (by simp)) 0
  refine ⟨M, le_max_right _ _, ?_⟩
  intro j hj x
  have hbase : ‖iteratedFDeriv ℝ j f x‖ * r ^ j ≤ A * r ^ j :=
    mul_le_mul_of_nonneg_right (hbound j hj x) (pow_nonneg hr.le j)
  have hT : A * r ^ j = T j * r ^ 2 := by
    dsimp [T]
    field_simp [hr.ne']
  have hTM : T j ≤ M :=
    (Finset.le_max' ((Finset.range (m + 1)).image T) (T j)
      (Finset.mem_image_of_mem T (by simpa using Nat.lt_succ_of_le hj))).trans
        (le_max_left _ _)
  calc
    ‖iteratedFDeriv ℝ j f x‖ * r ^ j ≤ A * r ^ j := hbase
    _ = T j * r ^ 2 := hT
    _ ≤ M * r ^ 2 := mul_le_mul_of_nonneg_right hTM (sq_nonneg r)

theorem exists_uniform_boundedSplitTangentialCutoff_first_deriv_bound
    (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (input : BoundedNormalizedLocalSplitInput n),
        input.tangentialRadius = b → ∀ j, j ≤ 1 → ∀ y,
          ‖iteratedFDeriv ℝ j (boundedSplitTangentialCutoff input) y‖ ≤ A := by
  obtain ⟨A, hA, hunit⟩ := unitScaleBump_uniform_deriv_bound n
  let r := b / 2
  have hr : 0 < r := div_pos hb (by norm_num)
  let D : ℕ → ℝ := fun j ↦ A / r ^ j
  let Aout := max (((Finset.range 2).image D).max' (by simp)) 0
  refine ⟨Aout, le_max_right _ _, ?_⟩
  intro input hinput j hj y
  have hscaled :
      ‖iteratedFDeriv ℝ j (boundedSplitTangentialCutoff input) y‖ * r ^ j ≤ A := by
    simpa [boundedSplitTangentialCutoff, r, hinput] using
      rescaledUnitBump_scaled_deriv_bound hunit 0 hr j (hj.trans (by norm_num)) y
  have hdiv : ‖iteratedFDeriv ℝ j (boundedSplitTangentialCutoff input) y‖ ≤ D j := by
    dsimp [D]
    exact (le_div_iff₀ (pow_pos hr j)).2 hscaled
  exact hdiv.trans ((Finset.le_max' ((Finset.range 2).image D) (D j)
    (Finset.mem_image_of_mem D (by simpa using Nat.lt_succ_of_le hj))).trans
      (le_max_left _ _))
theorem exists_boundedSplitComparisonQuadratic_first_deriv_bound
    (n : ℕ) (a : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ j, j ≤ 1 →
      ∀ z : ℝ × (Fin n → ℝ), ‖z‖ ≤ a →
        ‖iteratedFDeriv ℝ j (boundedSplitComparisonQuadratic (n := n)) z‖ ≤ A := by
  have hsmooth : ContDiff ℝ 1 (boundedSplitComparisonQuadratic (n := n)) :=
    boundedSplitComparisonQuadratic_contDiff.of_le (by norm_num)
  have hbound (j : ℕ) (hj : j ≤ 1) :
      ∃ K : ℝ, ∀ z ∈ Metric.closedBall (0 : ℝ × (Fin n → ℝ)) a,
        ‖iteratedFDeriv ℝ j (boundedSplitComparisonQuadratic (n := n)) z‖ ≤ K := by
    exact (isCompact_closedBall (0 : ℝ × (Fin n → ℝ)) a).exists_bound_of_continuousOn
      ((hsmooth.continuous_iteratedFDeriv (by exact_mod_cast hj)).continuousOn)
  obtain ⟨K0, hK0⟩ := hbound 0 (by norm_num)
  obtain ⟨K1, hK1⟩ := hbound 1 (by norm_num)
  let A := max (max K0 K1) 0
  refine ⟨A, le_max_right _ _, ?_⟩
  intro j hj z hz
  have hzball : z ∈ Metric.closedBall (0 : ℝ × (Fin n → ℝ)) a := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  interval_cases j
  · exact (hK0 z hzball).trans ((le_max_left K0 K1).trans (le_max_left _ _))
  · exact (hK1 z hzball).trans ((le_max_right K0 K1).trans (le_max_left _ _))
theorem exists_uniform_boundedSplitResidualCutoff_deriv_bound
    (n : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ {Φ : (Fin (n + 1) → ℝ) → ℝ}
        (prep : IntrinsicBoundedSplitPreprocessing n Φ C)
        (j : ℕ), j ≤ 6 → ∀ y,
          ‖iteratedFDeriv ℝ j (boundedSplitResidualCutoff prep.input) y‖ ≤ A := by
  obtain ⟨A, hA, hunit⟩ := unitScaleBump_uniform_deriv_bound n
  let r := positiveCurvatureTangentialRadius C / 4
  have hr : 0 < r := div_pos (positiveCurvatureTangentialRadius_pos hC) (by norm_num)
  let M : ℕ → ℝ := fun j ↦ A / r ^ j
  let Aout := max (((Finset.range 7).image M).max' (by simp)) 0
  refine ⟨Aout, le_max_right _ _, ?_⟩
  intro Φ prep j hj y
  have hscaled :
      ‖iteratedFDeriv ℝ j (boundedSplitResidualCutoff prep.input) y‖ * r ^ j ≤ A := by
    simpa [boundedSplitResidualCutoff, r, prep.tangentialRadius_eq] using
      rescaledUnitBump_scaled_deriv_bound hunit 0 hr j hj y
  have hdiv : ‖iteratedFDeriv ℝ j (boundedSplitResidualCutoff prep.input) y‖ ≤ M j := by
    dsimp [M]
    exact (le_div_iff₀ (pow_pos hr j)).2 hscaled
  exact hdiv.trans ((Finset.le_max' ((Finset.range 7).image M) (M j)
    (Finset.mem_image_of_mem M (by simpa using Nat.lt_succ_of_le hj))).trans
      (le_max_left _ _))
/-- A fine-cover threshold which leaves enough room for the coordinate-frame inverse. -/
def boundedSplitSigmaMax (C : ℝ) : ℝ :=
  min (1 / 2) (positiveCurvatureTangentialRadius C / 16)

theorem boundedSplitSigmaMax_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < boundedSplitSigmaMax C := by
  rw [boundedSplitSigmaMax]
  exact lt_min (by norm_num) (div_pos (positiveCurvatureTangentialRadius_pos hC) (by norm_num))

theorem boundedSplitSigmaMax_le_half (C : ℝ) :
    boundedSplitSigmaMax C ≤ 1 / 2 := by
  exact min_le_left _ _

theorem boundedSplitSigmaMax_le_one (C : ℝ) :
    boundedSplitSigmaMax C ≤ 1 := by
  exact (boundedSplitSigmaMax_le_half C).trans (by norm_num)

theorem four_mul_boundedSplitSigmaMax_le_quarter_tangentialRadius (C : ℝ) :
    4 * boundedSplitSigmaMax C ≤ positiveCurvatureTangentialRadius C / 4 := by
  have h := min_le_right (1 / 2 : ℝ) (positiveCurvatureTangentialRadius C / 16)
  dsimp [boundedSplitSigmaMax]
  linarith

theorem intrinsicCutoff_in_boundedSplitInner
    {n : ℕ} {u : (Fin (n + 1) → ℝ) → ℝ}
    {D sigma A : ℝ} {B : ℕ}
    (cover : FineQuantitativeScaleCover u D sigma A B)
    {i : ℕ} (hi : i ∈ cover.active)
    {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    (prep : IntrinsicBoundedSplitPreprocessing n Φ C)
    (hC : 0 ≤ C) (hsigma : sigma ≤ boundedSplitSigmaMax C)
    {z : ℝ × (Fin n → ℝ)}
    (hz : cover.intrinsicCutoff i
      (unitDirectionCoordinateFrame prep.direction prep.direction_norm z) ≠ 0) :
    z ∈ boundedSplitCylinder prep.input.normalRadius
      (prep.input.tangentialRadius / 4) := by
  let T := unitDirectionCoordinateFrame prep.direction prep.direction_norm
  have hTz : ‖T z‖ < 2 * sigma := cover.intrinsicCutoff_ne_zero_norm_lt hi hz
  have hzinv : ‖z‖ ≤ 2 * ‖T z‖ := by
    have h := norm_unitDirectionCoordinateFrame_symm_apply_le_two_mul
      prep.direction prep.direction_norm (T z)
    simpa [T] using h
  have hzlt : ‖z‖ < 4 * sigma := by nlinarith
  have hsigma' : 4 * sigma ≤ positiveCurvatureTangentialRadius C / 4 := by
    calc
      4 * sigma ≤ 4 * boundedSplitSigmaMax C := by gcongr
      _ ≤ positiveCurvatureTangentialRadius C / 4 :=
        four_mul_boundedSplitSigmaMax_le_quarter_tangentialRadius C
  have hzquarter : ‖z‖ ≤ positiveCurvatureTangentialRadius C / 4 :=
    (hzlt.trans_le hsigma').le
  have hnormal : |z.1| ≤ prep.input.normalRadius := by
    have hfirst : |z.1| ≤ ‖z‖ := by
      rw [Prod.norm_def]
      simp [Real.norm_eq_abs]
    calc
      |z.1| ≤ ‖z‖ := hfirst
      _ ≤ positiveCurvatureTangentialRadius C / 4 := hzquarter
      _ ≤ positiveCurvatureTangentialRadius C := by
        nlinarith [positiveCurvatureTangentialRadius_pos hC]
      _ ≤ positiveCurvatureCoordinateRadius C :=
        positiveCurvatureTangentialRadius_le_coordinateRadius hC
      _ = prep.input.normalRadius := prep.normalRadius_eq.symm
  have htangential : ‖z.2‖ ≤ prep.input.tangentialRadius / 4 := by
    have hsecond : ‖z.2‖ ≤ ‖z‖ := by
      rw [Prod.norm_def]
      exact le_max_right _ _
    calc
      ‖z.2‖ ≤ ‖z‖ := hsecond
      _ ≤ positiveCurvatureTangentialRadius C / 4 := hzquarter
      _ = prep.input.tangentialRadius / 4 := by rw [prep.tangentialRadius_eq]
  exact ⟨hnormal, htangential⟩

/-- Package an explicit bounded split once only its quantitative derivative estimates have
been supplied.  Exactness and nonnegativity come from the proved bounded construction. -/
noncomputable def quantitativeCurvatureSplitOutputOfBounds
    {n : ℕ} {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    (prep : IntrinsicBoundedSplitPreprocessing n Φ C)
    (cutoff : (Fin (n + 1) → ℝ) → ℝ)
    (parentRadius Mmain Azeta Aresidual : ℝ)
    (hcutoffInner : ∀ z,
      cutoff (unitDirectionCoordinateFrame prep.direction prep.direction_norm z) ≠ 0 →
        z ∈ boundedSplitCylinder prep.input.normalRadius
          (prep.input.tangentialRadius / 4))
    (hmain : ∀ j, j ≤ 4 → ∀ x,
      ‖iteratedFDeriv ℝ j
          (curvatureMainRoot prep cutoff
            (boundedUniformLocalSplitData prep.input).root) x‖ *
          (2 * parentRadius) ^ j ≤ Mmain * (2 * parentRadius) ^ 2)
    (hzeta : ∀ j, j ≤ 6 → ∀ y,
      ‖iteratedFDeriv ℝ j (boundedSplitResidualCutoff prep.input) y‖ ≤ Azeta)
    (hresidual : ∀ j, j ≤ 6 → ∀ y,
      ‖iteratedFDeriv ℝ j
        (boundedUniformLocalSplitData prep.input).residual y‖ ≤ Aresidual) :
    QuantitativeCurvatureSplitOutput prep cutoff
      parentRadius Mmain Azeta Aresidual := by
  let data := boundedUniformLocalSplitData prep.input
  exact {
    root := data.root
    residual := data.residual
    zeta := boundedSplitResidualCutoff prep.input
    root_contDiff := data.root_contDiff
    residual_contDiff := data.residual_contDiff
    residual_nonnegative := data.residual_nonnegative
    zeta_contDiff := boundedSplitResidualCutoff_contDiff prep.input
    zeta_compactSupport := boundedSplitResidualCutoff_compactSupport prep.input
    exact_square_on_cutoff := by
      intro z hz
      apply data.exact_square z
      have hinner := hcutoffInner z hz
      exact ⟨hinner.1, hinner.2.trans (by
        linarith [prep.input.tangentialRadius_pos])⟩
    zeta_eq_one_on_cutoff := by
      intro z hz
      exact boundedSplitResidualCutoff_eq_one prep.input (hcutoffInner z hz).2
    main_scaled_jets := hmain
    zeta_global_jets := hzeta
    residual_global_jets := hresidual }
theorem curvatureMainRoot_uniform_deriv_bound_of_local
    {n : ℕ} {u : (Fin (n + 1) → ℝ) → ℝ}
    {parentDilation sigma parentA : ℝ} {parentB : ℕ}
    (cover : FineQuantitativeScaleCover
      u parentDilation sigma parentA parentB)
    {i : ℕ} (hi : i ∈ cover.active)
    {Φ : (Fin (n + 1) → ℝ) → ℝ} {C Aroot : ℝ}
    (prep : IntrinsicBoundedSplitPreprocessing n Φ C)
    (hparentA : 1 ≤ parentA) (hAroot : 0 ≤ Aroot)
    (hsigma : sigma ≤ boundedSplitSigmaMax C)
    (hrootLocal : ∀ z, ‖z‖ ≤ positiveCurvatureTangentialRadius C / 4 →
      ∀ j, j ≤ 4 →
        ‖iteratedFDeriv ℝ j (boundedUniformLocalSplitData prep.input).root z‖ ≤
          Aroot) :
    ∀ j, j ≤ 4 → ∀ x,
      ‖iteratedFDeriv ℝ j
        (curvatureMainRoot prep (cover.intrinsicCutoff i)
          (boundedUniformLocalSplitData prep.input).root) x‖ ≤
        256 * parentA ^ 7 * Aroot := by
  let data := boundedUniformLocalSplitData prep.input
  let cutoff := cover.intrinsicCutoff i
  let q := cover.radius i / nonnegativeJetScale u (cover.center i)
  let T := (unitDirectionCoordinateFrame prep.direction prep.direction_norm).symm
  let pulledRoot : (Fin (n + 1) → ℝ) → ℝ := fun x ↦ data.root (T x)
  have hcutoff : ContDiff ℝ 4 cutoff :=
    (cover.intrinsicCutoff_contDiff i).of_le (by norm_num)
  have hpulled : ContDiff ℝ 4 pulledRoot := data.root_contDiff.comp T.contDiff
  have hqPos : 0 < q := by
    simpa [q] using cover.radiusRatio_pos hi
  have hqSigma : q ≤ sigma := by
    have hR : 0 < nonnegativeJetScale u (cover.center i) :=
      (cover.radius_pos i hi).trans_le (cover.radius_comparable i hi).1
    dsimp [q]
    rw [div_le_iff₀ hR]
    exact cover.radius_le_fine i hi
  have hqTangential : 4 * q ≤ positiveCurvatureTangentialRadius C / 4 :=
    calc
      4 * q ≤ 4 * sigma := by gcongr
      _ ≤ 4 * boundedSplitSigmaMax C := by gcongr
      _ ≤ positiveCurvatureTangentialRadius C / 4 :=
        four_mul_boundedSplitSigmaMax_le_quarter_tangentialRadius C
  have hsupport : Function.support cutoff ⊆
      Metric.ball (0 : Fin (n + 1) → ℝ) (2 * q) := by
    have hbase := cover.intrinsicCutoff_support_subset_radius hi
    have hradiusEq : cover.intrinsicCutoffRadius i = 2 * q := by
      dsimp [FineQuantitativeScaleCover.intrinsicCutoffRadius, q]
      ring
    simpa [cutoff, hradiusEq] using hbase
  have hmainSupport : Function.support
      (curvatureMainRoot prep cutoff data.root) ⊆ Function.support cutoff :=
    support_curvatureMainRoot_subset prep cutoff data.root
  have hmainTopologicalSupport : tsupport
      (curvatureMainRoot prep cutoff data.root) ⊆
      Metric.closedBall (0 : Fin (n + 1) → ℝ) (2 * q) :=
    closure_minimal
      (hmainSupport.trans (hsupport.trans Metric.ball_subset_closedBall))
      Metric.isClosed_closedBall
  intro j hj x
  by_cases hx : ‖x‖ ≤ 2 * q
  · have hTx : ‖T x‖ ≤ positiveCurvatureTangentialRadius C / 4 := by
      have hTnorm : ‖T x‖ ≤ 2 * ‖x‖ :=
        norm_unitDirectionCoordinateFrame_symm_apply_le_two_mul
          prep.direction prep.direction_norm x
      calc
        ‖T x‖ ≤ 2 * ‖x‖ := hTnorm
        _ ≤ 4 * q := by linarith
        _ ≤ positiveCurvatureTangentialRadius C / 4 := hqTangential
    have hpulledBound : ∀ k, k ≤ 4 →
        ‖iteratedFDeriv ℝ k pulledRoot x‖ ≤ 16 * Aroot := by
      intro k hk
      have hcomp : iteratedFDeriv ℝ k pulledRoot x =
          (iteratedFDeriv ℝ k data.root (T x)).compContinuousLinearMap
            (fun _ ↦ T.toContinuousLinearMap) := by
        exact T.toContinuousLinearMap.iteratedFDeriv_comp_right
          data.root_contDiff x (by exact_mod_cast hk)
      rw [hcomp]
      have hnormT : ‖T.toContinuousLinearMap‖ ≤ 2 := by
        simpa [T] using norm_unitDirectionCoordinateFrame_symm_le_two
          prep.direction prep.direction_norm
      have hprod : (∏ _ : Fin k, ‖T.toContinuousLinearMap‖) ≤ (2 : ℝ) ^ k := by
        calc
          (∏ _ : Fin k, ‖T.toContinuousLinearMap‖) ≤ ∏ _ : Fin k, (2 : ℝ) :=
            Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ hnormT)
          _ = (2 : ℝ) ^ k := by simp
      have hpow : (2 : ℝ) ^ k ≤ 16 := by
        interval_cases k <;> norm_num
      calc
        ‖(iteratedFDeriv ℝ k data.root (T x)).compContinuousLinearMap
            (fun _ ↦ T.toContinuousLinearMap)‖ ≤
            ‖iteratedFDeriv ℝ k data.root (T x)‖ *
              ∏ _ : Fin k, ‖T.toContinuousLinearMap‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ ≤ Aroot * (2 : ℝ) ^ k :=
          mul_le_mul (hrootLocal (T x) hTx k hk) hprod (by positivity) hAroot
        _ ≤ Aroot * 16 := mul_le_mul_of_nonneg_left hpow hAroot
        _ = 16 * Aroot := by ring
    have hproduct := norm_iteratedFDeriv_mul_le hcutoff hpulled x
      (by exact_mod_cast hj)
    have hsum :
        ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) *
            ‖iteratedFDeriv ℝ k cutoff x‖ *
              ‖iteratedFDeriv ℝ (j - k) pulledRoot x‖ ≤
          ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) *
            parentA ^ 7 * (16 * Aroot) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkj : k ≤ j := Finset.mem_range_succ_iff.mp hk
      gcongr
      · exact cover.intrinsicCutoff_uniform_deriv_bound hparentA hi x k
          (hkj.trans hj |>.trans (by norm_num))
      · exact hpulledBound (j - k) ((Nat.sub_le j k).trans hj)
    have hchoose :
        (∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) *
          parentA ^ 7 * (16 * Aroot)) =
            (2 : ℝ) ^ j * parentA ^ 7 * (16 * Aroot) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      norm_cast
      rw [Nat.sum_range_choose]
    have hpow : (2 : ℝ) ^ j ≤ 16 := by
      interval_cases j <;> norm_num
    have hraw : ‖iteratedFDeriv ℝ j
        (fun y ↦ cutoff y * pulledRoot y) x‖ ≤
          256 * parentA ^ 7 * Aroot := by
      calc
        _ ≤ ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) *
              ‖iteratedFDeriv ℝ k cutoff x‖ *
                ‖iteratedFDeriv ℝ (j - k) pulledRoot x‖ := hproduct
        _ ≤ ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) *
              parentA ^ 7 * (16 * Aroot) := hsum
        _ = (2 : ℝ) ^ j * parentA ^ 7 * (16 * Aroot) := hchoose
        _ ≤ 16 * parentA ^ 7 * (16 * Aroot) := by gcongr
        _ = 256 * parentA ^ 7 * Aroot := by ring
    have hfun : curvatureMainRoot prep cutoff data.root =
        (Real.sqrt (1 / 2 : ℝ)) • (fun y ↦ cutoff y * pulledRoot y) := by
      funext y
      simp [curvatureMainRoot, pulledRoot, T, curvatureSplitCoordinates, smul_eq_mul]
      ring
    rw [hfun, iteratedFDeriv_const_smul_apply
      ((hcutoff.mul hpulled).of_le (by exact_mod_cast hj) |>.contDiffAt), norm_smul]
    have hsqrt : ‖Real.sqrt (1 / 2 : ℝ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.sqrt_nonneg (1 / 2)]
    exact (mul_le_mul hsqrt hraw (norm_nonneg _) (by norm_num)).trans (by simp)
  · have hxBall : x ∉ Metric.closedBall (0 : Fin (n + 1) → ℝ) (2 * q) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    have hxTopological : x ∉ tsupport (curvatureMainRoot prep cutoff data.root) :=
      fun hmem ↦ hxBall (hmainTopologicalSupport hmem)
    have hxDeriv : x ∉ Function.support
        (iteratedFDeriv ℝ j (curvatureMainRoot prep cutoff data.root)) :=
      fun hmem ↦ hxTopological (support_iteratedFDeriv_subset j hmem)
    have hzero : iteratedFDeriv ℝ j
        (curvatureMainRoot prep cutoff data.root) x = 0 := by
      simpa [Function.mem_support] using hxDeriv
    rw [hzero, norm_zero]
    positivity
theorem scaled_four_jet_bound_of_global_bound
    {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {q parentA Aglobal : ℝ}
    (hq : 0 < q) (hqLower : parentA⁻¹ ≤ q) (hqHalf : q ≤ 1 / 2)
    (hparentA : 1 ≤ parentA) (hAglobal : 0 ≤ Aglobal)
    (hglobal : ∀ j, j ≤ 4 → ∀ x,
      ‖iteratedFDeriv ℝ j f x‖ ≤ Aglobal) :
    ∀ j, j ≤ 4 → ∀ x,
      ‖iteratedFDeriv ℝ j f x‖ * (2 * q) ^ j ≤
        (Aglobal * parentA ^ 2) * (2 * q) ^ 2 := by
  have hparentApos : 0 < parentA := lt_of_lt_of_le zero_lt_one hparentA
  have hAQ : 1 ≤ parentA * q := by
    calc
      1 = parentA * parentA⁻¹ := (mul_inv_cancel₀ hparentApos.ne').symm
      _ ≤ parentA * q := mul_le_mul_of_nonneg_left hqLower hparentApos.le
  have hr0 : 0 ≤ 2 * q := by positivity
  have hr1 : 2 * q ≤ 1 := by linarith
  have hpr : 1 ≤ parentA * (2 * q) := by nlinarith
  have hpaSq : parentA ≤ parentA ^ 2 := by
    nlinarith [mul_nonneg hparentApos.le (sub_nonneg.mpr hparentA)]
  have hfactorZero : 1 ≤ parentA ^ 2 * (2 * q) ^ 2 := by
    have hsq : 1 ≤ (parentA * (2 * q)) ^ 2 := by
      nlinarith [sq_nonneg (parentA * (2 * q) - 1)]
    simpa [mul_pow] using hsq
  have hfactorOne : 1 ≤ parentA ^ 2 * (2 * q) := by
    exact hpr.trans (mul_le_mul_of_nonneg_right hpaSq hr0)
  have hAexpand : Aglobal ≤ Aglobal * parentA ^ 2 := by
    have honeSq : (1 : ℝ) ≤ parentA ^ 2 := hparentA.trans hpaSq
    simpa only [mul_one] using mul_le_mul_of_nonneg_left honeSq hAglobal
  intro j hj x
  have hnorm := hglobal j hj x
  interval_cases j
  · simp only [pow_zero, mul_one]
    calc
      ‖iteratedFDeriv ℝ 0 f x‖ ≤ Aglobal := hnorm
      _ = Aglobal * 1 := by ring
      _ ≤ Aglobal * (parentA ^ 2 * (2 * q) ^ 2) :=
        mul_le_mul_of_nonneg_left hfactorZero hAglobal
      _ = (Aglobal * parentA ^ 2) * (2 * q) ^ 2 := by ring
  · simp only [pow_one]
    calc
      ‖iteratedFDeriv ℝ 1 f x‖ * (2 * q) ≤ Aglobal * (2 * q) :=
        mul_le_mul_of_nonneg_right hnorm hr0
      _ = (Aglobal * (2 * q)) * 1 := by ring
      _ ≤ (Aglobal * (2 * q)) * (parentA ^ 2 * (2 * q)) :=
        mul_le_mul_of_nonneg_left hfactorOne (mul_nonneg hAglobal hr0)
      _ = (Aglobal * parentA ^ 2) * (2 * q) ^ 2 := by ring
  · calc
      ‖iteratedFDeriv ℝ 2 f x‖ * (2 * q) ^ 2 ≤
          Aglobal * (2 * q) ^ 2 :=
        mul_le_mul_of_nonneg_right hnorm (sq_nonneg (2 * q))
      _ ≤ (Aglobal * parentA ^ 2) * (2 * q) ^ 2 :=
        mul_le_mul_of_nonneg_right hAexpand (sq_nonneg (2 * q))
  · have hr3 : (2 * q) ^ 3 ≤ (2 * q) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg (2 * q)) (sub_nonneg.mpr hr1)]
    calc
      ‖iteratedFDeriv ℝ 3 f x‖ * (2 * q) ^ 3 ≤
          Aglobal * (2 * q) ^ 3 :=
        mul_le_mul_of_nonneg_right hnorm (pow_nonneg hr0 3)
      _ ≤ Aglobal * (2 * q) ^ 2 := mul_le_mul_of_nonneg_left hr3 hAglobal
      _ ≤ (Aglobal * parentA ^ 2) * (2 * q) ^ 2 :=
        mul_le_mul_of_nonneg_right hAexpand (sq_nonneg (2 * q))
  · have hrSq : (2 * q) ^ 2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hr0 hr1 2
    have hr4 : (2 * q) ^ 4 ≤ (2 * q) ^ 2 := by
      have hprod := mul_nonneg (sq_nonneg (2 * q)) (sub_nonneg.mpr hrSq)
      nlinarith
    calc
      ‖iteratedFDeriv ℝ 4 f x‖ * (2 * q) ^ 4 ≤
          Aglobal * (2 * q) ^ 4 :=
        mul_le_mul_of_nonneg_right hnorm (pow_nonneg hr0 4)
      _ ≤ Aglobal * (2 * q) ^ 2 := mul_le_mul_of_nonneg_left hr4 hAglobal
      _ ≤ (Aglobal * parentA ^ 2) * (2 * q) ^ 2 :=
        mul_le_mul_of_nonneg_right hAexpand (sq_nonneg (2 * q))
/-- Parent jet control gives a fixed jet bound for the actual bounded input throughout the
whole coordinate cylinder used by the minimizing-graph construction. -/
theorem intrinsicBoundedSplitInput_uniform_deriv_on_coordinateBall
    {n : ℕ} {u : (Fin (n + 1) → ℝ) → ℝ}
    (hu : NormalizedNonnegativeC6 u) {C : ℝ}
    (hcontrol : NonnegativeJetControl u C)
    (c : Fin (n + 1) → ℝ) (hR : 0 < nonnegativeJetScale u c)
    (prep : IntrinsicBoundedSplitPreprocessing n
      (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) C)
    {z : ℝ × (Fin n → ℝ)}
    (hz : ‖z‖ ≤ positiveCurvatureCoordinateRadius C) :
    ∀ j, j ≤ 6 →
      ‖iteratedFDeriv ℝ j prep.input.function z‖ ≤ 512 * (C + 1) := by
  have hC : 0 ≤ C := hcontrol.constant_nonneg
  have hzHalf : ‖z‖ ≤ 1 / 2 := by
    calc
      ‖z‖ ≤ positiveCurvatureCoordinateRadius C := hz
      _ = positiveCurvaturePersistenceRadius C / 2 := rfl
      _ ≤ 1 / 2 := by gcongr; exact positiveCurvaturePersistenceRadius_le_one hC
  let pullback := intrinsicUnitDirectionCoordinatePullback
    u c prep.direction prep.direction_norm
  have hpullback : ContDiff ℝ 6 pullback :=
    intrinsicUnitDirectionCoordinatePullback_contDiff_six hu.contDiff
      c prep.direction prep.direction_norm
  have hfun : prep.input.function = (2 : ℝ) • pullback := by
    rw [prep.function_eq]
    funext w
    simp [doubledCurvaturePullback, pullback,
      intrinsicUnitDirectionCoordinatePullback, unitDirectionCoordinatePullback,
      coordinateFramePullback,
      Pi.smul_apply, smul_eq_mul]
  intro j hj
  have hpull := intrinsicUnitDirectionCoordinatePullback_uniform_deriv_on_halfBall
    hu hcontrol c prep.direction prep.direction_norm hR z hzHalf j hj
  rw [hfun, iteratedFDeriv_const_smul_apply
    ((hpullback.of_le (by exact_mod_cast hj)).contDiffAt), norm_smul, Real.norm_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 2)]
  have hpow : (2 : ℝ) ^ j ≤ 64 := by
    interval_cases j <;> norm_num
  calc
    2 * ‖iteratedFDeriv ℝ j pullback z‖ ≤
        2 * ((4 * (C + 1)) * 2 ^ j) := mul_le_mul_of_nonneg_left hpull (by norm_num)
    _ ≤ 2 * ((4 * (C + 1)) * 64) := by gcongr
    _ = 512 * (C + 1) := by ring
-- These radius hypotheses are retained so all derivative-bound interfaces have one signature.
set_option linter.unusedVariables false in
theorem exists_globalizedBoundedSplitFunction_first_deriv_bound
    (n : ℕ) (normalRadius tangentialRadius M : ℝ)
    (hnormal : 0 < normalRadius) (htangential : 0 < tangentialRadius)
    (htangentialNormal : tangentialRadius ≤ normalRadius) (hM : 0 ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (input : BoundedNormalizedLocalSplitInput n),
        input.normalRadius = normalRadius →
        input.tangentialRadius = tangentialRadius →
        (∀ z, ‖z‖ ≤ normalRadius → ∀ j, j ≤ 6 →
          ‖iteratedFDeriv ℝ j input.function z‖ ≤ M) →
        ∀ z ∈ boundedSplitCylinder normalRadius tangentialRadius,
          ‖iteratedFDeriv ℝ 1 (globalizedBoundedSplitFunction input) z‖ ≤ A := by
  obtain ⟨Achi, hAchi, hchi⟩ :=
    exists_uniform_boundedSplitTangentialCutoff_first_deriv_bound n htangential
  obtain ⟨Aq, hAq, hq⟩ :=
    exists_boundedSplitComparisonQuadratic_first_deriv_bound n normalRadius
  let A := 2 * Achi * M + 2 * (1 + Achi) * Aq
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro input hnormalEq htangentialEq hinput z hz
  let chi : (ℝ × (Fin n → ℝ)) → ℝ :=
    fun w ↦ boundedSplitTangentialCutoff input w.2
  let oneSubChi : (ℝ × (Fin n → ℝ)) → ℝ := fun w ↦ 1 - chi w
  let q := boundedSplitComparisonQuadratic (n := n)
  have hchiSmooth : ContDiff ℝ 4 chi :=
    (boundedSplitTangentialCutoff_contDiff input).of_le (by norm_num) |>.comp contDiff_snd
  have honeSmooth : ContDiff ℝ 4 oneSubChi := contDiff_const.sub hchiSmooth
  have hinputSmooth : ContDiff ℝ 4 input.function := input.contDiff.of_le (by norm_num)
  have hqSmooth : ContDiff ℝ 4 q := boundedSplitComparisonQuadratic_contDiff.of_le (by norm_num)
  have hzNorm : ‖z‖ ≤ normalRadius := by
    rw [Prod.norm_def]
    apply max_le
    · simpa [Real.norm_eq_abs] using hz.1
    · exact hz.2.trans htangentialNormal
  have hchiBound : ∀ k, k ≤ 1 →
      ‖iteratedFDeriv ℝ k chi z‖ ≤ Achi := by
    intro k hk
    simpa [chi, tangentialCoordinatePullback] using
      (norm_iteratedFDeriv_tangentialCoordinatePullback_le
        ((boundedSplitTangentialCutoff_contDiff input).of_le (by norm_num))
        (hk.trans (by norm_num)) z).trans
          (hchi input htangentialEq k hk z.2)
  have honeBound : ∀ k, k ≤ 1 →
      ‖iteratedFDeriv ℝ k oneSubChi z‖ ≤ 1 + Achi := by
    intro k hk
    interval_cases k
    · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      have hmem := boundedSplitTangentialCutoff_mem_Icc input z.2
      change |1 - boundedSplitTangentialCutoff input z.2| ≤ 1 + Achi
      rw [abs_of_nonneg (sub_nonneg.mpr hmem.2)]
      linarith
    · rw [norm_iteratedFDeriv_one]
      change ‖fderiv ℝ (fun w ↦ 1 - chi w) z‖ ≤ _
      rw [fderiv_const_sub]
      rw [norm_neg]
      have hb := hchiBound 1 (by norm_num)
      simpa [norm_iteratedFDeriv_one] using hb.trans (by linarith)
  have hinputBound : ∀ k, k ≤ 1 →
      ‖iteratedFDeriv ℝ k input.function z‖ ≤ M := by
    exact fun k hk ↦ hinput z hzNorm k (hk.trans (by norm_num))
  have hqBound : ∀ k, k ≤ 1 →
      ‖iteratedFDeriv ℝ k q z‖ ≤ Aq := fun k hk ↦ hq k hk z hzNorm
  have hfirstProduct : ‖iteratedFDeriv ℝ 1 (fun w ↦ chi w * input.function w) z‖ ≤
      2 * Achi * M := by
    have hprod := norm_iteratedFDeriv_mul_le hchiSmooth hinputSmooth z
      (by norm_num : (1 : ℕ) ≤ (4 : WithTop ℕ∞))
    calc
      _ ≤ ∑ k ∈ Finset.range 2, (Nat.choose 1 k : ℝ) *
          ‖iteratedFDeriv ℝ k chi z‖ *
            ‖iteratedFDeriv ℝ (1 - k) input.function z‖ := hprod
      _ ≤ ∑ k ∈ Finset.range 2, (Nat.choose 1 k : ℝ) * Achi * M := by
        apply Finset.sum_le_sum
        intro k hk
        have hk1 : k ≤ 1 := Finset.mem_range_succ_iff.mp hk
        gcongr
        · exact hchiBound k hk1
        · exact hinputBound (1 - k) (Nat.sub_le 1 k)
      _ = 2 * Achi * M := by norm_num [Finset.sum_range_succ]; ring
  have hsecondProduct : ‖iteratedFDeriv ℝ 1 (fun w ↦ oneSubChi w * q w) z‖ ≤
      2 * (1 + Achi) * Aq := by
    have hprod := norm_iteratedFDeriv_mul_le honeSmooth hqSmooth z
      (by norm_num : (1 : ℕ) ≤ (4 : WithTop ℕ∞))
    calc
      _ ≤ ∑ k ∈ Finset.range 2, (Nat.choose 1 k : ℝ) *
          ‖iteratedFDeriv ℝ k oneSubChi z‖ *
            ‖iteratedFDeriv ℝ (1 - k) q z‖ := hprod
      _ ≤ ∑ k ∈ Finset.range 2, (Nat.choose 1 k : ℝ) * (1 + Achi) * Aq := by
        apply Finset.sum_le_sum
        intro k hk
        have hk1 : k ≤ 1 := Finset.mem_range_succ_iff.mp hk
        gcongr
        · exact honeBound k hk1
        · exact hqBound (1 - k) (Nat.sub_le 1 k)
      _ = 2 * (1 + Achi) * Aq := by norm_num [Finset.sum_range_succ]; ring
  have hfun : globalizedBoundedSplitFunction input =
      (fun w ↦ chi w * input.function w) + (fun w ↦ oneSubChi w * q w) := by
    funext w
    rfl
  rw [hfun, iteratedFDeriv_add_apply
    ((hchiSmooth.mul hinputSmooth).of_le (by norm_num) |>.contDiffAt)
    ((honeSmooth.mul hqSmooth).of_le (by norm_num) |>.contDiffAt)]
  exact (norm_add_le _ _).trans (add_le_add hfirstProduct hsecondProduct)
theorem exists_boundedUniformLocalSplitData_residual_first_deriv_bound
    (n : ℕ) (normalRadius tangentialRadius M : ℝ)
    (hnormal : 0 < normalRadius) (htangential : 0 < tangentialRadius)
    (htangentialNormal : tangentialRadius ≤ normalRadius) (hM : 0 ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (input : BoundedNormalizedLocalSplitInput n),
        input.normalRadius = normalRadius →
        input.tangentialRadius = tangentialRadius →
        (∀ z, ‖z‖ ≤ normalRadius → ∀ j, j ≤ 6 →
          ‖iteratedFDeriv ℝ j input.function z‖ ≤ M) → ∀ y,
        ‖iteratedFDeriv ℝ 1 (boundedUniformLocalSplitData input).residual y‖ ≤ A := by
  obtain ⟨A, hA, hglobal⟩ := exists_globalizedBoundedSplitFunction_first_deriv_bound
    n normalRadius tangentialRadius M hnormal htangential htangentialNormal hM
  refine ⟨A, hA, ?_⟩
  intro input hnormalEq htangentialEq hinput y
  let data := boundedUniformLocalSplitData input
  have hresidualSupport : Function.support data.residual ⊆
      Function.support (boundedSplitTangentialCutoff input) := by
    intro w hw hcut
    exact hw (data.residual_eq_zero_of_tangentialCutoff_eq_zero w hcut)
  have hcutoffSupport : Function.support (boundedSplitTangentialCutoff input) =
      Metric.ball (0 : Fin n → ℝ) tangentialRadius := by
    rw [boundedSplitTangentialCutoff,
      support_rescaledUnitBump 0 (div_pos input.tangentialRadius_pos (by norm_num))]
    rw [htangentialEq]
    congr 1
    ring
  have hresidualTopologicalSupport : tsupport data.residual ⊆
      Metric.closedBall (0 : Fin n → ℝ) tangentialRadius := by
    apply closure_minimal
    · intro w hw
      exact Metric.ball_subset_closedBall (hcutoffSupport ▸ hresidualSupport hw)
    · exact Metric.isClosed_closedBall
  by_cases hy : ‖y‖ ≤ tangentialRadius
  · have hgraphMem := data.graph.graph_point_mem y
    have hnormalGraph : |data.graph.graph y| ≤ normalRadius := by
      rw [(globalizedBoundedSplitInput input).cylinder_eq] at hgraphMem
      rw [← hnormalEq]
      exact abs_le.mpr hgraphMem
    have hpoint : (data.graph.graph y, y) ∈
        boundedSplitCylinder normalRadius tangentialRadius := ⟨hnormalGraph, hy⟩
    have hambient := hglobal input hnormalEq htangentialEq hinput
      (data.graph.graph y, y) hpoint
    have hambient' : ‖fderiv ℝ (globalizedBoundedSplitInput input).function
        (data.graph.graph y, y)‖ ≤ A := by
      rw [← norm_iteratedFDeriv_one]
      exact hambient
    let T : (Fin n → ℝ) →L[ℝ] (ℝ × (Fin n → ℝ)) :=
      ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)
    have hT : ‖T‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro v
      change ‖((0 : ℝ), v)‖ ≤ 1 * ‖v‖
      simp [Prod.norm_def]
    rw [norm_iteratedFDeriv_one,
      data.fderiv_residual_eq_tangential y]
    calc
      ‖(fderiv ℝ (globalizedBoundedSplitInput input).function
        (data.graph.graph y, y)).comp T‖ ≤
          ‖fderiv ℝ (globalizedBoundedSplitInput input).function
            (data.graph.graph y, y)‖ * ‖T‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ A * 1 := mul_le_mul hambient' hT (norm_nonneg _) hA
      _ = A := mul_one A
  · have hyBall : y ∉ Metric.closedBall (0 : Fin n → ℝ) tangentialRadius := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hy
    have hyTopological : y ∉ tsupport data.residual :=
      fun hmem ↦ hyBall (hresidualTopologicalSupport hmem)
    have hyDeriv : y ∉ Function.support (iteratedFDeriv ℝ 1 data.residual) :=
      fun hmem ↦ hyTopological (support_iteratedFDeriv_subset 1 hmem)
    have hzero : iteratedFDeriv ℝ 1 data.residual y = 0 := by
      simpa [Function.mem_support] using hyDeriv
    rw [hzero, norm_zero]
    exact hA
theorem exists_uniform_boundedSplitTangentialCutoff_second_deriv_bound
    (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (input : BoundedNormalizedLocalSplitInput n),
        input.tangentialRadius = b → ∀ j, j ≤ 2 → ∀ y,
          ‖iteratedFDeriv ℝ j (boundedSplitTangentialCutoff input) y‖ ≤ A := by
  obtain ⟨A, hA, hunit⟩ := unitScaleBump_uniform_deriv_bound n
  let r := b / 2
  have hr : 0 < r := div_pos hb (by norm_num)
  let D : ℕ → ℝ := fun j ↦ A / r ^ j
  let Aout := max (((Finset.range 3).image D).max' (by simp)) 0
  refine ⟨Aout, le_max_right _ _, ?_⟩
  intro input hinput j hj y
  have hscaled :
      ‖iteratedFDeriv ℝ j (boundedSplitTangentialCutoff input) y‖ * r ^ j ≤ A := by
    simpa [boundedSplitTangentialCutoff, r, hinput] using
      rescaledUnitBump_scaled_deriv_bound hunit 0 hr j (hj.trans (by norm_num)) y
  have hdiv : ‖iteratedFDeriv ℝ j (boundedSplitTangentialCutoff input) y‖ ≤ D j := by
    dsimp [D]
    exact (le_div_iff₀ (pow_pos hr j)).2 hscaled
  exact hdiv.trans ((Finset.le_max' ((Finset.range 3).image D) (D j)
    (Finset.mem_image_of_mem D (by simpa using Nat.lt_succ_of_le hj))).trans
      (le_max_left _ _))

theorem exists_boundedSplitComparisonQuadratic_second_deriv_bound
    (n : ℕ) (a : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ j, j ≤ 2 →
      ∀ z : ℝ × (Fin n → ℝ), ‖z‖ ≤ a →
        ‖iteratedFDeriv ℝ j (boundedSplitComparisonQuadratic (n := n)) z‖ ≤ A := by
  have hsmooth : ContDiff ℝ 2 (boundedSplitComparisonQuadratic (n := n)) :=
    boundedSplitComparisonQuadratic_contDiff.of_le (by norm_num)
  have hbound (j : ℕ) (hj : j ≤ 2) :
      ∃ K : ℝ, ∀ z ∈ Metric.closedBall (0 : ℝ × (Fin n → ℝ)) a,
        ‖iteratedFDeriv ℝ j (boundedSplitComparisonQuadratic (n := n)) z‖ ≤ K := by
    exact (isCompact_closedBall (0 : ℝ × (Fin n → ℝ)) a).exists_bound_of_continuousOn
      ((hsmooth.continuous_iteratedFDeriv (by exact_mod_cast hj)).continuousOn)
  let K : ℕ → ℝ := fun j ↦ if hj : j ≤ 2 then Classical.choose (hbound j hj) else 0
  have hK : ∀ j, j ≤ 2 → ∀ z ∈ Metric.closedBall (0 : ℝ × (Fin n → ℝ)) a,
      ‖iteratedFDeriv ℝ j (boundedSplitComparisonQuadratic (n := n)) z‖ ≤ K j := by
    intro j hj z hz
    dsimp only [K]
    rw [dif_pos hj]
    exact Classical.choose_spec (hbound j hj) z hz
  let A := max (((Finset.range 3).image K).max' (by simp)) 0
  refine ⟨A, le_max_right _ _, ?_⟩
  intro j hj z hz
  have hzball : z ∈ Metric.closedBall (0 : ℝ × (Fin n → ℝ)) a := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  exact (hK j hj z hzball).trans ((Finset.le_max' ((Finset.range 3).image K) (K j)
    (Finset.mem_image_of_mem K (by simpa using Nat.lt_succ_of_le hj))).trans
      (le_max_left _ _))


-- These normalization hypotheses are retained for a uniform derivative-bound interface.
set_option linter.unusedVariables false in
theorem exists_globalizedBoundedSplitFunction_second_deriv_bound
    (n : ℕ) (normalRadius tangentialRadius M : ℝ)
    (hnormal : 0 < normalRadius) (htangential : 0 < tangentialRadius)
    (htangentialNormal : tangentialRadius ≤ normalRadius) (hM : 0 ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (input : BoundedNormalizedLocalSplitInput n),
        input.normalRadius = normalRadius →
        input.tangentialRadius = tangentialRadius →
        (∀ z, ‖z‖ ≤ normalRadius → ∀ j, j ≤ 6 →
          ‖iteratedFDeriv ℝ j input.function z‖ ≤ M) →
        ∀ j, j ≤ 2 → ∀ z ∈ boundedSplitCylinder normalRadius tangentialRadius,
          ‖iteratedFDeriv ℝ j (globalizedBoundedSplitFunction input) z‖ ≤ A := by
  obtain ⟨Achi, hAchi, hchi⟩ :=
    exists_uniform_boundedSplitTangentialCutoff_second_deriv_bound n htangential
  obtain ⟨Aq, hAq, hq⟩ :=
    exists_boundedSplitComparisonQuadratic_second_deriv_bound n normalRadius
  let B : ℕ → ℝ := fun j ↦
    (∑ k ∈ Finset.range (j + 1), (Nat.choose j k : ℝ) * Achi * M) +
    ∑ k ∈ Finset.range (j + 1), (Nat.choose j k : ℝ) * (1 + Achi) * Aq
  let A := max (((Finset.range 3).image B).max' (by simp)) 0
  refine ⟨A, le_max_right _ _, ?_⟩
  intro input hnormalEq htangentialEq hinput j hj z hz
  let chi : (ℝ × (Fin n → ℝ)) → ℝ :=
    fun w ↦ boundedSplitTangentialCutoff input w.2
  let oneSubChi : (ℝ × (Fin n → ℝ)) → ℝ := fun w ↦ 1 - chi w
  let q := boundedSplitComparisonQuadratic (n := n)
  have hchiSmooth : ContDiff ℝ 6 chi :=
    (boundedSplitTangentialCutoff_contDiff input).comp contDiff_snd
  have honeSmooth : ContDiff ℝ 6 oneSubChi := contDiff_const.sub hchiSmooth
  have hinputSmooth : ContDiff ℝ 6 input.function := input.contDiff
  have hqSmooth : ContDiff ℝ 6 q := boundedSplitComparisonQuadratic_contDiff.of_le (by norm_num)
  have hzNorm : ‖z‖ ≤ normalRadius := by
    rw [Prod.norm_def]
    apply max_le
    · simpa [Real.norm_eq_abs] using hz.1
    · exact hz.2.trans htangentialNormal
  have hchiBound : ∀ k, k ≤ j → ‖iteratedFDeriv ℝ k chi z‖ ≤ Achi := by
    intro k hk
    simpa [chi, tangentialCoordinatePullback] using
      (norm_iteratedFDeriv_tangentialCoordinatePullback_le
        ((boundedSplitTangentialCutoff_contDiff input).of_le (by norm_num))
        (by exact_mod_cast hk.trans (hj.trans (by norm_num : 2 ≤ 4))) z).trans
          (hchi input htangentialEq k (hk.trans hj) z.2)
  have honeBound : ∀ k, k ≤ j →
      ‖iteratedFDeriv ℝ k oneSubChi z‖ ≤ 1 + Achi := by
    intro k hk
    by_cases hkzero : k = 0
    · subst k
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      have hmem := boundedSplitTangentialCutoff_mem_Icc input z.2
      change |1 - boundedSplitTangentialCutoff input z.2| ≤ 1 + Achi
      rw [abs_of_nonneg (sub_nonneg.mpr hmem.2)]
      linarith
    · have hk6 : k ≤ 6 := hk.trans (hj.trans (by norm_num))
      have hconstSmooth : ContDiff ℝ k (fun _ : ℝ × (Fin n → ℝ) ↦ (1 : ℝ)) :=
        contDiff_const
      have hnegSmooth : ContDiff ℝ k (-chi) := hchiSmooth.neg.of_le (by exact_mod_cast hk6)
      have honeEq : oneSubChi = (fun _ : ℝ × (Fin n → ℝ) ↦ (1 : ℝ)) + (-chi) := by
        funext w
        exact sub_eq_add_neg _ _
      rw [honeEq, iteratedFDeriv_add_apply hconstSmooth.contDiffAt hnegSmooth.contDiffAt,
        show iteratedFDeriv ℝ k (fun _ : ℝ × (Fin n → ℝ) ↦ (1 : ℝ)) = 0 from
          iteratedFDeriv_const_of_ne hkzero 1,
        Pi.zero_apply, zero_add, iteratedFDeriv_neg_apply, norm_neg]
      exact (hchiBound k hk).trans (by linarith)
  have hinputBound : ∀ k, k ≤ j →
      ‖iteratedFDeriv ℝ k input.function z‖ ≤ M := by
    exact fun k hk ↦ hinput z hzNorm k (hk.trans (hj.trans (by norm_num)))
  have hqBound : ∀ k, k ≤ j →
      ‖iteratedFDeriv ℝ k q z‖ ≤ Aq := fun k hk ↦ hq k (hk.trans hj) z hzNorm
  have hfirstProduct :
      ‖iteratedFDeriv ℝ j (fun w ↦ chi w * input.function w) z‖ ≤
        ∑ k ∈ Finset.range (j + 1), (Nat.choose j k : ℝ) * Achi * M := by
    have hprod := norm_iteratedFDeriv_mul_le hchiSmooth hinputSmooth z
      (by exact_mod_cast hj.trans (by norm_num))
    calc
      _ ≤ ∑ k ∈ Finset.range (j + 1), (Nat.choose j k : ℝ) *
          ‖iteratedFDeriv ℝ k chi z‖ *
            ‖iteratedFDeriv ℝ (j - k) input.function z‖ := hprod
      _ ≤ ∑ k ∈ Finset.range (j + 1), (Nat.choose j k : ℝ) * Achi * M := by
        apply Finset.sum_le_sum
        intro k hk
        have hkj : k ≤ j := Finset.mem_range_succ_iff.mp hk
        gcongr
        · exact hchiBound k hkj
        · exact hinputBound (j - k) (Nat.sub_le j k)
  have hsecondProduct :
      ‖iteratedFDeriv ℝ j (fun w ↦ oneSubChi w * q w) z‖ ≤
        ∑ k ∈ Finset.range (j + 1),
          (Nat.choose j k : ℝ) * (1 + Achi) * Aq := by
    have hprod := norm_iteratedFDeriv_mul_le honeSmooth hqSmooth z
      (by exact_mod_cast hj.trans (by norm_num))
    calc
      _ ≤ ∑ k ∈ Finset.range (j + 1), (Nat.choose j k : ℝ) *
          ‖iteratedFDeriv ℝ k oneSubChi z‖ *
            ‖iteratedFDeriv ℝ (j - k) q z‖ := hprod
      _ ≤ ∑ k ∈ Finset.range (j + 1),
          (Nat.choose j k : ℝ) * (1 + Achi) * Aq := by
        apply Finset.sum_le_sum
        intro k hk
        have hkj : k ≤ j := Finset.mem_range_succ_iff.mp hk
        gcongr
        · exact honeBound k hkj
        · exact hqBound (j - k) (Nat.sub_le j k)
  have hfun : globalizedBoundedSplitFunction input =
      (fun w ↦ chi w * input.function w) + (fun w ↦ oneSubChi w * q w) := by
    funext w
    rfl
  have hnorm : ‖iteratedFDeriv ℝ j (globalizedBoundedSplitFunction input) z‖ ≤ B j := by
    rw [hfun, iteratedFDeriv_add_apply
      ((hchiSmooth.mul hinputSmooth).of_le
        (by exact_mod_cast hj.trans (by norm_num : 2 ≤ 6)) |>.contDiffAt)
      ((honeSmooth.mul hqSmooth).of_le
        (by exact_mod_cast hj.trans (by norm_num : 2 ≤ 6)) |>.contDiffAt)]
    exact (norm_add_le _ _).trans (by simpa [B] using add_le_add hfirstProduct hsecondProduct)
  exact hnorm.trans ((Finset.le_max' ((Finset.range 3).image B) (B j)
    (Finset.mem_image_of_mem B (by simpa using Nat.lt_succ_of_le hj))).trans
      (le_max_left _ _))
/-- Uniform residual Hessian control for the explicit bounded split. -/
theorem exists_boundedUniformLocalSplitData_residual_second_deriv_bound
    (n : ℕ) (normalRadius tangentialRadius M : ℝ)
    (hnormal : 0 < normalRadius) (htangential : 0 < tangentialRadius)
    (htangentialNormal : tangentialRadius ≤ normalRadius) (hM : 0 ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (input : BoundedNormalizedLocalSplitInput n),
        input.normalRadius = normalRadius →
        input.tangentialRadius = tangentialRadius →
        (∀ z, ‖z‖ ≤ normalRadius → ∀ j, j ≤ 6 →
          ‖iteratedFDeriv ℝ j input.function z‖ ≤ M) → ∀ y,
        ‖iteratedFDeriv ℝ 2 (boundedUniformLocalSplitData input).residual y‖ ≤ A := by
  obtain ⟨Aglobal, hAglobal, hglobal⟩ :=
    exists_globalizedBoundedSplitFunction_second_deriv_bound n
      normalRadius tangentialRadius M hnormal htangential htangentialNormal hM
  let A := Aglobal * max (4 * Aglobal) 1
  refine ⟨A, mul_nonneg hAglobal (zero_le_one.trans (le_max_right _ _)), ?_⟩
  intro input hnormalEq htangentialEq hinput y
  let data := boundedUniformLocalSplitData input
  apply data.norm_iteratedFDeriv_two_residual_le_global hAglobal
  intro z hz
  apply hglobal input hnormalEq htangentialEq hinput 2 (by norm_num) z
  simpa [boundedSplitCylinder, hnormalEq, htangentialEq] using hz
/-- Tangential pullback through the norm-one projection preserves derivative norms through six. -/
theorem norm_iteratedFDeriv_tangentialCoordinatePullback_le_six {n j : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 6 f) (hj : j ≤ 6)
    (z : ℝ × (Fin n → ℝ)) :
    ‖iteratedFDeriv ℝ j (tangentialCoordinatePullback f) z‖ ≤
      ‖iteratedFDeriv ℝ j f z.2‖ := by
  let L : (ℝ × (Fin n → ℝ)) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    simpa only [one_mul] using norm_snd_le w
  have hcomp : iteratedFDeriv ℝ j (f ∘ L) z =
      (iteratedFDeriv ℝ j f (L z)).compContinuousLinearMap (fun _ ↦ L) :=
    L.iteratedFDeriv_comp_right hf z (by exact_mod_cast hj)
  change ‖iteratedFDeriv ℝ j (f ∘ L) z‖ ≤ _
  rw [hcomp]
  calc
    ‖(iteratedFDeriv ℝ j f (L z)).compContinuousLinearMap (fun _ ↦ L)‖ ≤
        ‖iteratedFDeriv ℝ j f (L z)‖ * ∏ _ : Fin j, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ j f (L z)‖ * ∏ _ : Fin j, (1 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod (fun _ _ ↦ norm_nonneg L) (fun _ _ ↦ hL))
        (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ j f z.2‖ := by simp [L]

theorem exists_uniform_boundedSplitTangentialCutoff_six_deriv_bound
    (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (input : BoundedNormalizedLocalSplitInput n),
        input.tangentialRadius = b → ∀ j, j ≤ 6 → ∀ y,
          ‖iteratedFDeriv ℝ j (boundedSplitTangentialCutoff input) y‖ ≤ A := by
  obtain ⟨A, hA, hunit⟩ := unitScaleBump_uniform_deriv_bound n
  let r := b / 2
  have hr : 0 < r := div_pos hb (by norm_num)
  let D : ℕ → ℝ := fun j ↦ A / r ^ j
  let Aout := max (((Finset.range 7).image D).max' (by simp)) 0
  refine ⟨Aout, le_max_right _ _, ?_⟩
  intro input hinput j hj y
  have hscaled :
      ‖iteratedFDeriv ℝ j (boundedSplitTangentialCutoff input) y‖ * r ^ j ≤ A := by
    simpa [boundedSplitTangentialCutoff, r, hinput] using
      rescaledUnitBump_scaled_deriv_bound hunit 0 hr j (hj.trans (by norm_num)) y
  have hdiv : ‖iteratedFDeriv ℝ j (boundedSplitTangentialCutoff input) y‖ ≤ D j := by
    dsimp [D]
    exact (le_div_iff₀ (pow_pos hr j)).2 hscaled
  exact hdiv.trans ((Finset.le_max' ((Finset.range 7).image D) (D j)
    (Finset.mem_image_of_mem D (by simpa using Nat.lt_succ_of_le hj))).trans
      (le_max_left _ _))

theorem exists_boundedSplitComparisonQuadratic_six_deriv_bound
    (n : ℕ) (a : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ j, j ≤ 6 →
      ∀ z : ℝ × (Fin n → ℝ), ‖z‖ ≤ a →
        ‖iteratedFDeriv ℝ j (boundedSplitComparisonQuadratic (n := n)) z‖ ≤ A := by
  have hsmooth : ContDiff ℝ 6 (boundedSplitComparisonQuadratic (n := n)) :=
    boundedSplitComparisonQuadratic_contDiff.of_le (by norm_num)
  have hbound (j : ℕ) (hj : j ≤ 6) :
      ∃ K : ℝ, ∀ z ∈ Metric.closedBall (0 : ℝ × (Fin n → ℝ)) a,
        ‖iteratedFDeriv ℝ j (boundedSplitComparisonQuadratic (n := n)) z‖ ≤ K := by
    exact (isCompact_closedBall (0 : ℝ × (Fin n → ℝ)) a).exists_bound_of_continuousOn
      ((hsmooth.continuous_iteratedFDeriv (by exact_mod_cast hj)).continuousOn)
  let K : ℕ → ℝ := fun j ↦ if hj : j ≤ 6 then Classical.choose (hbound j hj) else 0
  have hK : ∀ j, j ≤ 6 → ∀ z ∈ Metric.closedBall (0 : ℝ × (Fin n → ℝ)) a,
      ‖iteratedFDeriv ℝ j (boundedSplitComparisonQuadratic (n := n)) z‖ ≤ K j := by
    intro j hj z hz
    dsimp only [K]
    rw [dif_pos hj]
    exact Classical.choose_spec (hbound j hj) z hz
  let A := max (((Finset.range 7).image K).max' (by simp)) 0
  refine ⟨A, le_max_right _ _, ?_⟩
  intro j hj z hz
  have hzball : z ∈ Metric.closedBall (0 : ℝ × (Fin n → ℝ)) a := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  exact (hK j hj z hzball).trans ((Finset.le_max' ((Finset.range 7).image K) (K j)
    (Finset.mem_image_of_mem K (by simpa using Nat.lt_succ_of_le hj))).trans
      (le_max_left _ _))


-- These normalization hypotheses are retained for a uniform derivative-bound interface.
set_option linter.unusedVariables false in
theorem exists_globalizedBoundedSplitFunction_six_deriv_bound
    (n : ℕ) (normalRadius tangentialRadius M : ℝ)
    (hnormal : 0 < normalRadius) (htangential : 0 < tangentialRadius)
    (htangentialNormal : tangentialRadius ≤ normalRadius) (hM : 0 ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (input : BoundedNormalizedLocalSplitInput n),
        input.normalRadius = normalRadius →
        input.tangentialRadius = tangentialRadius →
        (∀ z, ‖z‖ ≤ normalRadius → ∀ j, j ≤ 6 →
          ‖iteratedFDeriv ℝ j input.function z‖ ≤ M) →
        ∀ j, j ≤ 6 → ∀ z ∈ boundedSplitCylinder normalRadius tangentialRadius,
          ‖iteratedFDeriv ℝ j (globalizedBoundedSplitFunction input) z‖ ≤ A := by
  obtain ⟨Achi, hAchi, hchi⟩ :=
    exists_uniform_boundedSplitTangentialCutoff_six_deriv_bound n htangential
  obtain ⟨Aq, hAq, hq⟩ :=
    exists_boundedSplitComparisonQuadratic_six_deriv_bound n normalRadius
  let B : ℕ → ℝ := fun j ↦
    (∑ k ∈ Finset.range (j + 1), (Nat.choose j k : ℝ) * Achi * M) +
    ∑ k ∈ Finset.range (j + 1), (Nat.choose j k : ℝ) * (1 + Achi) * Aq
  let A := max (((Finset.range 7).image B).max' (by simp)) 0
  refine ⟨A, le_max_right _ _, ?_⟩
  intro input hnormalEq htangentialEq hinput j hj z hz
  let chi : (ℝ × (Fin n → ℝ)) → ℝ :=
    fun w ↦ boundedSplitTangentialCutoff input w.2
  let oneSubChi : (ℝ × (Fin n → ℝ)) → ℝ := fun w ↦ 1 - chi w
  let q := boundedSplitComparisonQuadratic (n := n)
  have hchiSmooth : ContDiff ℝ 6 chi :=
    (boundedSplitTangentialCutoff_contDiff input).comp contDiff_snd
  have honeSmooth : ContDiff ℝ 6 oneSubChi := contDiff_const.sub hchiSmooth
  have hinputSmooth : ContDiff ℝ 6 input.function := input.contDiff
  have hqSmooth : ContDiff ℝ 6 q := boundedSplitComparisonQuadratic_contDiff.of_le (by norm_num)
  have hzNorm : ‖z‖ ≤ normalRadius := by
    rw [Prod.norm_def]
    apply max_le
    · simpa [Real.norm_eq_abs] using hz.1
    · exact hz.2.trans htangentialNormal
  have hchiBound : ∀ k, k ≤ j → ‖iteratedFDeriv ℝ k chi z‖ ≤ Achi := by
    intro k hk
    simpa [chi, tangentialCoordinatePullback] using
      (norm_iteratedFDeriv_tangentialCoordinatePullback_le_six
        (boundedSplitTangentialCutoff_contDiff input)
        (hk.trans hj) z).trans
          (hchi input htangentialEq k (hk.trans hj) z.2)
  have honeBound : ∀ k, k ≤ j →
      ‖iteratedFDeriv ℝ k oneSubChi z‖ ≤ 1 + Achi := by
    intro k hk
    by_cases hkzero : k = 0
    · subst k
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      have hmem := boundedSplitTangentialCutoff_mem_Icc input z.2
      change |1 - boundedSplitTangentialCutoff input z.2| ≤ 1 + Achi
      rw [abs_of_nonneg (sub_nonneg.mpr hmem.2)]
      linarith
    · have hk6 : k ≤ 6 := hk.trans (hj.trans (by norm_num))
      have hconstSmooth : ContDiff ℝ k (fun _ : ℝ × (Fin n → ℝ) ↦ (1 : ℝ)) :=
        contDiff_const
      have hnegSmooth : ContDiff ℝ k (-chi) := hchiSmooth.neg.of_le (by exact_mod_cast hk6)
      have honeEq : oneSubChi = (fun _ : ℝ × (Fin n → ℝ) ↦ (1 : ℝ)) + (-chi) := by
        funext w
        exact sub_eq_add_neg _ _
      rw [honeEq, iteratedFDeriv_add_apply hconstSmooth.contDiffAt hnegSmooth.contDiffAt,
        show iteratedFDeriv ℝ k (fun _ : ℝ × (Fin n → ℝ) ↦ (1 : ℝ)) = 0 from
          iteratedFDeriv_const_of_ne hkzero 1,
        Pi.zero_apply, zero_add, iteratedFDeriv_neg_apply, norm_neg]
      exact (hchiBound k hk).trans (by linarith)
  have hinputBound : ∀ k, k ≤ j →
      ‖iteratedFDeriv ℝ k input.function z‖ ≤ M := by
    exact fun k hk ↦ hinput z hzNorm k (hk.trans (hj.trans (by norm_num)))
  have hqBound : ∀ k, k ≤ j →
      ‖iteratedFDeriv ℝ k q z‖ ≤ Aq := fun k hk ↦ hq k (hk.trans hj) z hzNorm
  have hfirstProduct :
      ‖iteratedFDeriv ℝ j (fun w ↦ chi w * input.function w) z‖ ≤
        ∑ k ∈ Finset.range (j + 1), (Nat.choose j k : ℝ) * Achi * M := by
    have hprod := norm_iteratedFDeriv_mul_le hchiSmooth hinputSmooth z
      (by exact_mod_cast hj.trans (by norm_num))
    calc
      _ ≤ ∑ k ∈ Finset.range (j + 1), (Nat.choose j k : ℝ) *
          ‖iteratedFDeriv ℝ k chi z‖ *
            ‖iteratedFDeriv ℝ (j - k) input.function z‖ := hprod
      _ ≤ ∑ k ∈ Finset.range (j + 1), (Nat.choose j k : ℝ) * Achi * M := by
        apply Finset.sum_le_sum
        intro k hk
        have hkj : k ≤ j := Finset.mem_range_succ_iff.mp hk
        gcongr
        · exact hchiBound k hkj
        · exact hinputBound (j - k) (Nat.sub_le j k)
  have hsecondProduct :
      ‖iteratedFDeriv ℝ j (fun w ↦ oneSubChi w * q w) z‖ ≤
        ∑ k ∈ Finset.range (j + 1),
          (Nat.choose j k : ℝ) * (1 + Achi) * Aq := by
    have hprod := norm_iteratedFDeriv_mul_le honeSmooth hqSmooth z
      (by exact_mod_cast hj.trans (by norm_num))
    calc
      _ ≤ ∑ k ∈ Finset.range (j + 1), (Nat.choose j k : ℝ) *
          ‖iteratedFDeriv ℝ k oneSubChi z‖ *
            ‖iteratedFDeriv ℝ (j - k) q z‖ := hprod
      _ ≤ ∑ k ∈ Finset.range (j + 1),
          (Nat.choose j k : ℝ) * (1 + Achi) * Aq := by
        apply Finset.sum_le_sum
        intro k hk
        have hkj : k ≤ j := Finset.mem_range_succ_iff.mp hk
        gcongr
        · exact honeBound k hkj
        · exact hqBound (j - k) (Nat.sub_le j k)
  have hfun : globalizedBoundedSplitFunction input =
      (fun w ↦ chi w * input.function w) + (fun w ↦ oneSubChi w * q w) := by
    funext w
    rfl
  have hnorm : ‖iteratedFDeriv ℝ j (globalizedBoundedSplitFunction input) z‖ ≤ B j := by
    rw [hfun, iteratedFDeriv_add_apply
      ((hchiSmooth.mul hinputSmooth).of_le (by exact_mod_cast hj) |>.contDiffAt)
      ((honeSmooth.mul hqSmooth).of_le (by exact_mod_cast hj) |>.contDiffAt)]
    exact (norm_add_le _ _).trans (by simpa [B] using add_le_add hfirstProduct hsecondProduct)
  exact hnorm.trans ((Finset.le_max' ((Finset.range 7).image B) (B j)
    (Finset.mem_image_of_mem B (by simpa using Nat.lt_succ_of_le hj))).trans
      (le_max_left _ _))
/-- Fixed input-jet bounds give a uniform Hessian bound for the explicit minimizing graph on the
bounded tangential base. -/
theorem exists_boundedUniformMinimizingGraph_second_deriv_bound
    (n : ℕ) (normalRadius tangentialRadius M : ℝ)
    (hnormal : 0 < normalRadius) (htangential : 0 < tangentialRadius)
    (htangentialNormal : tangentialRadius ≤ normalRadius) (hM : 0 ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (input : BoundedNormalizedLocalSplitInput n),
        input.normalRadius = normalRadius →
        input.tangentialRadius = tangentialRadius →
        (∀ z, ‖z‖ ≤ normalRadius → ∀ j, j ≤ 6 →
          ‖iteratedFDeriv ℝ j input.function z‖ ≤ M) → ∀ y,
        ‖y‖ ≤ tangentialRadius →
        ‖iteratedFDeriv ℝ 2 (boundedUniformMinimizingGraph input).graph y‖ ≤ A := by
  obtain ⟨Aglobal, hAglobal, hglobal⟩ :=
    exists_globalizedBoundedSplitFunction_six_deriv_bound n
      normalRadius tangentialRadius M hnormal htangential htangentialNormal hM
  let A := 4 * Aglobal * (max (4 * Aglobal) 1) ^ 2
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro input hnormalEq htangentialEq hinput y hy
  let graph := boundedUniformMinimizingGraph input
  have hgraphMem := graph.graph_point_mem y
  have hnormalGraph : |graph.graph y| ≤ normalRadius := by
    rw [(globalizedBoundedSplitInput input).cylinder_eq] at hgraphMem
    rw [← hnormalEq]
    exact abs_le.mpr hgraphMem
  have hpoint : (graph.graph y, y) ∈
      boundedSplitCylinder normalRadius tangentialRadius := ⟨hnormalGraph, hy⟩
  apply graph.norm_iteratedFDeriv_two_graph_le_of_third_deriv_bound
  · exact hglobal input hnormalEq htangentialEq hinput 2 (by norm_num) _ hpoint
  · exact hglobal input hnormalEq htangentialEq hinput 3 (by norm_num) _ hpoint
/-- Every affine normal segment used by the raw Taylor coefficient stays in the fixed bounded
cylinder when its endpoint lies in the root region. -/
theorem boundedUniform_localSquareCoefficientPath_mem
    {n : ℕ} (input : BoundedNormalizedLocalSplitInput n)
    (htangentialNormal : input.tangentialRadius ≤ input.normalRadius)
    (z : ℝ × (Fin n → ℝ)) (hz : ‖z‖ ≤ input.tangentialRadius / 4)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    localSquareCoefficientPath (boundedUniformMinimizingGraph input) s z ∈
      boundedSplitCylinder input.normalRadius input.tangentialRadius := by
  let graph := boundedUniformMinimizingGraph input
  have hgraphMem := graph.graph_point_mem z.2
  have hgraphAbs : |graph.graph z.2| ≤ input.normalRadius := by
    rw [(globalizedBoundedSplitInput input).cylinder_eq] at hgraphMem
    exact abs_le.mpr hgraphMem
  have hzFirst : |z.1| ≤ input.normalRadius := by
    have hfirst : |z.1| ≤ ‖z‖ := by
      rw [Prod.norm_def]
      simp [Real.norm_eq_abs]
    exact hfirst.trans (hz.trans ((div_le_self input.tangentialRadius_pos.le
      (by norm_num)).trans htangentialNormal))
  have hzSecond : ‖z.2‖ ≤ input.tangentialRadius := by
    calc
      ‖z.2‖ ≤ ‖z‖ := by rw [Prod.norm_def]; exact le_max_right _ _
      _ ≤ input.tangentialRadius / 4 := hz
      _ ≤ input.tangentialRadius := div_le_self input.tangentialRadius_pos.le (by norm_num)
  constructor
  · change |graph.graph z.2 + s * (z.1 - graph.graph z.2)| ≤ input.normalRadius
    rw [show graph.graph z.2 + s * (z.1 - graph.graph z.2) =
      (1 - s) * graph.graph z.2 + s * z.1 by ring]
    calc
      |(1 - s) * graph.graph z.2 + s * z.1| ≤
          |1 - s| * |graph.graph z.2| + |s| * |z.1| := by
        simpa [abs_mul] using abs_add_le ((1 - s) * graph.graph z.2) (s * z.1)
      _ ≤ (1 - s) * input.normalRadius + s * input.normalRadius := by
        rw [abs_of_nonneg (sub_nonneg.mpr hs.2), abs_of_nonneg hs.1]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hgraphAbs (sub_nonneg.mpr hs.2))
          (mul_le_mul_of_nonneg_left hzFirst hs.1)
      _ = input.normalRadius := by ring
  · change ‖z.2‖ ≤ input.tangentialRadius
    exact hzSecond
-- Lower-bound hypotheses are kept explicit to match the recurrence interface used by callers.
set_option linter.unusedVariables false in
/-- Once the graph lift has power-form jets, the stationarity identity bounds every positive
residual jet through order six using one fewer chain-rule differentiation. -/
theorem BoundedUniformLocalSplitData.norm_iteratedFDeriv_residual_le_of_lift_jets
    {n : ℕ} {input : BoundedNormalizedLocalSplitInput n}
    (data : BoundedUniformLocalSplitData input) (y : Fin n → ℝ)
    {M B : ℝ} (hM : 1 ≤ M) (hB : 1 ≤ B)
    (hambient : ∀ k, k ≤ 6 →
      ‖iteratedFDeriv ℝ k (globalizedBoundedSplitInput input).function
        (data.graph.graph y, y)‖ ≤ M)
    (hlift : ∀ k, 1 ≤ k → k ≤ 5 →
      ‖iteratedFDeriv ℝ k (fun w ↦ (data.graph.graph w, w)) y‖ ≤ B ^ k)
    {j : ℕ} (hjOne : 1 ≤ j) (hj : j ≤ 6) :
    ‖iteratedFDeriv ℝ j data.residual y‖ ≤
      (j - 1).factorial * M * B ^ (j - 1) := by
  let F := (globalizedBoundedSplitInput input).function
  let G : (Fin n → ℝ) → (ℝ × (Fin n → ℝ)) :=
    fun w ↦ (data.graph.graph w, w)
  let T : (Fin n → ℝ) →L[ℝ] (ℝ × (Fin n → ℝ)) :=
    ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)
  let P : (((ℝ × (Fin n → ℝ)) →L[ℝ] ℝ) →L[ℝ]
      ((Fin n → ℝ) →L[ℝ] ℝ)) :=
    (ContinuousLinearMap.compL ℝ (Fin n → ℝ)
      (ℝ × (Fin n → ℝ)) ℝ).flip T
  let H := (fderiv ℝ F) ∘ G
  have hFderiv : ContDiff ℝ 5 (fderiv ℝ F) := by
    exact (globalizedBoundedSplitInput input).contDiff.fderiv_right
      (m := 5) (by norm_num)
  have hG : ContDiff ℝ 5 G := data.graph.graph_contDiff.prodMk contDiff_id
  have hH : ContDiff ℝ 5 H := hFderiv.comp hG
  have hjSub : j - 1 ≤ 5 := by omega
  have hcomp : ‖iteratedFDeriv ℝ (j - 1) H y‖ ≤
      (j - 1).factorial * M * B ^ (j - 1) := by
    apply norm_iteratedFDeriv_comp_le hFderiv hG
      (by exact_mod_cast hjSub) y
    · intro q hq
      rw [norm_iteratedFDeriv_fderiv]
      exact hambient (q + 1) (by omega)
    · intro q hqOne hq
      exact hlift q hqOne (hq.trans hjSub)
  have hTnorm : ‖T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    change ‖((0 : ℝ), v)‖ ≤ 1 * ‖v‖
    simp [Prod.norm_def]
  have hPnorm : ‖P‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro L
    change ‖L.comp T‖ ≤ 1 * ‖L‖
    calc
      ‖L.comp T‖ ≤ ‖L‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le L T
      _ ≤ ‖L‖ * 1 := mul_le_mul_of_nonneg_left hTnorm (norm_nonneg L)
      _ = 1 * ‖L‖ := by ring
  have hfirst : fderiv ℝ data.residual = P ∘ H := by
    funext w
    simpa [P, H, F, G, T] using data.fderiv_residual_eq_tangential w
  have hpost : ‖iteratedFDeriv ℝ (j - 1) (P ∘ H) y‖ ≤
      ‖P‖ * ‖iteratedFDeriv ℝ (j - 1) H y‖ :=
    P.norm_iteratedFDeriv_comp_left hH.contDiffAt (by exact_mod_cast hjSub)
  calc
    ‖iteratedFDeriv ℝ j data.residual y‖ =
        ‖iteratedFDeriv ℝ (j - 1) (fderiv ℝ data.residual) y‖ := by
      rw [norm_iteratedFDeriv_fderiv, Nat.sub_add_cancel hjOne]
    _ = ‖iteratedFDeriv ℝ (j - 1) (P ∘ H) y‖ := by rw [hfirst]
    _ ≤ ‖P‖ * ‖iteratedFDeriv ℝ (j - 1) H y‖ := hpost
    _ ≤ 1 * ((j - 1).factorial * M * B ^ (j - 1)) := by gcongr
    _ = (j - 1).factorial * M * B ^ (j - 1) := one_mul _
/-- The preceding residual estimate is global because the bounded split residual is supported
inside the fixed tangential base. -/
theorem BoundedUniformLocalSplitData.norm_iteratedFDeriv_residual_le_global_of_lift_jets
    {n : ℕ} {input : BoundedNormalizedLocalSplitInput n}
    (data : BoundedUniformLocalSplitData input) {M B : ℝ}
    (hM : 1 ≤ M) (hB : 1 ≤ B)
    (hambient : ∀ y, ‖y‖ ≤ input.tangentialRadius → ∀ k, k ≤ 6 →
      ‖iteratedFDeriv ℝ k (globalizedBoundedSplitInput input).function
        (data.graph.graph y, y)‖ ≤ M)
    (hlift : ∀ y, ‖y‖ ≤ input.tangentialRadius → ∀ k, 1 ≤ k → k ≤ 5 →
      ‖iteratedFDeriv ℝ k (fun w ↦ (data.graph.graph w, w)) y‖ ≤ B ^ k)
    {j : ℕ} (hjOne : 1 ≤ j) (hj : j ≤ 6) (y : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ j data.residual y‖ ≤
      (j - 1).factorial * M * B ^ (j - 1) := by
  by_cases hy : ‖y‖ ≤ input.tangentialRadius
  · exact data.norm_iteratedFDeriv_residual_le_of_lift_jets y hM hB
      (hambient y hy) (hlift y hy) hjOne hj
  · have hresidualSupport : Function.support data.residual ⊆
        Function.support (boundedSplitTangentialCutoff input) := by
      intro w hw hcut
      exact hw (data.residual_eq_zero_of_tangentialCutoff_eq_zero w hcut)
    have hcutoffSupport : Function.support (boundedSplitTangentialCutoff input) =
        Metric.ball (0 : Fin n → ℝ) input.tangentialRadius := by
      rw [boundedSplitTangentialCutoff,
        support_rescaledUnitBump 0 (div_pos input.tangentialRadius_pos (by norm_num))]
      congr 1
      ring
    have hresidualTopologicalSupport : tsupport data.residual ⊆
        Metric.closedBall (0 : Fin n → ℝ) input.tangentialRadius := by
      apply closure_minimal
      · intro w hw
        exact Metric.ball_subset_closedBall (hcutoffSupport ▸ hresidualSupport hw)
      · exact Metric.isClosed_closedBall
    have hyBall : y ∉ Metric.closedBall (0 : Fin n → ℝ) input.tangentialRadius := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hy
    have hyTopological : y ∉ tsupport data.residual :=
      fun hmem ↦ hyBall (hresidualTopologicalSupport hmem)
    have hyDeriv : y ∉ Function.support (iteratedFDeriv ℝ j data.residual) :=
      fun hmem ↦ hyTopological (support_iteratedFDeriv_subset j hmem)
    have hzero : iteratedFDeriv ℝ j data.residual y = 0 := by
      simpa [Function.mem_support] using hyDeriv
    rw [hzero, norm_zero]
    positivity
/-- Core derivative bounds expressed for a bounded input, independently of its geometric
origin. -/
structure BoundedLocalSplitCoreDerivativeBounds {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n)
    (rootRegionRadius Aroot Aresidual : ℝ) : Prop where
  root_local_jets : ∀ z, ‖z‖ ≤ rootRegionRadius →
    ∀ j, j ≤ 4 →
      ‖iteratedFDeriv ℝ j (boundedUniformLocalSplitData input).root z‖ ≤ Aroot
  residual_global_jets : ∀ j, j ≤ 6 → ∀ y,
    ‖iteratedFDeriv ℝ j (boundedUniformLocalSplitData input).residual y‖ ≤ Aresidual

/-- Remaining derivative bounds after treating residual orders one and two directly; zeroth-order
bounds follow directly from exactness, nonnegativity, and the input value bound. -/
structure BoundedLocalSplitPositiveDerivativeBounds {n : ℕ}
    (input : BoundedNormalizedLocalSplitInput n)
    (rootRegionRadius Aroot Aresidual : ℝ) : Prop where
  root_positive_jets : ∀ z, ‖z‖ ≤ rootRegionRadius →
    ∀ j, 1 ≤ j → j ≤ 4 →
      ‖iteratedFDeriv ℝ j (boundedUniformLocalSplitData input).root z‖ ≤ Aroot
  residual_positive_jets : ∀ j, 3 ≤ j → j ≤ 6 → ∀ y,
    ‖iteratedFDeriv ℝ j (boundedUniformLocalSplitData input).residual y‖ ≤ Aresidual

/-- The remaining quantitative IFT/Taylor estimate for positive root derivatives and residual
derivatives of order at least three. -/
theorem uniformBoundedLocalSplitPositiveDerivativeBounds_of_functionJets
    (n : ℕ) (normalRadius tangentialRadius M : ℝ)
    (hnormal : 0 < normalRadius) (htangential : 0 < tangentialRadius)
    (htangentialNormal : tangentialRadius ≤ normalRadius) (hM : 0 ≤ M) :
    ∃ Aroot Aresidual : ℝ, 0 ≤ Aroot ∧ 0 ≤ Aresidual ∧
      ∀ (input : BoundedNormalizedLocalSplitInput n),
        input.normalRadius = normalRadius →
        input.tangentialRadius = tangentialRadius →
        (∀ z, ‖z‖ ≤ normalRadius → ∀ j, j ≤ 6 →
          ‖iteratedFDeriv ℝ j input.function z‖ ≤ M) →
        BoundedLocalSplitPositiveDerivativeBounds input
          (tangentialRadius / 4) Aroot Aresidual := by
  obtain ⟨Aglobal, hAglobal, hglobal⟩ :=
    exists_globalizedBoundedSplitFunction_six_deriv_bound n
      normalRadius tangentialRadius M hnormal htangential htangentialNormal hM
  let Mglobal := max Aglobal 1
  have hMglobal : 1 ≤ Mglobal := le_max_right _ _
  obtain ⟨Bgraph, hBgraph, hgraphBound⟩ :=
    exists_uniform_minimizingGraph_five_deriv_bound Mglobal hMglobal
  obtain ⟨Aroot, hAroot, hrootBound⟩ :=
    exists_uniform_explicitLocalSplitRoot_deriv_bound
      (1 / 8) normalRadius Mglobal Bgraph (by norm_num)
        (zero_le_one.trans hMglobal) hBgraph
  let residualBound : ℕ → ℝ := fun j ↦
    (j - 1).factorial * Mglobal * Bgraph ^ (j - 1)
  let Aresidual := max (((Finset.range 7).image residualBound).max' (by simp)) 0
  have hAresidual : 0 ≤ Aresidual := le_max_right _ _
  refine ⟨Aroot, Aresidual, hAroot, hAresidual, ?_⟩
  intro input hnormalEq htangentialEq hinput
  let graph := boundedUniformMinimizingGraph input
  let data := boundedUniformLocalSplitData input
  have hgraphPoint (y : Fin n → ℝ) (hy : ‖y‖ ≤ tangentialRadius) :
      implicitGraphLift graph y ∈
        boundedSplitCylinder normalRadius tangentialRadius := by
    have hmem := graph.graph_point_mem y
    have hnormalGraph : |graph.graph y| ≤ normalRadius := by
      rw [(globalizedBoundedSplitInput input).cylinder_eq] at hmem
      rw [← hnormalEq]
      exact abs_le.mpr hmem
    exact ⟨hnormalGraph, hy⟩
  have hambientGraph (y : Fin n → ℝ) (hy : ‖y‖ ≤ tangentialRadius)
      (k : ℕ) (hk : k ≤ 6) :
      ‖iteratedFDeriv ℝ k (globalizedBoundedSplitInput input).function
        (implicitGraphLift graph y)‖ ≤ Mglobal := by
    exact (hglobal input hnormalEq htangentialEq hinput k hk _
      (hgraphPoint y hy)).trans (le_max_left _ _)
  have hgraphJets (y : Fin n → ℝ) (hy : ‖y‖ ≤ tangentialRadius)
      (q : ℕ) (hqOne : 1 ≤ q) (hq : q ≤ 5) :
      ‖iteratedFDeriv ℝ q graph.graph y‖ ≤ Bgraph := by
    exact hgraphBound graph y (hambientGraph y hy) q hqOne hq
  refine {
    root_positive_jets := ?_
    residual_positive_jets := ?_ }
  · intro z hz j hjOne hj
    have hzSecond : ‖z.2‖ ≤ tangentialRadius := by
      calc
        ‖z.2‖ ≤ ‖z‖ := by rw [Prod.norm_def]; exact le_max_right _ _
        _ ≤ tangentialRadius / 4 := hz
        _ ≤ tangentialRadius := by linarith
    have hzFirst : |z.1| ≤ normalRadius := by
      have hfirst : |z.1| ≤ ‖z‖ := by
        rw [Prod.norm_def]
        simp [Real.norm_eq_abs]
      exact hfirst.trans (hz.trans ((div_le_self htangential.le (by norm_num)).trans
        htangentialNormal))
    have hgraphValue : |graph.graph z.2| ≤ normalRadius := by
      have hmem := graph.graph_point_mem z.2
      rw [(globalizedBoundedSplitInput input).cylinder_eq] at hmem
      rw [← hnormalEq]
      exact abs_le.mpr hmem
    have hfunctionPath (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
        (k : ℕ) (hk : k ≤ 6) :
        ‖iteratedFDeriv ℝ k (globalizedBoundedSplitInput input).function
          (localSquareCoefficientPath graph s z)‖ ≤ Mglobal := by
      have hpathInput := boundedUniform_localSquareCoefficientPath_mem input
        (by simpa [hnormalEq, htangentialEq] using htangentialNormal) z
        (by simpa [htangentialEq] using hz) s hs
      have hpath : localSquareCoefficientPath graph s z ∈
          boundedSplitCylinder normalRadius tangentialRadius := by
        simpa [hnormalEq, htangentialEq] using hpathInput
      exact (hglobal input hnormalEq htangentialEq hinput k hk _ hpath).trans
        (le_max_left _ _)
    have hroot := hrootBound (globalizedBoundedSplitInput input) graph z
      hzFirst hgraphValue hfunctionPath
      (fun k hkOne hk ↦ hgraphJets z.2 hzSecond k hkOne (hk.trans (by norm_num)))
      j hj
    change ‖iteratedFDeriv ℝ j (explicitBoundedUniformRoot input) z‖ ≤ Aroot
    have hrootEq : explicitBoundedUniformRoot input =
        explicitLocalSplitRoot (1 / 8) (globalizedBoundedSplitInput input) graph := by
      rfl
    rw [hrootEq]
    exact hroot
  · intro j hjThree hj y
    have hambientData : ∀ w, ‖w‖ ≤ input.tangentialRadius → ∀ k, k ≤ 6 →
        ‖iteratedFDeriv ℝ k (globalizedBoundedSplitInput input).function
          (data.graph.graph w, w)‖ ≤ Mglobal := by
      intro w hw k hk
      have hw' : ‖w‖ ≤ tangentialRadius := by simpa [htangentialEq] using hw
      simpa [data, graph, implicitGraphLift] using hambientGraph w hw' k hk
    have hliftData : ∀ w, ‖w‖ ≤ input.tangentialRadius → ∀ k, 1 ≤ k → k ≤ 5 →
        ‖iteratedFDeriv ℝ k (fun v ↦ (data.graph.graph v, v)) w‖ ≤ Bgraph ^ k := by
      intro w hw k hkOne hk
      have hw' : ‖w‖ ≤ tangentialRadius := by simpa [htangentialEq] using hw
      have h := norm_iteratedFDeriv_implicitGraphLift_le graph w hBgraph
        (fun q hqOne hq ↦ hgraphJets w hw' q hqOne (hq.trans hk)) hkOne hk
      simpa [data, graph, implicitGraphLift] using h
    have hresidual := data.norm_iteratedFDeriv_residual_le_global_of_lift_jets
      hMglobal hBgraph hambientData hliftData (by omega) hj y
    exact hresidual.trans
      ((Finset.le_max' ((Finset.range 7).image residualBound) (residualBound j)
        (Finset.mem_image_of_mem residualBound
          (by simpa using Nat.lt_succ_of_le hj))).trans (le_max_left _ _))
/-- Quantitative bounded-cylinder implicit-function theorem for the explicit construction in
`boundedUniformLocalSplitData`.  The radii and the common input C6 bound are the complete
quantitative parameters. -/
theorem uniformBoundedLocalSplitCoreDerivativeBounds_of_functionJets
    (n : ℕ) (normalRadius tangentialRadius M : ℝ)
    (hnormal : 0 < normalRadius) (htangential : 0 < tangentialRadius)
    (htangentialNormal : tangentialRadius ≤ normalRadius) (hM : 0 ≤ M) :
    ∃ Aroot Aresidual : ℝ, 0 ≤ Aroot ∧ 0 ≤ Aresidual ∧
      ∀ (input : BoundedNormalizedLocalSplitInput n),
        input.normalRadius = normalRadius →
        input.tangentialRadius = tangentialRadius →
        (∀ z, ‖z‖ ≤ normalRadius → ∀ j, j ≤ 6 →
          ‖iteratedFDeriv ℝ j input.function z‖ ≤ M) →
        BoundedLocalSplitCoreDerivativeBounds input
          (tangentialRadius / 4) Aroot Aresidual := by
  obtain ⟨Aroot, Aresidual, hAroot, hAresidual, hpositive⟩ :=
    uniformBoundedLocalSplitPositiveDerivativeBounds_of_functionJets n
      normalRadius tangentialRadius M hnormal htangential htangentialNormal hM
  obtain ⟨AresidualFirst, hAresidualFirst, hresidualFirst⟩ :=
    exists_boundedUniformLocalSplitData_residual_first_deriv_bound n
      normalRadius tangentialRadius M hnormal htangential htangentialNormal hM
  obtain ⟨AresidualSecond, hAresidualSecond, hresidualSecond⟩ :=
    exists_boundedUniformLocalSplitData_residual_second_deriv_bound n
      normalRadius tangentialRadius M hnormal htangential htangentialNormal hM
  let ArootOut := max Aroot (Real.sqrt M)
  let AresidualOut := max (max (max Aresidual AresidualFirst) AresidualSecond) M
  have hArootOut : 0 ≤ ArootOut := hAroot.trans (le_max_left _ _)
  have hAresidualOut : 0 ≤ AresidualOut := by
    exact hAresidual.trans
      (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _))
  refine ⟨ArootOut, AresidualOut, hArootOut, hAresidualOut, ?_⟩
  intro input hnormalEq htangentialEq hinput
  let data := boundedUniformLocalSplitData input
  have hpositiveInput := hpositive input hnormalEq htangentialEq hinput
  have hresidualFirstInput := hresidualFirst input hnormalEq htangentialEq hinput
  have hresidualSecondInput := hresidualSecond input hnormalEq htangentialEq hinput
  refine {
    root_local_jets := ?_
    residual_global_jets := ?_ }
  · intro z hz j hj
    by_cases hjzero : j = 0
    · subst j
      have hzNormal : ‖z‖ ≤ normalRadius := by
        calc
          ‖z‖ ≤ tangentialRadius / 4 := hz
          _ ≤ tangentialRadius := by nlinarith
          _ ≤ normalRadius := htangentialNormal
      have hzCylinder : z ∈ boundedSplitCylinder input.normalRadius
          (input.tangentialRadius / 2) := by
        have hfirst : |z.1| ≤ ‖z‖ := by
          rw [Prod.norm_def]
          simp [Real.norm_eq_abs]
        have hsecond : ‖z.2‖ ≤ ‖z‖ := by
          rw [Prod.norm_def]
          exact le_max_right _ _
        constructor
        · rw [hnormalEq]
          exact hfirst.trans hzNormal
        · rw [htangentialEq]
          exact hsecond.trans (hz.trans (by nlinarith))
      have hsquare := data.exact_square z hzCylinder
      have hrootSq : data.root z ^ 2 ≤ input.function z := by
        nlinarith [data.residual_nonnegative z.2]
      have hvalueNorm := hinput z hzNormal 0 (by norm_num)
      have hvalue : input.function z ≤ M := by
        simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs,
          abs_of_nonneg (input.nonnegative z)] using hvalueNorm
      have hrootSqM : data.root z ^ 2 ≤ (Real.sqrt M) ^ 2 := by
        rw [Real.sq_sqrt hM]
        exact hrootSq.trans hvalue
      have hrootAbs : |data.root z| ≤ Real.sqrt M :=
        abs_le_of_sq_le_sq hrootSqM (Real.sqrt_nonneg M)
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      exact hrootAbs.trans (le_max_right Aroot (Real.sqrt M))
    · exact (hpositiveInput.root_positive_jets z hz j
        (Nat.one_le_iff_ne_zero.mpr hjzero) hj).trans (le_max_left _ _)
  · intro j hj y
    by_cases hjzero : j = 0
    · subst j
      by_cases hcut : boundedSplitTangentialCutoff input y = 0
      · have hzero := data.residual_eq_zero_of_tangentialCutoff_eq_zero y hcut
        rw [norm_iteratedFDeriv_zero]
        change ‖data.residual y‖ ≤ AresidualOut
        rw [hzero, norm_zero]
        exact hAresidualOut
      · have hylt :=
          norm_lt_tangentialRadius_of_boundedSplitTangentialCutoff_ne_zero input hcut
        have hyNormal : ‖y‖ ≤ normalRadius := by
          calc
            ‖y‖ ≤ input.tangentialRadius := hylt.le
            _ = tangentialRadius := htangentialEq
            _ ≤ normalRadius := htangentialNormal
        have hpair : ‖((0 : ℝ), y)‖ ≤ normalRadius := by
          rw [Prod.norm_def]
          simpa using hyNormal
        have hvalueNorm := hinput ((0 : ℝ), y) hpair 0 (by norm_num)
        have hvalue : input.function (0, y) ≤ M := by
          simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs,
            abs_of_nonneg (input.nonnegative (0, y))] using hvalueNorm
        have hres : data.residual y ≤ M := (data.residual_le_center y).trans hvalue
        have hresNorm : ‖data.residual y‖ ≤ M := by
          simpa [Real.norm_eq_abs, abs_of_nonneg (data.residual_nonnegative y)] using hres
        rw [norm_iteratedFDeriv_zero]
        exact hresNorm.trans (le_max_right (max (max Aresidual AresidualFirst) AresidualSecond) M)
    · by_cases hjone : j = 1
      · subst j
        exact (hresidualFirstInput y).trans
          (((le_max_right Aresidual AresidualFirst).trans (le_max_left _ _)).trans
            (le_max_left _ _))
      · by_cases hjtwo : j = 2
        · subst j
          exact (hresidualSecondInput y).trans
            ((le_max_right (max Aresidual AresidualFirst) AresidualSecond).trans
              (le_max_left _ _))
        · exact (hpositiveInput.residual_positive_jets j (by omega) hj y).trans
            (((le_max_left Aresidual AresidualFirst).trans (le_max_left _ _)).trans
              (le_max_left _ _))
/-- The irreducible quantitative implicit-function content: local jets of the canonical square
root and global jets of its compactly supported envelope residual. -/
structure BoundedSplitCoreDerivativeBounds
    {n : ℕ} {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    (prep : IntrinsicBoundedSplitPreprocessing n Φ C)
    (Aroot Aresidual : ℝ) : Prop where
  root_local_jets : ∀ z,
    ‖z‖ ≤ positiveCurvatureTangentialRadius C / 4 →
      ∀ j, j ≤ 4 →
        ‖iteratedFDeriv ℝ j
          (boundedUniformLocalSplitData prep.input).root z‖ ≤ Aroot
  residual_global_jets : ∀ j, j ≤ 6 → ∀ y,
    ‖iteratedFDeriv ℝ j
      (boundedUniformLocalSplitData prep.input).residual y‖ ≤ Aresidual

-- The quantified analytic inputs document the normalized family consumed by this interface.
set_option linter.unusedVariables false in
/-- Uniform core estimates for the explicit minimizing graph, integral Taylor coefficient, and
envelope.  This is precisely the remaining quantitative implicit-function theorem. -/
theorem uniformBoundedSplitCoreDerivativeBounds
    (n : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    ∃ Aroot Aresidual : ℝ,
      0 ≤ Aroot ∧ 0 ≤ Aresidual ∧
      ∀ {u : (Fin (n + 1) → ℝ) → ℝ}
        (hu : NormalizedNonnegativeC6 u)
        (hcontrol : NonnegativeJetControl u C)
        (c : Fin (n + 1) → ℝ)
        (hR : 0 < nonnegativeJetScale u c)
        (prep : IntrinsicBoundedSplitPreprocessing n
          (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) C),
        BoundedSplitCoreDerivativeBounds prep Aroot Aresidual := by
  obtain ⟨Aroot, Aresidual, hAroot, hAresidual, hbounded⟩ :=
    uniformBoundedLocalSplitCoreDerivativeBounds_of_functionJets n
      (positiveCurvatureCoordinateRadius C)
      (positiveCurvatureTangentialRadius C) (512 * (C + 1))
      (positiveCurvatureCoordinateRadius_pos hC)
      (positiveCurvatureTangentialRadius_pos hC)
      (positiveCurvatureTangentialRadius_le_coordinateRadius hC)
      (by positivity : 0 ≤ 512 * (C + 1))
  refine ⟨Aroot, Aresidual, hAroot, hAresidual, ?_⟩
  intro u hu hcontrol c hR prep
  have hb := hbounded prep.input prep.normalRadius_eq prep.tangentialRadius_eq ?_
  · exact {
      root_local_jets := by
        intro z hz j hj
        exact hb.root_local_jets z hz j hj
      residual_global_jets := hb.residual_global_jets }
  · intro z hz j hj
    exact intrinsicBoundedSplitInput_uniform_deriv_on_coordinateBall
      hu hcontrol c hR prep hz j hj
/-- The two genuinely analytic estimates needed for the canonical bounded split.  Keeping these
estimates separate ensures that the exact square identity and residual nonnegativity are not
hidden behind the quantitative analytic input. -/
structure BoundedSplitAnalyticDerivativeBounds
    {n : ℕ} {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    (prep : IntrinsicBoundedSplitPreprocessing n Φ C)
    (cutoff : (Fin (n + 1) → ℝ) → ℝ)
    (parentRadius Mmain Aresidual : ℝ) : Prop where
  main_scaled_jets : ∀ j, j ≤ 4 → ∀ x,
    ‖iteratedFDeriv ℝ j
        (curvatureMainRoot prep cutoff
          (boundedUniformLocalSplitData prep.input).root) x‖ *
      (2 * parentRadius) ^ j ≤ Mmain * (2 * parentRadius) ^ 2
  residual_global_jets : ∀ j, j ≤ 6 → ∀ y,
    ‖iteratedFDeriv ℝ j
      (boundedUniformLocalSplitData prep.input).residual y‖ ≤ Aresidual

-- Cover hypotheses remain explicit to keep this theorem interchangeable with later refinements.
set_option linter.unusedVariables false in
/-- Uniform quantitative implicit-function and square-root estimates for the explicit canonical
bounded split.  This estimate is proved by the graph five-jet recurrence together with the concrete
globalization and assembly arguments. -/
theorem uniformBoundedSplitAnalyticDerivativeBounds
    (n : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    ∀ parentA : ℝ, 1 ≤ parentA →
      ∃ Mmain Aresidual : ℝ,
        0 ≤ Mmain ∧ 0 ≤ Aresidual ∧
        ∀ {u : (Fin (n + 1) → ℝ) → ℝ}
          (hu : NormalizedNonnegativeC6 u)
          (hcontrol : NonnegativeJetControl u C)
          {parentDilation sigma : ℝ} {parentB : ℕ}
          (cover : FineQuantitativeScaleCover
            u parentDilation sigma parentA parentB)
          {i : ℕ} (hi : i ∈ cover.active)
          (hsigma : sigma ≤ boundedSplitSigmaMax C)
          (prep : IntrinsicBoundedSplitPreprocessing n
            (intrinsicRescaledPatch u (cover.center i)
              (nonnegativeJetScale u (cover.center i))) C),
          BoundedSplitAnalyticDerivativeBounds prep (cover.intrinsicCutoff i)
            (cover.radius i / nonnegativeJetScale u (cover.center i))
            Mmain Aresidual := by
  obtain ⟨Aroot, Aresidual, hAroot, hAresidual, hcore⟩ :=
    uniformBoundedSplitCoreDerivativeBounds n hC
  intro parentA hparentA
  let Aglobal := 256 * parentA ^ 7 * Aroot
  let Mmain := Aglobal * parentA ^ 2
  have hAglobal : 0 ≤ Aglobal := by
    dsimp [Aglobal]
    positivity
  have hMmain : 0 ≤ Mmain := mul_nonneg hAglobal (sq_nonneg parentA)
  refine ⟨Mmain, Aresidual, hMmain, hAresidual, ?_⟩
  intro u hu hcontrol parentDilation sigma parentB cover i hi hsigma prep
  have hR : 0 < nonnegativeJetScale u (cover.center i) :=
    (cover.radius_pos i hi).trans_le (cover.radius_comparable i hi).1
  have hc := hcore hu hcontrol (cover.center i) hR prep
  let q := cover.radius i / nonnegativeJetScale u (cover.center i)
  have hq : 0 < q := by simpa [q] using cover.radiusRatio_pos hi
  have hparentApos : 0 < parentA := lt_of_lt_of_le zero_lt_one hparentA
  have hqLower : parentA⁻¹ ≤ q := by
    simpa [q] using cover.inv_le_radiusRatio hi hparentApos
  have hqSigma : q ≤ sigma := by
    dsimp [q]
    rw [div_le_iff₀ hR]
    exact cover.radius_le_fine i hi
  have hqHalf : q ≤ 1 / 2 :=
    hqSigma.trans (hsigma.trans (boundedSplitSigmaMax_le_half C))
  refine {
    main_scaled_jets := ?_
    residual_global_jets := hc.residual_global_jets }
  have hglobal : ∀ j, j ≤ 4 → ∀ x,
      ‖iteratedFDeriv ℝ j
        (curvatureMainRoot prep (cover.intrinsicCutoff i)
          (boundedUniformLocalSplitData prep.input).root) x‖ ≤ Aglobal := by
    simpa [Aglobal] using curvatureMainRoot_uniform_deriv_bound_of_local
      cover hi prep hparentA hAroot hsigma hc.root_local_jets
  simpa [q, Mmain] using
    scaled_four_jet_bound_of_global_bound hq hqLower hqHalf hparentA hAglobal hglobal

-- Cover hypotheses remain explicit to preserve the assembly-level public interface.
set_option linter.unusedVariables false in
/-- Uniform quantitative curvature-split data for every bounded-preprocessing parent in an
actual sufficiently fine cover.  All identities, supports, and nonnegativity fields are proved;
the only analytic input is `uniformBoundedSplitAnalyticDerivativeBounds`. -/
theorem exists_uniformFineCoverQuantitativeCurvatureSplitOutput
    (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (parentA : ℝ) (hparentA : 1 ≤ parentA) :
    ∃ Mmain Azeta Aresidual : ℝ,
      0 ≤ Mmain ∧ 0 ≤ Azeta ∧ 0 ≤ Aresidual ∧
      ∀ {u : (Fin (n + 1) → ℝ) → ℝ}
        (hu : NormalizedNonnegativeC6 u)
        (hcontrol : NonnegativeJetControl u C)
        {parentDilation sigma : ℝ} {parentB : ℕ}
        (cover : FineQuantitativeScaleCover
          u parentDilation sigma parentA parentB)
        {i : ℕ} (hi : i ∈ cover.active)
        (hsigma : sigma ≤ boundedSplitSigmaMax C)
        (prep : IntrinsicBoundedSplitPreprocessing n
          (intrinsicRescaledPatch u (cover.center i)
            (nonnegativeJetScale u (cover.center i))) C),
        Nonempty (QuantitativeCurvatureSplitOutput prep (cover.intrinsicCutoff i)
          (cover.radius i / nonnegativeJetScale u (cover.center i))
          Mmain Azeta Aresidual) := by
  obtain ⟨Mmain, Aresidual, hMmain, hAresidual, hbounds⟩ :=
    uniformBoundedSplitAnalyticDerivativeBounds n hC parentA hparentA
  obtain ⟨Azeta, hAzeta, hzeta⟩ :=
    exists_uniform_boundedSplitResidualCutoff_deriv_bound n hC
  refine ⟨Mmain, Azeta, Aresidual, hMmain, hAzeta, hAresidual, ?_⟩
  intro u hu hcontrol parentDilation sigma parentB cover i hi hsigma prep
  have hb := hbounds hu hcontrol cover hi hsigma prep
  refine ⟨quantitativeCurvatureSplitOutputOfBounds prep (cover.intrinsicCutoff i)
    (cover.radius i / nonnegativeJetScale u (cover.center i))
    Mmain Azeta Aresidual ?_ hb.main_scaled_jets (hzeta prep)
      hb.residual_global_jets⟩
  intro z hz
  exact intrinsicCutoff_in_boundedSplitInner cover hi prep hC hsigma hz
/-- Every concrete bounded split and compact parent cutoff has quantitative constants.  This
pointwise theorem deliberately makes no claim that the constants are uniform in the input. -/
theorem exists_quantitativeCurvatureSplitOutput
    {n : ℕ} {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    (prep : IntrinsicBoundedSplitPreprocessing n Φ C)
    {cutoff : (Fin (n + 1) → ℝ) → ℝ} {parentRadius : ℝ}
    (hparentRadius : 0 < parentRadius)
    (hcutoffSmooth : ContDiff ℝ 4 cutoff) (hcutoffCompact : HasCompactSupport cutoff)
    (hcutoffInner : ∀ z,
      cutoff (unitDirectionCoordinateFrame prep.direction prep.direction_norm z) ≠ 0 →
        z ∈ boundedSplitCylinder prep.input.normalRadius
          (prep.input.tangentialRadius / 4)) :
    ∃ Mmain Azeta Aresidual : ℝ,
      0 ≤ Mmain ∧ 0 ≤ Azeta ∧ 0 ≤ Aresidual ∧
        Nonempty (QuantitativeCurvatureSplitOutput prep cutoff
          parentRadius Mmain Azeta Aresidual) := by
  let data := Classical.choice (boundedUniformLocalSplit n prep.input)
  let zeta := boundedSplitResidualCutoff prep.input
  have hmainSmooth : ContDiff ℝ 4 (curvatureMainRoot prep cutoff data.root) :=
    curvatureMainRoot_contDiff prep hcutoffSmooth data.root_contDiff
  have hmainCompact : HasCompactSupport (curvatureMainRoot prep cutoff data.root) :=
    curvatureMainRoot_compactSupport prep data.root hcutoffCompact
  obtain ⟨Mmain, hMmain, hmainBound⟩ :=
    exists_scaled_global_iteratedFDeriv_bound_of_compactSupport (r := 2 * parentRadius)
      hmainSmooth hmainCompact (mul_pos (by norm_num) hparentRadius)
  obtain ⟨Azeta, hAzeta, hzetaBound⟩ :=
    exists_boundedSplitResidualCutoff_deriv_bound prep.input
  obtain ⟨Aresidual, hAresidual, hresidualBound⟩ :=
    exists_global_iteratedFDeriv_bound_of_compactSupport data.residual_contDiff
      data.residual_compactSupport
  refine ⟨Mmain, Azeta, Aresidual, hMmain, hAzeta, hAresidual, ⟨{
    root := data.root
    residual := data.residual
    zeta := zeta
    root_contDiff := data.root_contDiff
    residual_contDiff := data.residual_contDiff
    residual_nonnegative := data.residual_nonnegative
    zeta_contDiff := boundedSplitResidualCutoff_contDiff prep.input
    zeta_compactSupport := boundedSplitResidualCutoff_compactSupport prep.input
    exact_square_on_cutoff := ?_
    zeta_eq_one_on_cutoff := ?_
    main_scaled_jets := hmainBound
    zeta_global_jets := hzetaBound
    residual_global_jets := hresidualBound }⟩⟩
  · intro z hz
    have hinner := hcutoffInner z hz
    apply data.exact_square z
    refine ⟨hinner.1, hinner.2.trans ?_⟩
    linarith [prep.input.tangentialRadius_pos]
  · intro z hz
    exact boundedSplitResidualCutoff_eq_one prep.input (hcutoffInner z hz).2
end QuarticConvergence
end OptimalConvergenceRates

end
