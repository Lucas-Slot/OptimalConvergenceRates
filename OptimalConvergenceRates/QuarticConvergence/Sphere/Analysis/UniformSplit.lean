/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Analysis/UniformSplit.lean

  The one-normal-coordinate split and the envelope regularity gain.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.JetBounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Maps.Proper.Basic

open Set
open Filter
open MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence
/-- Integrating a finite-order smooth scalar function over a fixed compact real interval preserves
its differentiability order in a finite-dimensional parameter. -/
theorem contDiff_setIntegral_Icc
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    (m : ℕ) {g : (D × ℝ) → ℝ} (hg : ContDiff ℝ m g) :
    ContDiff ℝ m (fun x : D ↦ ∫ t in Set.Icc (0 : ℝ) 1, g (x, t)) := by
  induction m generalizing g with
  | zero =>
      exact contDiff_zero.2
        (continuous_parametric_integral_of_continuous
          (f := fun x t ↦ g (x, t)) (by fun_prop) isCompact_Icc)
  | succ m ih =>
      let inl : D →L[ℝ] (D × ℝ) := ContinuousLinearMap.inl ℝ D ℝ
      let F : D → ℝ → ℝ := fun x t ↦ g (x, t)
      let F' : D → ℝ → D →L[ℝ] ℝ := fun x t ↦ (fderiv ℝ g (x, t)).comp inl
      have hF'cont : Continuous (Function.uncurry F') := by
        let precompose : (((D × ℝ) →L[ℝ] ℝ) →L[ℝ] (D →L[ℝ] ℝ)) :=
          (ContinuousLinearMap.compL ℝ D (D × ℝ) ℝ).flip inl
        exact precompose.continuous.comp
          (hg.continuous_fderiv (by norm_num : ((m + 1 : ℕ) : WithTop ℕ∞) ≠ 0))
      have hderiv : ∀ x : D,
          HasFDerivAt (fun x : D ↦ ∫ t in Set.Icc (0 : ℝ) 1, F x t)
            (∫ t in Set.Icc (0 : ℝ) 1, F' x t) x := by
        intro x₀
        have hcompact : IsCompact (Metric.closedBall x₀ 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
          (isCompact_closedBall x₀ 1).prod isCompact_Icc
        obtain ⟨C, hC⟩ := hcompact.bddAbove_image hF'cont.norm.continuousOn
        have hbound : ∀ x ∈ Metric.closedBall x₀ 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
            ‖F' x t‖ ≤ C := by
          intro x hx t ht
          apply hC
          exact ⟨(x, t), ⟨hx, ht⟩, rfl⟩
        apply hasFDerivAt_integral_of_dominated_of_fderiv_le
            (s := Metric.closedBall x₀ 1) (bound := fun _ ↦ C)
        · exact Metric.closedBall_mem_nhds x₀ zero_lt_one
        · filter_upwards with x
          exact (hg.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
        · exact (hg.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
            |>.integrableOn_compact isCompact_Icc
        · exact (hF'cont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
        · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          exact fun x hx ↦ hbound x hx t ht
        · exact continuousOn_const.integrableOn_compact isCompact_Icc
        · refine Filter.Eventually.of_forall fun t x hx ↦ by
            have hpair : HasFDerivAt (fun x : D ↦ (x, t)) inl x := by
              fun_prop
            simpa only [F, F', Function.comp_def] using
              (hg.differentiable (by norm_num) (x, t)).hasFDerivAt.comp x hpair
      have hdiff : Differentiable ℝ (fun x : D ↦ ∫ t in Set.Icc (0 : ℝ) 1, F x t) :=
        fun x ↦ (hderiv x).differentiableAt
      rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = m + 1 by norm_num,
        contDiff_succ_iff_fderiv_apply]
      refine ⟨hdiff, ?_, ?_⟩
      · simp
      · intro v
        rw [show (fun x : D ↦ fderiv ℝ
            (fun x : D ↦ ∫ t in Set.Icc (0 : ℝ) 1, F x t) x v) =
            fun x : D ↦ ∫ t in Set.Icc (0 : ℝ) 1, F' x t v by
          funext x
          rw [(hderiv x).fderiv]
          exact ContinuousLinearMap.integral_apply
            (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
            ((hF'cont.comp (continuous_const.prodMk continuous_id)).continuousOn
              |>.integrableOn_compact isCompact_Icc) v]
        apply ih (g := fun p ↦ F' p.1 p.2 v)
        exact ((hg.fderiv_right (m := m) (by norm_num)).clm_apply contDiff_const).comp
          (contDiff_fst.prodMk contDiff_snd)


/-- The distinguished normal direction in `ℝ × ℝⁿ`. -/
def splitNormalDirection (n : ℕ) : ℝ × (Fin n → ℝ) := (1, 0)

/-- Normalized hypotheses for the positive-curvature local splitting alternative. -/
structure NormalizedLocalSplitInput (n : ℕ) where
  function : (ℝ × (Fin n → ℝ)) → ℝ
  cylinder : Set (ℝ × (Fin n → ℝ))
  tLeft : ℝ
  tRight : ℝ
  left_lt_right : tLeft < tRight
  cylinder_eq : cylinder = {z | tLeft ≤ z.1 ∧ z.1 ≤ tRight}
  nonnegative_on : ∀ z ∈ cylinder, 0 ≤ function z
  contDiff : ContDiff ℝ 6 function
  normal_derivative_left_nonpos : ∀ y,
    fderiv ℝ function (tLeft, y) (splitNormalDirection n) ≤ 0
  normal_derivative_right_nonneg : ∀ y,
    0 ≤ fderiv ℝ function (tRight, y) (splitNormalDirection n)
  normal_curvature : ∀ z ∈ cylinder,
    (1 / 4 : ℝ) ≤
      fderiv ℝ (fun w ↦ fderiv ℝ function w (splitNormalDirection n)) z
        (splitNormalDirection n)

/-- A single minimizing graph on the fixed cylinder projection. -/
structure MinimizingGraphData {n : ℕ} (input : NormalizedLocalSplitInput n) where
  graph : (Fin n → ℝ) → ℝ
  graph_contDiff : ContDiff ℝ 5 graph
  graph_point_mem : ∀ y, (graph y, y) ∈ input.cylinder
  first_derivative_zero : ∀ y,
    fderiv ℝ input.function (graph y, y) (splitNormalDirection n) = 0

/-- The envelope obtained by restricting to the minimizing graph. -/
def localSplitEnvelope {n : ℕ} (input : NormalizedLocalSplitInput n)
    (graph : MinimizingGraphData input) (y : Fin n → ℝ) : ℝ :=
  input.function (graph.graph y, y)

/-- Exact local square splitting with the regularities required by dimension induction. -/
structure UniformLocalSplitData {n : ℕ} (input : NormalizedLocalSplitInput n) where
  graph : MinimizingGraphData input
  root : (ℝ × (Fin n → ℝ)) → ℝ
  residual : (Fin n → ℝ) → ℝ
  root_contDiff : ContDiff ℝ 4 root
  residual_contDiff : ContDiff ℝ 6 residual
  residual_eq_envelope : residual = localSplitEnvelope input graph
  exact_square : ∀ z ∈ input.cylinder,
    input.function z = root z ^ 2 + residual z.2

/-- Uniform local splitting in a fixed tangential dimension. -/
def HasUniformLocalSplit (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ input : NormalizedLocalSplitInput n, Nonempty (UniformLocalSplitData input)
/-- Every tangential point has a normal critical point in the prescribed interval. -/
theorem exists_normalCriticalPoint {n : ℕ} (input : NormalizedLocalSplitInput n)
    (y : Fin n → ℝ) :
    ∃ t ∈ Set.Icc input.tLeft input.tRight,
      fderiv ℝ input.function (t, y) (splitNormalDirection n) = 0 := by
  let φ : ℝ → ℝ := fun t =>
    fderiv ℝ input.function (t, y) (splitNormalDirection n)
  have hnormal : ContDiff ℝ 5 (fun z =>
      fderiv ℝ input.function z (splitNormalDirection n)) := by
    exact (input.contDiff.fderiv_right (m := 5) (by norm_num)).clm_apply contDiff_const
  have hφ : Continuous φ := hnormal.continuous.comp (by fun_prop)
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc input.left_lt_right.le hφ.continuousOn
    (Set.mem_Icc.mpr
      ⟨input.normal_derivative_left_nonpos y,
        input.normal_derivative_right_nonneg y⟩)
  exact ⟨t, ht, hzero⟩

/-- Strict positive normal curvature makes the normal critical point unique. -/
theorem normalCriticalPoint_unique {n : ℕ} (input : NormalizedLocalSplitInput n)
    (y : Fin n → ℝ) {a b : ℝ}
    (ha : a ∈ Set.Icc input.tLeft input.tRight)
    (hb : b ∈ Set.Icc input.tLeft input.tRight)
    (hza : fderiv ℝ input.function (a, y) (splitNormalDirection n) = 0)
    (hzb : fderiv ℝ input.function (b, y) (splitNormalDirection n) = 0) :
    a = b := by
  let N : (ℝ × (Fin n → ℝ)) → ℝ := fun z =>
    fderiv ℝ input.function z (splitNormalDirection n)
  let φ : ℝ → ℝ := fun t => N (t, y)
  have hnormal : ContDiff ℝ 5 N := by
    exact (input.contDiff.fderiv_right (m := 5) (by norm_num)).clm_apply contDiff_const
  have hφ : Continuous φ := hnormal.continuous.comp (by fun_prop)
  have hmono : StrictMonoOn φ (Set.Icc input.tLeft input.tRight) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hφ.continuousOn
    intro t ht
    have htIcc : t ∈ Set.Icc input.tLeft input.tRight := interior_subset ht
    have htcyl : (t, y) ∈ input.cylinder := by
      rw [input.cylinder_eq]
      exact htIcc
    have hcurv := input.normal_curvature (t, y) htcyl
    have he : HasDerivAt (fun s : ℝ => (s, y)) (splitNormalDirection n) t := by
      simpa only [id_eq, splitNormalDirection] using
        (HasDerivAt.prodMk (hasDerivAt_id t) (hasDerivAt_const t y))
    have hchain :=
      (hnormal.differentiable (by norm_num) (t, y)).hasFDerivAt.comp_hasDerivAt t he
    rw [show deriv φ t = fderiv ℝ N (t, y) (splitNormalDirection n) by
      simpa only [φ, Function.comp_def] using hchain.deriv]
    exact (by norm_num : (0 : ℝ) < 1 / 4).trans_le hcurv
  apply hmono.injOn ha hb
  simpa [φ, N] using hza.trans hzb.symm

/-- The canonical normal critical point chosen in the fixed interval. -/
noncomputable def minimizingGraphValue {n : ℕ} (input : NormalizedLocalSplitInput n)
    (y : Fin n → ℝ) : ℝ :=
  Classical.choose (exists_normalCriticalPoint input y)

theorem minimizingGraphValue_mem_Icc {n : ℕ} (input : NormalizedLocalSplitInput n)
    (y : Fin n → ℝ) :
    minimizingGraphValue input y ∈ Set.Icc input.tLeft input.tRight :=
  (Classical.choose_spec (exists_normalCriticalPoint input y)).1

theorem minimizingGraphValue_normalDerivative_eq_zero {n : ℕ}
    (input : NormalizedLocalSplitInput n) (y : Fin n → ℝ) :
    fderiv ℝ input.function (minimizingGraphValue input y, y) (splitNormalDirection n) = 0 :=
  (Classical.choose_spec (exists_normalCriticalPoint input y)).2

/-- The normal critical-point equation with the tangential variable first, as required by
mathlib's implicit-function theorem. -/
def normalCriticalEquation {n : ℕ} (input : NormalizedLocalSplitInput n)
    (p : (Fin n → ℝ) × ℝ) : ℝ :=
  fderiv ℝ input.function (p.2, p.1) (splitNormalDirection n)

theorem normalCriticalEquation_contDiff_five {n : ℕ}
    (input : NormalizedLocalSplitInput n) :
    ContDiff ℝ 5 (normalCriticalEquation input) := by
  have hnormal : ContDiff ℝ 5 (fun z =>
      fderiv ℝ input.function z (splitNormalDirection n)) := by
    exact (input.contDiff.fderiv_right (m := 5) (by norm_num)).clm_apply contDiff_const
  exact hnormal.comp (by fun_prop)

theorem normalCriticalEquation_partial_apply_one {n : ℕ}
    (input : NormalizedLocalSplitInput n) (y : Fin n → ℝ) (t : ℝ) :
    (fderiv ℝ (normalCriticalEquation input) (y, t)).comp
        (ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ) 1 =
      fderiv ℝ (fun z => fderiv ℝ input.function z (splitNormalDirection n))
        (t, y) (splitNormalDirection n) := by
  let N : (ℝ × (Fin n → ℝ)) → ℝ := fun z =>
    fderiv ℝ input.function z (splitNormalDirection n)
  have hN : DifferentiableAt ℝ N (t, y) :=
    ((input.contDiff.fderiv_right (m := 5) (by norm_num)).clm_apply
      contDiff_const).differentiable (by norm_num) (t, y)
  let L : ((Fin n → ℝ) × ℝ) →L[ℝ] (ℝ × (Fin n → ℝ)) :=
    (ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ).prod
      (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ)
  have hswapHas : HasFDerivAt (fun p : (Fin n → ℝ) × ℝ => (p.2, p.1)) L (y, t) := by
    fun_prop
  have hswap : DifferentiableAt ℝ (fun p : (Fin n → ℝ) × ℝ => (p.2, p.1)) (y, t) := by
    fun_prop
  change ((fderiv ℝ (N ∘ fun p : (Fin n → ℝ) × ℝ => (p.2, p.1)) (y, t)).comp
      (ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ)) 1 = _
  rw [fderiv_comp (y, t) hN hswap, hswapHas.fderiv]
  simp [N, L, splitNormalDirection]

/-- The normal partial derivative is invertible throughout the cylinder. -/
theorem normalCriticalEquation_partial_bijective {n : ℕ}
    (input : NormalizedLocalSplitInput n) (y : Fin n → ℝ) (t : ℝ)
    (ht : t ∈ Set.Icc input.tLeft input.tRight) :
    Function.Bijective ((fderiv ℝ (normalCriticalEquation input) (y, t)).comp
      (ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ)) := by
  let L : ℝ →L[ℝ] ℝ := (fderiv ℝ (normalCriticalEquation input) (y, t)).comp
    (ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ)
  have htcyl : (t, y) ∈ input.cylinder := by
    rw [input.cylinder_eq]
    exact ht
  have hLone : (1 / 4 : ℝ) ≤ L 1 := by
    rw [show L 1 = fderiv ℝ (fun z =>
        fderiv ℝ input.function z (splitNormalDirection n))
          (t, y) (splitNormalDirection n) by
      exact normalCriticalEquation_partial_apply_one input y t]
    exact input.normal_curvature (t, y) htcyl
  have hLone_ne : L 1 ≠ 0 :=
    ne_of_gt ((by norm_num : (0 : ℝ) < 1 / 4).trans_le hLone)
  have hformula (z : ℝ) : L z = z * L 1 := by
    calc
      L z = L (z • (1 : ℝ)) := by simp
      _ = z • L 1 := map_smul L z 1
      _ = z * L 1 := by simp [smul_eq_mul]
  constructor
  · intro a b hab
    rw [hformula a, hformula b] at hab
    exact mul_right_cancel₀ hLone_ne hab
  · intro z
    refine ⟨z / L 1, ?_⟩
    rw [hformula]
    field_simp

/-- At every selected critical point, the normal partial derivative is invertible. -/
theorem normalCriticalEquation_partial_isInvertible {n : ℕ}
    (input : NormalizedLocalSplitInput n) (y : Fin n → ℝ) :
    ((fderiv ℝ (normalCriticalEquation input) (y, minimizingGraphValue input y)).comp
      (ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ)).IsInvertible := by
  let L : ℝ →L[ℝ] ℝ :=
    (fderiv ℝ (normalCriticalEquation input) (y, minimizingGraphValue input y)).comp
      (ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ)
  have hbij : Function.Bijective L := normalCriticalEquation_partial_bijective input y
    (minimizingGraphValue input y) (minimizingGraphValue_mem_Icc input y)
  have hL : L.IsInvertible := by
    refine ⟨ContinuousLinearEquiv.ofBijective L
      (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2), ?_⟩
    rfl
  simpa [L] using hL

/-- The unique critical-point selection is continuous. The proof realizes its graph as a closed
subset of tangential space times the compact interval and uses that the graph projection is a
continuous closed bijection. -/
theorem minimizingGraphValue_continuous {n : ℕ} (input : NormalizedLocalSplitInput n) :
    Continuous (minimizingGraphValue input) := by
  let K : Set ℝ := Set.Icc input.tLeft input.tRight
  letI : CompactSpace K :=
    ⟨isCompact_iff_isCompact_univ.mp (show IsCompact K from isCompact_Icc)⟩
  let equation : ((Fin n → ℝ) × K) → ℝ := fun p =>
    fderiv ℝ input.function (p.2.1, p.1) (splitNormalDirection n)
  have hequation : Continuous equation := by
    have hnormal : ContDiff ℝ 5 (fun z =>
        fderiv ℝ input.function z (splitNormalDirection n)) := by
      exact (input.contDiff.fderiv_right (m := 5) (by norm_num)).clm_apply contDiff_const
    exact hnormal.continuous.comp (by fun_prop)
  let Z : Set ((Fin n → ℝ) × K) := {p | equation p = 0}
  have hZclosed : IsClosed Z := isClosed_eq hequation continuous_const
  let P : Z → (Fin n → ℝ) := fun p => p.1.1
  have hPcont : Continuous P := by fun_prop
  have hPclosed : IsClosedMap P := by
    change IsClosedMap ((Prod.fst : ((Fin n → ℝ) × K) → (Fin n → ℝ)) ∘
      (fun p : Z => (p : (Fin n → ℝ) × K)))
    exact isClosedMap_fst_of_compactSpace.comp hZclosed.isClosedEmbedding_subtypeVal.isClosedMap
  have hPbij : Function.Bijective P := by
    constructor
    · intro a b hab
      change a.1.1 = b.1.1 at hab
      apply Subtype.ext
      apply Prod.ext hab
      apply Subtype.ext
      apply normalCriticalPoint_unique input b.1.1 a.1.2.property b.1.2.property
      · simpa only [Z, Set.mem_ofPred_eq, equation, hab] using a.property
      · simpa only [Z, Set.mem_ofPred_eq, equation] using b.property
    · intro y
      let t : K := ⟨minimizingGraphValue input y, minimizingGraphValue_mem_Icc input y⟩
      have hzero : equation (y, t) = 0 := by
        exact minimizingGraphValue_normalDerivative_eq_zero input y
      exact ⟨⟨(y, t), hzero⟩, rfl⟩
  let e : Z ≃ (Fin n → ℝ) := Equiv.ofBijective P hPbij
  let h : Z ≃ₜ (Fin n → ℝ) := e.toHomeomorphOfContinuousClosed hPcont hPclosed
  have hinv (y : Fin n → ℝ) : ((h.symm y).1.2 : ℝ) = minimizingGraphValue input y := by
    have hy : (h.symm y).1.1 = y := by
      change e (h.symm y) = y
      exact h.apply_symm_apply y
    apply normalCriticalPoint_unique input y
    · exact (h.symm y).1.2.property
    · exact minimizingGraphValue_mem_Icc input y
    · simpa only [Z, Set.mem_ofPred_eq, equation, hy] using (h.symm y).property
    · exact minimizingGraphValue_normalDerivative_eq_zero input y
  have hcontinuous : Continuous (fun y : Fin n → ℝ => ((h.symm y).1.2 : ℝ)) := by
    fun_prop
  exact hcontinuous.congr hinv

/-- The unique critical-point selection is globally `C⁵`; its existence and uniqueness are
proved above. -/
theorem minimizingGraphValue_contDiff_five {n : ℕ} (input : NormalizedLocalSplitInput n) :
    ContDiff ℝ 5 (minimizingGraphValue input) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  let cdf : ContDiffAt ℝ 5 (normalCriticalEquation input)
      (y, minimizingGraphValue input y) :=
    (normalCriticalEquation_contDiff_five input).contDiffAt
  have pn : (5 : WithTop ℕ∞) ≠ 0 := by norm_num
  have if₂ :
      ((fderiv ℝ (normalCriticalEquation input) (y, minimizingGraphValue input y)).comp
        (ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ)).IsInvertible :=
    normalCriticalEquation_partial_isInvertible input y
  have hpair : ContinuousAt (fun z => (z, minimizingGraphValue input z)) y := by
    exact continuousAt_id.prodMk (minimizingGraphValue_continuous input).continuousAt
  have hpull := hpair.eventually
    (cdf.eventually_apply_eq_iff_implicitFunction pn if₂)
  have heq : cdf.implicitFunction pn if₂ =ᶠ[𝓝 y] minimizingGraphValue input := by
    filter_upwards [hpull] with z hz
    apply hz.mp
    have hz0 : normalCriticalEquation input (z, minimizingGraphValue input z) = 0 := by
      exact minimizingGraphValue_normalDerivative_eq_zero input z
    have hy0 : normalCriticalEquation input (y, minimizingGraphValue input y) = 0 := by
      exact minimizingGraphValue_normalDerivative_eq_zero input y
    rw [hz0, hy0]
  exact (cdf.contDiffAt_implicitFunction pn if₂).congr_of_eventuallyEq heq.symm

/-- Strict normal convexity and endpoint signs produce one global minimizing graph. -/
theorem uniformMinimizingGraph {n : ℕ} (input : NormalizedLocalSplitInput n) :
    Nonempty (MinimizingGraphData input) := by
  refine ⟨{
    graph := minimizingGraphValue input
    graph_contDiff := minimizingGraphValue_contDiff_five input
    graph_point_mem := ?_
    first_derivative_zero := minimizingGraphValue_normalDerivative_eq_zero input
  }⟩
  intro y
  rw [input.cylinder_eq]
  exact minimizingGraphValue_mem_Icc input y

/-- The identity `D ψ = Φ_y(X(y),y)` recovers the sixth derivative of the envelope. -/
theorem localSplitEnvelope_contDiff_six {n : ℕ} (input : NormalizedLocalSplitInput n)
    (graph : MinimizingGraphData input) :
    ContDiff ℝ 6 (localSplitEnvelope input graph) := by
  let G : (Fin n → ℝ) → (ℝ × (Fin n → ℝ)) := fun y => (graph.graph y, y)
  let T : (Fin n → ℝ) →L[ℝ] (ℝ × (Fin n → ℝ)) :=
    ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)
  have hG : ContDiff ℝ 5 G := graph.graph_contDiff.prodMk contDiff_id
  have henvelope5 : ContDiff ℝ 5 (localSplitEnvelope input graph) := by
    exact (input.contDiff.of_le (by norm_num)).comp hG
  have hfd : fderiv ℝ (localSplitEnvelope input graph) =
      fun y => (fderiv ℝ input.function (G y)).comp T := by
    funext y
    have hfDiff : DifferentiableAt ℝ input.function (G y) :=
      input.contDiff.differentiable (by norm_num) (G y)
    have hgraphDiff : DifferentiableAt ℝ graph.graph y :=
      graph.graph_contDiff.differentiable (by norm_num) y
    have hGDiff : DifferentiableAt ℝ G y := hG.differentiable (by norm_num) y
    change fderiv ℝ (input.function ∘ G) y = _
    rw [fderiv_comp y hfDiff hGDiff]
    rw [show fderiv ℝ G y = (fderiv ℝ graph.graph y).prod
        (ContinuousLinearMap.id ℝ (Fin n → ℝ)) by
      simpa [G, fderiv_fun_id] using hgraphDiff.fderiv_prodMk differentiableAt_id]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply]
    let L := fderiv ℝ input.function (G y)
    change L (fderiv ℝ graph.graph y v, v) = L (T v)
    have hdecomp : (fderiv ℝ graph.graph y v, v) =
        (fderiv ℝ graph.graph y v, 0) + T v := by
      simp [T]
    rw [hdecomp, map_add]
    have hnormal : L (fderiv ℝ graph.graph y v, 0) = 0 := by
      have hsmul : (fderiv ℝ graph.graph y v, 0) =
          (fderiv ℝ graph.graph y v) • splitNormalDirection n := by
        ext <;> simp [splitNormalDirection]
      rw [hsmul, map_smul, graph.first_derivative_zero y]
      simp
    rw [hnormal, zero_add]
  rw [show (6 : WithTop ℕ∞) = 5 + 1 by norm_num, contDiff_succ_iff_fderiv]
  refine ⟨henvelope5.differentiable (by norm_num), ?_, ?_⟩
  · simp
  · rw [hfd]
    let precompose : ((ℝ × (Fin n → ℝ)) →L[ℝ] ℝ) →L[ℝ]
        ((Fin n → ℝ) →L[ℝ] ℝ) :=
      (ContinuousLinearMap.compL ℝ (Fin n → ℝ) (ℝ × (Fin n → ℝ)) ℝ).flip T
    have hfder5 : ContDiff ℝ 5 (fderiv ℝ input.function) :=
      input.contDiff.fderiv_right (by norm_num)
    exact precompose.contDiff.comp (hfder5.comp hG)

theorem taylor_quadratic_lower_of_lt {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a < b) (hf : ContDiff ℝ 2 f) (hda : deriv f a = 0)
    (hsecond : ∀ x ∈ Set.Icc a b, c ≤ iteratedDeriv 2 f x) :
    c / 2 * (b - a) ^ 2 ≤ f b - f a := by
  obtain ⟨x, hx, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hab.ne hf.contDiffOn
  rw [Set.uIoo_of_le hab.le] at hx
  rw [Set.uIcc_of_le hab.le] at hrem
  have hxa : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2.le⟩
  have hsecondx := hsecond x hxa
  have hud : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hab
  have hzero : a ∈ Set.Icc a b := left_mem_Icc.2 hab.le
  have hwithin0 : iteratedDerivWithin 0 f (Set.Icc a b) a = iteratedDeriv 0 f a :=
    iteratedDerivWithin_eq_iteratedDeriv hud (hf.contDiffAt.of_le (by norm_num)) hzero
  have hwithin1 : iteratedDerivWithin 1 f (Set.Icc a b) a = iteratedDeriv 1 f a :=
    iteratedDerivWithin_eq_iteratedDeriv hud (hf.contDiffAt.of_le (by norm_num)) hzero
  rw [taylor_within_apply] at hrem
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hrem
  rw [hwithin0, hwithin1] at hrem
  norm_num [iteratedDeriv_zero, iteratedDeriv_one, smul_eq_mul, Nat.factorial] at hrem
  nlinarith [sq_nonneg (b - a)]

theorem taylor_quadratic_lower {f : ℝ → ℝ} {a b c : ℝ}
    (hf : ContDiff ℝ 2 f) (hda : deriv f a = 0)
    (hsecond : ∀ x ∈ Set.uIcc a b, c ≤ iteratedDeriv 2 f x) :
    c / 2 * (b - a) ^ 2 ≤ f b - f a := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact taylor_quadratic_lower_of_lt hab hf hda (fun x hx => hsecond x (by
      simpa [Set.uIcc_of_le hab.le] using hx))
  · subst b
    simp
  · let g : ℝ → ℝ := fun s => f (a - s)
    have hlen : 0 < a - b := sub_pos.mpr hab
    have hg : ContDiff ℝ 2 g := hf.comp (by fun_prop)
    have hdg : deriv g 0 = 0 := by
      rw [show deriv g 0 = iteratedDeriv 1 g 0 by simp [iteratedDeriv_one]]
      rw [show iteratedDeriv 1 g = fun s => (-1 : ℝ) ^ 1 *
          iteratedDeriv 1 f (a - s) by
        simpa only [smul_eq_mul, Pi.sub_apply, Function.const_apply, id_eq, zero_sub] using
          (iteratedDeriv_comp_const_sub (f := f) (s := a) (n := 1))]
      simp [iteratedDeriv_one, hda]
    have hsecondg : ∀ s ∈ Set.Icc (0 : ℝ) (a - b),
        c ≤ iteratedDeriv 2 g s := by
      intro s hs
      rw [show iteratedDeriv 2 g = fun q => (-1 : ℝ) ^ 2 *
          iteratedDeriv 2 f (a - q) by
        simpa only [smul_eq_mul] using
          (iteratedDeriv_comp_const_sub (f := f) (s := a) (n := 2))]
      simp only [one_mul, Even.neg_one_pow (by decide : Even 2)]
      apply hsecond
      rw [Set.uIcc_of_ge hab.le]
      constructor <;> linarith [hs.1, hs.2]
    have h := taylor_quadratic_lower_of_lt hlen hg hdg hsecondg
    dsimp [g] at h
    convert h using 1 <;> ring_nf

theorem localSplit_quadratic_lower {n : ℕ} (input : NormalizedLocalSplitInput n)
    (graph : MinimizingGraphData input) (z : ℝ × (Fin n → ℝ)) (hz : z ∈ input.cylinder) :
    (1 / 8 : ℝ) * (z.1 - graph.graph z.2) ^ 2 ≤
      input.function z - localSplitEnvelope input graph z.2 := by
  let X : ℝ := graph.graph z.2
  let φ : ℝ → ℝ := fun t => input.function (t, z.2)
  let N : (ℝ × (Fin n → ℝ)) → ℝ := fun w =>
    fderiv ℝ input.function w (splitNormalDirection n)
  have hφ : ContDiff ℝ 2 φ :=
    (input.contDiff.of_le (by norm_num)).comp (by fun_prop)
  have hderivφ : deriv φ = fun t => N (t, z.2) := by
    funext t
    have hline : HasDerivAt (fun s : ℝ => (s, z.2)) (splitNormalDirection n) t := by
      simpa only [id_eq, splitNormalDirection] using
        (HasDerivAt.prodMk (hasDerivAt_id t) (hasDerivAt_const t z.2))
    have hchain := (input.contDiff.differentiable (by norm_num) (t, z.2)).hasFDerivAt
      |>.comp_hasDerivAt t hline
    simpa only [φ, N, Function.comp_def] using hchain.deriv
  have hdX : deriv φ X = 0 := by
    rw [hderivφ]
    exact graph.first_derivative_zero z.2
  have hXIcc : X ∈ Set.Icc input.tLeft input.tRight := by
    simpa [X, input.cylinder_eq] using graph.graph_point_mem z.2
  have hzIcc : z.1 ∈ Set.Icc input.tLeft input.tRight := by
    simpa [input.cylinder_eq] using hz
  have hsecond : ∀ t ∈ Set.uIcc X z.1, (1 / 4 : ℝ) ≤ iteratedDeriv 2 φ t := by
    intro t ht
    have htIcc : t ∈ Set.Icc input.tLeft input.tRight := by
      rcases le_total X z.1 with hle | hge
      · rw [Set.uIcc_of_le hle] at ht
        exact ⟨hXIcc.1.trans ht.1, ht.2.trans hzIcc.2⟩
      · rw [Set.uIcc_of_ge hge] at ht
        exact ⟨hzIcc.1.trans ht.1, ht.2.trans hXIcc.2⟩
    have hN : ContDiff ℝ 5 N := by
      exact (input.contDiff.fderiv_right (m := 5) (by norm_num)).clm_apply contDiff_const
    have hline : HasDerivAt (fun s : ℝ => (s, z.2)) (splitNormalDirection n) t := by
      simpa only [id_eq, splitNormalDirection] using
        (HasDerivAt.prodMk (hasDerivAt_id t) (hasDerivAt_const t z.2))
    have hchain := (hN.differentiable (by norm_num) (t, z.2)).hasFDerivAt
      |>.comp_hasDerivAt t hline
    have hiter : iteratedDeriv 2 φ t =
        fderiv ℝ N (t, z.2) (splitNormalDirection n) := by
      rw [show iteratedDeriv 2 φ t = deriv (deriv φ) t by
        simp only [iteratedDeriv_succ, iteratedDeriv_zero]]
      rw [hderivφ]
      exact hchain.deriv
    rw [hiter]
    apply input.normal_curvature (t, z.2)
    rw [input.cylinder_eq]
    exact htIcc
  have h := taylor_quadratic_lower hφ hdX hsecond
  change (1 / 8 : ℝ) * (z.1 - X) ^ 2 ≤ input.function z - input.function (X, z.2)
  convert h using 1; norm_num [φ]



/-- Smoothly replace arbitrary real values by positive ones while leaving every value at least
`a` unchanged.  This is the extension device for the integral Taylor coefficient. -/
def positiveIdentityRegularization (a x : ℝ) : ℝ :=
  let θ := Real.smoothTransition (x / a)
  θ * x + (1 - θ) * a

/-- The positive identity regularization is `C⁴` (in fact, smooth). -/
theorem positiveIdentityRegularization_contDiff (a : ℝ) :
    ContDiff ℝ 4 (positiveIdentityRegularization a) := by
  unfold positiveIdentityRegularization
  fun_prop

/-- Above its positive threshold, the regularization is exactly the identity. -/
theorem positiveIdentityRegularization_eq_self {a x : ℝ} (ha : 0 < a)
    (hax : a ≤ x) : positiveIdentityRegularization a x = x := by
  have hratio : 1 ≤ x / a := (le_div_iff₀ ha).2 (by simpa using hax)
  simp [positiveIdentityRegularization, Real.smoothTransition.one_of_one_le hratio]

/-- At every input, the regularized value is strictly positive. -/
theorem positiveIdentityRegularization_pos {a x : ℝ} (ha : 0 < a) :
    0 < positiveIdentityRegularization a x := by
  by_cases hax : a ≤ x
  · rw [positiveIdentityRegularization_eq_self ha hax]
    exact ha.trans_le hax
  have hxa : x < a := lt_of_not_ge hax
  by_cases hx : 0 < x
  · let θ := Real.smoothTransition (x / a)
    have hθ0 : 0 ≤ θ := Real.smoothTransition.nonneg _
    have hratio : x / a < 1 := (div_lt_one ha).2 hxa
    have hθ1 : θ < 1 := Real.smoothTransition.lt_one_of_lt_one hratio
    change 0 < θ * x + (1 - θ) * a
    have hfirst : 0 ≤ θ * x := mul_nonneg hθ0 hx.le
    have hsecond : 0 < (1 - θ) * a := mul_pos (sub_pos.mpr hθ1) ha
    linarith
  · have hx0 : x ≤ 0 := le_of_not_gt hx
    have hratio : x / a ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx0 ha.le
    rw [show positiveIdentityRegularization a x = a by
      simp [positiveIdentityRegularization,
        Real.smoothTransition.zero_of_nonpos hratio]]
    exact ha

/-- The second derivative in the distinguished normal direction. -/
def localNormalSecondDerivative {n : ℕ} (input : NormalizedLocalSplitInput n)
    (z : ℝ × (Fin n → ℝ)) : ℝ :=
  fderiv ℝ (fun w ↦ fderiv ℝ input.function w (splitNormalDirection n)) z
    (splitNormalDirection n)

theorem localNormalSecondDerivative_contDiff {n : ℕ}
    (input : NormalizedLocalSplitInput n) :
    ContDiff ℝ 4 (localNormalSecondDerivative input) := by
  have hnormal : ContDiff ℝ 5 (fun z ↦
      fderiv ℝ input.function z (splitNormalDirection n)) := by
    exact (input.contDiff.fderiv_right (m := 5) (by norm_num)).clm_apply contDiff_const
  exact (hnormal.fderiv_right (m := 4) (by norm_num)).clm_apply contDiff_const

def localRawSquareCoefficientIntegrand {n : ℕ}
    (input : NormalizedLocalSplitInput n) (graph : MinimizingGraphData input)
    (p : (ℝ × (Fin n → ℝ)) × ℝ) : ℝ :=
  (1 - p.2) * localNormalSecondDerivative input
    (graph.graph p.1.2 + p.2 * (p.1.1 - graph.graph p.1.2), p.1.2)

theorem localRawSquareCoefficientIntegrand_contDiff {n : ℕ}
    (input : NormalizedLocalSplitInput n) (graph : MinimizingGraphData input) :
    ContDiff ℝ 4 (localRawSquareCoefficientIntegrand input graph) := by
  have hgraph : ContDiff ℝ 4 graph.graph := graph.graph_contDiff.of_le (by norm_num)
  have hpath : ContDiff ℝ 4 (fun p : (ℝ × (Fin n → ℝ)) × ℝ ↦
      (graph.graph p.1.2 + p.2 * (p.1.1 - graph.graph p.1.2), p.1.2)) := by
    fun_prop
  exact (contDiff_const.sub contDiff_snd).mul
    ((localNormalSecondDerivative_contDiff input).comp hpath)

def localRawSquareCoefficientFn {n : ℕ}
    (input : NormalizedLocalSplitInput n) (graph : MinimizingGraphData input)
    (z : ℝ × (Fin n → ℝ)) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) 1, localRawSquareCoefficientIntegrand input graph (z, s)

theorem localRawSquareCoefficientFn_contDiff {n : ℕ}
    (input : NormalizedLocalSplitInput n) (graph : MinimizingGraphData input) :
    ContDiff ℝ 4 (localRawSquareCoefficientFn input graph) := by
  exact contDiff_setIntegral_Icc 4
    (localRawSquareCoefficientIntegrand_contDiff input graph)

open scoped Interval in
/-- The exact second-order integral remainder at a stationary point on the unit interval. -/
theorem integralTaylor_two {φ φ' φ'' : ℝ → ℝ}
    (hφ' : ∀ s, HasDerivAt φ (φ' s) s)
    (hφ'' : ∀ s, HasDerivAt φ' (φ'' s) s)
    (hφ''cont : Continuous φ'') (hzero : φ' 0 = 0) :
    φ 1 - φ 0 = ∫ s in Set.Icc (0 : ℝ) 1, (1 - s) * φ'' s := by
  have hφ'cont : Continuous φ' := continuous_iff_continuousAt.2 fun s ↦
    (hφ'' s).continuousAt
  have hftc : ∫ s in (0 : ℝ)..1, φ' s = φ 1 - φ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ ↦ hφ' s) (hφ'cont.intervalIntegrable 0 1)
  have hip : ∫ s in (0 : ℝ)..1, (1 - s) * φ'' s =
      (1 - 1) * φ' 1 - (1 - 0) * φ' 0 -
        ∫ s in (0 : ℝ)..1, (-1) * φ' s := by
    simpa only [smul_eq_mul, Pi.sub_apply, Function.const_apply, id_eq, zero_sub] using
      intervalIntegral.integral_smul_deriv_eq_deriv_smul
        (fun s _ ↦ (hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s))
        (fun s _ ↦ hφ'' s) (continuous_const.intervalIntegrable 0 1)
        (hφ''cont.intervalIntegrable 0 1)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  rw [← hftc]
  simpa [hzero] using hip.symm

/-- The explicit integral coefficient gives the exact quadratic factorization globally. -/
theorem localRawSquareCoefficientFn_factorization {n : ℕ}
    (input : NormalizedLocalSplitInput n) (graph : MinimizingGraphData input)
    (z : ℝ × (Fin n → ℝ)) :
    input.function z - localSplitEnvelope input graph z.2 =
      (z.1 - graph.graph z.2) ^ 2 * localRawSquareCoefficientFn input graph z := by
  let X : ℝ := graph.graph z.2
  let d : ℝ := z.1 - X
  let path : ℝ → ℝ × (Fin n → ℝ) := fun s ↦ (X + s * d, z.2)
  let φ : ℝ → ℝ := fun s ↦ input.function (path s)
  let N : (ℝ × (Fin n → ℝ)) → ℝ := fun w ↦
    fderiv ℝ input.function w (splitNormalDirection n)
  let H : (ℝ × (Fin n → ℝ)) → ℝ := localNormalSecondDerivative input
  let φ' : ℝ → ℝ := fun s ↦ d * N (path s)
  let φ'' : ℝ → ℝ := fun s ↦ d ^ 2 * H (path s)
  have hpath (s : ℝ) : HasDerivAt path (d • splitNormalDirection n) s := by
    have hfirst : HasDerivAt (fun q : ℝ ↦ X + q * d) d s := by
      simpa only [id_eq, one_mul] using (hasDerivAt_id s).mul_const d |>.const_add X
    have hp : HasDerivAt path (d, 0) s := by
      simpa only [path] using
        (HasDerivAt.prodMk hfirst (hasDerivAt_const s z.2))
    exact hp.congr_deriv (by simp [splitNormalDirection])
  have hN : ContDiff ℝ 5 N := by
    exact (input.contDiff.fderiv_right (m := 5) (by norm_num)).clm_apply contDiff_const
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  have hφ' (s : ℝ) : HasDerivAt φ (φ' s) s := by
    have hchain := (input.contDiff.differentiable (by norm_num) (path s)).hasFDerivAt
      |>.comp_hasDerivAt s (hpath s)
    simpa [φ, φ', N, map_smul, this, Function.comp_def] using hchain
  have hφ'' (s : ℝ) : HasDerivAt φ' (φ'' s) s := by
    have hchain := (hN.differentiable (by norm_num) (path s)).hasFDerivAt
      |>.comp_hasDerivAt s (hpath s)
    have hbase : HasDerivAt (fun q ↦ N (path q)) (d * H (path s)) s := by
      simpa [H, localNormalSecondDerivative, map_smul, mul_comm, this, Function.comp_def] using hchain
    simpa [φ', φ'', pow_two, mul_assoc] using hbase.const_mul d
  have hφ''cont : Continuous φ'' := by
    have hpathCont : Continuous path := by fun_prop
    exact continuous_const.mul
      ((localNormalSecondDerivative_contDiff input).continuous.comp hpathCont)
  have hzero : φ' 0 = 0 := by
    simp [φ', path, N, X, graph.first_derivative_zero]
  have htaylor := integralTaylor_two hφ' hφ'' hφ''cont hzero
  have hleft : φ 1 - φ 0 =
      input.function z - localSplitEnvelope input graph z.2 := by
    dsimp [φ, path, X, d, localSplitEnvelope]
    congr 2
    · congr 1
      ring
    · congr 1
      ring
  rw [← hleft, htaylor]
  dsimp [φ'', H, localRawSquareCoefficientFn,
    localRawSquareCoefficientIntegrand, path, X, d]
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro s _
  ring

/-- The raw Taylor coefficient before values away from the cylinder are regularized. The integral
remainder must supply its global `C⁴` regularity and exact factorization. -/
structure LocalRawSquareCoefficientData {n : ℕ} (input : NormalizedLocalSplitInput n)
    (graph : MinimizingGraphData input) where
  coefficient : (ℝ × (Fin n → ℝ)) → ℝ
  coefficient_contDiff : ContDiff ℝ 4 coefficient
  factorization : ∀ z ∈ input.cylinder,
    input.function z - localSplitEnvelope input graph z.2 =
      (z.1 - graph.graph z.2) ^ 2 * coefficient z
/-- The positive coefficient in the quadratic Taylor factorization about the minimizing graph.
Keeping this intermediate object explicit separates the analytic extension argument from
the elementary construction of its square root. -/
structure LocalSquareCoefficientData {n : ℕ} (input : NormalizedLocalSplitInput n)
    (graph : MinimizingGraphData input) where
  coefficient : (ℝ × (Fin n → ℝ)) → ℝ
  coefficient_contDiff : ContDiff ℝ 4 coefficient
  coefficient_pos : ∀ z, 0 < coefficient z
  factorization : ∀ z ∈ input.cylinder,
    input.function z - localSplitEnvelope input graph z.2 =
      (z.1 - graph.graph z.2) ^ 2 * coefficient z

/-- Continuity and exact factorization force every quadratic coefficient to inherit the `1/8`
curvature lower bound on the cylinder, including on the minimizing graph itself. -/
theorem localSquareCoefficient_lower_of_factorization {n : ℕ}
    {input : NormalizedLocalSplitInput n} {graph : MinimizingGraphData input}
    (coefficient : (ℝ × (Fin n → ℝ)) → ℝ)
    (hcontinuous : Continuous coefficient)
    (hfactorization : ∀ z ∈ input.cylinder,
      input.function z - localSplitEnvelope input graph z.2 =
        (z.1 - graph.graph z.2) ^ 2 * coefficient z) :
    ∀ z ∈ input.cylinder, (1 / 8 : ℝ) ≤ coefficient z := by
  have lower_of_ne : ∀ (z : ℝ × (Fin n → ℝ)), z ∈ input.cylinder →
      z.1 - graph.graph z.2 ≠ 0 → (1 / 8 : ℝ) ≤ coefficient z := by
    intro z hz hd
    let d : ℝ := z.1 - graph.graph z.2
    have hd2 : 0 < d ^ 2 := sq_pos_of_ne_zero hd
    have hgrowth := localSplit_quadratic_lower input graph z hz
    have hfac := hfactorization z hz
    have hmul : (1 / 8 : ℝ) * d ^ 2 ≤ coefficient z * d ^ 2 := by
      rw [mul_comm (coefficient z) (d ^ 2)]
      simpa [d, hfac] using hgrowth
    exact le_of_mul_le_mul_right hmul hd2
  intro z hz
  by_cases hd : z.1 - graph.graph z.2 = 0
  · have hfirst : z.1 = graph.graph z.2 := sub_eq_zero.mp hd
    have hzEq : z = (graph.graph z.2, z.2) := by
      apply Prod.ext
      · exact hfirst
      · rfl
    rw [hzEq]
    let X := graph.graph z.2
    have hXIcc : X ∈ Set.Icc input.tLeft input.tRight := by
      simpa [X, input.cylinder_eq] using graph.graph_point_mem z.2
    have hinv : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    by_cases hright : X < input.tRight
    · let t : ℕ → ℝ := fun m => X + (input.tRight - X) * (1 / ((m : ℝ) + 1))
      have htend : Tendsto t atTop (𝓝 X) := by
        simpa [t] using
          (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv))
      have hpair : Tendsto (fun m => (t m, z.2)) atTop (𝓝 (X, z.2)) :=
        by simpa only [nhds_prod_eq] using htend.prodMk tendsto_const_nhds
      change (1 / 8 : ℝ) ≤ coefficient (X, z.2)
      apply ge_of_tendsto' (hcontinuous.continuousAt.tendsto.comp hpair)
      intro m
      have hden : 0 < (m : ℝ) + 1 := by positivity
      have hfrac0 : 0 < (1 : ℝ) / ((m : ℝ) + 1) := div_pos zero_lt_one hden
      have hfrac1 : (1 : ℝ) / ((m : ℝ) + 1) ≤ 1 := by
        apply (div_le_one hden).2
        exact_mod_cast Nat.le_add_left 1 m
      have htIcc : t m ∈ Set.Icc input.tLeft input.tRight := by
        dsimp [t]
        constructor <;> nlinarith [hXIcc.1, hXIcc.2]
      apply lower_of_ne (t m, z.2)
      · rw [input.cylinder_eq]
        exact htIcc
      · dsimp [t, X]
        apply sub_ne_zero.mpr
        have hp := mul_pos (sub_pos.mpr hright) hfrac0
        nlinarith
    · have hleft : input.tLeft < X := by
        have hXeq : X = input.tRight := le_antisymm hXIcc.2 (le_of_not_gt hright)
        rw [hXeq]
        exact input.left_lt_right
      let t : ℕ → ℝ := fun m => X + (input.tLeft - X) * (1 / ((m : ℝ) + 1))
      have htend : Tendsto t atTop (𝓝 X) := by
        simpa [t] using
          (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv))
      have hpair : Tendsto (fun m => (t m, z.2)) atTop (𝓝 (X, z.2)) :=
        by simpa only [nhds_prod_eq] using htend.prodMk tendsto_const_nhds
      change (1 / 8 : ℝ) ≤ coefficient (X, z.2)
      apply ge_of_tendsto' (hcontinuous.continuousAt.tendsto.comp hpair)
      intro m
      have hden : 0 < (m : ℝ) + 1 := by positivity
      have hfrac0 : 0 < (1 : ℝ) / ((m : ℝ) + 1) := div_pos zero_lt_one hden
      have hfrac1 : (1 : ℝ) / ((m : ℝ) + 1) ≤ 1 := by
        apply (div_le_one hden).2
        exact_mod_cast Nat.le_add_left 1 m
      have htIcc : t m ∈ Set.Icc input.tLeft input.tRight := by
        dsimp [t]
        constructor <;> nlinarith [hXIcc.1, hXIcc.2]
      apply lower_of_ne (t m, z.2)
      · rw [input.cylinder_eq]
        exact htIcc
      · dsimp [t, X]
        apply sub_ne_zero.mpr
        have hp := mul_neg_of_neg_of_pos (sub_neg.mpr hleft) hfrac0
        nlinarith
  · exact lower_of_ne z hz hd

/-- A globally positive coefficient inherits the cylinder lower bound from its factorization. -/
theorem LocalSquareCoefficientData.coefficient_lower {n : ℕ}
    {input : NormalizedLocalSplitInput n} {graph : MinimizingGraphData input}
    (coeff : LocalSquareCoefficientData input graph) :
    ∀ z ∈ input.cylinder, (1 / 8 : ℝ) ≤ coeff.coefficient z :=
  localSquareCoefficient_lower_of_factorization coeff.coefficient
    coeff.coefficient_contDiff.continuous coeff.factorization
/-- The raw global `C⁴` coefficient has an exact quadratic factorization; curvature then
supplies its lower bound by the theorem above. -/
theorem localRawSquareCoefficient {n : ℕ} (input : NormalizedLocalSplitInput n)
    (graph : MinimizingGraphData input) :
    Nonempty (LocalRawSquareCoefficientData input graph) := by
  exact ⟨{
    coefficient := localRawSquareCoefficientFn input graph
    coefficient_contDiff := localRawSquareCoefficientFn_contDiff input graph
    factorization := fun z _ ↦ localRawSquareCoefficientFn_factorization input graph z
  }⟩

/-- Taylor's raw coefficient, followed by smooth positive identity regularization at `1/8`,
produces the globally positive coefficient without changing the cylinder factorization. -/
theorem localSquareCoefficient {n : ℕ} (input : NormalizedLocalSplitInput n)
    (graph : MinimizingGraphData input) :
    Nonempty (LocalSquareCoefficientData input graph) := by
  let raw := Classical.choice (localRawSquareCoefficient input graph)
  let coefficient : (ℝ × (Fin n → ℝ)) → ℝ := fun z =>
    positiveIdentityRegularization (1 / 8) (raw.coefficient z)
  refine ⟨{
    coefficient := coefficient
    coefficient_contDiff := ?_
    coefficient_pos := ?_
    factorization := ?_
  }⟩
  · exact (positiveIdentityRegularization_contDiff (1 / 8)).comp
      raw.coefficient_contDiff
  · intro z
    exact positiveIdentityRegularization_pos (by norm_num)
  · intro z hz
    have heq : coefficient z = raw.coefficient z := by
      exact positiveIdentityRegularization_eq_self (by norm_num)
        (localSquareCoefficient_lower_of_factorization raw.coefficient
          raw.coefficient_contDiff.continuous raw.factorization z hz)
    rw [heq]
    exact raw.factorization z hz

/-- A positive `C⁴` quadratic coefficient gives the exact uniformly `C⁴` square root. -/
theorem exactLocalSquare {n : ℕ} (input : NormalizedLocalSplitInput n)
    (graph : MinimizingGraphData input)
    (henvelope : ContDiff ℝ 6 (localSplitEnvelope input graph)) :
    Nonempty (UniformLocalSplitData input) := by
  let coeff := Classical.choice (localSquareCoefficient input graph)
  let root : (ℝ × (Fin n → ℝ)) → ℝ := fun z =>
    (z.1 - graph.graph z.2) * Real.sqrt (coeff.coefficient z)
  have hroot : ContDiff ℝ 4 root := by
    have hlinear : ContDiff ℝ 4 (fun z : ℝ × (Fin n → ℝ) =>
        z.1 - graph.graph z.2) := by
      exact contDiff_fst.sub ((graph.graph_contDiff.of_le (by norm_num)).comp contDiff_snd)
    have hsqrt : ContDiff ℝ 4 (fun z => Real.sqrt (coeff.coefficient z)) :=
      coeff.coefficient_contDiff.sqrt (fun z => ne_of_gt (coeff.coefficient_pos z))
    exact hlinear.mul hsqrt
  refine ⟨{
    graph := graph
    root := root
    residual := localSplitEnvelope input graph
    root_contDiff := hroot
    residual_contDiff := henvelope
    residual_eq_envelope := rfl
    exact_square := ?_
  }⟩
  intro z hz
  have hcoeff0 : 0 ≤ coeff.coefficient z :=
    (coeff.coefficient_lower z hz).trans' (by norm_num)
  have hfac := coeff.factorization z hz
  dsimp [root]
  rw [mul_pow, Real.sq_sqrt hcoeff0]
  nlinarith

/-- Assemble the minimizing graph, envelope gain, and exact-square leaves. -/
theorem uniformLocalSplit (n : ℕ) : HasUniformLocalSplit n := by
  refine ⟨1, by norm_num, ?_⟩
  intro input
  let graph := Classical.choice (uniformMinimizingGraph input)
  exact exactLocalSquare input graph (localSplitEnvelope_contDiff_six input graph)

end QuarticConvergence
end OptimalConvergenceRates

end
