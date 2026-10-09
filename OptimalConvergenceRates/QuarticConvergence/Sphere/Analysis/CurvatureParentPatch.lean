import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.CurvatureDichotomy
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.CoordinateSplit

open Set
open scoped Topology

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence

/-!
# The positive-curvature parent patch

The curvature dichotomy gives a positive Hessian diagonal at the centre of an intrinsically
rescaled parent patch. The estimates in `ParentPatch` are local to the intrinsic unit ball.
This file records quantitative persistence and packages it on a genuinely bounded cylinder.

The tangential bound is essential: `NormalizedLocalSplitInput.cylinder_eq` describes an entire
slab, hence contains arbitrarily distant tangential points in positive tangential dimension.
-/

/-- A local third-derivative bound gives a Lipschitz estimate for the Hessian along a segment. -/
theorem norm_hessian_sub_le_of_third_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 3 f) {x y : E} {M : ℝ}
    (hthird : ∀ z ∈ segment ℝ x y, ‖iteratedFDeriv ℝ 3 f z‖ ≤ M) :
    ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f x‖ ≤ M * dist x y := by
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ 2 f) :=
    hf.differentiable_iteratedFDeriv (by norm_num)
  have hbound (z : E) (hz : z ∈ segment ℝ x y) :
      ‖fderiv ℝ (iteratedFDeriv ℝ 2 f) z‖ ≤ M := by
    rw [norm_fderiv_iteratedFDeriv]
    exact hthird z hz
  have hmv := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
    (s := segment ℝ x y) (x := x) (y := y) (C := M)
    (fun z _ ↦ hdiff z) hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa [dist_eq_norm, norm_sub_rev] using hmv

/-- Unit diagonal evaluation loses at most the operator-norm distance of two Hessians. -/
theorem diagonal_hessian_lower_of_norm_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H K : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ)
    {v : E} (hv : ‖v‖ ≤ 1) {a ε : ℝ}
    (ha : a ≤ H ![v, v]) (hdiff : ‖K - H‖ ≤ ε) :
    a - ε ≤ K ![v, v] := by
  have heval :
      ‖(K - H) ![v, v]‖ ≤ ‖K - H‖ * ∏ _ : Fin 2, ‖v‖ :=
    (K - H).le_opNorm _
  have hprod : (∏ _ : Fin 2, ‖v‖) ≤ 1 := by
    simpa using (pow_le_one₀ (norm_nonneg v) hv : ‖v‖ ^ 2 ≤ 1)
  have hsmall : |K ![v, v] - H ![v, v]| ≤ ε := by
    calc
      |K ![v, v] - H ![v, v]| = ‖(K - H) ![v, v]‖ := by
        simp [Real.norm_eq_abs]
      _ ≤ ‖K - H‖ * ∏ _ : Fin 2, ‖v‖ := heval
      _ ≤ ‖K - H‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ ≤ ε := by simpa using hdiff
  linarith [neg_le_of_abs_le hsmall]

/-- Ambient radius on which centre curvature `1 / 4` persists as `1 / 8`. -/
def positiveCurvaturePersistenceRadius (C : ℝ) : ℝ :=
  1 / (32 * (C + 1))

theorem positiveCurvaturePersistenceRadius_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < positiveCurvaturePersistenceRadius C := by
  dsimp [positiveCurvaturePersistenceRadius]
  positivity

theorem positiveCurvaturePersistenceRadius_le_one {C : ℝ} (hC : 0 ≤ C) :
    positiveCurvaturePersistenceRadius C ≤ 1 := by
  rw [positiveCurvaturePersistenceRadius,
    div_le_one (by positivity : (0 : ℝ) < 32 * (C + 1))]
  linarith

theorem four_mul_curvatureRadius {C : ℝ} (hC : 0 ≤ C) :
    4 * (C + 1) * positiveCurvaturePersistenceRadius C = 1 / 8 := by
  dsimp [positiveCurvaturePersistenceRadius]
  field_simp
  ring

/-- On the fixed positive-curvature ball the intrinsic parent Hessian varies by at most
`1 / 8`. -/
theorem intrinsicRescaledPatch_hessian_variation_on_curvatureBall
    {n : ℕ} {u : (Fin n → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C) (c : Fin n → ℝ)
    (hR : 0 < nonnegativeJetScale u c)
    {z : Fin n → ℝ} (hz : ‖z‖ ≤ positiveCurvaturePersistenceRadius C) :
    ‖iteratedFDeriv ℝ 2
          (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) z -
        iteratedFDeriv ℝ 2
          (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) 0‖ ≤
      1 / 8 := by
  let Φ := intrinsicRescaledPatch u c (nonnegativeJetScale u c)
  have hC : 0 ≤ C := hcontrol.constant_nonneg
  have hrOne : positiveCurvaturePersistenceRadius C ≤ 1 :=
    positiveCurvaturePersistenceRadius_le_one hC
  have hsmooth : ContDiff ℝ 3 Φ :=
    (intrinsicRescaledPatch_contDiff hu.contDiff c (nonnegativeJetScale u c)).of_le
      (by norm_num)
  have hthird (w : Fin n → ℝ) (hw : w ∈ segment ℝ (0 : Fin n → ℝ) z) :
      ‖iteratedFDeriv ℝ 3 Φ w‖ ≤ 4 * (C + 1) := by
    apply intrinsicRescaledPatch_uniform_deriv_on_unitBall hu hcontrol c hR w
    · have hwz : ‖w - 0‖ ≤ ‖z - 0‖ := norm_sub_le_of_mem_segment hw
      have hwz' : ‖w‖ ≤ ‖z‖ := by simpa only [sub_zero] using hwz
      exact hwz'.trans (hz.trans hrOne)
    · norm_num
  have hvariation := norm_hessian_sub_le_of_third_bound hsmooth hthird
  have hdist : dist (0 : Fin n → ℝ) z = ‖z‖ := by simp [dist_eq_norm]
  rw [hdist] at hvariation
  calc
    ‖iteratedFDeriv ℝ 2 Φ z - iteratedFDeriv ℝ 2 Φ 0‖
        ≤ 4 * (C + 1) * ‖z‖ := hvariation
    _ ≤ 4 * (C + 1) * positiveCurvaturePersistenceRadius C := by gcongr
    _ = 1 / 8 := four_mul_curvatureRadius hC

/-- A positive Hessian diagonal returned by the dichotomy persists on the parent-patch ball. -/
theorem intrinsicRescaledPatch_positive_curvature_on_ball
    {n : ℕ} {u : (Fin n → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C) (c : Fin n → ℝ)
    (hR : 0 < nonnegativeJetScale u c)
    {v : Fin n → ℝ} (hv : ‖v‖ = 1)
    (hcurvature :
      1 / 4 ≤ iteratedFDeriv ℝ 2
        (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) 0 ![v, v])
    {z : Fin n → ℝ} (hz : ‖z‖ ≤ positiveCurvaturePersistenceRadius C) :
    1 / 8 ≤ iteratedFDeriv ℝ 2
      (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) z ![v, v] := by
  have h := diagonal_hessian_lower_of_norm_sub_le
    (iteratedFDeriv ℝ 2
      (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) 0)
    (iteratedFDeriv ℝ 2
      (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) z)
    hv.le hcurvature
    (intrinsicRescaledPatch_hessian_variation_on_curvatureBall
      hu hcontrol c hR hz)
  norm_num at h ⊢
  exact h

/-- A genuinely bounded replacement for the slab in `NormalizedLocalSplitInput`. -/
def boundedSplitCylinder {n : ℕ} (normalRadius tangentialRadius : ℝ) :
    Set (ℝ × (Fin n → ℝ)) :=
  {z | |z.1| ≤ normalRadius ∧ ‖z.2‖ ≤ tangentialRadius}

/-- Positive-curvature data on a bounded cylinder. Endpoint conditions require additional
small-value/recentring information, so they are not smuggled into this interface. -/
structure BoundedCurvatureCylinderData (n : ℕ) where
  function : (ℝ × (Fin n → ℝ)) → ℝ
  normalRadius : ℝ
  tangentialRadius : ℝ
  normalRadius_pos : 0 < normalRadius
  tangentialRadius_pos : 0 < tangentialRadius
  nonnegative : ∀ z, 0 ≤ function z
  contDiff : ContDiff ℝ 6 function
  normal_curvature : ∀ z ∈ boundedSplitCylinder normalRadius tangentialRadius,
    (1 / 4 : ℝ) ≤
      fderiv ℝ (fun w ↦ fderiv ℝ function w (splitNormalDirection n)) z
        (splitNormalDirection n)

/-- Half the ambient persistence radius leaves room for the norm-two coordinate frame. -/
def positiveCurvatureCoordinateRadius (C : ℝ) : ℝ :=
  positiveCurvaturePersistenceRadius C / 2

theorem positiveCurvatureCoordinateRadius_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < positiveCurvatureCoordinateRadius C := by
  exact div_pos (positiveCurvaturePersistenceRadius_pos hC) (by norm_num)

theorem norm_le_of_mem_boundedSplitCylinder_same
    {n : ℕ} {r : ℝ} {z : ℝ × (Fin n → ℝ)}
    (hz : z ∈ boundedSplitCylinder r r) :
    ‖z‖ ≤ r := by
  rw [Prod.norm_def]
  exact max_le (by simpa [Real.norm_eq_abs] using hz.1) hz.2

/-- Doubling restores the `1 / 4` normalization after the `1 / 8` persistence loss. -/
def doubledCurvaturePullback {n : ℕ}
    (Φ : (Fin (n + 1) → ℝ) → ℝ) (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1) :
    (ℝ × (Fin n → ℝ)) → ℝ :=
  fun z ↦ 2 * Φ (unitDirectionCoordinateFrame v hv z)

theorem doubledCurvaturePullback_contDiff {n : ℕ}
    {Φ : (Fin (n + 1) → ℝ) → ℝ} (hΦ : ContDiff ℝ 6 Φ)
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1) :
    ContDiff ℝ 6 (doubledCurvaturePullback Φ v hv) := by
  exact contDiff_const.mul (hΦ.comp (unitDirectionCoordinateFrame v hv).contDiff)

theorem doubledCurvaturePullback_normal_curvature {n : ℕ}
    {Φ : (Fin (n + 1) → ℝ) → ℝ} (hΦ : ContDiff ℝ 6 Φ)
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1)
    (z : ℝ × (Fin n → ℝ)) :
    fderiv ℝ
        (fun w ↦ fderiv ℝ (doubledCurvaturePullback Φ v hv) w
          (splitNormalDirection n)) z (splitNormalDirection n) =
      2 * iteratedFDeriv ℝ 2 Φ
        (unitDirectionCoordinateFrame v hv z) ![v, v] := by
  rw [fderiv_directionalFDeriv_eq_iteratedFDeriv_two
    ((doubledCurvaturePullback_contDiff hΦ v hv).of_le (by norm_num))
    z (splitNormalDirection n)]
  let T := unitDirectionCoordinateFrame v hv
  rw [show doubledCurvaturePullback Φ v hv = (2 : ℝ) • (Φ ∘ T) by
      funext x
      simp [doubledCurvaturePullback, T, smul_eq_mul]]
  have hpull : ContDiff ℝ 2 (Φ ∘ T) :=
    (hΦ.of_le (by norm_num)).comp T.contDiff
  rw [iteratedFDeriv_const_smul_apply hpull.contDiffAt]
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  have hcomp :
      iteratedFDeriv ℝ 2 (Φ ∘ T) z =
        (iteratedFDeriv ℝ 2 Φ (T z)).compContinuousLinearMap
          (fun _ ↦ T.toContinuousLinearMap) := by
    exact T.toContinuousLinearMap.iteratedFDeriv_comp_right
      hΦ z (by norm_num)
  rw [hcomp, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 2
  funext i
  fin_cases i <;> simp [T]

/-- The curvature branch supplies all analytic data on a fixed bounded cylinder. -/
noncomputable def boundedCurvatureCylinderData_of_intrinsic
    {n : ℕ} {u : (Fin (n + 1) → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C) (c : Fin (n + 1) → ℝ)
    (hR : 0 < nonnegativeJetScale u c)
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1)
    (hcurvature :
      1 / 4 ≤ iteratedFDeriv ℝ 2
        (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) 0 ![v, v]) :
    BoundedCurvatureCylinderData n where
  function := doubledCurvaturePullback
    (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) v hv
  normalRadius := positiveCurvatureCoordinateRadius C
  tangentialRadius := positiveCurvatureCoordinateRadius C
  normalRadius_pos := positiveCurvatureCoordinateRadius_pos hcontrol.constant_nonneg
  tangentialRadius_pos := positiveCurvatureCoordinateRadius_pos hcontrol.constant_nonneg
  nonnegative z := by
    exact mul_nonneg (by norm_num)
      (intrinsicRescaledPatch_nonnegative hu.nonnegative c hR
        (unitDirectionCoordinateFrame v hv z))
  contDiff := doubledCurvaturePullback_contDiff
    (intrinsicRescaledPatch_contDiff hu.contDiff c (nonnegativeJetScale u c)) v hv
  normal_curvature z hz := by
    rw [doubledCurvaturePullback_normal_curvature
      (intrinsicRescaledPatch_contDiff hu.contDiff c (nonnegativeJetScale u c)) v hv z]
    have hzcoord : ‖z‖ ≤ positiveCurvatureCoordinateRadius C :=
      norm_le_of_mem_boundedSplitCylinder_same hz
    have hzambient :
        ‖unitDirectionCoordinateFrame v hv z‖ ≤ positiveCurvaturePersistenceRadius C := by
      calc
        ‖unitDirectionCoordinateFrame v hv z‖ ≤ 2 * ‖z‖ :=
          norm_unitDirectionCoordinateFrame_apply_le_two_mul v hv z
        _ ≤ 2 * positiveCurvatureCoordinateRadius C := by gcongr
        _ = positiveCurvaturePersistenceRadius C := by
          rw [positiveCurvatureCoordinateRadius]
          ring
    have hpersist := intrinsicRescaledPatch_positive_curvature_on_ball
      hu hcontrol c hR hv hcurvature hzambient
    linarith

/-- The tangential radius used for endpoint control is smaller than the normal radius. -/
def positiveCurvatureTangentialRadius (C : ℝ) : ℝ :=
  positiveCurvatureCoordinateRadius C / (128 * (C + 1))

theorem positiveCurvatureTangentialRadius_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < positiveCurvatureTangentialRadius C := by
  rw [positiveCurvatureTangentialRadius]
  exact div_pos (positiveCurvatureCoordinateRadius_pos hC) (by positivity)

theorem positiveCurvatureTangentialRadius_le_coordinateRadius
    {C : ℝ} (hC : 0 ≤ C) :
    positiveCurvatureTangentialRadius C ≤ positiveCurvatureCoordinateRadius C := by
  have ha0 : 0 ≤ positiveCurvatureCoordinateRadius C :=
    (positiveCurvatureCoordinateRadius_pos hC).le
  rw [positiveCurvatureTangentialRadius]
  apply div_le_self ha0
  linarith

/-- A smaller positive-value threshold reserves enough room both for curvature persistence and
for the endpoint derivative signs. -/
def curvaturePreprocessValueThreshold (C : ℝ) : ℝ :=
  (positiveCurvatureCoordinateRadius C / (16 * (C + 1))) ^ 2

theorem curvaturePreprocessValueThreshold_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < curvaturePreprocessValueThreshold C := by
  rw [curvaturePreprocessValueThreshold]
  exact sq_pos_of_pos
    (div_pos (positiveCurvatureCoordinateRadius_pos hC) (by positivity))

theorem curvaturePreprocessValueThreshold_le_curvatureValueThreshold
    {C : ℝ} (hC : 0 ≤ C) :
    curvaturePreprocessValueThreshold C ≤ curvatureValueThreshold C := by
  have ha0 : 0 ≤ positiveCurvatureCoordinateRadius C :=
    (positiveCurvatureCoordinateRadius_pos hC).le
  have ha1 : positiveCurvatureCoordinateRadius C ≤ 1 := by
    calc
      positiveCurvatureCoordinateRadius C
          ≤ positiveCurvaturePersistenceRadius C := by
            rw [positiveCurvatureCoordinateRadius]
            linarith [positiveCurvaturePersistenceRadius_pos hC]
      _ ≤ 1 := positiveCurvaturePersistenceRadius_le_one hC
  have hden : 0 < 16 * (C + 1) := by positivity
  have hquot :
      positiveCurvatureCoordinateRadius C / (16 * (C + 1)) ≤
        1 / (16 * (C + 1)) :=
    div_le_div_of_nonneg_right ha1 hden.le
  exact pow_le_pow_left₀ (div_nonneg ha0 hden.le) hquot 2

/-- A refinement of the existing dichotomy which retains the small-value fact in the curvature
branch. The smaller threshold is harmless because an intermediate value is assigned to the
positive-value branch. -/
theorem intrinsicRescaledPatch_value_or_small_positive_curvature
    {n : ℕ} {u : (Fin n → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C) (c : Fin n → ℝ)
    (hR : 0 < nonnegativeJetScale u c) :
    curvaturePreprocessValueThreshold C ≤
        intrinsicRescaledPatch u c (nonnegativeJetScale u c) 0 ∨
      intrinsicRescaledPatch u c (nonnegativeJetScale u c) 0 <
          curvaturePreprocessValueThreshold C ∧
        ∃ v : Fin n → ℝ, ‖v‖ = 1 ∧
          1 / 4 ≤ iteratedFDeriv ℝ 2
            (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) 0 ![v, v] := by
  let Φ := intrinsicRescaledPatch u c (nonnegativeJetScale u c)
  by_cases hvalue : curvaturePreprocessValueThreshold C ≤ Φ 0
  · exact Or.inl hvalue
  · right
    refine ⟨lt_of_not_ge hvalue, ?_⟩
    rcases intrinsicRescaledPatch_value_or_positive_curvature hu hcontrol c hR with
      hold | hcurv
    · exfalso
      apply hvalue
      exact (curvaturePreprocessValueThreshold_le_curvatureValueThreshold
        hcontrol.constant_nonneg).trans hold
    · exact hcurv

/-- At the centre, intrinsic fourth-order rescaling preserves the scale-free first-derivative
estimate from `NonnegativeJetControl`. -/
theorem norm_fderiv_intrinsicRescaledPatch_zero_le
    {n : ℕ} {u : (Fin n → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C) (c : Fin n → ℝ)
    (hR : 0 < nonnegativeJetScale u c) :
    ‖fderiv ℝ (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) 0‖ ≤
      C * Real.sqrt
        (intrinsicRescaledPatch u c (nonnegativeJetScale u c) 0) := by
  let R := nonnegativeJetScale u c
  have hscale := intrinsicRescaledPatch_iteratedFDeriv_le
    hu.contDiff c hR (j := 1) (by norm_num) (0 : Fin n → ℝ)
  have hfirst := hcontrol.first c
  rw [← norm_iteratedFDeriv_one]
  calc
    ‖iteratedFDeriv ℝ 1 (intrinsicRescaledPatch u c R) 0‖
        ≤ (R ^ 4)⁻¹ * ‖iteratedFDeriv ℝ 1 u (c + R • (0 : Fin n → ℝ))‖ *
            R ^ 1 := hscale
    _ = (R ^ 4)⁻¹ * ‖iteratedFDeriv ℝ 1 u c‖ * R := by simp
    _ ≤ (R ^ 4)⁻¹ * (C * R * Real.sqrt (u c)) * R := by
      gcongr
    _ = C * (R ^ 2)⁻¹ * Real.sqrt (u c) := by
      field_simp [hR.ne']
    _ = C * Real.sqrt (intrinsicRescaledPatch u c R 0) := by
      rw [sqrt_intrinsicRescaledPatch_zero c hR]
      simp only [R]
      ring

/-- A local Hessian bound makes the first iterated derivative Lipschitz along a segment. -/
theorem norm_iteratedFDeriv_one_sub_le_of_hessian_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {x y : E} {M : ℝ}
    (hsecond : ∀ z ∈ segment ℝ x y, ‖iteratedFDeriv ℝ 2 f z‖ ≤ M) :
    ‖iteratedFDeriv ℝ 1 f y - iteratedFDeriv ℝ 1 f x‖ ≤ M * dist x y := by
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ 1 f) :=
    hf.differentiable_iteratedFDeriv (by norm_num)
  have hbound (z : E) (hz : z ∈ segment ℝ x y) :
      ‖fderiv ℝ (iteratedFDeriv ℝ 1 f) z‖ ≤ M := by
    rw [norm_fderiv_iteratedFDeriv]
    exact hsecond z hz
  have hmv := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
    (s := segment ℝ x y) (x := x) (y := y) (C := M)
    (fun z _ ↦ hdiff z) hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa [dist_eq_norm, norm_sub_rev] using hmv

/-- Exact normal first derivative of the doubled canonical-frame pullback. -/
theorem doubledCurvaturePullback_normal_fderiv {n : ℕ}
    {Φ : (Fin (n + 1) → ℝ) → ℝ} (hΦ : ContDiff ℝ 6 Φ)
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1)
    (z : ℝ × (Fin n → ℝ)) :
    fderiv ℝ (doubledCurvaturePullback Φ v hv) z (splitNormalDirection n) =
      2 * fderiv ℝ Φ (unitDirectionCoordinateFrame v hv z) v := by
  let T := unitDirectionCoordinateFrame v hv
  rw [← iteratedFDeriv_one_apply
    (f := doubledCurvaturePullback Φ v hv) (x := z)
    (m := fun _ ↦ splitNormalDirection n)]
  rw [← iteratedFDeriv_one_apply
    (f := Φ) (x := T z) (m := fun _ ↦ v)]
  rw [show doubledCurvaturePullback Φ v hv = (2 : ℝ) • (Φ ∘ T) by
      funext x
      simp [doubledCurvaturePullback, T, smul_eq_mul]]
  have hpull : ContDiff ℝ 1 (Φ ∘ T) :=
    (hΦ.of_le (by norm_num)).comp T.contDiff
  rw [iteratedFDeriv_const_smul_apply
    (i := 1) (a := (2 : ℝ)) (f := Φ ∘ T) (x := z) hpull.contDiffAt]
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  have hcomp :
      iteratedFDeriv ℝ 1 (Φ ∘ T) z =
        (iteratedFDeriv ℝ 1 Φ (T z)).compContinuousLinearMap
          (fun _ ↦ T.toContinuousLinearMap) := by
    exact T.toContinuousLinearMap.iteratedFDeriv_comp_right hΦ z (by norm_num)
  rw [hcomp, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 2
  funext i
  fin_cases i
  simp [T]

/-- Normal derivative of the doubled pullback at the coordinate origin is small in the
small-value curvature branch. -/
theorem abs_doubledCurvaturePullback_normal_fderiv_zero_le
    {n : ℕ} {u : (Fin (n + 1) → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C) (c : Fin (n + 1) → ℝ)
    (hR : 0 < nonnegativeJetScale u c)
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1)
    (hsmall :
      intrinsicRescaledPatch u c (nonnegativeJetScale u c) 0 <
        curvaturePreprocessValueThreshold C) :
    |fderiv ℝ
        (doubledCurvaturePullback
          (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) v hv)
        0 (splitNormalDirection n)| ≤
      positiveCurvatureCoordinateRadius C / 8 := by
  let Φ := intrinsicRescaledPatch u c (nonnegativeJetScale u c)
  let a := positiveCurvatureCoordinateRadius C
  let q := a / (16 * (C + 1))
  have hC : 0 ≤ C := hcontrol.constant_nonneg
  have ha : 0 < a := positiveCurvatureCoordinateRadius_pos hC
  have hq : 0 < q := by dsimp [q]; positivity
  have hΦ0 : 0 ≤ Φ 0 := intrinsicRescaledPatch_nonnegative hu.nonnegative c hR 0
  have hsqrtSq : Real.sqrt (Φ 0) ^ 2 = Φ 0 := Real.sq_sqrt hΦ0
  have hsqrt : Real.sqrt (Φ 0) ≤ q := by
    have hlt : Φ 0 < q ^ 2 := by simpa [Φ, q, a, curvaturePreprocessValueThreshold] using hsmall
    nlinarith [Real.sqrt_nonneg (Φ 0), sq_nonneg (Real.sqrt (Φ 0) - q)]
  have hgrad : ‖fderiv ℝ Φ 0‖ ≤ C * Real.sqrt (Φ 0) := by
    simpa [Φ] using norm_fderiv_intrinsicRescaledPatch_zero_le hu hcontrol c hR
  have heval : ‖fderiv ℝ Φ 0 v‖ ≤ ‖fderiv ℝ Φ 0‖ := by
    calc
      ‖fderiv ℝ Φ 0 v‖ ≤ ‖fderiv ℝ Φ 0‖ * ‖v‖ :=
        (fderiv ℝ Φ 0).le_opNorm v
      _ = ‖fderiv ℝ Φ 0‖ := by rw [hv, mul_one]
  rw [doubledCurvaturePullback_normal_fderiv
    (intrinsicRescaledPatch_contDiff hu.contDiff c (nonnegativeJetScale u c)) v hv]
  simp only [map_zero]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← Real.norm_eq_abs]
  calc
    2 * ‖fderiv ℝ Φ 0 v‖ ≤ 2 * ‖fderiv ℝ Φ 0‖ := by gcongr
    _ ≤ 2 * (C * Real.sqrt (Φ 0)) := by gcongr
    _ ≤ 2 * (C * q) := by gcongr
    _ ≤ a / 8 := by
      dsimp [q]
      have hCp : 0 < C + 1 := by linarith
      have hratio : C * (C + 1)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one hCp]
        linarith
      calc
        2 * (C * (a / (16 * (C + 1)))) =
            (a / 8) * (C * (C + 1)⁻¹) := by
              field_simp [hCp.ne']
              ring
        _ ≤ (a / 8) * 1 :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = a / 8 := mul_one _

/-- Directional first derivatives vary by at most the Hessian operator bound times distance. -/
theorem abs_fderiv_apply_sub_le_of_hessian_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {x y v : E} (hv : ‖v‖ ≤ 1) {M : ℝ}
    (hsecond : ∀ z ∈ segment ℝ x y, ‖iteratedFDeriv ℝ 2 f z‖ ≤ M) :
    |fderiv ℝ f y v - fderiv ℝ f x v| ≤ M * dist x y := by
  have hvariation :=
    norm_iteratedFDeriv_one_sub_le_of_hessian_bound hf hsecond
  have heval :
      ‖(iteratedFDeriv ℝ 1 f y - iteratedFDeriv ℝ 1 f x) (fun _ ↦ v)‖ ≤
        ‖iteratedFDeriv ℝ 1 f y - iteratedFDeriv ℝ 1 f x‖ *
          ∏ _ : Fin 1, ‖v‖ :=
    (iteratedFDeriv ℝ 1 f y - iteratedFDeriv ℝ 1 f x).le_opNorm _
  calc
    |fderiv ℝ f y v - fderiv ℝ f x v| =
        ‖(iteratedFDeriv ℝ 1 f y - iteratedFDeriv ℝ 1 f x) (fun _ ↦ v)‖ := by
      simp [iteratedFDeriv_one_apply, Real.norm_eq_abs]
    _ ≤ ‖iteratedFDeriv ℝ 1 f y - iteratedFDeriv ℝ 1 f x‖ *
          ∏ _ : Fin 1, ‖v‖ := heval
    _ ≤ ‖iteratedFDeriv ℝ 1 f y - iteratedFDeriv ℝ 1 f x‖ * 1 := by
      gcongr
      simpa using hv
    _ ≤ M * dist x y := by simpa using hvariation

/-- The normal derivative stays within `a / 4` of zero on the bounded tangential centre
slice. This is the quantitative input needed to obtain endpoint signs from positive curvature. -/
theorem abs_doubledCurvaturePullback_normal_fderiv_centerSlice_le
    {n : ℕ} {u : (Fin (n + 1) → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C) (c : Fin (n + 1) → ℝ)
    (hR : 0 < nonnegativeJetScale u c)
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1)
    (hsmall :
      intrinsicRescaledPatch u c (nonnegativeJetScale u c) 0 <
        curvaturePreprocessValueThreshold C)
    (y : Fin n → ℝ) (hy : ‖y‖ ≤ positiveCurvatureTangentialRadius C) :
    |fderiv ℝ
        (doubledCurvaturePullback
          (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) v hv)
        (0, y) (splitNormalDirection n)| ≤
      positiveCurvatureCoordinateRadius C / 4 := by
  let Φ := intrinsicRescaledPatch u c (nonnegativeJetScale u c)
  let T := unitDirectionCoordinateFrame v hv
  let a := positiveCurvatureCoordinateRadius C
  let b := positiveCurvatureTangentialRadius C
  let p : ℝ × (Fin n → ℝ) := (0, y)
  have hC : 0 ≤ C := hcontrol.constant_nonneg
  have ha : 0 < a := positiveCurvatureCoordinateRadius_pos hC
  have hb_le_a : b ≤ a := positiveCurvatureTangentialRadius_le_coordinateRadius hC
  have hpNorm : ‖p‖ = ‖y‖ := by simp [p, Prod.norm_def]
  have hTp :
      ‖T p‖ ≤ positiveCurvaturePersistenceRadius C := by
    calc
      ‖T p‖ ≤ 2 * ‖p‖ :=
        norm_unitDirectionCoordinateFrame_apply_le_two_mul v hv p
      _ = 2 * ‖y‖ := by rw [hpNorm]
      _ ≤ 2 * b := by gcongr
      _ ≤ 2 * a := by gcongr
      _ = positiveCurvaturePersistenceRadius C := by
        dsimp [a]
        rw [positiveCurvatureCoordinateRadius]
        ring
  have hrOne : positiveCurvaturePersistenceRadius C ≤ 1 :=
    positiveCurvaturePersistenceRadius_le_one hC
  have hsecond (w : Fin (n + 1) → ℝ)
      (hw : w ∈ segment ℝ (0 : Fin (n + 1) → ℝ) (T p)) :
      ‖iteratedFDeriv ℝ 2 Φ w‖ ≤ 4 * (C + 1) := by
    apply intrinsicRescaledPatch_uniform_deriv_on_unitBall hu hcontrol c hR w
    · have hwp : ‖w - 0‖ ≤ ‖T p - 0‖ := norm_sub_le_of_mem_segment hw
      have hwp' : ‖w‖ ≤ ‖T p‖ := by simpa only [sub_zero] using hwp
      exact hwp'.trans (hTp.trans hrOne)
    · norm_num
  have hambient :
      |fderiv ℝ Φ (T p) v - fderiv ℝ Φ 0 v| ≤
        4 * (C + 1) * dist (0 : Fin (n + 1) → ℝ) (T p) :=
    abs_fderiv_apply_sub_le_of_hessian_bound
      ((intrinsicRescaledPatch_contDiff hu.contDiff c
        (nonnegativeJetScale u c)).of_le (by norm_num)) hv.le hsecond
  have hambient' :
      |fderiv ℝ Φ (T p) v - fderiv ℝ Φ 0 v| ≤
        2 * (C + 1) * 4 * b := by
    calc
      |fderiv ℝ Φ (T p) v - fderiv ℝ Φ 0 v|
          ≤ 4 * (C + 1) * dist (0 : Fin (n + 1) → ℝ) (T p) := hambient
      _ = 4 * (C + 1) * ‖T p‖ := by simp [dist_eq_norm]
      _ ≤ 4 * (C + 1) * (2 * b) := by
        gcongr
        calc
          ‖T p‖ ≤ 2 * ‖p‖ :=
            norm_unitDirectionCoordinateFrame_apply_le_two_mul v hv p
          _ = 2 * ‖y‖ := by rw [hpNorm]
          _ ≤ 2 * b := by gcongr
      _ = 2 * (C + 1) * 4 * b := by ring
  have hnormalVariation :
      |fderiv ℝ (doubledCurvaturePullback Φ v hv) p (splitNormalDirection n) -
        fderiv ℝ (doubledCurvaturePullback Φ v hv) 0 (splitNormalDirection n)| ≤
          a / 8 := by
    rw [doubledCurvaturePullback_normal_fderiv
      (intrinsicRescaledPatch_contDiff hu.contDiff c (nonnegativeJetScale u c)) v hv p]
    rw [doubledCurvaturePullback_normal_fderiv
      (intrinsicRescaledPatch_contDiff hu.contDiff c (nonnegativeJetScale u c)) v hv 0]
    simp only [map_zero]
    rw [show 2 * fderiv ℝ Φ (T p) v - 2 * fderiv ℝ Φ 0 v =
      2 * (fderiv ℝ Φ (T p) v - fderiv ℝ Φ 0 v) by ring]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      2 * |fderiv ℝ Φ (T p) v - fderiv ℝ Φ 0 v|
          ≤ 2 * (2 * (C + 1) * 4 * b) := by gcongr
      _ = a / 8 := by
        dsimp [a, b, positiveCurvatureTangentialRadius]
        have hCp : C + 1 ≠ 0 := ne_of_gt (by linarith)
        field_simp [hCp]
        ring
  have hcenter :
      |fderiv ℝ (doubledCurvaturePullback Φ v hv) 0
        (splitNormalDirection n)| ≤ a / 8 := by
    simpa [Φ, a] using
      abs_doubledCurvaturePullback_normal_fderiv_zero_le
        hu hcontrol c hR v hv hsmall
  calc
    |fderiv ℝ (doubledCurvaturePullback Φ v hv) (0, y)
        (splitNormalDirection n)| =
      |(fderiv ℝ (doubledCurvaturePullback Φ v hv) p
          (splitNormalDirection n) -
        fderiv ℝ (doubledCurvaturePullback Φ v hv) 0
          (splitNormalDirection n)) +
        fderiv ℝ (doubledCurvaturePullback Φ v hv) 0
          (splitNormalDirection n)| := by
            simp only [p]
            congr 1
            ring
    _ ≤ |fderiv ℝ (doubledCurvaturePullback Φ v hv) p
          (splitNormalDirection n) -
        fderiv ℝ (doubledCurvaturePullback Φ v hv) 0
          (splitNormalDirection n)| +
        |fderiv ℝ (doubledCurvaturePullback Φ v hv) 0
          (splitNormalDirection n)| := abs_add_le _ _
    _ ≤ a / 8 + a / 8 := add_le_add hnormalVariation hcenter
    _ = a / 4 := by ring

/-- A lower normal-curvature bound and a small derivative on the centre slice force the two
normal endpoint signs, uniformly over a bounded tangential base. -/
theorem bounded_normal_endpoint_signs
    {n : ℕ} {F : (ℝ × (Fin n → ℝ)) → ℝ} (hF : ContDiff ℝ 6 F)
    {a b : ℝ} (ha : 0 < a)
    (hcenter : ∀ y, ‖y‖ ≤ b →
      |fderiv ℝ F (0, y) (splitNormalDirection n)| ≤ a / 4)
    (hcurvature : ∀ z ∈ boundedSplitCylinder a b,
      (1 / 4 : ℝ) ≤
        fderiv ℝ (fun w ↦ fderiv ℝ F w (splitNormalDirection n)) z
          (splitNormalDirection n)) :
    (∀ y, ‖y‖ ≤ b →
      fderiv ℝ F (-a, y) (splitNormalDirection n) ≤ 0) ∧
    (∀ y, ‖y‖ ≤ b →
      0 ≤ fderiv ℝ F (a, y) (splitNormalDirection n)) := by
  let N : (ℝ × (Fin n → ℝ)) → ℝ :=
    fun z ↦ fderiv ℝ F z (splitNormalDirection n)
  have hN : ContDiff ℝ 5 N :=
    (hF.fderiv_right (m := 5) (by norm_num)).clm_apply contDiff_const
  constructor
  · intro y hy
    let φ : ℝ → ℝ := fun t ↦ N (t, y)
    have hφ : ContDiff ℝ 5 φ := hN.comp (by fun_prop)
    have hderiv (t : ℝ) :
        deriv φ t = fderiv ℝ N (t, y) (splitNormalDirection n) := by
      have hline : HasDerivAt (fun s : ℝ ↦ (s, y)) (splitNormalDirection n) t := by
        convert (hasDerivAt_id t).prodMk (hasDerivAt_const t y) using 1
      have hchain :=
        (hN.differentiable (by norm_num) (t, y)).hasFDerivAt.comp_hasDerivAt t hline
      simpa [φ] using hchain.deriv
    have hlower : ∀ t ∈ interior (Set.Icc (-a) a), (1 / 4 : ℝ) ≤ deriv φ t := by
      intro t ht
      rw [hderiv]
      apply hcurvature (t, y)
      have htIcc : t ∈ Set.Icc (-a) a := interior_subset ht
      exact ⟨(abs_le).2 htIcc, hy⟩
    have hgrowth := (convex_Icc (-a) a).mul_sub_le_image_sub_of_le_deriv
      hφ.continuous.continuousOn
        (hφ.differentiable (by norm_num)).differentiableOn hlower
      (-a) (by exact ⟨le_rfl, by linarith⟩)
      0 (by exact ⟨by linarith, ha.le⟩) (by linarith)
    have hc := (abs_le.mp (hcenter y hy)).2
    dsimp [φ, N] at hgrowth
    nlinarith
  · intro y hy
    let φ : ℝ → ℝ := fun t ↦ N (t, y)
    have hφ : ContDiff ℝ 5 φ := hN.comp (by fun_prop)
    have hderiv (t : ℝ) :
        deriv φ t = fderiv ℝ N (t, y) (splitNormalDirection n) := by
      have hline : HasDerivAt (fun s : ℝ ↦ (s, y)) (splitNormalDirection n) t := by
        convert (hasDerivAt_id t).prodMk (hasDerivAt_const t y) using 1
      have hchain :=
        (hN.differentiable (by norm_num) (t, y)).hasFDerivAt.comp_hasDerivAt t hline
      simpa [φ] using hchain.deriv
    have hlower : ∀ t ∈ interior (Set.Icc (-a) a), (1 / 4 : ℝ) ≤ deriv φ t := by
      intro t ht
      rw [hderiv]
      apply hcurvature (t, y)
      have htIcc : t ∈ Set.Icc (-a) a := interior_subset ht
      exact ⟨(abs_le).2 htIcc, hy⟩
    have hgrowth := (convex_Icc (-a) a).mul_sub_le_image_sub_of_le_deriv
      hφ.continuous.continuousOn
        (hφ.differentiable (by norm_num)).differentiableOn hlower
      0 (by exact ⟨by linarith, ha.le⟩)
      a (by exact ⟨by linarith, le_rfl⟩) ha.le
    have hc := (abs_le.mp (hcenter y hy)).1
    dsimp [φ, N] at hgrowth
    nlinarith

/-- The exact bounded analogue of the analytic fields of `NormalizedLocalSplitInput`.
Unlike that structure, endpoint signs and curvature are requested only above a bounded
tangential base. -/
structure BoundedNormalizedLocalSplitInput (n : ℕ)
    extends BoundedCurvatureCylinderData n where
  normal_derivative_left_nonpos : ∀ y, ‖y‖ ≤ tangentialRadius →
    fderiv ℝ function (-normalRadius, y) (splitNormalDirection n) ≤ 0
  normal_derivative_right_nonneg : ∀ y, ‖y‖ ≤ tangentialRadius →
    0 ≤ fderiv ℝ function (normalRadius, y) (splitNormalDirection n)

/-- The retained small-value information closes the endpoint signs, so the positive-curvature
branch produces the full bounded analogue of `NormalizedLocalSplitInput` without an admission. -/
noncomputable def boundedNormalizedLocalSplitInput_of_intrinsic
    {n : ℕ} {u : (Fin (n + 1) → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C) (c : Fin (n + 1) → ℝ)
    (hR : 0 < nonnegativeJetScale u c)
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1)
    (hsmall :
      intrinsicRescaledPatch u c (nonnegativeJetScale u c) 0 <
        curvaturePreprocessValueThreshold C)
    (hcurvature :
      1 / 4 ≤ iteratedFDeriv ℝ 2
        (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) 0 ![v, v]) :
    BoundedNormalizedLocalSplitInput n := by
  let Φ := intrinsicRescaledPatch u c (nonnegativeJetScale u c)
  let F := doubledCurvaturePullback Φ v hv
  let a := positiveCurvatureCoordinateRadius C
  let b := positiveCurvatureTangentialRadius C
  have hC : 0 ≤ C := hcontrol.constant_nonneg
  have ha : 0 < a := positiveCurvatureCoordinateRadius_pos hC
  have hb : 0 < b := positiveCurvatureTangentialRadius_pos hC
  have hb_le_a : b ≤ a := positiveCurvatureTangentialRadius_le_coordinateRadius hC
  have hF : ContDiff ℝ 6 F :=
    doubledCurvaturePullback_contDiff
      (intrinsicRescaledPatch_contDiff hu.contDiff c (nonnegativeJetScale u c)) v hv
  have hcurvBox : ∀ z ∈ boundedSplitCylinder a b,
      (1 / 4 : ℝ) ≤
        fderiv ℝ (fun w ↦ fderiv ℝ F w (splitNormalDirection n)) z
          (splitNormalDirection n) := by
    intro z hz
    have hz' : z ∈ boundedSplitCylinder a a :=
      ⟨hz.1, hz.2.trans hb_le_a⟩
    exact (boundedCurvatureCylinderData_of_intrinsic
      hu hcontrol c hR v hv hcurvature).normal_curvature z hz'
  have hcenter : ∀ y, ‖y‖ ≤ b →
      |fderiv ℝ F (0, y) (splitNormalDirection n)| ≤ a / 4 := by
    intro y hy
    simpa [F, Φ, a, b] using
      abs_doubledCurvaturePullback_normal_fderiv_centerSlice_le
        hu hcontrol c hR v hv hsmall y hy
  have hsigns := bounded_normal_endpoint_signs hF ha hcenter hcurvBox
  exact {
    function := F
    normalRadius := a
    tangentialRadius := b
    normalRadius_pos := ha
    tangentialRadius_pos := hb
    nonnegative := by
      intro z
      exact mul_nonneg (by norm_num)
        (intrinsicRescaledPatch_nonnegative hu.nonnegative c hR
          (unitDirectionCoordinateFrame v hv z))
    contDiff := hF
    normal_curvature := hcurvBox
    normal_derivative_left_nonpos := hsigns.1
    normal_derivative_right_nonneg := hsigns.2
  }

/-- The corrected cylinder is genuinely bounded in the product sup norm. -/
theorem boundedSplitCylinder_subset_closedBall
    {n : ℕ} {a b : ℝ} :
    boundedSplitCylinder (n := n) a b ⊆
      Metric.closedBall 0 (max a b) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [Prod.norm_def]
  apply max_le
  · exact (by simpa [Real.norm_eq_abs] using hz.1.trans (le_max_left a b))
  · exact hz.2.trans (le_max_right a b)

/-- In positive tangential dimension, every nondegenerate full slab contains points outside
every ball. This is the precise obstruction to deriving `NormalizedLocalSplitInput.cylinder`
from parent-patch estimates on an intrinsic ball. -/
theorem splitSlab_not_subset_closedBall
    {n : ℕ} (hn : 0 < n) {tLeft tRight R : ℝ} (htr : tLeft < tRight) :
    ¬ ({z : ℝ × (Fin n → ℝ) | tLeft ≤ z.1 ∧ z.1 ≤ tRight} ⊆
      Metric.closedBall 0 R) := by
  intro hsubset
  let p : Fin n := ⟨0, hn⟩
  let y : Fin n → ℝ := fun _ ↦ |R| + 1
  let z : ℝ × (Fin n → ℝ) := (tLeft, y)
  have hzslab :
      z ∈ {w : ℝ × (Fin n → ℝ) | tLeft ≤ w.1 ∧ w.1 ≤ tRight} :=
    ⟨le_rfl, htr.le⟩
  have hzball := hsubset hzslab
  have hycoord : |R| + 1 ≤ ‖y‖ := by
    have hp := norm_le_pi_norm y p
    have hnonneg : 0 ≤ |R| + 1 := by positivity
    simpa only [y, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hp
  have hypair : ‖y‖ ≤ ‖z‖ := by
    change ‖y‖ ≤ max ‖tLeft‖ ‖y‖
    exact le_max_right _ _
  have hnorm : |R| + 1 ≤ ‖z‖ := hycoord.trans hypair
  have hball : ‖z‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hzball
  nlinarith [le_abs_self R]

/-- Consequently, the current local-split cylinder of any positive-dimensional input is never
contained in a parent-patch ball. -/
theorem NormalizedLocalSplitInput.cylinder_not_subset_closedBall
    {n : ℕ} (input : NormalizedLocalSplitInput n) (hn : 0 < n) (R : ℝ) :
    ¬ input.cylinder ⊆ Metric.closedBall 0 R := by
  rw [input.cylinder_eq]
  exact splitSlab_not_subset_closedBall hn input.left_lt_right

/-- With no tangential coordinate the obstruction disappears, and the bounded data does give
the existing full-slab interface. -/
def BoundedNormalizedLocalSplitInput.toNormalizedLocalSplitInputZero
    (input : BoundedNormalizedLocalSplitInput 0) :
    NormalizedLocalSplitInput 0 where
  function := input.function
  cylinder :=
    {z : ℝ × (Fin 0 → ℝ) |
      -input.normalRadius ≤ z.1 ∧ z.1 ≤ input.normalRadius}
  tLeft := -input.normalRadius
  tRight := input.normalRadius
  left_lt_right := by linarith [input.normalRadius_pos]
  cylinder_eq := rfl
  nonnegative_on := fun z _ ↦ input.nonnegative z
  contDiff := input.contDiff
  normal_derivative_left_nonpos := by
    intro y
    apply input.normal_derivative_left_nonpos y
    simpa using input.tangentialRadius_pos.le
  normal_derivative_right_nonneg := by
    intro y
    apply input.normal_derivative_right_nonneg y
    simpa using input.tangentialRadius_pos.le
  normal_curvature := by
    intro z hz
    apply input.normal_curvature z
    refine ⟨(abs_le).2 hz, ?_⟩
    simpa using input.tangentialRadius_pos.le

/-- Bounded split data tied to the parent function, rather than merely asserting that
some abstract bounded input exists.  The equations retain the coordinate frame, amplitude
normalization, and both quantitative radii needed to transport a split back to the parent. -/
structure IntrinsicBoundedSplitPreprocessing
    (n : ℕ) (Φ : (Fin (n + 1) → ℝ) → ℝ) (C : ℝ) where
  direction : Fin (n + 1) → ℝ
  direction_norm : ‖direction‖ = 1
  small_value : Φ 0 < curvaturePreprocessValueThreshold C
  center_curvature :
    1 / 4 ≤ iteratedFDeriv ℝ 2 Φ 0 ![direction, direction]
  input : BoundedNormalizedLocalSplitInput n
  function_eq :
    input.function = doubledCurvaturePullback Φ direction direction_norm
  normalRadius_eq :
    input.normalRadius = positiveCurvatureCoordinateRadius C
  tangentialRadius_eq :
    input.tangentialRadius = positiveCurvatureTangentialRadius C

/-- The explicit constructor retains all relations between the bounded input and its intrinsic
parent patch. -/
noncomputable def intrinsicBoundedSplitPreprocessing_of_intrinsic
    {n : ℕ} {u : (Fin (n + 1) → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C) (c : Fin (n + 1) → ℝ)
    (hR : 0 < nonnegativeJetScale u c)
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1)
    (hsmall :
      intrinsicRescaledPatch u c (nonnegativeJetScale u c) 0 <
        curvaturePreprocessValueThreshold C)
    (hcurvature :
      1 / 4 ≤ iteratedFDeriv ℝ 2
        (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) 0 ![v, v]) :
    IntrinsicBoundedSplitPreprocessing n
      (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) C where
  direction := v
  direction_norm := hv
  small_value := hsmall
  center_curvature := hcurvature
  input := boundedNormalizedLocalSplitInput_of_intrinsic
    hu hcontrol c hR v hv hsmall hcurvature
  function_eq := rfl
  normalRadius_eq := rfl
  tangentialRadius_eq := rfl

/-- The complete preprocessing dichotomy: either the parent has a quantitative positive value,
or the positive-curvature branch carries bounded split data explicitly tied to that parent. -/
theorem intrinsicRescaledPatch_value_or_boundedSplitPreprocessing
    {n : ℕ} {u : (Fin (n + 1) → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C) (c : Fin (n + 1) → ℝ)
    (hR : 0 < nonnegativeJetScale u c) :
    curvaturePreprocessValueThreshold C ≤
        intrinsicRescaledPatch u c (nonnegativeJetScale u c) 0 ∨
      Nonempty (IntrinsicBoundedSplitPreprocessing n
        (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) C) := by
  rcases intrinsicRescaledPatch_value_or_small_positive_curvature
    hu hcontrol c hR with hvalue | ⟨hsmall, v, hv, hcurvature⟩
  · exact Or.inl hvalue
  · exact Or.inr ⟨intrinsicBoundedSplitPreprocessing_of_intrinsic
      hu hcontrol c hR v hv hsmall hcurvature⟩

end OptimalConvergenceRates.QuarticConvergence
