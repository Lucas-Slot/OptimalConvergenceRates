import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.CurvatureDichotomy
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.UniformSplit

open Set
open scoped Topology

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence

/-!
# Splitting off one Euclidean coordinate

This file packages the elementary identification
`(Fin (n + 1) → ℝ) ≃ ℝ × (Fin n → ℝ)` as a linear isometry.  It also records the
pullback identities needed to put a function into the one-normal-coordinate form used by
`NormalizedLocalSplitInput`.

The function-space norm here is the sup norm. Thus a general unit curvature direction need not be
the image of the first coordinate under a linear isometry. The canonical continuous linear frame
below handles every unit direction and has forward and inverse operator norms at most two.
-/

/-- Split the leading coordinate from a finite real tuple. -/
def finSuccSplitIsometry (n : ℕ) :
    (Fin (n + 1) → ℝ) ≃ₗᵢ[ℝ] ℝ × (Fin n → ℝ) where
  toLinearEquiv :=
    (Fin.consLinearEquiv ℝ (fun _ : Fin (n + 1) ↦ ℝ)).symm
  norm_map' x := by
    change max ‖x 0‖ ‖Fin.tail x‖ = ‖x‖
    apply le_antisymm
    · apply max_le
      · exact norm_le_pi_norm x 0
      · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2
        intro i
        exact norm_le_pi_norm x i.succ
    · apply (pi_norm_le_iff_of_nonneg
        ((norm_nonneg (x 0)).trans (le_max_left _ _))).2
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact le_max_left _ _
      · exact (norm_le_pi_norm (Fin.tail x) j).trans (le_max_right _ _)

/-- Reassemble a finite real tuple from its leading and trailing coordinates. -/
def finSuccJoinIsometry (n : ℕ) :
    (ℝ × (Fin n → ℝ)) ≃ₗᵢ[ℝ] (Fin (n + 1) → ℝ) :=
  (finSuccSplitIsometry n).symm

/-- The continuous linear equivalence underlying `finSuccSplitIsometry`. -/
abbrev finSuccSplitEquiv (n : ℕ) :
    (Fin (n + 1) → ℝ) ≃L[ℝ] ℝ × (Fin n → ℝ) :=
  (finSuccSplitIsometry n).toContinuousLinearEquiv

/-- The continuous linear equivalence underlying `finSuccJoinIsometry`. -/
abbrev finSuccJoinEquiv (n : ℕ) :
    (ℝ × (Fin n → ℝ)) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
  (finSuccJoinIsometry n).toContinuousLinearEquiv

@[simp]
theorem finSuccSplitIsometry_apply (n : ℕ) (x : Fin (n + 1) → ℝ) :
    finSuccSplitIsometry n x = (x 0, Fin.tail x) :=
  rfl

@[simp]
theorem finSuccJoinIsometry_apply (n : ℕ) (z : ℝ × (Fin n → ℝ)) :
    finSuccJoinIsometry n z = Fin.cons z.1 z.2 :=
  rfl

@[simp]
theorem finSuccSplit_join (n : ℕ) (z : ℝ × (Fin n → ℝ)) :
    finSuccSplitIsometry n (Fin.cons z.1 z.2) = z := by
  exact (finSuccSplitIsometry n).apply_symm_apply z

@[simp]
theorem finSuccJoin_split (n : ℕ) (x : Fin (n + 1) → ℝ) :
    finSuccJoinIsometry n (x 0, Fin.tail x) = x := by
  exact (finSuccSplitIsometry n).symm_apply_apply x

/-- The first standard coordinate vector. -/
def firstCoordinateDirection (n : ℕ) : Fin (n + 1) → ℝ :=
  Fin.cons 1 0

@[simp]
theorem finSuccJoin_splitNormalDirection (n : ℕ) :
    finSuccJoinIsometry n (splitNormalDirection n) = firstCoordinateDirection n :=
  rfl

@[simp]
theorem norm_splitNormalDirection (n : ℕ) : ‖splitNormalDirection n‖ = 1 := by
  simp [splitNormalDirection, Prod.norm_def]

@[simp]
theorem norm_firstCoordinateDirection (n : ℕ) : ‖firstCoordinateDirection n‖ = 1 := by
  rw [← finSuccJoin_splitNormalDirection]
  simpa using (finSuccJoinIsometry n).norm_map (splitNormalDirection n)

theorem dist_finSuccSplitIsometry (n : ℕ) (x y : Fin (n + 1) → ℝ) :
    dist (finSuccSplitIsometry n x) (finSuccSplitIsometry n y) = dist x y :=
  (finSuccSplitIsometry n).isometry.dist_eq x y

theorem dist_finSuccJoinIsometry (n : ℕ) (x y : ℝ × (Fin n → ℝ)) :
    dist (finSuccJoinIsometry n x) (finSuccJoinIsometry n y) = dist x y :=
  (finSuccJoinIsometry n).isometry.dist_eq x y

theorem finSuccJoin_preimage_closedBall (n : ℕ) (c : Fin (n + 1) → ℝ) (R : ℝ) :
    finSuccJoinIsometry n ⁻¹' Metric.closedBall c R =
      Metric.closedBall (finSuccSplitIsometry n c) R := by
  ext z
  simp only [Set.mem_preimage, Metric.mem_closedBall]
  rw [← dist_finSuccJoinIsometry n z (finSuccSplitIsometry n c)]
  simp

theorem finSuccJoin_contDiff (n m : ℕ) :
    ContDiff ℝ m (finSuccJoinIsometry n) :=
  (finSuccJoinEquiv n).contDiff

theorem finSuccSplit_contDiff (n m : ℕ) :
    ContDiff ℝ m (finSuccSplitIsometry n) :=
  (finSuccSplitEquiv n).contDiff

/-- Pull a function on `Fin (n + 1) → ℝ` back to one normal and `n` tangential coordinates. -/
def coordinateSplitPullback {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) :
    (ℝ × (Fin n → ℝ)) → ℝ :=
  f ∘ finSuccJoinIsometry n

theorem coordinateSplitPullback_contDiff_iff {n m : ℕ}
    (f : (Fin (n + 1) → ℝ) → ℝ) :
    ContDiff ℝ m (coordinateSplitPullback f) ↔ ContDiff ℝ m f := by
  exact (finSuccJoinEquiv n).contDiff_comp_iff

theorem coordinateSplitPullback_iteratedFDeriv {n m j : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : ContDiff ℝ m f)
    (z : ℝ × (Fin n → ℝ)) (hj : j ≤ m) :
    iteratedFDeriv ℝ j (coordinateSplitPullback f) z =
      (iteratedFDeriv ℝ j f (finSuccJoinIsometry n z)).compContinuousLinearMap
        (fun _ ↦ (finSuccJoinEquiv n).toContinuousLinearMap) := by
  exact (finSuccJoinEquiv n).toContinuousLinearMap.iteratedFDeriv_comp_right hf z
    (by exact_mod_cast hj)

theorem norm_coordinateSplitPullback_iteratedFDeriv {n j : ℕ}
    (f : (Fin (n + 1) → ℝ) → ℝ) (z : ℝ × (Fin n → ℝ)) :
    ‖iteratedFDeriv ℝ j (coordinateSplitPullback f) z‖ =
      ‖iteratedFDeriv ℝ j f (finSuccJoinIsometry n z)‖ := by
  exact (finSuccJoinIsometry n).norm_iteratedFDeriv_comp_right f z j

/-- A coordinate frame obtained by first joining the normal/tangential coordinates and then
applying a chosen linear isometry of the ambient Euclidean space. -/
def rotatedCoordinateJoin {n : ℕ}
    (Q : (Fin (n + 1) → ℝ) ≃ₗᵢ[ℝ] (Fin (n + 1) → ℝ)) :
    (ℝ × (Fin n → ℝ)) ≃ₗᵢ[ℝ] (Fin (n + 1) → ℝ) :=
  (finSuccJoinIsometry n).trans Q

/-- The ambient unit vector represented by the normal coordinate of a rotated frame. -/
def rotatedCoordinateDirection {n : ℕ}
    (Q : (Fin (n + 1) → ℝ) ≃ₗᵢ[ℝ] (Fin (n + 1) → ℝ)) :
    Fin (n + 1) → ℝ :=
  Q (firstCoordinateDirection n)

@[simp]
theorem rotatedCoordinateJoin_splitNormalDirection {n : ℕ}
    (Q : (Fin (n + 1) → ℝ) ≃ₗᵢ[ℝ] (Fin (n + 1) → ℝ)) :
    rotatedCoordinateJoin Q (splitNormalDirection n) = rotatedCoordinateDirection Q := by
  rfl

@[simp]
theorem norm_rotatedCoordinateDirection {n : ℕ}
    (Q : (Fin (n + 1) → ℝ) ≃ₗᵢ[ℝ] (Fin (n + 1) → ℝ)) :
    ‖rotatedCoordinateDirection Q‖ = 1 := by
  rw [rotatedCoordinateDirection, Q.norm_map, norm_firstCoordinateDirection]

/-- Pull a function back through a chosen rotated normal/tangential coordinate frame. -/
def rotatedCoordinatePullback {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ)
    (Q : (Fin (n + 1) → ℝ) ≃ₗᵢ[ℝ] (Fin (n + 1) → ℝ)) :
    (ℝ × (Fin n → ℝ)) → ℝ :=
  f ∘ rotatedCoordinateJoin Q

theorem rotatedCoordinatePullback_contDiff_iff {n m : ℕ}
    (f : (Fin (n + 1) → ℝ) → ℝ)
    (Q : (Fin (n + 1) → ℝ) ≃ₗᵢ[ℝ] (Fin (n + 1) → ℝ)) :
    ContDiff ℝ m (rotatedCoordinatePullback f Q) ↔ ContDiff ℝ m f := by
  exact (rotatedCoordinateJoin Q).toContinuousLinearEquiv.contDiff_comp_iff

theorem rotatedCoordinatePullback_iteratedFDeriv {n m j : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : ContDiff ℝ m f)
    (Q : (Fin (n + 1) → ℝ) ≃ₗᵢ[ℝ] (Fin (n + 1) → ℝ))
    (z : ℝ × (Fin n → ℝ)) (hj : j ≤ m) :
    iteratedFDeriv ℝ j (rotatedCoordinatePullback f Q) z =
      (iteratedFDeriv ℝ j f (rotatedCoordinateJoin Q z)).compContinuousLinearMap
        (fun _ ↦ (rotatedCoordinateJoin Q).toContinuousLinearEquiv.toContinuousLinearMap) := by
  exact (rotatedCoordinateJoin Q).toContinuousLinearEquiv.toContinuousLinearMap
    |>.iteratedFDeriv_comp_right hf z (by exact_mod_cast hj)

theorem norm_rotatedCoordinatePullback_iteratedFDeriv {n j : ℕ}
    (f : (Fin (n + 1) → ℝ) → ℝ)
    (Q : (Fin (n + 1) → ℝ) ≃ₗᵢ[ℝ] (Fin (n + 1) → ℝ))
    (z : ℝ × (Fin n → ℝ)) :
    ‖iteratedFDeriv ℝ j (rotatedCoordinatePullback f Q) z‖ =
      ‖iteratedFDeriv ℝ j f (rotatedCoordinateJoin Q z)‖ := by
  exact (rotatedCoordinateJoin Q).norm_iteratedFDeriv_comp_right f z j

theorem rotatedCoordinatePullback_iteratedFDeriv_two_normal {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (Q : (Fin (n + 1) → ℝ) ≃ₗᵢ[ℝ] (Fin (n + 1) → ℝ))
    (z : ℝ × (Fin n → ℝ)) :
    iteratedFDeriv ℝ 2 (rotatedCoordinatePullback f Q) z
        ![splitNormalDirection n, splitNormalDirection n] =
      iteratedFDeriv ℝ 2 f (rotatedCoordinateJoin Q z)
        ![rotatedCoordinateDirection Q, rotatedCoordinateDirection Q] := by
  rw [rotatedCoordinatePullback_iteratedFDeriv hf Q z (by norm_num)]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  apply congrArg (iteratedFDeriv ℝ 2 f (rotatedCoordinateJoin Q z))
  funext i
  fin_cases i <;> simp

theorem rotatedCoordinatePullback_normal_fderiv {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (Q : (Fin (n + 1) → ℝ) ≃ₗᵢ[ℝ] (Fin (n + 1) → ℝ))
    (z : ℝ × (Fin n → ℝ)) :
    fderiv ℝ (rotatedCoordinatePullback f Q) z (splitNormalDirection n) =
      fderiv ℝ f (rotatedCoordinateJoin Q z) (rotatedCoordinateDirection Q) := by
  have hcomp := rotatedCoordinatePullback_iteratedFDeriv hf Q z (j := 1) (by norm_num)
  have happ := congrArg
    (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin 1 ↦ ℝ × (Fin n → ℝ)) ℝ ↦
      A (fun _ ↦ splitNormalDirection n)) hcomp
  simpa [iteratedFDeriv_one_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply] using happ

/-- The nested directional derivative used by `NormalizedLocalSplitInput.normal_curvature` is the
diagonal evaluation of the second iterated Fréchet derivative. -/
theorem fderiv_directionalFDeriv_eq_iteratedFDeriv_two {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v : E) :
    fderiv ℝ (fun y ↦ fderiv ℝ f y v) x v = iteratedFDeriv ℝ 2 f x ![v, v] := by
  have hfirst : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 f) x :=
    (hf.differentiable_iteratedFDeriv (by norm_num)).differentiableAt
  rw [show (fun y ↦ fderiv ℝ f y v) =
      (fun y ↦ iteratedFDeriv ℝ 1 f y (fun _ ↦ v)) by
        funext y
        simp [iteratedFDeriv_one_apply]]
  rw [fderiv_continuousMultilinear_apply_const hfirst (fun _ : Fin 1 ↦ v)]
  calc
    ((fderiv ℝ (iteratedFDeriv ℝ 1 f) x).flipMultilinear (fun _ ↦ v)) v =
        iteratedFDeriv ℝ 2 f x (fun _ ↦ v) := by
      rw [iteratedFDeriv_succ_apply_left]
      rfl
    _ = iteratedFDeriv ℝ 2 f x ![v, v] := by
      apply congrArg (iteratedFDeriv ℝ 2 f x)
      ext i
      fin_cases i <;> rfl

/-- Curvature in the normal coordinate of a rotated frame is exactly curvature of the original
function along the ambient direction represented by that frame. -/
theorem rotatedCoordinatePullback_normal_curvature {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (Q : (Fin (n + 1) → ℝ) ≃ₗᵢ[ℝ] (Fin (n + 1) → ℝ))
    (z : ℝ × (Fin n → ℝ)) :
    fderiv ℝ
        (fun w ↦ fderiv ℝ (rotatedCoordinatePullback f Q) w (splitNormalDirection n))
        z (splitNormalDirection n) =
      iteratedFDeriv ℝ 2 f (rotatedCoordinateJoin Q z)
        ![rotatedCoordinateDirection Q, rotatedCoordinateDirection Q] := by
  rw [fderiv_directionalFDeriv_eq_iteratedFDeriv_two
    ((rotatedCoordinatePullback_contDiff_iff f Q).2 hf) z (splitNormalDirection n)]
  exact rotatedCoordinatePullback_iteratedFDeriv_two_normal hf Q z

@[simp]
theorem rotatedCoordinateJoin_zero {n : ℕ}
    (Q : (Fin (n + 1) → ℝ) ≃ₗᵢ[ℝ] (Fin (n + 1) → ℝ)) :
    rotatedCoordinateJoin Q 0 = 0 :=
  map_zero _

/-- Origin form of `rotatedCoordinatePullback_normal_curvature`, matching the output of the
intrinsic-patch curvature dichotomy. -/
theorem rotatedCoordinatePullback_normal_curvature_zero {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (Q : (Fin (n + 1) → ℝ) ≃ₗᵢ[ℝ] (Fin (n + 1) → ℝ)) :
    fderiv ℝ
        (fun w ↦ fderiv ℝ (rotatedCoordinatePullback f Q) w (splitNormalDirection n))
        0 (splitNormalDirection n) =
      iteratedFDeriv ℝ 2 f 0
        ![rotatedCoordinateDirection Q, rotatedCoordinateDirection Q] := by
  simpa using rotatedCoordinatePullback_normal_curvature hf Q 0

/-- A general continuous linear coordinate frame. Unlike `rotatedCoordinateJoin`, this permits
Euclidean rotations transported to the repository's sup-norm coordinate model. -/
def continuousFrameCoordinateJoin {n : ℕ}
    (Q : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)) :
    (ℝ × (Fin n → ℝ)) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
  (finSuccJoinEquiv n).trans Q

/-- The ambient vector represented by the normal coordinate of a continuous linear frame. -/
def continuousFrameCoordinateDirection {n : ℕ}
    (Q : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)) :
    Fin (n + 1) → ℝ :=
  Q (firstCoordinateDirection n)

@[simp]
theorem continuousFrameCoordinateJoin_splitNormalDirection {n : ℕ}
    (Q : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)) :
    continuousFrameCoordinateJoin Q (splitNormalDirection n) =
      continuousFrameCoordinateDirection Q := by
  rfl

@[simp]
theorem continuousFrameCoordinateJoin_zero {n : ℕ}
    (Q : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)) :
    continuousFrameCoordinateJoin Q 0 = 0 :=
  map_zero _

/-- Pullback through an arbitrary continuous linear normal/tangential frame. -/
def continuousFrameCoordinatePullback {n : ℕ}
    (f : (Fin (n + 1) → ℝ) → ℝ)
    (Q : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)) :
    (ℝ × (Fin n → ℝ)) → ℝ :=
  f ∘ continuousFrameCoordinateJoin Q

theorem continuousFrameCoordinatePullback_contDiff_iff {n m : ℕ}
    (f : (Fin (n + 1) → ℝ) → ℝ)
    (Q : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)) :
    ContDiff ℝ m (continuousFrameCoordinatePullback f Q) ↔ ContDiff ℝ m f := by
  exact (continuousFrameCoordinateJoin Q).contDiff_comp_iff

theorem continuousFrameCoordinatePullback_iteratedFDeriv {n m j : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : ContDiff ℝ m f)
    (Q : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ))
    (z : ℝ × (Fin n → ℝ)) (hj : j ≤ m) :
    iteratedFDeriv ℝ j (continuousFrameCoordinatePullback f Q) z =
      (iteratedFDeriv ℝ j f (continuousFrameCoordinateJoin Q z)).compContinuousLinearMap
        (fun _ ↦ (continuousFrameCoordinateJoin Q).toContinuousLinearMap) := by
  exact (continuousFrameCoordinateJoin Q).toContinuousLinearMap.iteratedFDeriv_comp_right hf z
    (by exact_mod_cast hj)

/-- A general continuous frame changes a `j`-jet by at most the `j`-th power of its operator
norm. This is the quantitative replacement for isometric invariance when a genuine Euclidean
rotation is viewed in the repository's sup-norm coordinates. -/
theorem norm_continuousFrameCoordinatePullback_iteratedFDeriv_le {n m j : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : ContDiff ℝ m f)
    (Q : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ))
    (z : ℝ × (Fin n → ℝ)) (hj : j ≤ m) :
    ‖iteratedFDeriv ℝ j (continuousFrameCoordinatePullback f Q) z‖ ≤
      ‖iteratedFDeriv ℝ j f (continuousFrameCoordinateJoin Q z)‖ *
        ‖(continuousFrameCoordinateJoin Q).toContinuousLinearMap‖ ^ j := by
  rw [continuousFrameCoordinatePullback_iteratedFDeriv hf Q z hj]
  simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ j f (continuousFrameCoordinateJoin Q z))
    (fun _ : Fin j ↦ (continuousFrameCoordinateJoin Q).toContinuousLinearMap)

theorem continuousFrameCoordinatePullback_iteratedFDeriv_two_normal {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (Q : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ))
    (z : ℝ × (Fin n → ℝ)) :
    iteratedFDeriv ℝ 2 (continuousFrameCoordinatePullback f Q) z
        ![splitNormalDirection n, splitNormalDirection n] =
      iteratedFDeriv ℝ 2 f (continuousFrameCoordinateJoin Q z)
        ![continuousFrameCoordinateDirection Q, continuousFrameCoordinateDirection Q] := by
  rw [continuousFrameCoordinatePullback_iteratedFDeriv hf Q z (by norm_num)]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  apply congrArg (iteratedFDeriv ℝ 2 f (continuousFrameCoordinateJoin Q z))
  ext i
  fin_cases i <;> simp

/-- UniformSplit's nested normal curvature after pullback through an arbitrary continuous frame. -/
theorem continuousFrameCoordinatePullback_normal_curvature {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (Q : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ))
    (z : ℝ × (Fin n → ℝ)) :
    fderiv ℝ
        (fun w ↦ fderiv ℝ (continuousFrameCoordinatePullback f Q) w
          (splitNormalDirection n)) z (splitNormalDirection n) =
      iteratedFDeriv ℝ 2 f (continuousFrameCoordinateJoin Q z)
        ![continuousFrameCoordinateDirection Q, continuousFrameCoordinateDirection Q] := by
  rw [fderiv_directionalFDeriv_eq_iteratedFDeriv_two
    ((continuousFrameCoordinatePullback_contDiff_iff f Q).2 hf) z (splitNormalDirection n)]
  exact continuousFrameCoordinatePullback_iteratedFDeriv_two_normal hf Q z

/-- A triangular change of variables on normal/tangential product coordinates. It sends
`(1, 0)` to `(a, b)` and is invertible exactly when `a` is nonzero. -/
def normalTangentialTriangularEquiv {n : ℕ} (a : ℝ) (ha : a ≠ 0)
    (b : Fin n → ℝ) :
    (ℝ × (Fin n → ℝ)) ≃ₗ[ℝ] ℝ × (Fin n → ℝ) where
  toFun z := (a * z.1, z.2 + z.1 • b)
  invFun z := (a⁻¹ * z.1, z.2 - (a⁻¹ * z.1) • b)
  left_inv z := by
    ext <;> simp [ha]
  right_inv z := by
    ext <;> simp [ha]
  map_add' x y := by
    ext <;> simp [add_smul] <;> ring
  map_smul' c x := by
    ext <;> simp [smul_add, smul_smul] ; ring

/-- The triangular change of variables as a continuous linear equivalence. -/
abbrev normalTangentialTriangularContinuousEquiv {n : ℕ} (a : ℝ) (ha : a ≠ 0)
    (b : Fin n → ℝ) :
    (ℝ × (Fin n → ℝ)) ≃L[ℝ] ℝ × (Fin n → ℝ) :=
  (normalTangentialTriangularEquiv a ha b).toContinuousLinearEquiv

@[simp]
theorem normalTangentialTriangularEquiv_splitNormalDirection {n : ℕ}
    (a : ℝ) (ha : a ≠ 0) (b : Fin n → ℝ) :
    normalTangentialTriangularEquiv a ha b (splitNormalDirection n) = (a, b) := by
  simp [normalTangentialTriangularEquiv, splitNormalDirection]

/-- If the leading coordinate of `v` is nonzero, this explicit frame has `v` as its normal
direction. -/
def leadingCoordinateFrame {n : ℕ} (v : Fin (n + 1) → ℝ) (hv : v 0 ≠ 0) :
    (ℝ × (Fin n → ℝ)) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
  (normalTangentialTriangularContinuousEquiv (v 0) hv (Fin.tail v)).trans
    (finSuccJoinEquiv n)

@[simp]
theorem leadingCoordinateFrame_splitNormalDirection {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hv : v 0 ≠ 0) :
    leadingCoordinateFrame v hv (splitNormalDirection n) = v := by
  simp [leadingCoordinateFrame]

/-- Swap the leading coordinate with a prescribed pivot. -/
def coordinateSwapEquiv {n : ℕ} (p : Fin (n + 1)) :
    (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (n + 1) ↦ ℝ) (Equiv.swap 0 p)

@[simp]
theorem coordinateSwapEquiv_symm_apply_zero {n : ℕ} (p : Fin (n + 1))
    (v : Fin (n + 1) → ℝ) :
    (coordinateSwapEquiv p).symm v 0 = v p := by
  change v (Equiv.swap 0 p 0) = v p
  simp

/-- An explicit continuous linear frame whose normal direction is `v`, using any nonzero
coordinate of `v` as a pivot. -/
noncomputable def pivotCoordinateFrame {n : ℕ} (v : Fin (n + 1) → ℝ)
    (p : Fin (n + 1)) (hp : v p ≠ 0) :
    (ℝ × (Fin n → ℝ)) ≃L[ℝ] (Fin (n + 1) → ℝ) := by
  let P := coordinateSwapEquiv p
  let w := P.symm v
  have hw : w 0 ≠ 0 := by
    simpa [w, P] using hp
  exact (leadingCoordinateFrame w hw).trans P

@[simp]
theorem pivotCoordinateFrame_splitNormalDirection {n : ℕ}
    (v : Fin (n + 1) → ℝ) (p : Fin (n + 1)) (hp : v p ≠ 0) :
    pivotCoordinateFrame v p hp (splitNormalDirection n) = v := by
  rw [pivotCoordinateFrame]
  simp

/-- Every nonzero ambient direction is the normal direction of a continuous linear frame. -/
theorem exists_coordinateFrame_of_ne_zero {n : ℕ} {v : Fin (n + 1) → ℝ}
    (hv : v ≠ 0) :
    ∃ T : (ℝ × (Fin n → ℝ)) ≃L[ℝ] (Fin (n + 1) → ℝ),
      T (splitNormalDirection n) = v := by
  obtain ⟨p, hp⟩ : ∃ p, v p ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  exact ⟨pivotCoordinateFrame v p hp, pivotCoordinateFrame_splitNormalDirection v p hp⟩

/-- In particular, every unit direction returned by the curvature dichotomy admits such a
normal/tangential coordinate frame. -/
theorem exists_coordinateFrame_of_norm_eq_one {n : ℕ} {v : Fin (n + 1) → ℝ}
    (hv : ‖v‖ = 1) :
    ∃ T : (ℝ × (Fin n → ℝ)) ≃L[ℝ] (Fin (n + 1) → ℝ),
      T (splitNormalDirection n) = v := by
  apply exists_coordinateFrame_of_ne_zero
  intro hvzero
  rw [hvzero, norm_zero] at hv
  norm_num at hv

/-- The sup norm of a nonempty finite tuple is attained by one coordinate. -/
theorem exists_coordinate_norm_eq_norm {n : ℕ} (v : Fin (n + 1) → ℝ) :
    ∃ p : Fin (n + 1), ‖v p‖ = ‖v‖ := by
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun i ↦ ‖v i‖₊)
  refine ⟨p, ?_⟩
  have hnn : ‖v‖₊ = ‖v p‖₊ := (Pi.nnnorm_def v).trans hp
  simpa using congrArg ((↑) : NNReal → ℝ) hnn.symm

/-- A coordinate at which the sup norm of a finite tuple is attained. -/
noncomputable def maxNormCoordinate {n : ℕ} (v : Fin (n + 1) → ℝ) : Fin (n + 1) :=
  Classical.choose (exists_coordinate_norm_eq_norm v)

@[simp]
theorem norm_apply_maxNormCoordinate {n : ℕ} (v : Fin (n + 1) → ℝ) :
    ‖v (maxNormCoordinate v)‖ = ‖v‖ :=
  Classical.choose_spec (exists_coordinate_norm_eq_norm v)

/-- The maximum-norm pivot of a unit direction is nonzero. -/
theorem apply_maxNormCoordinate_ne_zero_of_norm_eq_one {n : ℕ}
    {v : Fin (n + 1) → ℝ} (hv : ‖v‖ = 1) :
    v (maxNormCoordinate v) ≠ 0 := by
  intro hzero
  have := norm_apply_maxNormCoordinate v
  rw [hzero, norm_zero, hv] at this
  norm_num at this

/-- The canonical well-pivoted continuous frame attached to a sup-norm unit direction. -/
noncomputable def unitDirectionCoordinateFrame {n : ℕ} (v : Fin (n + 1) → ℝ)
    (hv : ‖v‖ = 1) :
    (ℝ × (Fin n → ℝ)) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
  pivotCoordinateFrame v (maxNormCoordinate v)
    (apply_maxNormCoordinate_ne_zero_of_norm_eq_one hv)

@[simp]
theorem unitDirectionCoordinateFrame_splitNormalDirection {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1) :
    unitDirectionCoordinateFrame v hv (splitNormalDirection n) = v := by
  exact pivotCoordinateFrame_splitNormalDirection v (maxNormCoordinate v)
    (apply_maxNormCoordinate_ne_zero_of_norm_eq_one hv)

@[simp]
theorem coordinateSwapEquiv_apply_swap {n : ℕ} (p : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    coordinateSwapEquiv p x (Equiv.swap 0 p i) = x i := by
  change (Equiv.piCongrLeft (fun _ : Fin (n + 1) ↦ ℝ) (Equiv.swap 0 p)) x
    (Equiv.swap 0 p i) = x i
  exact Equiv.piCongrLeft_apply_apply (fun _ : Fin (n + 1) ↦ ℝ) (Equiv.swap 0 p) x i

@[simp]
theorem norm_coordinateSwapEquiv {n : ℕ} (p : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) :
    ‖coordinateSwapEquiv p x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2
    intro i
    let e : Fin (n + 1) ≃ Fin (n + 1) := Equiv.swap 0 p
    let j := e.symm i
    have hij : e j = i := e.apply_symm_apply i
    rw [← hij]
    exact (by simpa [e] using norm_le_pi_norm x j)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (coordinateSwapEquiv p x))).2
    intro i
    have hi := norm_le_pi_norm (coordinateSwapEquiv p x) (Equiv.swap 0 p i)
    simpa using hi

theorem norm_finTail_le {n : ℕ} (x : Fin (n + 1) → ℝ) :
    ‖Fin.tail x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2
  intro i
  exact norm_le_pi_norm x i.succ

/-- With unit leading coefficient and a unit-bounded tangential component, the triangular frame
has forward Lipschitz constant two in the repository's product sup norm. -/
theorem norm_normalTangentialTriangularEquiv_le_two_mul {n : ℕ}
    {a : ℝ} (ha : a ≠ 0) (hanorm : ‖a‖ = 1) {b : Fin n → ℝ} (hb : ‖b‖ ≤ 1)
    (z : ℝ × (Fin n → ℝ)) :
    ‖normalTangentialTriangularEquiv a ha b z‖ ≤ 2 * ‖z‖ := by
  rw [Prod.norm_def]
  apply max_le
  · change ‖a * z.1‖ ≤ 2 * ‖z‖
    rw [norm_mul, hanorm, one_mul]
    nlinarith [norm_fst_le z, norm_nonneg z]
  · change ‖z.2 + z.1 • b‖ ≤ 2 * ‖z‖
    calc
      ‖z.2 + z.1 • b‖ ≤ ‖z.2‖ + ‖z.1 • b‖ := norm_add_le _ _
      _ = ‖z.2‖ + ‖z.1‖ * ‖b‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖z‖ + ‖z‖ * 1 := by
        gcongr
        · exact norm_snd_le z
        · exact norm_fst_le z
      _ = 2 * ‖z‖ := by ring

/-- Operator-norm form of `norm_normalTangentialTriangularEquiv_le_two_mul`. -/
theorem norm_normalTangentialTriangularContinuousEquiv_le_two {n : ℕ}
    {a : ℝ} (ha : a ≠ 0) (hanorm : ‖a‖ = 1) {b : Fin n → ℝ} (hb : ‖b‖ ≤ 1) :
    ‖(normalTangentialTriangularContinuousEquiv a ha b).toContinuousLinearMap‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  exact norm_normalTangentialTriangularEquiv_le_two_mul ha hanorm hb z

@[simp]
theorem norm_coordinateSwapEquiv_symm {n : ℕ} (p : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) :
    ‖(coordinateSwapEquiv p).symm x‖ = ‖x‖ := by
  have h := norm_coordinateSwapEquiv p ((coordinateSwapEquiv p).symm x)
  simpa using h.symm

@[simp]
theorem norm_finSuccJoinEquiv (n : ℕ) (z : ℝ × (Fin n → ℝ)) :
    ‖finSuccJoinEquiv n z‖ = ‖z‖ := by
  exact (finSuccJoinIsometry n).norm_map z

theorem norm_leadingCoordinateFrame_apply_le_two_mul {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hv : v 0 ≠ 0) (hvzero : ‖v 0‖ = 1)
    (hvtail : ‖Fin.tail v‖ ≤ 1) (z : ℝ × (Fin n → ℝ)) :
    ‖leadingCoordinateFrame v hv z‖ ≤ 2 * ‖z‖ := by
  change ‖finSuccJoinEquiv n
      (normalTangentialTriangularContinuousEquiv (v 0) hv (Fin.tail v) z)‖ ≤ _
  rw [norm_finSuccJoinEquiv]
  exact norm_normalTangentialTriangularEquiv_le_two_mul hv hvzero hvtail z

/-- A pivot frame based at a norm-one coordinate has forward operator norm at most two. -/
theorem norm_pivotCoordinateFrame_apply_le_two_mul {n : ℕ}
    (v : Fin (n + 1) → ℝ) (p : Fin (n + 1)) (hp : v p ≠ 0)
    (hv : ‖v‖ = 1) (hpNorm : ‖v p‖ = 1) (z : ℝ × (Fin n → ℝ)) :
    ‖pivotCoordinateFrame v p hp z‖ ≤ 2 * ‖z‖ := by
  let P := coordinateSwapEquiv p
  let w := P.symm v
  have hw : w 0 ≠ 0 := by
    simpa [w, P] using hp
  have hwzero : ‖w 0‖ = 1 := by
    simpa [w, P] using hpNorm
  have hwtail : ‖Fin.tail w‖ ≤ 1 := by
    calc
      ‖Fin.tail w‖ ≤ ‖w‖ := norm_finTail_le w
      _ = ‖v‖ := by simp [w, P]
      _ = 1 := hv
  rw [pivotCoordinateFrame]
  change ‖P (leadingCoordinateFrame w hw z)‖ ≤ _
  rw [show ‖P (leadingCoordinateFrame w hw z)‖ =
      ‖leadingCoordinateFrame w hw z‖ by simp [P]]
  exact norm_leadingCoordinateFrame_apply_le_two_mul w hw hwzero hwtail z

/-- The canonical frame of a sup-norm unit direction has forward Lipschitz constant two. -/
theorem norm_unitDirectionCoordinateFrame_apply_le_two_mul {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1) (z : ℝ × (Fin n → ℝ)) :
    ‖unitDirectionCoordinateFrame v hv z‖ ≤ 2 * ‖z‖ := by
  apply norm_pivotCoordinateFrame_apply_le_two_mul v (maxNormCoordinate v)
    (apply_maxNormCoordinate_ne_zero_of_norm_eq_one hv) hv
  simpa using (norm_apply_maxNormCoordinate v).trans hv

theorem norm_unitDirectionCoordinateFrame_le_two {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1) :
    ‖(unitDirectionCoordinateFrame v hv).toContinuousLinearMap‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  exact norm_unitDirectionCoordinateFrame_apply_le_two_mul v hv

/-- The inverse triangular frame has the same Lipschitz constant two under the unit hypotheses. -/
theorem norm_normalTangentialTriangularEquiv_symm_le_two_mul {n : ℕ}
    {a : ℝ} (ha : a ≠ 0) (hanorm : ‖a‖ = 1) {b : Fin n → ℝ} (hb : ‖b‖ ≤ 1)
    (z : ℝ × (Fin n → ℝ)) :
    ‖(normalTangentialTriangularEquiv a ha b).symm z‖ ≤ 2 * ‖z‖ := by
  rw [Prod.norm_def]
  apply max_le
  · change ‖a⁻¹ * z.1‖ ≤ 2 * ‖z‖
    rw [norm_mul, norm_inv, hanorm, inv_one, one_mul]
    nlinarith [norm_fst_le z, norm_nonneg z]
  · change ‖z.2 - (a⁻¹ * z.1) • b‖ ≤ 2 * ‖z‖
    calc
      ‖z.2 - (a⁻¹ * z.1) • b‖ ≤ ‖z.2‖ + ‖(a⁻¹ * z.1) • b‖ := norm_sub_le _ _
      _ = ‖z.2‖ + ‖a⁻¹ * z.1‖ * ‖b‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = ‖z.2‖ + ‖z.1‖ * ‖b‖ := by
        rw [norm_mul, norm_inv, hanorm, inv_one, one_mul]
      _ ≤ ‖z‖ + ‖z‖ * 1 := by
        gcongr
        · exact norm_snd_le z
        · exact norm_fst_le z
      _ = 2 * ‖z‖ := by ring

@[simp]
theorem norm_finSuccSplitEquiv (n : ℕ) (x : Fin (n + 1) → ℝ) :
    ‖finSuccSplitEquiv n x‖ = ‖x‖ := by
  exact (finSuccSplitIsometry n).norm_map x

theorem norm_leadingCoordinateFrame_symm_apply_le_two_mul {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hv : v 0 ≠ 0) (hvzero : ‖v 0‖ = 1)
    (hvtail : ‖Fin.tail v‖ ≤ 1) (x : Fin (n + 1) → ℝ) :
    ‖(leadingCoordinateFrame v hv).symm x‖ ≤ 2 * ‖x‖ := by
  change ‖(normalTangentialTriangularContinuousEquiv (v 0) hv (Fin.tail v)).symm
      (finSuccSplitEquiv n x)‖ ≤ _
  calc
    ‖(normalTangentialTriangularContinuousEquiv (v 0) hv (Fin.tail v)).symm
        (finSuccSplitEquiv n x)‖ ≤ 2 * ‖finSuccSplitEquiv n x‖ :=
      norm_normalTangentialTriangularEquiv_symm_le_two_mul hv hvzero hvtail _
    _ = 2 * ‖x‖ := by rw [norm_finSuccSplitEquiv]

theorem norm_pivotCoordinateFrame_symm_apply_le_two_mul {n : ℕ}
    (v : Fin (n + 1) → ℝ) (p : Fin (n + 1)) (hp : v p ≠ 0)
    (hv : ‖v‖ = 1) (hpNorm : ‖v p‖ = 1) (x : Fin (n + 1) → ℝ) :
    ‖(pivotCoordinateFrame v p hp).symm x‖ ≤ 2 * ‖x‖ := by
  let P := coordinateSwapEquiv p
  let w := P.symm v
  have hw : w 0 ≠ 0 := by
    simpa [w, P] using hp
  have hwzero : ‖w 0‖ = 1 := by
    simpa [w, P] using hpNorm
  have hwtail : ‖Fin.tail w‖ ≤ 1 := by
    calc
      ‖Fin.tail w‖ ≤ ‖w‖ := norm_finTail_le w
      _ = ‖v‖ := by simp [w, P]
      _ = 1 := hv
  rw [pivotCoordinateFrame]
  change ‖(leadingCoordinateFrame w hw).symm (P.symm x)‖ ≤ _
  calc
    ‖(leadingCoordinateFrame w hw).symm (P.symm x)‖ ≤ 2 * ‖P.symm x‖ :=
      norm_leadingCoordinateFrame_symm_apply_le_two_mul w hw hwzero hwtail _
    _ = 2 * ‖x‖ := by simp [P]

theorem norm_unitDirectionCoordinateFrame_symm_apply_le_two_mul {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1) (x : Fin (n + 1) → ℝ) :
    ‖(unitDirectionCoordinateFrame v hv).symm x‖ ≤ 2 * ‖x‖ := by
  apply norm_pivotCoordinateFrame_symm_apply_le_two_mul v (maxNormCoordinate v)
    (apply_maxNormCoordinate_ne_zero_of_norm_eq_one hv) hv
  simpa using (norm_apply_maxNormCoordinate v).trans hv

theorem norm_unitDirectionCoordinateFrame_symm_le_two {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1) :
    ‖(unitDirectionCoordinateFrame v hv).symm.toContinuousLinearMap‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  exact norm_unitDirectionCoordinateFrame_symm_apply_le_two_mul v hv

/-- Pullback through a supplied normal/tangential continuous linear frame. -/
def coordinateFramePullback {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ)
    (T : (ℝ × (Fin n → ℝ)) ≃L[ℝ] (Fin (n + 1) → ℝ)) :
    (ℝ × (Fin n → ℝ)) → ℝ :=
  f ∘ T

theorem coordinateFramePullback_contDiff_iff {n m : ℕ}
    (f : (Fin (n + 1) → ℝ) → ℝ)
    (T : (ℝ × (Fin n → ℝ)) ≃L[ℝ] (Fin (n + 1) → ℝ)) :
    ContDiff ℝ m (coordinateFramePullback f T) ↔ ContDiff ℝ m f := by
  exact T.contDiff_comp_iff

theorem coordinateFramePullback_iteratedFDeriv {n m j : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : ContDiff ℝ m f)
    (T : (ℝ × (Fin n → ℝ)) ≃L[ℝ] (Fin (n + 1) → ℝ))
    (z : ℝ × (Fin n → ℝ)) (hj : j ≤ m) :
    iteratedFDeriv ℝ j (coordinateFramePullback f T) z =
      (iteratedFDeriv ℝ j f (T z)).compContinuousLinearMap
        (fun _ ↦ T.toContinuousLinearMap) := by
  exact T.toContinuousLinearMap.iteratedFDeriv_comp_right hf z (by exact_mod_cast hj)

theorem norm_coordinateFramePullback_iteratedFDeriv_le {n m j : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : ContDiff ℝ m f)
    (T : (ℝ × (Fin n → ℝ)) ≃L[ℝ] (Fin (n + 1) → ℝ))
    (z : ℝ × (Fin n → ℝ)) (hj : j ≤ m) :
    ‖iteratedFDeriv ℝ j (coordinateFramePullback f T) z‖ ≤
      ‖iteratedFDeriv ℝ j f (T z)‖ * ‖T.toContinuousLinearMap‖ ^ j := by
  rw [coordinateFramePullback_iteratedFDeriv hf T z hj]
  simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ j f (T z)) (fun _ : Fin j ↦ T.toContinuousLinearMap)

/-- Exact second directional derivative after pullback through a frame with prescribed normal. -/
theorem coordinateFramePullback_iteratedFDeriv_two_normal {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (T : (ℝ × (Fin n → ℝ)) ≃L[ℝ] (Fin (n + 1) → ℝ))
    (v : Fin (n + 1) → ℝ) (hT : T (splitNormalDirection n) = v)
    (z : ℝ × (Fin n → ℝ)) :
    iteratedFDeriv ℝ 2 (coordinateFramePullback f T) z
        ![splitNormalDirection n, splitNormalDirection n] =
      iteratedFDeriv ℝ 2 f (T z) ![v, v] := by
  rw [coordinateFramePullback_iteratedFDeriv hf T z (by norm_num)]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  apply congrArg (iteratedFDeriv ℝ 2 f (T z))
  ext i
  fin_cases i <;> simp [hT]

/-- Exact nested normal curvature in the form required by `NormalizedLocalSplitInput`. -/
theorem coordinateFramePullback_normal_curvature {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (T : (ℝ × (Fin n → ℝ)) ≃L[ℝ] (Fin (n + 1) → ℝ))
    (v : Fin (n + 1) → ℝ) (hT : T (splitNormalDirection n) = v)
    (z : ℝ × (Fin n → ℝ)) :
    fderiv ℝ (fun w ↦ fderiv ℝ (coordinateFramePullback f T) w
        (splitNormalDirection n)) z (splitNormalDirection n) =
      iteratedFDeriv ℝ 2 f (T z) ![v, v] := by
  rw [fderiv_directionalFDeriv_eq_iteratedFDeriv_two
    ((coordinateFramePullback_contDiff_iff f T).2 hf) z (splitNormalDirection n)]
  exact coordinateFramePullback_iteratedFDeriv_two_normal hf T v hT z

/-- Pullback through the canonical uniformly conditioned frame attached to a unit direction. -/
def unitDirectionCoordinatePullback {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ)
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1) :
    (ℝ × (Fin n → ℝ)) → ℝ :=
  coordinateFramePullback f (unitDirectionCoordinateFrame v hv)

theorem unitDirectionCoordinatePullback_contDiff_iff {n m : ℕ}
    (f : (Fin (n + 1) → ℝ) → ℝ) (v : Fin (n + 1) → ℝ)
    (hv : ‖v‖ = 1) :
    ContDiff ℝ m (unitDirectionCoordinatePullback f v hv) ↔ ContDiff ℝ m f :=
  coordinateFramePullback_contDiff_iff f (unitDirectionCoordinateFrame v hv)

theorem norm_unitDirectionCoordinatePullback_iteratedFDeriv_le {n m j : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : ContDiff ℝ m f)
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1)
    (z : ℝ × (Fin n → ℝ)) (hj : j ≤ m) :
    ‖iteratedFDeriv ℝ j (unitDirectionCoordinatePullback f v hv) z‖ ≤
      ‖iteratedFDeriv ℝ j f (unitDirectionCoordinateFrame v hv z)‖ * 2 ^ j := by
  calc
    ‖iteratedFDeriv ℝ j (unitDirectionCoordinatePullback f v hv) z‖ ≤
        ‖iteratedFDeriv ℝ j f (unitDirectionCoordinateFrame v hv z)‖ *
          ‖(unitDirectionCoordinateFrame v hv).toContinuousLinearMap‖ ^ j :=
      norm_coordinateFramePullback_iteratedFDeriv_le hf _ z hj
    _ ≤ ‖iteratedFDeriv ℝ j f (unitDirectionCoordinateFrame v hv z)‖ * 2 ^ j := by
      gcongr
      exact norm_unitDirectionCoordinateFrame_le_two v hv

theorem unitDirectionCoordinatePullback_normal_curvature {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1)
    (z : ℝ × (Fin n → ℝ)) :
    fderiv ℝ (fun w ↦ fderiv ℝ (unitDirectionCoordinatePullback f v hv) w
        (splitNormalDirection n)) z (splitNormalDirection n) =
      iteratedFDeriv ℝ 2 f (unitDirectionCoordinateFrame v hv z) ![v, v] := by
  exact coordinateFramePullback_normal_curvature hf (unitDirectionCoordinateFrame v hv) v
    (unitDirectionCoordinateFrame_splitNormalDirection v hv) z

theorem unitDirectionCoordinatePullback_normal_curvature_zero {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1) :
    fderiv ℝ (fun w ↦ fderiv ℝ (unitDirectionCoordinatePullback f v hv) w
        (splitNormalDirection n)) 0 (splitNormalDirection n) =
      iteratedFDeriv ℝ 2 f 0 ![v, v] := by
  simpa using unitDirectionCoordinatePullback_normal_curvature hf v hv 0

/-- A positive-curvature witness from the intrinsic dichotomy becomes the precise origin
curvature bound required by the one-normal-coordinate split. -/
theorem unitDirectionCoordinatePullback_normal_curvature_zero_ge_quarter {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1)
    (hcurv : (1 / 4 : ℝ) ≤ iteratedFDeriv ℝ 2 f 0 ![v, v]) :
    (1 / 4 : ℝ) ≤
      fderiv ℝ (fun w ↦ fderiv ℝ (unitDirectionCoordinatePullback f v hv) w
        (splitNormalDirection n)) 0 (splitNormalDirection n) := by
  rwa [unitDirectionCoordinatePullback_normal_curvature_zero hf v hv]

/-- The intrinsically rescaled parent patch in the canonical coordinates of a unit curvature
direction. -/
def intrinsicUnitDirectionCoordinatePullback {n : ℕ}
    (u : (Fin (n + 1) → ℝ) → ℝ) (c v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1) :
    (ℝ × (Fin n → ℝ)) → ℝ :=
  unitDirectionCoordinatePullback
    (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) v hv

theorem intrinsicUnitDirectionCoordinatePullback_contDiff_six {n : ℕ}
    {u : (Fin (n + 1) → ℝ) → ℝ} (hu : ContDiff ℝ 6 u)
    (c v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1) :
    ContDiff ℝ 6 (intrinsicUnitDirectionCoordinatePullback u c v hv) := by
  exact (unitDirectionCoordinatePullback_contDiff_iff _ v hv).2
    (intrinsicRescaledPatch_contDiff hu c (nonnegativeJetScale u c))

theorem intrinsicUnitDirectionCoordinatePullback_nonnegative {n : ℕ}
    {u : (Fin (n + 1) → ℝ) → ℝ} (hu : ∀ x, 0 ≤ u x)
    (c v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1)
    (hR : 0 < nonnegativeJetScale u c) :
    ∀ z, 0 ≤ intrinsicUnitDirectionCoordinatePullback u c v hv z := by
  intro z
  exact intrinsicRescaledPatch_nonnegative hu c hR (unitDirectionCoordinateFrame v hv z)

/-- On the half unit ball, the canonical direction frame preserves the intrinsic uniform jet
bound with only the explicit factor `2 ^ j`. -/
theorem intrinsicUnitDirectionCoordinatePullback_uniform_deriv_on_halfBall {n : ℕ}
    {u : (Fin (n + 1) → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C) (c v : Fin (n + 1) → ℝ)
    (hv : ‖v‖ = 1) (hR : 0 < nonnegativeJetScale u c)
    (z : ℝ × (Fin n → ℝ)) (hz : ‖z‖ ≤ 1 / 2) :
    ∀ j, j ≤ 6 →
      ‖iteratedFDeriv ℝ j (intrinsicUnitDirectionCoordinatePullback u c v hv) z‖ ≤
        (4 * (C + 1)) * 2 ^ j := by
  intro j hj
  have hpoint : ‖unitDirectionCoordinateFrame v hv z‖ ≤ 1 := by
    calc
      ‖unitDirectionCoordinateFrame v hv z‖ ≤ 2 * ‖z‖ :=
        norm_unitDirectionCoordinateFrame_apply_le_two_mul v hv z
      _ ≤ 1 := by nlinarith
  calc
    ‖iteratedFDeriv ℝ j (intrinsicUnitDirectionCoordinatePullback u c v hv) z‖ ≤
        ‖iteratedFDeriv ℝ j
          (intrinsicRescaledPatch u c (nonnegativeJetScale u c))
          (unitDirectionCoordinateFrame v hv z)‖ * 2 ^ j :=
      norm_unitDirectionCoordinatePullback_iteratedFDeriv_le
        (intrinsicRescaledPatch_contDiff hu.contDiff c (nonnegativeJetScale u c))
        v hv z hj
    _ ≤ (4 * (C + 1)) * 2 ^ j := by
      gcongr
      exact intrinsicRescaledPatch_uniform_deriv_on_unitBall
        hu hcontrol c hR (unitDirectionCoordinateFrame v hv z) hpoint j hj

/-- The intrinsic value-versus-curvature dichotomy, with its curvature branch already expressed
in the exact normal-coordinate form consumed by `NormalizedLocalSplitInput`. -/
theorem intrinsicRescaledPatch_value_or_splitNormalCurvature {n : ℕ}
    {u : (Fin (n + 1) → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C) (c : Fin (n + 1) → ℝ)
    (hR : 0 < nonnegativeJetScale u c) :
    curvatureValueThreshold C ≤
        intrinsicRescaledPatch u c (nonnegativeJetScale u c) 0 ∨
      ∃ (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1),
        (1 / 4 : ℝ) ≤
          fderiv ℝ
            (fun w ↦ fderiv ℝ (intrinsicUnitDirectionCoordinatePullback u c v hv) w
              (splitNormalDirection n)) 0 (splitNormalDirection n) := by
  rcases intrinsicRescaledPatch_value_or_positive_curvature hu hcontrol c hR with
    hvalue | ⟨v, hv, hcurv⟩
  · exact Or.inl hvalue
  · right
    refine ⟨v, hv, ?_⟩
    exact unitDirectionCoordinatePullback_normal_curvature_zero_ge_quarter
      ((intrinsicRescaledPatch_contDiff hu.contDiff c (nonnegativeJetScale u c)).of_le
        (by norm_num)) v hv hcurv

end OptimalConvergenceRates.QuarticConvergence
