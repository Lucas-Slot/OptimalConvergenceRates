/- Quantitative geometry for products of two axial reflections. -/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FilterRotationAction
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FilterLinearGeometry

open Finset Set
open scoped RealInnerProductSpace

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

/-- The repository's axial reflection, transported to the ambient coordinate norm. -/
noncomputable def sphereAxialReflectionCoordinateEquiv {n : ℕ}
    (x : sphereSet n) : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  (((EuclideanSpace.equiv (Fin n) ℝ).symm.trans
      (sphereAxialReflectionLinearIsometry x).toContinuousLinearEquiv).trans
    (EuclideanSpace.equiv (Fin n) ℝ))

/-- The continuous-linear-map version used in derivative pullbacks. -/
noncomputable def sphereAxialReflectionCoordinateCLM {n : ℕ}
    (x : sphereSet n) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (sphereAxialReflectionCoordinateEquiv x).toContinuousLinearMap

@[simp] theorem sphereAxialReflectionCoordinateEquiv_apply {n : ℕ}
    (x : sphereSet n) (y : Fin n → ℝ) :
    sphereAxialReflectionCoordinateEquiv x y =
      sphereAxialReflectionRaw x.1 y := by
  apply (EuclideanSpace.equiv (Fin n) ℝ).symm.injective
  change sphereAxialReflectionLinearIsometry x
      ((EuclideanSpace.equiv (Fin n) ℝ).symm y) =
    (EuclideanSpace.equiv (Fin n) ℝ).symm
      (sphereAxialReflectionRaw x.1 y)
  rw [sphereAxialReflectionLinearIsometry_apply]
  congr 1

@[simp] theorem sphereAxialReflectionCoordinateCLM_apply {n : ℕ}
    (x : sphereSet n) (y : Fin n → ℝ) :
    sphereAxialReflectionCoordinateCLM x y =
      sphereAxialReflectionRaw x.1 y :=
  sphereAxialReflectionCoordinateEquiv_apply x y

/-- The raw reflection formula is involutive on the entire ambient space. -/
theorem sphereAxialReflectionRaw_involutive {n : ℕ}
    (x : sphereSet n) :
    Function.Involutive (sphereAxialReflectionRaw x.1) := by
  intro y
  funext i
  change 2 *
      (∑ j, sphereAxialReflectionRaw x.1 y j * x.1 j) * x.1 i -
        sphereAxialReflectionRaw x.1 y i = y i
  rw [sum_sphereAxialReflectionRaw_mul_axis x.2 y]
  unfold sphereAxialReflectionRaw
  ring

@[simp] theorem sphereAxialReflectionCoordinateCLM_comp_self {n : ℕ}
    (x : sphereSet n) :
    (sphereAxialReflectionCoordinateCLM x).comp
        (sphereAxialReflectionCoordinateCLM x) =
      ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
  ext y
  simp only [ContinuousLinearMap.comp_apply,
    sphereAxialReflectionCoordinateCLM_apply,
    ContinuousLinearMap.id_apply]
  exact congrFun (sphereAxialReflectionRaw_involutive x y) _

/-- Reflections through nearby unit axes are close in Euclidean operator norm. -/
theorem norm_reflection_sub_reflection_apply_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a x u : E) (ha : ‖a‖ = 1) (hx : ‖x‖ = 1) :
    ‖(ℝ ∙ a).reflection u - (ℝ ∙ x).reflection u‖ ≤
      4 * ‖a - x‖ * ‖u‖ := by
  have hexpand :
      (ℝ ∙ a).reflection u - (ℝ ∙ x).reflection u =
        (2 : ℝ) • ((inner ℝ a u) • (a - x) +
          (inner ℝ (a - x) u) • x) := by
    rw [Submodule.reflection_singleton_apply,
      Submodule.reflection_singleton_apply, ha, hx]
    norm_num
    rw [inner_sub_left]
    module
  rw [hexpand, norm_smul]
  have hiau : ‖inner ℝ a u‖ ≤ ‖u‖ := by
    simpa [ha] using (norm_inner_le_norm (𝕜 := ℝ) a u)
  have hidx : ‖inner ℝ (a - x) u‖ ≤ ‖a - x‖ * ‖u‖ :=
    norm_inner_le_norm (𝕜 := ℝ) (a - x) u
  calc
    ‖(2 : ℝ)‖ * ‖(inner ℝ a u) • (a - x) +
        (inner ℝ (a - x) u) • x‖ ≤
      2 * (‖(inner ℝ a u) • (a - x)‖ +
        ‖(inner ℝ (a - x) u) • x‖) := by
          rw [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          gcongr
          exact norm_add_le _ _
    _ = 2 * (‖inner ℝ a u‖ * ‖a - x‖ +
        ‖inner ℝ (a - x) u‖ * ‖x‖) := by
          rw [norm_smul, norm_smul]
    _ ≤ 2 * (‖u‖ * ‖a - x‖ +
        (‖a - x‖ * ‖u‖) * 1) := by
          gcongr
          exact hx.le
    _ = 4 * ‖a - x‖ * ‖u‖ := by ring

/-- The Euclidean distance between two algebraic sphere points is the square
root of their chordal square. -/
theorem norm_sphereSetEuclideanCoordinates_sub_eq_sqrt_chordalSq
    {n : ℕ} (a x : sphereSet n) :
    ‖(sphereSetEuclideanCoordinates a).1 -
        (sphereSetEuclideanCoordinates x).1‖ =
      Real.sqrt (sphereChordalSq a.1 x.1) := by
  have hsq := sphereChordalSq_euclideanSphereCoordinates_eq_dist_sq
    (sphereSetEuclideanCoordinates a) (sphereSetEuclideanCoordinates x)
  change sphereChordalSq a.1 x.1 =
      dist (sphereSetEuclideanCoordinates a)
        (sphereSetEuclideanCoordinates x) ^ 2 at hsq
  calc
    _ = dist (sphereSetEuclideanCoordinates a)
        (sphereSetEuclideanCoordinates x) := by
      rw [Subtype.dist_eq, dist_eq_norm]
    _ = Real.sqrt (sphereChordalSq a.1 x.1) := by
      rw [hsq, Real.sqrt_sq (dist_nonneg)]

/-- If an axial reflection sends `x` to `y` and its axis has nonnegative
inner product with `x`, then the axis is no farther from `x` than `y` is. -/
theorem sphereChordalSq_axis_le_of_reflection_eq
    {n : ℕ} (a x y : sphereSet n)
    (hs : 0 ≤ ∑ i, x.1 i * a.1 i)
    (hmap : sphereAxialReflection a x = y) :
    sphereChordalSq a.1 x.1 ≤ sphereChordalSq y.1 x.1 := by
  let s : ℝ := ∑ i, x.1 i * a.1 i
  have has : ∑ i, a.1 i * x.1 i = s := by
    unfold s
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsle : s ≤ 1 := by
    have hdot := (sphereDot_mem_Icc a.2 x.2).2
    rw [has] at hdot
    exact hdot
  have hyx : ∑ i, y.1 i * x.1 i = 2 * s ^ 2 - 1 := by
    calc
      _ = ∑ i, (2 * s * a.1 i - x.1 i) * x.1 i := by
        apply Finset.sum_congr rfl
        intro i _
        have hi := congrFun (congrArg Subtype.val hmap) i
        change 2 * s * a.1 i - x.1 i = y.1 i at hi
        rw [← hi]
      _ = ∑ i, (2 * s * (a.1 i * x.1 i) - x.1 i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 2 * s * (∑ i, a.1 i * x.1 i) -
          ∑ i, x.1 i ^ 2 := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 2 * s ^ 2 - 1 := by
        rw [has]
        have hxnorm : ∑ i, x.1 i ^ 2 = 1 := by
          simpa [sphereSet, sphereQuadratic, pow_two] using x.2
        rw [hxnorm]
        ring
  rw [sphereChordalSq_eq_two_mul_one_sub_dot a.2 x.2,
    sphereChordalSq_eq_two_mul_one_sub_dot y.2 x.2, has, hyx]
  have hfac : 0 ≤ (1 - s) * (1 + 2 * s) :=
    mul_nonneg (sub_nonneg.mpr hsle) (by dsimp [s] at hs ⊢; linarith)
  nlinarith

/-- In dimension at least two the reflecting axis may be chosen on the
`x`-hemisphere, and hence quantitatively close to `x`. -/
theorem exists_sphereAxialReflection_eq_axis_chordalSq_le
    {n : ℕ} (hn : 2 ≤ n) (x y : sphereSet n) :
    ∃ a : sphereSet n,
      sphereAxialReflection a x = y ∧
        sphereChordalSq a.1 x.1 ≤ sphereChordalSq y.1 x.1 := by
  obtain ⟨a, hmap⟩ := exists_sphereAxialReflection_eq hn x y
  let s : ℝ := ∑ i, x.1 i * a.1 i
  by_cases hs : 0 ≤ s
  · exact ⟨a, hmap,
      sphereChordalSq_axis_le_of_reflection_eq a x y hs hmap⟩
  · let aneg : sphereSet n := ⟨-a.1, by
      simpa [sphereSet, sphereQuadratic, pow_two] using a.2⟩
    have hrefl : sphereAxialReflection aneg x = sphereAxialReflection a x := by
      apply Subtype.ext
      funext i
      change 2 * (∑ j, x.1 j * (-a.1 j)) * (-a.1 i) - x.1 i =
        2 * (∑ j, x.1 j * a.1 j) * a.1 i - x.1 i
      have hsum : (∑ j, x.1 j * (-a.1 j)) = -s := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        simp
      rw [hsum]
      unfold s
      ring
    have hmapneg : sphereAxialReflection aneg x = y := hrefl.trans hmap
    have hsneg : 0 ≤ ∑ i, x.1 i * aneg.1 i := by
      change 0 ≤ ∑ i, x.1 i * (-a.1 i)
      rw [show (∑ i, x.1 i * (-a.1 i)) = -s by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        simp]
      exact neg_nonneg.mpr (le_of_not_ge hs)
    exact ⟨aneg, hmapneg,
      sphereChordalSq_axis_le_of_reflection_eq aneg x y hsneg hmapneg⟩

/-- Distortion caused only by transporting between the Euclidean `L²` model
and the repository's product norm on coordinate functions. -/
noncomputable def sphereCoordinateNormDistortion (n : ℕ) : ℝ :=
  ‖(EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap‖ *
    ‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖

theorem sphereCoordinateNormDistortion_nonneg (n : ℕ) :
    0 ≤ sphereCoordinateNormDistortion n := by
  exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- Every coordinate axial reflection has a norm bound depending only on the
ambient dimension, not on its axis. -/
theorem norm_sphereAxialReflectionCoordinateCLM_le {n : ℕ}
    (a : sphereSet n) :
    ‖sphereAxialReflectionCoordinateCLM a‖ ≤
      sphereCoordinateNormDistortion n := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (sphereCoordinateNormDistortion_nonneg n)
  intro y
  let u : EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm y
  change ‖(EuclideanSpace.equiv (Fin n) ℝ)
      (sphereAxialReflectionLinearIsometry a u)‖ ≤
    sphereCoordinateNormDistortion n * ‖y‖
  calc
    _ ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap‖ *
        ‖sphereAxialReflectionLinearIsometry a u‖ :=
      (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap.le_opNorm _
    _ = ‖(EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap‖ *
        ‖u‖ := by rw [(sphereAxialReflectionLinearIsometry a).norm_map]
    _ ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap‖ *
        (‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖ *
          ‖y‖) := by
      gcongr
      exact (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.le_opNorm y
    _ = sphereCoordinateNormDistortion n * ‖y‖ := by
      unfold sphereCoordinateNormDistortion
      ring

/-- Coordinate axial reflections are Lipschitz in the axis, with all norm
conversion isolated in `sphereCoordinateNormDistortion`. -/
theorem norm_sphereAxialReflectionCoordinateCLM_sub_le {n : ℕ}
    (a x : sphereSet n) :
    ‖sphereAxialReflectionCoordinateCLM a -
        sphereAxialReflectionCoordinateCLM x‖ ≤
      4 * sphereCoordinateNormDistortion n *
        Real.sqrt (sphereChordalSq a.1 x.1) := by
  have hC : 0 ≤ 4 * sphereCoordinateNormDistortion n *
      Real.sqrt (sphereChordalSq a.1 x.1) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (sphereCoordinateNormDistortion_nonneg n))
      (Real.sqrt_nonneg _)
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro y
  let u : EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm y
  have ha : ‖(sphereSetEuclideanCoordinates a).1‖ = 1 := by
    simp
  have hx : ‖(sphereSetEuclideanCoordinates x).1‖ = 1 := by
    simp
  change ‖(EuclideanSpace.equiv (Fin n) ℝ)
      (sphereAxialReflectionLinearIsometry a u) -
    (EuclideanSpace.equiv (Fin n) ℝ)
      (sphereAxialReflectionLinearIsometry x u)‖ ≤ _
  rw [← map_sub]
  calc
    _ ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap‖ *
        ‖sphereAxialReflectionLinearIsometry a u -
          sphereAxialReflectionLinearIsometry x u‖ :=
      (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap.le_opNorm _
    _ ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap‖ *
        (4 * ‖(sphereSetEuclideanCoordinates a).1 -
            (sphereSetEuclideanCoordinates x).1‖ * ‖u‖) := by
      gcongr
      change ‖(ℝ ∙ (sphereSetEuclideanCoordinates a).1).reflection u -
          (ℝ ∙ (sphereSetEuclideanCoordinates x).1).reflection u‖ ≤ _
      exact norm_reflection_sub_reflection_apply_le _ _ _ ha hx
    _ ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap‖ *
        (4 * ‖(sphereSetEuclideanCoordinates a).1 -
            (sphereSetEuclideanCoordinates x).1‖ *
          (‖(EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap‖ *
            ‖y‖)) := by
      gcongr
      exact (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.le_opNorm y
    _ = (4 * sphereCoordinateNormDistortion n *
          Real.sqrt (sphereChordalSq a.1 x.1)) * ‖y‖ := by
      rw [norm_sphereSetEuclideanCoordinates_sub_eq_sqrt_chordalSq]
      unfold sphereCoordinateNormDistortion
      ring
@[simp] theorem sphereAxialReflectionCoordinateCLM_self {n : ℕ}
    (x : sphereSet n) :
    sphereAxialReflectionCoordinateCLM x x.1 = x.1 := by
  rw [sphereAxialReflectionCoordinateCLM_apply]
  funext i
  change 2 * (∑ j, x.1 j * x.1 j) * x.1 i - x.1 i = x.1 i
  have hx : ∑ j, x.1 j * x.1 j = 1 := by
    simpa [sphereSet, sphereQuadratic, pow_two] using x.2
  rw [hx]
  ring

/-- The forward product of axial reflections, sending `x` to any point reached
by the reflection with axis `a`. -/
noncomputable def sphereForwardRotationCLM {n : ℕ}
    (a x : sphereSet n) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (sphereAxialReflectionCoordinateCLM a).comp
    (sphereAxialReflectionCoordinateCLM x)

/-- The inverse product, with the reflection order reversed. -/
noncomputable def sphereReverseRotationCLM {n : ℕ}
    (a x : sphereSet n) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (sphereAxialReflectionCoordinateCLM x).comp
    (sphereAxialReflectionCoordinateCLM a)

@[simp] theorem sphereForwardRotationCLM_apply_axis {n : ℕ}
    (a x : sphereSet n) :
    sphereForwardRotationCLM a x x.1 =
      (sphereAxialReflection a x).1 := by
  rw [sphereForwardRotationCLM, ContinuousLinearMap.comp_apply,
    sphereAxialReflectionCoordinateCLM_self,
    sphereAxialReflectionCoordinateCLM_apply]
  rfl

@[simp] theorem sphereReverseRotationCLM_apply_axis {n : ℕ}
    (a x : sphereSet n) :
    sphereReverseRotationCLM a x x.1 =
      (sphereAxialReflection x (sphereAxialReflection a x)).1 := by
  simp [sphereReverseRotationCLM, sphereAxialReflection_coe]

@[simp] theorem sphereForwardRotationCLM_comp_reverse {n : ℕ}
    (a x : sphereSet n) :
    (sphereForwardRotationCLM a x).comp (sphereReverseRotationCLM a x) =
      ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
  ext z
  simp only [sphereForwardRotationCLM, sphereReverseRotationCLM,
    ContinuousLinearMap.comp_apply]
  rw [show sphereAxialReflectionCoordinateCLM x
      (sphereAxialReflectionCoordinateCLM x
        (sphereAxialReflectionCoordinateCLM a z)) =
      sphereAxialReflectionCoordinateCLM a z by
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using DFunLike.congr_fun
        (sphereAxialReflectionCoordinateCLM_comp_self x)
        (sphereAxialReflectionCoordinateCLM a z)]
  exact congrFun (by
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using DFunLike.congr_fun
        (sphereAxialReflectionCoordinateCLM_comp_self a) z) _

@[simp] theorem sphereReverseRotationCLM_comp_forward {n : ℕ}
    (a x : sphereSet n) :
    (sphereReverseRotationCLM a x).comp (sphereForwardRotationCLM a x) =
      ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
  ext z
  simp only [sphereForwardRotationCLM, sphereReverseRotationCLM,
    ContinuousLinearMap.comp_apply]
  rw [show sphereAxialReflectionCoordinateCLM a
      (sphereAxialReflectionCoordinateCLM a
        (sphereAxialReflectionCoordinateCLM x z)) =
      sphereAxialReflectionCoordinateCLM x z by
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using DFunLike.congr_fun
        (sphereAxialReflectionCoordinateCLM_comp_self a)
        (sphereAxialReflectionCoordinateCLM x z)]
  exact congrFun (by
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using DFunLike.congr_fun
        (sphereAxialReflectionCoordinateCLM_comp_self x) z) _

/-- A reflecting axis can be chosen so that the corresponding coordinate
reflection differs from the base reflection by first order in chordal distance. -/
theorem exists_axis_reflectionCLM_sub_le {n : ℕ} (hn : 2 ≤ n)
    (x y : sphereSet n) :
    ∃ a : sphereSet n,
      sphereAxialReflection a x = y ∧
      ‖sphereAxialReflectionCoordinateCLM a -
          sphereAxialReflectionCoordinateCLM x‖ ≤
        4 * sphereCoordinateNormDistortion n *
          Real.sqrt (sphereChordalSq y.1 x.1) := by
  obtain ⟨a, hmap, haxis⟩ :=
    exists_sphereAxialReflection_eq_axis_chordalSq_le hn x y
  refine ⟨a, hmap, (norm_sphereAxialReflectionCoordinateCLM_sub_le a x).trans ?_⟩
  have hsqrt : Real.sqrt (sphereChordalSq a.1 x.1) ≤
      Real.sqrt (sphereChordalSq y.1 x.1) := Real.sqrt_le_sqrt haxis
  exact mul_le_mul_of_nonneg_left hsqrt
    (mul_nonneg (by norm_num) (sphereCoordinateNormDistortion_nonneg n))
/-- The forward two-reflection product has a dimension-only norm bound. -/
theorem norm_sphereForwardRotationCLM_le {n : ℕ} (a x : sphereSet n) :
    ‖sphereForwardRotationCLM a x‖ ≤ sphereCoordinateNormDistortion n ^ 2 := by
  calc
    _ ≤ ‖sphereAxialReflectionCoordinateCLM a‖ *
        ‖sphereAxialReflectionCoordinateCLM x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ sphereCoordinateNormDistortion n * sphereCoordinateNormDistortion n :=
      mul_le_mul (norm_sphereAxialReflectionCoordinateCLM_le a)
        (norm_sphereAxialReflectionCoordinateCLM_le x) (norm_nonneg _)
        (sphereCoordinateNormDistortion_nonneg n)
    _ = _ := by ring

/-- The reverse two-reflection product has the same dimension-only norm bound. -/
theorem norm_sphereReverseRotationCLM_le {n : ℕ} (a x : sphereSet n) :
    ‖sphereReverseRotationCLM a x‖ ≤ sphereCoordinateNormDistortion n ^ 2 := by
  calc
    _ ≤ ‖sphereAxialReflectionCoordinateCLM x‖ *
        ‖sphereAxialReflectionCoordinateCLM a‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ sphereCoordinateNormDistortion n * sphereCoordinateNormDistortion n :=
      mul_le_mul (norm_sphereAxialReflectionCoordinateCLM_le x)
        (norm_sphereAxialReflectionCoordinateCLM_le a) (norm_nonneg _)
        (sphereCoordinateNormDistortion_nonneg n)
    _ = _ := by ring

/-- The forward displacement factors through the difference of its two
reflection axes. -/
theorem sphereForwardRotationCLM_sub_id_factor {n : ℕ}
    (a x : sphereSet n) :
    sphereForwardRotationCLM a x - ContinuousLinearMap.id ℝ (Fin n → ℝ) =
      (sphereAxialReflectionCoordinateCLM a -
        sphereAxialReflectionCoordinateCLM x).comp
          (sphereAxialReflectionCoordinateCLM x) := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [sphereForwardRotationCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  have hxx : sphereAxialReflectionCoordinateCLM x
      (sphereAxialReflectionCoordinateCLM x z) = z := by
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using DFunLike.congr_fun
        (sphereAxialReflectionCoordinateCLM_comp_self x) z
  rw [hxx]

/-- The reverse displacement has the symmetric factorization. -/
theorem sphereReverseRotationCLM_sub_id_factor {n : ℕ}
    (a x : sphereSet n) :
    sphereReverseRotationCLM a x - ContinuousLinearMap.id ℝ (Fin n → ℝ) =
      (sphereAxialReflectionCoordinateCLM x -
        sphereAxialReflectionCoordinateCLM a).comp
          (sphereAxialReflectionCoordinateCLM a) := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [sphereReverseRotationCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  have haa : sphereAxialReflectionCoordinateCLM a
      (sphereAxialReflectionCoordinateCLM a z) = z := by
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using DFunLike.congr_fun
        (sphereAxialReflectionCoordinateCLM_comp_self a) z
  rw [haa]

/-- Quantitative first-order displacement of the forward product. -/
theorem norm_sphereForwardRotationCLM_sub_id_le {n : ℕ}
    (a x : sphereSet n) :
    ‖sphereForwardRotationCLM a x -
        ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤
      4 * sphereCoordinateNormDistortion n ^ 2 *
        Real.sqrt (sphereChordalSq a.1 x.1) := by
  rw [sphereForwardRotationCLM_sub_id_factor]
  calc
    _ ≤ ‖sphereAxialReflectionCoordinateCLM a -
          sphereAxialReflectionCoordinateCLM x‖ *
        ‖sphereAxialReflectionCoordinateCLM x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (4 * sphereCoordinateNormDistortion n *
          Real.sqrt (sphereChordalSq a.1 x.1)) *
        sphereCoordinateNormDistortion n :=
      mul_le_mul (norm_sphereAxialReflectionCoordinateCLM_sub_le a x)
        (norm_sphereAxialReflectionCoordinateCLM_le x) (norm_nonneg _)
        (mul_nonneg (mul_nonneg (by norm_num)
          (sphereCoordinateNormDistortion_nonneg n)) (Real.sqrt_nonneg _))
    _ = _ := by ring

/-- Quantitative first-order displacement of the reverse product. -/
theorem norm_sphereReverseRotationCLM_sub_id_le {n : ℕ}
    (a x : sphereSet n) :
    ‖sphereReverseRotationCLM a x -
        ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤
      4 * sphereCoordinateNormDistortion n ^ 2 *
        Real.sqrt (sphereChordalSq a.1 x.1) := by
  rw [sphereReverseRotationCLM_sub_id_factor]
  calc
    _ ≤ ‖sphereAxialReflectionCoordinateCLM x -
          sphereAxialReflectionCoordinateCLM a‖ *
        ‖sphereAxialReflectionCoordinateCLM a‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖sphereAxialReflectionCoordinateCLM a -
          sphereAxialReflectionCoordinateCLM x‖ *
        ‖sphereAxialReflectionCoordinateCLM a‖ := by
      rw [norm_sub_rev]
    _ ≤ (4 * sphereCoordinateNormDistortion n *
          Real.sqrt (sphereChordalSq a.1 x.1)) *
        sphereCoordinateNormDistortion n :=
      mul_le_mul (norm_sphereAxialReflectionCoordinateCLM_sub_le a x)
        (norm_sphereAxialReflectionCoordinateCLM_le a) (norm_nonneg _)
        (mul_nonneg (mul_nonneg (by norm_num)
          (sphereCoordinateNormDistortion_nonneg n)) (Real.sqrt_nonneg _))
    _ = _ := by ring
/-- Complete quantitative package for the inverse pair of two-reflection maps
used to compare the filter error at `x`, `y`, and the axial reflection of `y`. -/
theorem exists_sphereRotationPair_bounds {n : ℕ} (hn : 2 ≤ n)
    (x y : sphereSet n) :
    ∃ a : sphereSet n,
      sphereAxialReflection a x = y ∧
      ‖sphereForwardRotationCLM a x‖ ≤ sphereCoordinateNormDistortion n ^ 2 ∧
      ‖sphereReverseRotationCLM a x‖ ≤ sphereCoordinateNormDistortion n ^ 2 ∧
      ‖sphereForwardRotationCLM a x -
          ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤
        (4 * sphereCoordinateNormDistortion n ^ 2) *
          Real.sqrt (sphereChordalSq y.1 x.1) ∧
      ‖sphereReverseRotationCLM a x -
          ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤
        (4 * sphereCoordinateNormDistortion n ^ 2) *
          Real.sqrt (sphereChordalSq y.1 x.1) ∧
      ‖sphereForwardRotationCLM a x + sphereReverseRotationCLM a x -
          2 • ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤
        ((4 * sphereCoordinateNormDistortion n ^ 2) *
          Real.sqrt (sphereChordalSq y.1 x.1)) ^ 2 := by
  obtain ⟨a, hmap, haxis⟩ :=
    exists_sphereAxialReflection_eq_axis_chordalSq_le hn x y
  have hsqrt : Real.sqrt (sphereChordalSq a.1 x.1) ≤
      Real.sqrt (sphereChordalSq y.1 x.1) := Real.sqrt_le_sqrt haxis
  have hcoef : 0 ≤ 4 * sphereCoordinateNormDistortion n ^ 2 := by
    exact mul_nonneg (by norm_num) (sq_nonneg _)
  have hforward :
      ‖sphereForwardRotationCLM a x -
          ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤
        (4 * sphereCoordinateNormDistortion n ^ 2) *
          Real.sqrt (sphereChordalSq y.1 x.1) :=
    (norm_sphereForwardRotationCLM_sub_id_le a x).trans
      (mul_le_mul_of_nonneg_left hsqrt hcoef)
  have hreverse :
      ‖sphereReverseRotationCLM a x -
          ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤
        (4 * sphereCoordinateNormDistortion n ^ 2) *
          Real.sqrt (sphereChordalSq y.1 x.1) :=
    (norm_sphereReverseRotationCLM_sub_id_le a x).trans
      (mul_le_mul_of_nonneg_left hsqrt hcoef)
  refine ⟨a, hmap, norm_sphereForwardRotationCLM_le a x,
    norm_sphereReverseRotationCLM_le a x, hforward, hreverse, ?_⟩
  have hcenter := norm_clm_add_inverse_sub_two_id_le
    (sphereForwardRotationCLM a x) (sphereReverseRotationCLM a x)
    (sphereForwardRotationCLM_comp_reverse a x) hforward hreverse
  simpa only [pow_two] using hcenter
end QuarticConvergence
end OptimalConvergenceRates

end
