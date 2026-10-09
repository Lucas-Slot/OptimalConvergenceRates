/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Kernel/Measure.lean

  Normalized Haar measure on the Euclidean unit sphere.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Defs
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open Set Metric MeasureTheory
open scoped Pointwise
open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

/-- The metric unit sphere in the Euclidean coordinate space of dimension n. -/
abbrev euclideanUnitSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- The canonical measurable structure used for Haar measure on Euclidean
coordinate space. Naming the instance locally keeps downstream declarations
stable while agreeing definitionally with mathlib's `WithLp` volume API. -/
noncomputable instance sphereEuclideanMeasurableSpace (n : ℕ) :
    MeasurableSpace (EuclideanSpace ℝ (Fin n)) :=
  WithLp.measurableSpace 2 (Fin n → ℝ)

instance sphereEuclideanBorelSpace (n : ℕ) :
    BorelSpace (EuclideanSpace ℝ (Fin n)) :=
  PiLp.borelSpace 2

/-- Haar surface measure normalized to have total mass one. -/
noncomputable def normalizedEuclideanSphereMeasure (n : ℕ) :
    Measure (euclideanUnitSphere n) :=
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
  (μ Set.univ)⁻¹ • μ

/-- The normalized surface mass of a measurable sphere set is the ambient
volume of its radial cone, times the explicit fixed normalization factor. -/
theorem normalizedEuclideanSphereMeasure_apply {n : ℕ}
    {s : Set (euclideanUnitSphere n)} (hs : MeasurableSet s) :
    normalizedEuclideanSphereMeasure n s =
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ)⁻¹ *
        ((n : ENNReal) *
          volume (Set.Ioo (0 : ℝ) 1 •
            ((↑) '' s : Set (EuclideanSpace ℝ (Fin n))))) := by
  rw [normalizedEuclideanSphereMeasure]
  rw [Measure.smul_apply]
  rw [Measure.toSphere_apply' _ hs]
  simp only [smul_eq_mul]
  congr 2
  norm_cast
  exact finrank_euclideanSpace_fin

/-- Real-valued form of the normalized radial-cone formula. -/
theorem normalizedEuclideanSphereMeasure_real_apply {n : ℕ}
    {s : Set (euclideanUnitSphere n)} (hs : MeasurableSet s) :
    (normalizedEuclideanSphereMeasure n).real s =
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ)⁻¹.toReal *
        (n : ℝ) *
          volume.real (Set.Ioo (0 : ℝ) 1 •
            ((↑) '' s : Set (EuclideanSpace ℝ (Fin n)))) := by
  rw [MeasureTheory.measureReal_def]
  rw [normalizedEuclideanSphereMeasure_apply hs]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
  rw [ENNReal.toReal_natCast]
  rw [MeasureTheory.measureReal_def]
  ring

/-- A radial cone over a measurable subset of the Euclidean unit sphere is
measurable in the ambient Euclidean space. -/
theorem measurableSet_radialCone {n : ℕ}
    {s : Set (euclideanUnitSphere n)} (hs : MeasurableSet s) :
    MeasurableSet ((Set.Ioo (0 : ℝ) 1) • ((↑) '' s :
      Set (EuclideanSpace ℝ (Fin n)))) := by
  let r : Set.Ioi (0 : ℝ) := ⟨1, Set.mem_Ioi.mpr one_pos⟩
  have hsprod : MeasurableSet (s ×ˢ Set.Iio r) :=
    hs.prod measurableSet_Iio
  have hset :
      (((↑) : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) →
        EuclideanSpace ℝ (Fin n)) ''
          ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin n))) ⁻¹'
            (s ×ˢ Set.Iio r))) = Set.Ioo (0 : ℝ) 1 • ((↑) '' s) := by
    dsimp [r]
    rw [← image2_smul, image2_image_right, ← Homeomorph.image_symm,
      image_image, ← image_subtype_val_Ioi_Iio
        (⟨1, Set.mem_Ioi.mpr one_pos⟩ : Set.Ioi (0 : ℝ)), image2_image_left,
      image2_swap, ← image_prod]
    rfl
  rw [← hset]
  exact (MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl).measurableSet_image.mpr
    ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin n))).measurable hsprod)
/-- A Euclidean linear isometry restricts to the metric unit sphere. -/
noncomputable def euclideanUnitSphereMap {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    euclideanUnitSphere n → euclideanUnitSphere n :=
  fun y ↦ ⟨L y.1, by
    rw [Metric.mem_sphere, dist_zero_right, L.norm_map]
    simp⟩

/-- The restriction of a Euclidean linear isometry to the unit sphere is a
homeomorphism, with inverse induced by the inverse linear isometry. -/
noncomputable def euclideanUnitSphereMapHomeomorph {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    euclideanUnitSphere n ≃ₜ euclideanUnitSphere n where
  toEquiv :=
    { toFun := euclideanUnitSphereMap L
      invFun := euclideanUnitSphereMap L.symm
      left_inv := fun y ↦ by
        apply Subtype.ext
        exact L.symm_apply_apply y.1
      right_inv := fun y ↦ by
        apply Subtype.ext
        exact L.apply_symm_apply y.1 }
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact L.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact L.symm.continuous.comp continuous_subtype_val

/-- `Measure.toSphere` is invariant under every Euclidean linear isometry. -/
theorem euclideanUnitSphereMap_measurePreserving_toSphere {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (euclideanUnitSphereMap L)
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
  let T := euclideanUnitSphereMap L
  have hTmeas : Measurable T := (euclideanUnitSphereMapHomeomorph L).measurable
  refine ⟨hTmeas, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hTmeas hs,
    Measure.toSphere_apply' _ (hs.preimage hTmeas),
    Measure.toSphere_apply' _ hs]
  congr 1
  have hcone : MeasurableSet
      (Set.Ioo (0 : ℝ) 1 • ((↑) '' s :
        Set (EuclideanSpace ℝ (Fin n)))) :=
    measurableSet_radialCone hs
  have hpre :
      Set.Ioo (0 : ℝ) 1 •
          ((↑) '' (T ⁻¹' s) : Set (EuclideanSpace ℝ (Fin n))) =
        L ⁻¹' (Set.Ioo (0 : ℝ) 1 •
          ((↑) '' s : Set (EuclideanSpace ℝ (Fin n)))) := by
    ext z
    constructor
    · rintro ⟨a, ha, _, ⟨y, hy, rfl⟩, rfl⟩
      change L (a • y.1) ∈
        Set.Ioo (0 : ℝ) 1 •
          ((↑) '' s : Set (EuclideanSpace ℝ (Fin n)))
      rw [L.map_smul]
      exact ⟨a, ha, (T y).1, ⟨T y, hy, rfl⟩, rfl⟩
    · intro hz
      change L z ∈ Set.Ioo (0 : ℝ) 1 •
        ((↑) '' s : Set (EuclideanSpace ℝ (Fin n))) at hz
      rcases hz with ⟨a, ha, _, ⟨y, hy, rfl⟩, hay⟩
      refine ⟨a, ha, (euclideanUnitSphereMap L.symm y).1, ?_, ?_⟩
      · refine ⟨euclideanUnitSphereMap L.symm y, ?_, rfl⟩
        change euclideanUnitSphereMap L
          (euclideanUnitSphereMap L.symm y) ∈ s
        have hcancel : euclideanUnitSphereMap L
            (euclideanUnitSphereMap L.symm y) = y := by
          apply Subtype.ext
          exact L.apply_symm_apply y.1
        rw [hcancel]
        exact hy
      · change a • L.symm y.1 = z
        calc
          a • L.symm y.1 = L.symm (a • y.1) :=
            (L.symm.map_smul a y.1).symm
          _ = L.symm (L z) := congrArg L.symm hay
          _ = z := L.symm_apply_apply z
  rw [hpre]
  calc
    volume (L ⁻¹' (Set.Ioo (0 : ℝ) 1 •
        ((↑) '' s : Set (EuclideanSpace ℝ (Fin n))))) =
        Measure.map L volume (Set.Ioo (0 : ℝ) 1 •
          ((↑) '' s : Set (EuclideanSpace ℝ (Fin n)))) := by
      rw [Measure.map_apply L.continuous.measurable hcone]
    _ = volume (Set.Ioo (0 : ℝ) 1 •
        ((↑) '' s : Set (EuclideanSpace ℝ (Fin n)))) :=
      congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n)) ↦
        μ (Set.Ioo (0 : ℝ) 1 •
          ((↑) '' s : Set (EuclideanSpace ℝ (Fin n)))))
        L.measurePreserving.map_eq

/-- Normalized Euclidean sphere measure is invariant under every Euclidean
linear isometry. -/
theorem euclideanUnitSphereMap_measurePreserving {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (euclideanUnitSphereMap L)
      (normalizedEuclideanSphereMeasure n)
      (normalizedEuclideanSphereMeasure n) := by
  have h := euclideanUnitSphereMap_measurePreserving_toSphere L
  refine ⟨h.measurable, ?_⟩
  simp only [normalizedEuclideanSphereMeasure, Measure.map_smul]
  rw [h.map_eq]

/-- Normalization preserves positivity on nonempty open subsets of the
Euclidean unit sphere. -/
theorem normalizedEuclideanSphereMeasure_isOpenPosMeasure (n : ℕ) :
    Measure.IsOpenPosMeasure (normalizedEuclideanSphereMeasure n) := by
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
  letI : Measure.IsOpenPosMeasure μ := inferInstance
  change Measure.IsOpenPosMeasure ((μ Set.univ)⁻¹ • μ)
  apply Measure.isOpenPosMeasure_smul
  exact ENNReal.inv_ne_zero.mpr (measure_ne_top μ Set.univ)

/-- In positive dimension the normalized surface measure is a probability
measure. -/
theorem normalizedEuclideanSphereMeasure_isProbability
    (n : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (normalizedEuclideanSphereMeasure n) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
  have hμ : μ ≠ 0 := Measure.toSphere_ne_zero volume
  letI : NeZero μ := ⟨hμ⟩
  change IsProbabilityMeasure ((μ Set.univ)⁻¹ • μ)
  infer_instance

@[simp] theorem normalizedEuclideanSphereMeasure_apply_univ
    (n : ℕ) (hn : 0 < n) :
    normalizedEuclideanSphereMeasure n Set.univ = 1 := by
  letI : IsProbabilityMeasure (normalizedEuclideanSphereMeasure n) :=
    normalizedEuclideanSphereMeasure_isProbability n hn
  exact measure_univ

/-- Forgetting the Euclidean wrapper gives the coordinate vector used by the
repository's polynomial definitions. -/
def euclideanSphereCoordinates {n : ℕ}
    (x : euclideanUnitSphere n) : Fin n → ℝ := fun i ↦ x.1 i

/-- Euclidean metric unit vectors satisfy the repository's algebraic sphere
equation. -/
theorem euclideanSphereCoordinates_mem_sphereSet {n : ℕ}
    (x : euclideanUnitSphere n) :
    euclideanSphereCoordinates x ∈ sphereSet n := by
  have hxnorm : ‖x.1‖ = 1 := by
    have hx := x.2
    simp only [Metric.mem_sphere, dist_zero_right] at hx
    exact hx
  have hsq := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n ↦ ℝ) x.1
  rw [hxnorm] at hsq
  simp only [one_pow] at hsq
  simp only [sphereSet, sphereQuadratic, map_sum, map_pow, eval_X,
    Set.mem_setOf_eq, euclideanSphereCoordinates]
  simpa [Real.norm_eq_abs, sq_abs, euclideanSphereCoordinates] using hsq.symm

/-- An algebraic sphere point regarded as a Euclidean unit vector. -/
noncomputable def sphereSetEuclideanCoordinates {n : ℕ}
    (x : sphereSet n) : euclideanUnitSphere n := by
  let z : EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm x.1
  have hsum : ∑ i, x.1 i ^ 2 = 1 := by
    simpa [sphereSet, sphereQuadratic] using x.2
  have hzsq : ‖z‖ ^ 2 = 1 := by
    calc
      ‖z‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 :=
        PiLp.norm_sq_eq_of_L2 (fun _ : Fin n ↦ ℝ) z
      _ = ∑ i, x.1 i ^ 2 := by
        simp [z, Real.norm_eq_abs, sq_abs]
      _ = 1 := hsum
  refine ⟨z, ?_⟩
  rw [Metric.mem_sphere, dist_zero_right]
  nlinarith [norm_nonneg z]

/-- The coordinate north pole as a point of mathlib's Euclidean unit sphere. -/
noncomputable def euclideanSphereNorthPole {n : ℕ} (hn : 0 < n) :
    euclideanUnitSphere n :=
  sphereSetEuclideanCoordinates (sphereNorthPolePoint hn)

/-- Coordinates of the Euclidean north pole. -/
@[simp] theorem euclideanSphereNorthPole_apply {n : ℕ} (hn : 0 < n) (i : Fin n) :
    (euclideanSphereNorthPole hn).1 i =
      if i = ⟨0, hn⟩ then 1 else 0 := by
  simp [euclideanSphereNorthPole, sphereSetEuclideanCoordinates,
    sphereNorthPolePoint, sphereNorthPole]

/-- The metric Euclidean sphere and the repository's algebraic sphere have the
same points in coordinates. -/
noncomputable def euclideanSphereEquivSphereSet (n : ℕ) :
    euclideanUnitSphere n ≃ sphereSet n where
  toFun x := ⟨euclideanSphereCoordinates x,
    euclideanSphereCoordinates_mem_sphereSet x⟩
  invFun := sphereSetEuclideanCoordinates
  left_inv x := by
    apply Subtype.ext
    ext i
    rfl
  right_inv x := by
    apply Subtype.ext
    ext i
    rfl

/-- The coordinate equivalence is a homeomorphism for the Euclidean and finite
product topologies. -/
noncomputable def euclideanSphereHomeomorphSphereSet (n : ℕ) :
    euclideanUnitSphere n ≃ₜ sphereSet n where
  toEquiv := euclideanSphereEquivSphereSet n
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun x : euclideanUnitSphere n ↦
      (EuclideanSpace.equiv (Fin n) ℝ) x.1)
    exact (EuclideanSpace.equiv (Fin n) ℝ).continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    change Continuous (fun x : sphereSet n ↦
      (EuclideanSpace.equiv (Fin n) ℝ).symm x.1)
    exact (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp continuous_subtype_val

/-- The normalized Haar surface measure transported to the exact algebraic
sphere subtype used throughout the repository's SOS hierarchy. -/
noncomputable def normalizedSphereMeasure (n : ℕ) : Measure (sphereSet n) :=
  Measure.map (euclideanSphereHomeomorphSphereSet n)
    (normalizedEuclideanSphereMeasure n)

/-- Conjugating a Euclidean linear isometry by the coordinate homeomorphism
gives a homeomorphism of the repository's algebraic sphere. -/
noncomputable def sphereSetLinearIsometryHomeomorph {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    sphereSet n ≃ₜ sphereSet n :=
  (euclideanSphereHomeomorphSphereSet n).symm.trans
    ((euclideanUnitSphereMapHomeomorph L).trans
      (euclideanSphereHomeomorphSphereSet n))

/-- The normalized measure on the algebraic sphere is invariant under every
Euclidean linear isometry, after transport through coordinates. -/
theorem sphereSetLinearIsometry_measurePreserving {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (sphereSetLinearIsometryHomeomorph L)
      (normalizedSphereMeasure n) (normalizedSphereMeasure n) := by
  let H := euclideanSphereHomeomorphSphereSet n
  let T := euclideanUnitSphereMap L
  let R := sphereSetLinearIsometryHomeomorph L
  have hT := euclideanUnitSphereMap_measurePreserving L
  have hHmeas : Measurable H := (euclideanSphereHomeomorphSphereSet n).measurable
  have hRmeas : Measurable R := (sphereSetLinearIsometryHomeomorph L).measurable
  refine ⟨hRmeas, ?_⟩
  change Measure.map R (Measure.map H (normalizedEuclideanSphereMeasure n)) =
    Measure.map H (normalizedEuclideanSphereMeasure n)
  rw [Measure.map_map hRmeas hHmeas]
  have hcomp : R ∘ H = H ∘ T := by
    rfl
  rw [hcomp, ← Measure.map_map hHmeas hT.measurable, hT.map_eq]
/-- Transport through the coordinate homeomorphism preserves positivity on
nonempty open subsets of the algebraic sphere. -/
theorem normalizedSphereMeasure_isOpenPosMeasure (n : ℕ) :
    Measure.IsOpenPosMeasure (normalizedSphereMeasure n) := by
  letI : Measure.IsOpenPosMeasure (normalizedEuclideanSphereMeasure n) :=
    normalizedEuclideanSphereMeasure_isOpenPosMeasure n
  exact (euclideanSphereHomeomorphSphereSet n).continuous.isOpenPosMeasure_map
    (euclideanSphereHomeomorphSphereSet n).surjective

/-- In positive dimension, the transported algebraic-sphere measure is a
probability measure. -/
theorem normalizedSphereMeasure_isProbability (n : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (normalizedSphereMeasure n) := by
  letI : IsProbabilityMeasure (normalizedEuclideanSphereMeasure n) :=
    normalizedEuclideanSphereMeasure_isProbability n hn
  exact Measure.isProbabilityMeasure_map
    (euclideanSphereHomeomorphSphereSet n).measurable.aemeasurable

@[simp] theorem normalizedSphereMeasure_apply_univ (n : ℕ) (hn : 0 < n) :
    normalizedSphereMeasure n Set.univ = 1 := by
  letI : IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  exact measure_univ

/-- Polynomial evaluation is integrable against normalized surface measure.
This packages the compactness/continuity argument used by all moment maps. -/
theorem integrable_eval_normalizedSphereMeasure {n : ℕ} (hn : 0 < n)
    (q : MvPolynomial (Fin n) ℝ) :
    Integrable (fun x : sphereSet n ↦ MvPolynomial.eval x.1 q)
      (normalizedSphereMeasure n) := by
  letI : CompactSpace (sphereSet n) :=
    isCompact_iff_compactSpace.mp sphereSet_compact
  letI : IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  apply Continuous.integrable_of_hasCompactSupport
  · exact (MvPolynomial.continuous_eval q).comp continuous_subtype_val
  · exact isCompact_univ.of_isClosed_subset
      (isClosed_tsupport
        (fun x : sphereSet n ↦ MvPolynomial.eval x.1 q))
      (subset_univ _)

theorem normalizedSphereMeasure_ne_zero (n : ℕ) (hn : 0 < n) :
    normalizedSphereMeasure n ≠ 0 := by
  letI : IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  exact IsProbabilityMeasure.ne_zero _

end QuarticConvergence
end OptimalConvergenceRates

end
