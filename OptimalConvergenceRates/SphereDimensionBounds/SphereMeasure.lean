import Mathlib.Data.ENNReal.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Measure
import OptimalConvergenceRates.SphereDimensionBounds.HomogeneousSphereBounds

/-! The dimension-dependent estimates use the repository's existing normalized
Euclidean sphere measure and orthogonal action. This module supplies the
small interface used by the local polynomial and matrix constructions. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.SphereMeasure

open Set Metric MeasureTheory
open scoped Pointwise BigOperators

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Sphere (n : ℕ) := Metric.sphere (0 : E n) 1

abbrev surface (n : ℕ) : Measure (Sphere n) :=
  QuarticConvergence.normalizedEuclideanSphereMeasure n

theorem raw_surface_nonzero (n : ℕ) (hn : 0 < n) :
    (volume : Measure (E n)).toSphere ≠ 0 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Measure.toSphere_ne_zero volume

theorem surface_isProbability (n : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (surface n) :=
  QuarticConvergence.normalizedEuclideanSphereMeasure_isProbability n hn

@[simp] theorem surface_univ (n : ℕ) (hn : 0 < n) : surface n Set.univ = 1 :=
  QuarticConvergence.normalizedEuclideanSphereMeasure_apply_univ n hn

theorem measurableSet_radialCone {n : ℕ} {s : Set (Sphere n)} (hs : MeasurableSet s) :
    MeasurableSet (Set.Ioo (0 : ℝ) 1 • ((↑) '' s : Set (E n))) :=
  QuarticConvergence.measurableSet_radialCone hs

abbrev sphereMap {n : ℕ} (L : E n ≃ₗᵢ[ℝ] E n) : Sphere n → Sphere n :=
  QuarticConvergence.euclideanUnitSphereMap L

abbrev sphereHomeomorph {n : ℕ} (L : E n ≃ₗᵢ[ℝ] E n) : Sphere n ≃ₜ Sphere n :=
  QuarticConvergence.euclideanUnitSphereMapHomeomorph L

theorem sphereMap_raw_measurePreserving {n : ℕ} (L : E n ≃ₗᵢ[ℝ] E n) :
    MeasurePreserving (sphereMap L)
      (volume : Measure (E n)).toSphere (volume : Measure (E n)).toSphere :=
  QuarticConvergence.euclideanUnitSphereMap_measurePreserving_toSphere L

theorem sphereMap_measurePreserving {n : ℕ} (L : E n ≃ₗᵢ[ℝ] E n) :
    MeasurePreserving (sphereMap L) (surface n) (surface n) :=
  QuarticConvergence.euclideanUnitSphereMap_measurePreserving L

theorem coordinates_unitSphere {n : ℕ} (x : Sphere n) :
    (fun i => x.1 i) ∈ OptimalConvergenceRates.SphereDimensionBounds.Foundation.unitSphere n := by
  have hx : ‖x.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using x.2
  change (∑ i,x.1 i^2)=1
  have hs : ‖x.1‖^2=∑ i,‖x.1 i‖^2 := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) x.1
  simp only [Real.norm_eq_abs,sq_abs] at hs
  nlinarith

theorem integrable_continuous {n : ℕ} (hn : 0 < n) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Sphere n → F) (hf : Continuous f) :
    Integrable f (surface n) := by
  letI := surface_isProbability n hn
  simpa only [IntegrableOn,Measure.restrict_univ] using
    hf.continuousOn.integrableOn_compact (μ:=surface n) isCompact_univ

end OptimalConvergenceRates.SphereDimensionBounds.SphereMeasure
