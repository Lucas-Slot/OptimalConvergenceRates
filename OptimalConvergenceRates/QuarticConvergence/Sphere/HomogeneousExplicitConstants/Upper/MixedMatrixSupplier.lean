import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.MatrixSmoothingConstraint

/-! The actual mixed-node matrix supplier, from original scalar quadratic
domination to a homogeneous polynomial matrix, pure-radius matrix SOS,
and literal polynomial weighted pairing. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace MixedMatrixSupplier

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
open MeasureTheory Matrix MvPolynomial SphereMeasure
  SmoothingKernelCoordinates SphereMatrixSmoothing HomogeneousMatrixSmoothing
  HomogeneousMatrixBound MatrixSmoothingConstraint
open WeightedQuadraticExistence

abbrev P (n : ℕ) := Foundation.Polynomial n
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

theorem projection_norm {n : ℕ} (U : Finset (Fin n)) (x : E n) :
    ‖CubicBlockInverse.projection U x‖=Real.sqrt (blockRadius U x) := by
  have hsq := OrthogonalDepthAggregation.project_norm_sq U x
  have hU : (∑i,if i∈U then x i^2 else 0)=∑i∈U,x i^2 := by
    calc
      (∑i,if i∈U then x i^2 else 0)=∑i∈U,if i∈U then x i^2 else 0 :=
        (Finset.sum_subset (Finset.subset_univ U) (by intro i _ hi;simp [hi])).symm
      _ = _ := by apply Finset.sum_congr rfl;intro i hi;simp [hi]
  rw [hU] at hsq
  have hh := congrArg Real.sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _)] at hh
  have hproj : CubicBlockInverse.projection U x=OrthogonalDepthAggregation.project U x := by
    ext i
    by_cases hi:i∈U <;> simp [CubicBlockInverse.projection_apply,
      OrthogonalDepthAggregation.project_apply,hi]
  rw [hproj]
  simpa only [blockRadius] using hh

/-- Actual entrywise Borel odd completion field on the same sphere, with
the exact projected-radius norm bound. No completion field is assumed. -/
theorem exists_completion_field {n d : ℕ} (L : Mat d) (hL : L.PosSemidef)
    (S : E n →ₗ[ℝ] Mat d) (hS : ∀ u, (S u).transpose = S u) {D : ℝ} (hD : 0 ≤ D)
    (hdom : ∀ u x, |quadraticValue (S u) x| ≤ (D * ‖u‖) * ‖Matrix.toEuclideanLin L x‖ * ‖x‖)
    (U : Finset (Fin n)) :
    ∃ F : Sphere n→Mat d,
      (∀i j, Measurable (fun y ↦ F y i j)) ∧
      (∀y, ‖F y‖≤blockBound (2*D) U y) ∧
      (∀y, F (antipode y)= -F y) ∧
      (∀y, weightedMap L (F y)=S (CubicBlockInverse.projection U y.1)) := by
  letI : MeasurableSpace (Mat d) := WeightedQuadraticSelection.matrixMeasurableSpace
  letI : BorelSpace (Mat d) := WeightedQuadraticSelection.matrixBorelSpace
  obtain ⟨C,hCmeas,hCnorm,hCeq,hCodd⟩ :=
    WeightedQuadraticSelection.exists_borel_odd_weighted_completion L S hL hS hD hdom
  let F : Sphere n→Mat d := fun y ↦ C (CubicBlockInverse.projection U y.1)
  have hP : Continuous (fun y : Sphere n ↦ CubicBlockInverse.projection U y.1) :=
    (CubicBlockInverse.projection U).toContinuousLinearMap.continuous.comp continuous_subtype_val
  refine ⟨F,?_,?_,?_,?_⟩
  · intro i j
    exact (entryLinear i j).toContinuousLinearMap.continuous.measurable.comp (hCmeas.comp
      hP.measurable)
  · intro y
    change ‖C (CubicBlockInverse.projection U y.1)‖≤_
    exact (hCnorm _).trans_eq (by rw [projection_norm];rfl)
  · intro y
    change C (CubicBlockInverse.projection U (antipode y).1)= -C (CubicBlockInverse.projection U
      y.1)
    change C (CubicBlockInverse.projection U (-y.1))= -C (CubicBlockInverse.projection U y.1)
    rw [map_neg,hCodd]
  · intro y
    exact hCeq _

/-- Complete mixed-matrix supplier. The only analytic input is the original
scalar domination of an actual linear symmetric family. -/
theorem exists_homogeneous_matrix_supplier {n s d : ℕ} (hn : 2 ≤ n) (hs : n ≤ 2 * s)
    (L : Mat d) (hL : L.PosSemidef) (S : E n →ₗ[ℝ] Mat d)
    (hS : ∀ u, (S u).transpose = S u) {D : ℝ} (hD : 0 ≤ D)
    (hdom : ∀ u x, |quadraticValue (S u) x| ≤ (D * ‖u‖) * ‖Matrix.toEuclideanLin L x‖ * ‖x‖)
    (U : Finset (Fin n)) :
    ∃ M : Matrix (Fin d) (Fin d) (P n),
      (∀i j,(M i j).IsHomogeneous (2*s-1)) ∧
      FiniteMatrixVariance.BoundedMatrixSOS (3*s)
        (radialBound s (16*D^2) (blockWeight U) M) ∧
      polynomialWeightedMap L M=(Foundation.radiusPolynomial n)^(s-1) •
        familyPolynomial (S.comp (CubicBlockInverse.projection U)) ∧
      ∀v : Fin d→P n,
        (∑i,(∑j,C (L i j)*v j)*(∑j,M i j*v j))=
          (Foundation.radiusPolynomial n)^(s-1)*FiniteMatrixVariance.quadraticForm
            (familyPolynomial (S.comp (CubicBlockInverse.projection U))) v := by
  obtain ⟨F,hFmeas,hFnorm,hFodd,hFeq⟩ := exists_completion_field L hL S hS hD hdom U
  have hB : 0≤2*D := by positivity
  have hbound : ∀y, ‖F y‖≤2*D := fun y ↦ (hFnorm y).trans (blockBound_le hB U y)
  have hpair := corrected_constraint_polynomial (s:=s) hn hs L
    (S.comp (CubicBlockInverse.projection U)) F hFmeas hbound hFeq hFodd
  refine ⟨correctedMean (s:=s) F,correctedMean_homogeneous F,?_,hpair,?_⟩
  · have hm := homogeneous_matrix_smoothing_bound (s:=s) hn hs hB U F hFmeas hFnorm hFodd
    have hb : 4*(2*D)^2=16*D^2 := by ring
    simpa only [hb] using hm
  · intro v
    have hLt : L.transpose=L := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hL.isHermitian.eq
    exact pairing_of_polynomial_constraint L hLt _ _ hpair v

end MixedMatrixSupplier
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
