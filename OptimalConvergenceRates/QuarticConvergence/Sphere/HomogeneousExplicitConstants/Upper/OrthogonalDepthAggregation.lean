import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.WeightedCubicBilinear

/-! Finite orthogonal aggregation for the external-prefix construction.
The local inverse estimate is supplied by WeightedCubicBilinear. Theorems
here verify the dimension-free sum within a depth and the linear cost in
the number of depths. They do not assert the missing tree coverage. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace OrthogonalDepthAggregation

open scoped BigOperators InnerProductSpace
open WeightedQuadraticSplit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Finite Pythagoras, with no assumption on the number of vectors. -/
theorem orthogonal_sum_norm_sq {I : Type*} [Fintype I] (v : I → E)
    (horth : Pairwise (fun i j ↦ ⟪v i, v j⟫_ℝ = 0)) :
    ‖∑ i,v i‖^2=∑ i,‖v i‖^2 := by
  classical
  rw [←real_inner_self_eq_norm_sq,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum,Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq _
  · intro j _ hji
    exact horth hji.symm
  · simp

section Coordinates
variable {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I]

def project (s : Finset ι) (x : Point ι) : Point ι :=
  (WithLp.equiv 2 (ι→ℝ)).symm (fun i ↦ if i∈s then x i else 0)

omit [Fintype ι] in
@[simp] theorem project_apply (s : Finset ι) (x : Point ι) (i : ι) :
    project s x i=if i∈s then x i else 0 := rfl

theorem project_norm_sq (s : Finset ι) (x : Point ι) :
    ‖project s x‖^2=∑ i,if i∈s then (x i)^2 else 0 := by
  rw [norm_sq]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i∈s <;> simp [project_apply,hi]

/-- Disjoint coordinate input blocks consume at most the full radius. -/
theorem disjoint_project_norm_sq_sum_le (s : I → Finset ι)
    (hs : Pairwise (fun i j ↦ Disjoint (s i) (s j))) (x : Point ι) :
    (∑ j,‖project (s j) x‖^2)≤‖x‖^2 := by
  classical
  simp only [project_norm_sq,norm_sq]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  by_cases hex : ∃ j,i∈s j
  · obtain ⟨j,hj⟩ := hex
    rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro k _ hkj
      have hk : i∉s k := by
        intro hi
        exact (Finset.disjoint_left.mp (hs hkj)) hi hj
      simp [hk]
    · simp
  · have hall : ∀ j,i∉s j := by simpa only [not_exists] using hex
    simp [hall,sq_nonneg]

omit [Fintype I] in
/-- Disjoint coordinate output supports imply orthogonality. -/
theorem supported_pairwise_orthogonal (s : I → Finset ι) (v : I → Point ι)
    (hs : Pairwise (fun i j ↦ Disjoint (s i) (s j)))
    (hv : ∀ j i, i ∉ s j → v j i = 0) :
    Pairwise (fun i j ↦ ⟪v i,v j⟫_ℝ=0) := by
  intro j k hjk
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i∈s j
  · have hk : i∉s k := fun hk ↦ (Finset.disjoint_left.mp (hs hjk)) hi hk
    rw [hv k i hk]
    simp
  · rw [hv j i hi]
    simp

/-- The576 node bound is exactly the actual inverse-prefix estimate.
Disjoint inputs and outputs give a24 bound for their complete depth. -/
theorem depth_norm_le (output input : I → Finset ι) (v : I → Point ι)
    (hout : Pairwise (fun i j ↦ Disjoint (output i) (output j)))
    (hin : Pairwise (fun i j ↦ Disjoint (input i) (input j)))
    (hv : ∀ j i, i ∉ output j → v j i = 0) (x : Point ι)
    (hnode : ∀ j, ‖v j‖ ^ 2 ≤ 576 * ‖x‖ ^ 2*‖project (input j) x‖ ^ 2) :
    ‖∑ j,v j‖≤24*‖x‖^2 := by
  have hs := disjoint_project_norm_sq_sum_le input hin x
  have hnorm : ‖∑ j,v j‖^2≤576*‖x‖^4 := by
    rw [orthogonal_sum_norm_sq v (supported_pairwise_orthogonal output v hout hv)]
    calc
      (∑ j,‖v j‖^2)≤∑ j,576*‖x‖^2*‖project (input j) x‖^2 :=
        Finset.sum_le_sum (fun j _ ↦ hnode j)
      _ = (576*‖x‖^2)*(∑ j,‖project (input j) x‖^2) := by rw [Finset.mul_sum]
      _ ≤ (576*‖x‖^2)*‖x‖^2 := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 576*‖x‖^4 := by ring
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤24*‖x‖^2)).mp
  nlinarith

/-- Summing actual depth outputs costs only the depth count. -/
theorem levels_norm_le {d : ℕ} (output input : Fin d → I → Finset ι)
    (v : Fin d → I → Point ι)
    (hout : ∀ l, Pairwise (fun i j ↦ Disjoint (output l i) (output l j)))
    (hin : ∀ l, Pairwise (fun i j ↦ Disjoint (input l i) (input l j)))
    (hv : ∀ l j i, i ∉ output l j → v l j i = 0) (x : Point ι)
    (hnode : ∀ l j, ‖v l j‖ ^ 2 ≤ 576 * ‖x‖ ^ 2*‖project (input l j) x‖ ^ 2) :
    ‖∑ l,∑ j,v l j‖≤24*(d:ℝ)*‖x‖^2 := by
  calc
    ‖∑ l,∑ j,v l j‖≤∑ l,‖∑ j,v l j‖ := norm_sum_le _ _
    _ ≤ ∑ l,24*‖x‖^2 := Finset.sum_le_sum (fun l _ ↦
      depth_norm_le (output l) (input l) (v l) (hout l) (hin l) (hv l) x (hnode l))
    _ = 24*(d:ℝ)*‖x‖^2 := by simp; ring

end Coordinates
end OrthogonalDepthAggregation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
