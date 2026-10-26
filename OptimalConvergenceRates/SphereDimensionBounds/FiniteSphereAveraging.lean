import OptimalConvergenceRates.SphereDimensionBounds.SpherePolynomialSpace
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Exact finite averaging of continuous families in finite-dimensional
spaces. Compact convex hulls supply an actual finite convex combination,
so pointwise certificates can be averaged without selecting their witnesses
continuously or measurably. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.FiniteSphereAveraging

open scoped BigOperators
open Set MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem compact_convexHull {s : Set V} (hs : IsCompact s) : IsCompact (convexHull ℝ s) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl|hsne
  · simp
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  let I := Fin (Module.finrank ℝ V+1)
  let P := (stdSimplex ℝ I)×(I → s)
  let barycenter : P → V := fun p => ∑ i,p.1.1 i • (p.2 i).1
  have hcontinuous : Continuous barycenter := by
    apply continuous_finsetSum
    intro i hi
    exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))
  have hrange : Set.range barycenter=convexHull ℝ s := by
    apply Set.Subset.antisymm
    · rintro z ⟨p,rfl⟩
      exact mem_convexHull_of_exists_fintype p.1.1 (fun i => (p.2 i).1)
        p.1.2.1 p.1.2.2 (fun i => (p.2 i).2) rfl
    · intro z hz
      let t := Caratheodory.minCardFinsetOfMemConvexHull hz
      have ht_sub : (t:Set V)⊆s := Caratheodory.minCardFinsetOfMemConvexHull_subseteq hz
      have ht_mem : z∈convexHull ℝ (t:Set V) := Caratheodory.mem_minCardFinsetOfMemConvexHull hz
      have ht_aff : AffineIndependent ℝ ((↑) : t → V) :=
        Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hz
      obtain ⟨w,hw_nonneg,hw_sum,hw_center⟩ := Finset.mem_convexHull'.mp ht_mem
      have hcard : Fintype.card t≤Module.finrank ℝ V+1 :=
        ht_aff.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
      have hcard' : Fintype.card t≤Fintype.card I := by simpa only [I,Fintype.card_fin] using hcard
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard'
      let z0 : s := ⟨hsne.some,hsne.some_mem⟩
      let W : I → ℝ := Function.extend e (fun i : t => w i.1) (fun _ => 0)
      let Z : I → s := Function.extend e (fun i : t => ⟨i.1,ht_sub i.2⟩) (fun _ => z0)
      have hW_nonneg : ∀ i,0≤W i := by
        intro i
        by_cases hi : ∃ j,e j=i
        · obtain ⟨j,rfl⟩ := hi
          simp [W,e.injective.extend_apply,hw_nonneg j.1 j.2]
        · simp [W,Function.extend_apply' _ _ _ hi]
      have hW_sum : ∑ i,W i=1 := by
        calc
          ∑ i,W i=∑ j : t,w j.1 := by
            symm
            apply Fintype.sum_of_injective e e.injective (fun j : t => w j.1) W
            · intro i hi
              simp [W,Function.extend_apply' _ _ _ hi]
            · intro j
              simp [W,e.injective.extend_apply]
          _=1 := (Finset.sum_finset_coe w t).trans hw_sum
      have hcenter : ∑ i,W i • (Z i).1=z := by
        calc
          ∑ i,W i • (Z i).1=∑ j : t,w j.1 • j.1 := by
            symm
            apply Fintype.sum_of_injective e e.injective (fun j : t => w j.1 • j.1)
              (fun i => W i • (Z i).1)
            · intro i hi
              simp [W,Function.extend_apply' _ _ _ hi]
            · intro j
              simp [W,Z,e.injective.extend_apply]
          _=z := (Finset.sum_finset_coe (fun y => w y • y) t).trans hw_center
      let a : stdSimplex ℝ I := ⟨W,hW_nonneg,hW_sum⟩
      exact ⟨(a,Z),hcenter⟩
  rw [←hrange]
  exact isCompact_range hcontinuous

theorem exists_finite_integral {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
    [T2Space Ω] [MeasurableSpace Ω] [BorelSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (f : Ω → V) (hf : Continuous f) :
    ∃ (N : ℕ) (w : Fin N → ℝ) (y : Fin N → Ω),
      (∀ i,0≤w i) ∧ (∑ i,w i)=1 ∧ (∫ x,f x ∂mu)=∑ i,w i • f (y i) := by
  classical
  have hfi : Integrable f mu := by
    simpa only [IntegrableOn,Measure.restrict_univ] using
      hf.continuousOn.integrableOn_compact (μ:=mu) isCompact_univ
  have hc := compact_convexHull (isCompact_range hf)
  have hmem : (∫ x,f x ∂mu)∈convexHull ℝ (Set.range f) :=
    (convex_convexHull ℝ _).integral_mem hc.isClosed
      (Filter.Eventually.of_forall (fun x => subset_convexHull ℝ _ (Set.mem_range_self x))) hfi
  obtain ⟨I,hI,w,z,hw,hs,hz,hcenter⟩ := mem_convexHull_iff_exists_fintype.mp hmem
  letI := hI
  choose y hy using hz
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I,fun i => w (e.symm i),fun i => y (e.symm i),fun i => hw _,?_,?_⟩
  · exact (e.symm.sum_comp w).trans hs
  · change (∫ x,f x ∂mu)=∑ i,w (e.symm i) • f (y (e.symm i))
    rw [e.symm.sum_comp (fun i => w i • f (y i))]
    rw [←hcenter]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hy i]

end OptimalConvergenceRates.SphereDimensionBounds.FiniteSphereAveraging
