import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMap
/-! Exact finite conical dual representations. Compactness of a normalized
convex hull makes its conical hull closed; finite-dimensional separation
then yields a finite positive combination, without a closure operation. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.SelectorFiniteDual

open Set Filter Topology
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual finite nonnegative combinations of a set. -/
def conicHull (S : Set E) : ConvexCone ℝ E where
  carrier := {x | ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (z : ι → E),
    (∀ i, 0 ≤ w i) ∧ (∀ i, z i ∈ S) ∧ ∑ i, w i • z i = x}
  smul_mem' c hc x hx := by
    rcases hx with ⟨ι, hι, w, z, hw, hz, rfl⟩
    refine ⟨ι, hι, (fun i => c*w i), z, (fun i => mul_nonneg hc.le (hw i)), hz, ?_⟩
    simp only [mul_smul, Finset.smul_sum]
  add_mem' x hx y hy := by
    rcases hx with ⟨ι, hι, w, z, hw, hz, rfl⟩
    rcases hy with ⟨κ, hκ, v, a, hv, ha, rfl⟩
    refine ⟨ι ⊕ κ, inferInstance, Sum.elim w v, Sum.elim z a, ?_, ?_, ?_⟩
    · intro i
      rcases i with i | i
      · exact hw i
      · exact hv i
    · intro i
      rcases i with i | i
      · exact hz i
      · exact ha i
    · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

theorem zero_mem_conicHull (S : Set E) : (0:E) ∈ conicHull S := by
  refine ⟨Empty, inferInstance, Empty.elim, Empty.elim, ?_, ?_, ?_⟩
  · intro i; exact i.elim
  · intro i; exact i.elim
  · simp

theorem subset_conicHull (S : Set E) : S ⊆ conicHull S := by
  intro x hx
  refine ⟨Unit, inferInstance, (fun _ => 1), (fun _ => x), (fun _ => zero_le_one),
    (fun _ => hx), ?_⟩
  simp

theorem convexHull_subset_conicHull (S : Set E) : convexHull ℝ S ⊆ conicHull S := by
  intro x hx
  rcases mem_convexHull_iff_exists_fintype.mp hx with ⟨ι,hι,w,z,hw,_,hz,hx⟩
  exact ⟨ι,hι,w,z,hw,hz,hx⟩

theorem mem_conicHull_iff_scaling {S : Set E} (hS : S.Nonempty) (x : E) :
    x ∈ conicHull S ↔ ∃ t : ℝ, 0 ≤ t ∧ ∃ y ∈ convexHull ℝ S, t • y = x := by
  constructor
  · rintro ⟨ι,hι,w,z,hw,hz,hx⟩
    let t := ∑ i, w i
    have ht : 0 ≤ t := Finset.sum_nonneg (fun i _ => hw i)
    by_cases ht0 : t = 0
    · have hw0 (i : ι) : w i = 0 := by
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hw i)).mp ht0 i (Finset.mem_univ _)
      obtain ⟨y,hy⟩ := hS
      refine ⟨0,le_rfl,y,subset_convexHull ℝ S hy,?_⟩
      simpa only [hw0,zero_smul,Finset.sum_const_zero] using hx
    · let v : ι → ℝ := fun i => w i/t
      have hv : ∀ i, 0 ≤ v i := fun i => div_nonneg (hw i) ht
      have hsum : ∑ i, v i = 1 := by
        change (∑ i, w i/t)=1
        rw [← Finset.sum_div]
        exact div_self ht0
      refine ⟨t,ht,∑ i, v i • z i,
        mem_convexHull_of_exists_fintype v z hv hsum hz rfl,?_⟩
      rw [Finset.smul_sum]
      simp only [smul_smul,v]
      have hc (i : ι) : t*(w i/t)=w i := by field_simp
      simp only [hc]
      exact hx
  · rintro ⟨t,ht,y,hy,rfl⟩
    rcases ht.eq_or_lt with rfl | ht
    · simpa only [zero_smul] using zero_mem_conicHull S
    · exact (conicHull S).smul_mem ht (convexHull_subset_conicHull S hy)

/-- A compact convex hull contained in a normalized affine hyperplane has
a closed conical hull. No positivity assumption on an inverse is used. -/
theorem isClosed_conicHull_of_compact_convexHull {S : Set E} (hS : S.Nonempty)
    (hcompact : IsCompact (convexHull ℝ S)) (l : E →L[ℝ] ℝ)
    (hnorm : ∀ z ∈ S, l z = 1) : IsClosed (conicHull S : Set E) := by
  have hslice : ∀ y ∈ convexHull ℝ S, l y = 1 := by
    exact convexHull_min hnorm ((convex_singleton (1:ℝ)).linear_preimage l.toLinearMap)
  apply isSeqClosed_iff_isClosed.mp
  intro u x hu hux
  choose t ht y hy heq using fun k => (mem_conicHull_iff_scaling hS (u k)).mp (hu k)
  have hteq (k : ℕ) : t k = l (u k) := by
    have h := congrArg l (heq k)
    simpa only [map_smul,smul_eq_mul,hslice (y k) (hy k),mul_one] using h
  have htlim : Tendsto t atTop (𝓝 (l x)) := by
    have he : t = fun k => l (u k) := funext hteq
    rw [he]
    exact l.continuous.tendsto x |>.comp hux
  have htx : 0 ≤ l x := ge_of_tendsto htlim (Eventually.of_forall ht)
  obtain ⟨z,hz,φ,hφ,hyz⟩ := hcompact.isSeqCompact (x:=y) hy
  have hprod : Tendsto (fun k => t (φ k) • y (φ k)) atTop (𝓝 (l x • z)) :=
    (htlim.comp hφ.tendsto_atTop).smul hyz
  have hlimit : l x • z = x := by
    apply tendsto_nhds_unique hprod
    simpa only [heq, Function.comp_def] using hux.comp hφ.tendsto_atTop
  exact (mem_conicHull_iff_scaling hS x).mpr ⟨l x,htx,z,hz,hlimit⟩

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- Caratheodory's theorem with zero-weight padding to one fixed length. -/
theorem exists_fixed_convex_combination {S : Set E} (hS : S.Nonempty)
    {x : E} (hx : x ∈ convexHull ℝ S) :
    ∃ (w : Fin (Module.finrank ℝ E+1) → ℝ)
      (z : Fin (Module.finrank ℝ E+1) → E),
      w ∈ stdSimplex ℝ _ ∧ (∀ i, z i ∈ S) ∧ ∑ i, w i • z i = x := by
  classical
  obtain ⟨ι,hι,z,w,hz,ha,hw,hwm,hcombo⟩ := eq_pos_convex_span_of_mem_convexHull hx
  obtain ⟨z0,hz0⟩ := hS
  let N := Module.finrank ℝ E+1
  have hcard : Fintype.card ι ≤ N :=
    ha.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  let κ := ι ⊕ Fin (N-Fintype.card ι)
  have hk : Fintype.card κ = N := by
    simp only [κ,Fintype.card_sum,Fintype.card_fin]
    omega
  let e : κ ≃ Fin N := (Fintype.equivFin κ).trans (finCongr hk)
  let wp : κ → ℝ := Sum.elim w (fun _ => 0)
  let zp : κ → E := Sum.elim z (fun _ => z0)
  have hwp (i : κ) : 0 ≤ wp i := by
    rcases i with i | i
    · exact (hw i).le
    · exact le_rfl
  have hzp (i : κ) : zp i ∈ S := by
    rcases i with i | i
    · exact hz (mem_range_self i)
    · exact hz0
  have hwpsum : ∑ i : κ, wp i = 1 := by
    simpa only [κ,wp,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
      Finset.sum_const_zero,add_zero] using hwm
  have hcombo' : ∑ i : κ, wp i • zp i = x := by
    simpa only [κ,wp,zp,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
      zero_smul,Finset.sum_const_zero,add_zero] using hcombo
  refine ⟨(fun i => wp (e.symm i)),(fun i => zp (e.symm i)),?_,?_,?_⟩
  · exact ⟨fun i => hwp _,(e.symm.sum_comp wp).trans hwpsum⟩
  · exact fun i => hzp _
  · exact (e.symm.sum_comp (fun i => wp i • zp i)).trans hcombo'

/-- In finite dimensions, the actual convex hull of a compact set is
compact. The proof uses a fixed simplex and a fixed finite power of S. -/
theorem isCompact_convexHull_of_isCompact {S : Set E} (hcompact : IsCompact S) :
    IsCompact (convexHull ℝ S) := by
  by_cases hS : S.Nonempty
  · let N := Module.finrank ℝ E+1
    let K := stdSimplex ℝ (Fin N) ×ˢ Set.pi Set.univ (fun _ : Fin N => S)
    let f : ((Fin N → ℝ) × (Fin N → E)) → E := fun p => ∑ i, p.1 i • p.2 i
    have hK : IsCompact K :=
      (isCompact_stdSimplex ℝ (Fin N)).prod (isCompact_univ_pi (fun _ => hcompact))
    have hf : Continuous f := by dsimp [f]; fun_prop
    have himage : f '' K = convexHull ℝ S := by
      ext x
      constructor
      · rintro ⟨⟨w,z⟩,⟨hw,hz⟩,hx⟩
        exact mem_convexHull_of_exists_fintype w z hw.1 hw.2
          (fun i => hz i (mem_univ _)) hx
      · intro hx
        obtain ⟨w,z,hw,hz,hx⟩ := exists_fixed_convex_combination hS hx
        exact ⟨(w,z),⟨hw,fun i _ => hz i⟩,hx⟩
    rw [← himage]
    exact hK.image hf
  · have he : S=∅ := Set.not_nonempty_iff_eq_empty.mp hS
    simp [he]

/-- Exact finite-dimensional duality for an evaluation set whose convex
hull is compact and normalized at a base element. The output is an actual
finite nonnegative combination, rather than membership in a closure. -/
theorem finite_dual_of_compact_convexHull
    (S : Set (E →L[ℝ] ℝ)) (hS : S.Nonempty)
    (hcompact : IsCompact (convexHull ℝ S))
    (b : E) (hnorm : ∀ l ∈ S, l b = 1)
    (L : E →L[ℝ] ℝ)
    (hL : ∀ x : E, (∀ l ∈ S, 0 ≤ l x) → 0 ≤ L x) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (z : ι → E →L[ℝ] ℝ),
      (∀ i, 0 ≤ w i) ∧ (∀ i, z i ∈ S) ∧ ∑ i, w i • z i = L := by
  change L ∈ conicHull S
  by_contra hnot
  have hclosed := isClosed_conicHull_of_compact_convexHull hS hcompact
    (ContinuousLinearMap.apply ℝ ℝ b) hnorm
  obtain ⟨T,c,hLc,hsep⟩ := geometric_hahn_banach_point_closed
    (conicHull S).convex hclosed hnot
  have hc : c < 0 := by simpa only [map_zero] using hsep 0 (zero_mem_conicHull S)
  have hT (a : E →L[ℝ] ℝ) (ha : a ∈ conicHull S) : 0 ≤ T a := by
    by_contra hneg
    have haneg : T a < 0 := lt_of_not_ge hneg
    have hpos : 0 < c/(T a)+1 := by
      have hdiv := div_pos_of_neg_of_neg hc haneg
      linarith
    have hs := hsep ((c/(T a)+1) • a) ((conicHull S).smul_mem hpos ha)
    rw [map_smul,smul_eq_mul] at hs
    have heq : (c/(T a)+1)*(T a)=c+T a := by
      rw [add_mul, div_mul_cancel₀ _ (ne_of_lt haneg), one_mul]
    rw [heq] at hs
    linarith
  let Tlin : Module.Dual ℝ (Module.Dual ℝ E) := T.toLinearMap.comp
    (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ).toLinearMap
  let x : E := (Module.evalEquiv ℝ E).symm Tlin
  have hx (a : E →L[ℝ] ℝ) : a x = T a := by
    change a.toLinearMap ((Module.evalEquiv ℝ E).symm Tlin)=Tlin a.toLinearMap
    exact Module.apply_evalEquiv_symm_apply ℝ E a.toLinearMap Tlin
  have hnonneg : 0 ≤ L x := hL x (fun a ha => by
    rw [hx]
    exact hT a (subset_conicHull S ha))
  rw [hx] at hnonneg
  linarith

/-- A compact normalized evaluation set has an exact finite conical dual
representation. No closure of the conical hull occurs in the conclusion. -/
theorem finite_dual_of_compact
    (S : Set (E →L[ℝ] ℝ)) (hS : S.Nonempty) (hcompact : IsCompact S)
    (b : E) (hnorm : ∀ l ∈ S, l b = 1)
    (L : E →L[ℝ] ℝ)
    (hL : ∀ x : E, (∀ l ∈ S, 0 ≤ l x) → 0 ≤ L x) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (z : ι → E →L[ℝ] ℝ),
      (∀ i, 0 ≤ w i) ∧ (∀ i, z i ∈ S) ∧ ∑ i, w i • z i = L :=
  finite_dual_of_compact_convexHull S hS
    (isCompact_convexHull_of_isCompact hcompact) b hnorm L hL

/-- A compact continuous family version with actual parameter points in
the final finite sum. -/
theorem finite_dual_of_compact_family {T : Type*} [TopologicalSpace T]
    [CompactSpace T] [Nonempty T] (ev : T → E →L[ℝ] ℝ) (hev : Continuous ev)
    (b : E) (hnorm : ∀ t, ev t b = 1) (L : E →L[ℝ] ℝ)
    (hL : ∀ x : E, (∀ t, 0 ≤ ev t x) → 0 ≤ L x) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (z : ι → T),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i • ev (z i) = L := by
  obtain ⟨ι,hι,w,z,hw,hz,hcombo⟩ := finite_dual_of_compact (Set.range ev)
    (Set.range_nonempty ev) (isCompact_range hev) b
    (by rintro _ ⟨t,rfl⟩; exact hnorm t) L (by
      intro x hx
      exact hL x (fun t => hx _ (mem_range_self t)))
  choose a ha using hz
  exact ⟨ι,hι,w,a,hw,by simpa only [ha] using hcombo⟩

end FiniteDimensional

end OptimalConvergenceRates.SphereDimensionBounds.SelectorFiniteDual
