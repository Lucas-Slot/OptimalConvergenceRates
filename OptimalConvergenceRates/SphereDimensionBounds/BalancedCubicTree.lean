import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.SphereDimensionBounds.CubicPrefixTree
import OptimalConvergenceRates.SphereDimensionBounds.WeightedQuadraticPadding

/-! An explicit balanced complete coordinate tree. Positivity and sorted
spectral order imply every required external-prefix invariant. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.BalancedCubicTree

set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open WeightedQuadraticTree WeightedQuadraticPadding WeightedQuadraticSplit
  WeightedCubicSplit OrderedCubicExpansion CubicPrefixTree

local instance (priority := 2000) finOrderDecidableEq (n : ℕ) : DecidableEq (Fin n) :=
  (inferInstance : LinearOrder (Fin n)).toDecidableEq

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def complete : (d : ℕ)→(Coord d→ι)→IndexTree ι
  | 0,f=>.leaf (f (0:Fin 1))
  | d+1,f=>.node (complete d (fun i=>f (Sum.inl i))) (complete d (fun j=>f (Sum.inr j)))

omit [Fintype ι] in
theorem complete_support (d : ℕ) (f : Coord d → ι) :
    support (complete d f)=Finset.univ.image f := by
  induction d with
  | zero=>
    change ({f (0:Fin 1)}:Finset ι)=Finset.univ.image f
    ext i
    simp only [Finset.mem_singleton,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · intro hi;exact ⟨(0:Fin 1),hi.symm⟩
    · rintro ⟨j,hj⟩;fin_cases j;exact hj.symm
  | succ d ih=>
    simp only [complete,support,ih]
    ext i
    simp only [Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro (⟨j,hj⟩|⟨j,hj⟩)
      · exact ⟨Sum.inl j,hj⟩
      · exact ⟨Sum.inr j,hj⟩
    · rintro ⟨j,hj⟩
      cases j with
      | inl j=>exact Or.inl ⟨j,hj⟩
      | inr j=>exact Or.inr ⟨j,hj⟩

omit [Fintype ι] [LinearOrder ι] in
theorem complete_depth (d : ℕ) (f : Coord d → ι) : depth (complete d f)=d := by
  induction d with
  | zero=>rfl
  | succ d ih=>simp only [complete,depth,ih,max_self]

omit [Fintype ι] in
theorem high_low_images_disjoint (d : ℕ) (f : Coord (d + 1) → ι) (hf : Function.Injective f) :
    Disjoint (Finset.univ.image (fun i:Coord d=>f (Sum.inl i)))
      (Finset.univ.image (fun i:Coord d=>f (Sum.inr i))) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨j,_,hjeq⟩:=Finset.mem_image.mp hi
  obtain ⟨k,_,hkeq⟩:=Finset.mem_image.mp hj
  have heq:=hf (hjeq.trans hkeq.symm)
  cases heq

omit [Fintype ι] in
/-- This establishes every tree invariant from actual spectral order and
an external coordinate set lying below the whole current block. -/
theorem complete_valid (d : ℕ) (f : Coord d → ι) (a : ι → ℝ)
    (hf : Function.Injective f) (ha : OrderedPositive d (fun i => a (f i)))
    (E : Finset ι) (hE : Disjoint E (Finset.univ.image f))
    (hEa : ∀ j ∈ E, 0 ≤ a j ∧ ∀ i:Coord d,a j≤a (f i)) :
    Valid a (complete d f) E := by
  induction d generalizing E with
  | zero=>
    refine ⟨ha (0:Fin 1),?_,?_⟩
    · intro hi
      exact (Finset.disjoint_left.mp hE) hi (Finset.mem_image.mpr ⟨(0:Fin 1),Finset.mem_univ _,rfl⟩)
    · intro j hj
      exact ⟨(hEa j hj).1,(hEa j hj).2 (0:Fin 1)⟩
  | succ d ih=>
    let fH:Coord d→ι:=fun i=>f (Sum.inl i)
    let fL:Coord d→ι:=fun i=>f (Sum.inr i)
    let H:=Finset.univ.image fH
    let U:=Finset.univ.image fL
    have hfH:Function.Injective fH:=fun _ _ hij=>Sum.inl.inj (hf hij)
    have hfL:Function.Injective fL:=fun _ _ hij=>Sum.inr.inj (hf hij)
    have hHU:Disjoint H U:=high_low_images_disjoint d f hf
    have hHsub:H⊆Finset.univ.image f:=by
      intro i hi
      obtain ⟨j,_,hj⟩:=Finset.mem_image.mp hi
      exact Finset.mem_image.mpr ⟨Sum.inl j,Finset.mem_univ _,hj⟩
    have hUsub:U⊆Finset.univ.image f:=by
      intro i hi
      obtain ⟨j,_,hj⟩:=Finset.mem_image.mp hi
      exact Finset.mem_image.mpr ⟨Sum.inr j,Finset.mem_univ _,hj⟩
    have hEH:Disjoint E H:=by
      apply Finset.disjoint_left.mpr
      intro i he hi
      exact (Finset.disjoint_left.mp hE) he (hHsub hi)
    have hEU:Disjoint E U:=by
      apply Finset.disjoint_left.mpr
      intro i he hi
      exact (Finset.disjoint_left.mp hE) he (hUsub hi)
    have hEH':Disjoint (U∪E) H:=Finset.disjoint_union_left.mpr ⟨hHU.symm,hEH⟩
    have hEaH:∀ j∈U∪E,0≤a j ∧ ∀ i:Coord d,a j≤a (fH i):=by
      intro j hj
      rcases Finset.mem_union.mp hj with hj|hj
      · obtain ⟨k,_,hk⟩:=Finset.mem_image.mp hj
        subst j
        exact ⟨(orderedPositive_pos d _ ha.2.1 k).le,fun i=>ha.2.2 i k⟩
      · exact ⟨(hEa j hj).1,fun i=>(hEa j hj).2 (Sum.inl i)⟩
    have hEaL:∀ j∈E,0≤a j ∧ ∀ i:Coord d,a j≤a (fL i):=by
      intro j hj
      exact ⟨(hEa j hj).1,fun i=>(hEa j hj).2 (Sum.inr i)⟩
    have hh:=ih fH hfH ha.1 (U∪E) hEH' hEaH
    have hl:=ih fL hfL ha.2.1 E hEU hEaL
    obtain ⟨m,hm⟩:=Finite.exists_min (fun i:Coord d=>a (fH i))
    have hgap:∃ tau:ℝ,0<tau ∧ (∀ i∈H,tau≤a i) ∧
        ∀ j∈U∪E,0≤a j ∧ a j≤tau:=by
      refine ⟨a (fH m),orderedPositive_pos d _ ha.1 m,?_,?_⟩
      · intro i hi
        obtain ⟨j,_,hj⟩:=Finset.mem_image.mp hi
        rw [←hj]
        exact hm j
      · intro j hj
        exact ⟨(hEaH j hj).1,(hEaH j hj).2 m⟩
    change Disjoint (support (complete d fH)) (support (complete d fL)) ∧
      Disjoint E (support (complete d fH)∪support (complete d fL)) ∧
      Valid a (complete d fH) (support (complete d fL)∪E) ∧
      Valid a (complete d fL) E ∧ _
    rw [complete_support,complete_support]
    exact ⟨hHU,Finset.disjoint_union_right.mpr ⟨hEH,hEU⟩,hh,hl,hgap⟩

theorem complete_support_of_surjective (d : ℕ) (f : Coord d → ι) (hf : Function.Surjective f) :
    support (complete d f)=Finset.univ := by
  rw [complete_support]
  exact Finset.image_univ_of_surjective hf

def fullTree (d : ℕ) : IndexTree (Fin (2^d)) := complete d (coordEquivFin d)

theorem fullTree_support (d : ℕ) : support (fullTree d)=Finset.univ :=
  complete_support_of_surjective d (coordEquivFin d) (coordEquivFin d).surjective

theorem fullTree_depth (d : ℕ) : depth (fullTree d)=d := complete_depth _ _

theorem fullTree_valid (d : ℕ) (a : Fin (2 ^ d) → ℝ) (ha : ∀ i, 0 < a i) (hmono : Antitone a) :
    Valid a (fullTree d) ∅ := by
  apply complete_valid d (coordEquivFin d) a (coordEquivFin d).injective
    (orderedPositive_of_antitone d a ha hmono)
  · simp
  · simp

set_option maxHeartbeats 1000000 in
/-- Actual quadratic polynomial division on a complete balanced tree;
the tree is constructed, rather than supplied as an extra premise. -/
theorem exists_quadratic_division_pow (d : ℕ) (a : Fin (2 ^ d) → ℝ)
    (ha : ∀ i, 0 < a i) (hmono : Antitone a) (T : Tri (Point (Fin (2 ^ d))))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2) :
    ∃ b:Fin (2^d)→MvPolynomial (Fin (2^d)) ℝ,
      (∀ i,(b i).IsHomogeneous 2) ∧
      (∑ i,MvPolynomial.C (a i)*MvPolynomial.X i*b i)=cubicFromTri T ∧
      ∀ h:Point (Fin (2^d)),‖(WithLp.equiv 2 (Fin (2^d)→ℝ)).symm
        (fun i=>MvPolynomial.eval (fun j=>h j) (b i))‖≤80*((d:ℝ)+1)*‖h‖^2 := by
  refine ⟨CubicPrefixTree.divisionPolynomial a T (fullTree d) ∅,
    CubicPrefixTree.divisionPolynomial_homogeneous a T (fullTree d) ∅,
    full_divisionPolynomial_identity a T h12 h23 (fullTree d)
      (fullTree_valid d a ha hmono) (fullTree_support d),?_⟩
  intro h
  have hh:=full_divisionPolynomial_norm_le_eighty a T h12 h23 hdom
    (fullTree d) (fullTree_valid d a ha hmono) (fullTree_support d) h
  simpa only [fullTree_depth] using hh

end OptimalConvergenceRates.SphereDimensionBounds.BalancedCubicTree
