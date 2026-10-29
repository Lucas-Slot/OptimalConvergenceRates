import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.BalancedCubicTree
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.WeightedQuadraticSingular

/-! Singular-spectrum continuation of the same explicit cubic prefix
constructor. No new vector is chosen at the boundary. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace CubicPrefixSingular
open scoped BigOperators InnerProductSpace
open Filter Topology
open MvPolynomial WeightedQuadraticSplit WeightedCubicSplit OrderedCubicExpansion
  CubicPrefixTree CubicBlockInverse BalancedCubicTree OrthogonalDepthAggregation

local instance (priority := 2000) finOrderDecidableEq (n : ℕ) : DecidableEq (Fin n) :=
  (inferInstance : LinearOrder (Fin n)).toDecidableEq

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem nodeMap_division (a : ι→ℝ) (T : Tri (Point ι)) (H U E : Finset ι)
    (x y : Point ι) (i : ι) :
    nodeMap a T H U E x y i=nodeMap (fun _↦1) T H U E x y i/a i := by
  change 3*(if i∈H then _/a i else 0)=(3*(if i∈H then _/(1:ℝ) else 0))/a i
  by_cases hi:i∈H <;> simp only [hi,ite_true,ite_false,div_one,mul_zero,zero_div]
  ring

theorem leafMap_division (a : ι→ℝ) (T : Tri (Point ι)) (j : ι) (E : Finset ι)
    (x y : Point ι) (i : ι) :
    leafMap a T j E x y i=leafMap (fun _↦1) T j E x y i/a i := by
  by_cases hij:i=j
  · subst i
    simp only [leafMap,LinearMap.mk₂_apply,PiLp.smul_apply,smul_eq_mul,
      coordinateAxis,div_one]
    ring
  · simp [leafMap,coordinateAxis,Pi.single_apply,hij]

theorem lastMap_division (a : ι→ℝ) (T : Tri (Point ι)) (tr : IndexTree ι) (E : Finset ι)
    (x y : Point ι) (i : ι) :
    lastMap a T tr E x y i=lastMap (fun _↦1) T tr E x y i/a i := by
  induction tr generalizing E with
  | leaf j=>simp [lastMap]
  | node hi lo ihh ihl=>
    change lastMap a T hi (support lo∪E) x y i+lastMap a T lo E x y i+
      nodeMap a T (support hi) (support lo) E x y i=_
    rw [ihh,ihl,nodeMap_division]
    simp only [lastMap,LinearMap.add_apply,PiLp.add_apply,add_div]

theorem leavesMap_division (a : ι→ℝ) (T : Tri (Point ι)) (tr : IndexTree ι) (E : Finset ι)
    (x y : Point ι) (i : ι) :
    leavesMap a T tr E x y i=leavesMap (fun _↦1) T tr E x y i/a i := by
  induction tr generalizing E with
  | leaf j=>exact leafMap_division a T j E x y i
  | node hi lo ihh ihl=>
    change leavesMap a T hi (support lo∪E) x y i+leavesMap a T lo E x y i=_
    rw [ihh,ihl]
    simp only [leavesMap,LinearMap.add_apply,PiLp.add_apply,add_div]

/-- Every coordinate depends on the spectrum through this one scalar
division, even when its denominator vanishes. -/
theorem divisionMap_division (a : ι→ℝ) (T : Tri (Point ι)) (tr : IndexTree ι) (E : Finset ι)
    (x y : Point ι) (i : ι) :
    divisionMap a T tr E x y i=divisionMap (fun _↦1) T tr E x y i/a i := by
  change leavesMap a T tr E x y i+lastMap a T tr E x y i=_
  rw [leavesMap_division,lastMap_division]
  simp only [divisionMap,LinearMap.add_apply,PiLp.add_apply,add_div]

theorem zero_of_bounded_div {u C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ e:ℝ,0<e→|u/e|≤C) : u=0 := by
  by_contra hu
  have hup:0 < |u|:=abs_pos.mpr hu
  have hCp:0<C+1:=by linarith
  have he:0 < |u|/(C+1):=div_pos hup hCp
  have hh:=hbound (|u|/(C+1)) he
  rw [abs_div,abs_of_pos he] at hh
  have hm:|u|≤C*(|u|/(C+1)) := (div_le_iff₀ he).mp hh
  have hi:= (le_div_iff₀ hCp).mp (show |u|≤C*|u|/(C+1) by simpa [mul_div_assoc] using hm)
  nlinarith

section Power

variable {d : ℕ}

theorem shifted_domination (a : Fin (2 ^ d) → ℝ) (ha : ∀ i, 0 ≤ a i) {e : ℝ} (he : 0 ≤ e)
    (T : Tri (Point (Fin (2 ^ d))))
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2) :
    ∀ x,|diagonalCubic T x|≤2*‖diagonal (fun i↦a i+e) x‖*‖x‖^2 := by
  intro x
  have hn:‖diagonal a x‖≤‖diagonal (fun i↦a i+e) x‖:=by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq,norm_sq]
    apply Finset.sum_le_sum
    intro i _
    rw [diagonal_apply,diagonal_apply,mul_pow,mul_pow]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (ha i) (add_nonneg (ha i) he)).mpr (le_add_of_nonneg_right he)) (sq_nonneg _)
  exact (hdom x).trans (by gcongr)

theorem shifted_norm_le (a : Fin (2 ^ d) → ℝ) (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a)
    {e : ℝ} (he : 0 < e) (T : Tri (Point (Fin (2 ^ d))))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2) (h : Point (Fin (2 ^ d))) :
    ‖divisionMap (fun i↦a i+e) T (fullTree d) ∅ h h‖≤80*((d:ℝ)+1)*‖h‖^2 := by
  have hp:∀ i,0<a i+e:=fun i↦add_pos_of_nonneg_of_pos (ha i) he
  have hm:Antitone (fun i↦a i+e):=fun i j hij↦by linarith [hmono hij]
  have hv:=fullTree_valid d (fun i↦a i+e) hp hm
  have hh:=divisionMap_norm_le (fun i↦a i+e) T h12 h23 (shifted_domination a ha he.le T hdom)
    (fullTree d) ∅ hv h
  have hu:project (Finset.univ:Finset (Fin (2^d))) h=h:=project_eq_self (by simp)
  simp only [fullTree_support,Finset.union_empty,hu,fullTree_depth] at hh
  have hd:0≤(d:ℝ):=by positivity
  exact hh.trans (by nlinarith [sq_nonneg ‖h‖])

/-- Uniform positive-spectrum control forces the fixed numerator to
vanish on every zero denominator. This is proved, not assumed. -/
theorem numerator_zero (a : Fin (2 ^ d) → ℝ) (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a)
    (T : Tri (Point (Fin (2 ^ d))))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2)
    (h : Point (Fin (2 ^ d))) (i : Fin (2 ^ d)) (hi : a i = 0) :
    divisionMap (fun _↦1) T (fullTree d) ∅ h h i=0 := by
  apply zero_of_bounded_div (C:=80*((d:ℝ)+1)*‖h‖^2) (by positivity)
  intro e he
  have hn:=shifted_norm_le a ha hmono he T h12 h23 hdom h
  have hc:=OrderedCubicLeafBounds.coordinate_abs_le_norm
    (divisionMap (fun j↦a j+e) T (fullTree d) ∅ h h) i
  rw [divisionMap_division,hi,zero_add] at hc
  exact hc.trans hn

theorem shift_coordinate_continuous (a : Fin (2 ^ d) → ℝ) (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a)
    (T : Tri (Point (Fin (2 ^ d))))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2)
    (h : Point (Fin (2 ^ d))) (i : Fin (2 ^ d)) :
    ContinuousAt (fun e:ℝ↦divisionMap (fun j↦a j+e) T (fullTree d) ∅ h h i) 0 := by
  have hf:(fun e:ℝ↦divisionMap (fun j↦a j+e) T (fullTree d) ∅ h h i)=
      (fun e:ℝ↦divisionMap (fun _↦1) T (fullTree d) ∅ h h i/(a i+e)):=by
    funext e
    exact divisionMap_division _ _ _ _ _ _ _
  rw [hf]
  exact WeightedQuadraticSingular.continuousAt_div_shift _ _
    (numerator_zero a ha hmono T h12 h23 hdom h i)

theorem point_norm_eq_sqrt (h : Point (Fin (2 ^ d))) : ‖h‖=Real.sqrt (∑ i,(h i)^2) := by
  rw [←norm_sq,Real.sqrt_sq (norm_nonneg h)]

theorem shift_norm_continuous (a : Fin (2 ^ d) → ℝ) (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a)
    (T : Tri (Point (Fin (2 ^ d))))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2) (h : Point (Fin (2 ^ d))) :
    ContinuousAt (fun e:ℝ↦‖divisionMap (fun j↦a j+e) T (fullTree d) ∅ h h‖) 0 := by
  have hs:ContinuousAt (fun e:ℝ↦∑ i,(divisionMap (fun j↦a j+e) T (fullTree d) ∅ h h i)^2) 0:=
    tendsto_finsetSum _ (fun i _↦(shift_coordinate_continuous a ha hmono T h12 h23 hdom h i).pow 2)
  have hf:(fun e:ℝ↦‖divisionMap (fun j↦a j+e) T (fullTree d) ∅ h h‖)=
      (fun e:ℝ↦Real.sqrt (∑ i,(divisionMap (fun j↦a j+e) T (fullTree d) ∅ h h i)^2)):=by
    funext e
    exact point_norm_eq_sqrt _
  rw [hf]
  exact Real.continuous_sqrt.continuousAt.comp hs

/-- The SAME explicit quadratic vector obeys the logarithmic bound at
all nonnegative antitone spectra, including the all-zero spectrum. -/
theorem divisionMap_norm_le_semidefinite (a : Fin (2 ^ d) → ℝ) (ha : ∀ i, 0 ≤ a i) (hmono :
  Antitone a)
    (T : Tri (Point (Fin (2 ^ d))))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2) (h : Point (Fin (2 ^ d))) :
    ‖divisionMap a T (fullTree d) ∅ h h‖≤80*((d:ℝ)+1)*‖h‖^2 := by
  let f:ℝ→ℝ:=fun e↦‖divisionMap (fun j↦a j+e) T (fullTree d) ∅ h h‖
  have hc:ContinuousAt f 0:=shift_norm_continuous a ha hmono T h12 h23 hdom h
  have ht:Filter.Tendsto f (𝓝[>] (0:ℝ)) (𝓝 (f 0)):=hc.continuousWithinAt.tendsto
  have he:∀ᶠ e:ℝ in 𝓝[>] (0:ℝ),f e≤80*((d:ℝ)+1)*‖h‖^2:=by
    filter_upwards [self_mem_nhdsWithin] with e he
    exact shifted_norm_le a ha hmono he T h12 h23 hdom h
  have hh:=le_of_tendsto ht he
  simpa only [f,add_zero] using hh

/-- The original exact cubic identity also survives on the same formula:
unit-spectrum numerators vanish at every zero denominator. -/
theorem divisionMap_pair_semidefinite (a : Fin (2 ^ d) → ℝ) (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a)
    (T : Tri (Point (Fin (2 ^ d))))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2) (h : Point (Fin (2 ^ d))) :
    ⟪diagonal a h,divisionMap a T (fullTree d) ∅ h h⟫_ℝ=diagonalCubic T h := by
  have hunit:=full_divisionMap_pair (fun _:Fin (2^d)↦(1:ℝ)) T h12 h23 (fullTree d)
    (fullTree_valid d (fun _↦1) (by intro i;norm_num) (by intro i j hij;rfl)) (fullTree_support d) h
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,diagonal_apply,one_mul] at hunit ⊢
  rw [←hunit]
  apply Finset.sum_congr rfl
  intro i _
  rw [divisionMap_division]
  by_cases hi:a i=0
  · rw [hi,numerator_zero a ha hmono T h12 h23 hdom h i hi]
    simp
  · field_simp [hi]

/-- Full actual polynomial division at singular nonnegative spectra. -/
theorem exists_quadratic_division_semidefinite (a : Fin (2 ^ d) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a) (T : Tri (Point (Fin (2 ^ d))))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2) :
    ∃ b:Fin (2^d)→MvPolynomial (Fin (2^d)) ℝ,(∀ i,(b i).IsHomogeneous 2) ∧
      (∑ i,C (a i)*X i*b i)=cubicFromTri T ∧
      ∀ h:Point (Fin (2^d)),‖(WithLp.equiv 2 (Fin (2^d)→ℝ)).symm
        (fun i↦eval (fun j↦h j) (b i))‖≤80*((d:ℝ)+1)*‖h‖^2 := by
  refine ⟨CubicPrefixTree.divisionPolynomial a T (fullTree d) ∅,
    CubicPrefixTree.divisionPolynomial_homogeneous a T (fullTree d) ∅,?_,?_⟩
  · apply MvPolynomial.funext
    intro x
    let h:Point (Fin (2^d)):=evaluationPoint x
    have hh:=divisionMap_pair_semidefinite a ha hmono T h12 h23 hdom h
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,diagonal_apply] at hh
    simp only [map_sum,map_mul,eval_C,eval_X,cubicFromTri_eval]
    change (∑ i,a i*h i*eval (fun j↦h j) (CubicPrefixTree.divisionPolynomial a T (fullTree d) ∅
      i))=diagonalCubic T h
    simp only [CubicPrefixTree.divisionPolynomial_eval]
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro h
    have heq:(WithLp.equiv 2 (Fin (2^d)→ℝ)).symm
        (fun i↦eval (fun j↦h j) (CubicPrefixTree.divisionPolynomial a T (fullTree d) ∅ i))=
        divisionMap a T (fullTree d) ∅ h h := by
      ext i
      exact CubicPrefixTree.divisionPolynomial_eval _ _ _ _ _ _
    rw [heq]
    exact divisionMap_norm_le_semidefinite a ha hmono T h12 h23 hdom h

end Power
end CubicPrefixSingular
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
