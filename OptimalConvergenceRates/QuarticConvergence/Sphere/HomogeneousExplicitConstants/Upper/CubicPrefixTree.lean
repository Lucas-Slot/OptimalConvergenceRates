import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.CubicBlockInverse

/-! Actual bilinear-map and quadratic-polynomial external-prefix tree
construction. Every output is fixed by the input tensor and coordinate
tree; no pointwise completion choice is made. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace CubicPrefixTree
open scoped BigOperators InnerProductSpace
open MvPolynomial WeightedQuadraticSplit WeightedCubicSplit OrderedCubicExpansion
  OrthogonalDepthAggregation CubicBlockInverse

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

inductive IndexTree (ι : Type*)
  | leaf : ι→IndexTree ι
  | node : IndexTree ι→IndexTree ι→IndexTree ι

def support : IndexTree ι→Finset ι
  | .leaf i=>{i}
  | .node hi lo=>support hi∪support lo

def depth : IndexTree ι→ℕ
  | .leaf _=>0
  | .node hi lo=>max (depth hi) (depth lo)+1

/-- Only coordinate disjointness and spectral order are required.
There is no completion, norm bound or division conclusion in this data. -/
def Valid (a : ι → ℝ) : IndexTree ι→Finset ι→Prop
  | .leaf i,E=>0<a i ∧ i∉E ∧ ∀ j∈E,0≤a j ∧ a j≤a i
  | .node hi lo,E=>
      Disjoint (support hi) (support lo) ∧ Disjoint E (support hi∪support lo) ∧
      Valid a hi (support lo∪E) ∧ Valid a lo E ∧
      ∃ tau : ℝ,0<tau ∧ (∀ i∈support hi,tau≤a i) ∧
        ∀ j∈support lo∪E,0≤a j ∧ a j≤tau

abbrev Bilin := Point ι→ₗ[ℝ] Point ι→ₗ[ℝ] Point ι

def nodeMap (a : ι → ℝ) (T : Tri (Point ι)) (H U E : Finset ι) : Bilin (ι:=ι) :=
  LinearMap.mk₂ ℝ
    (fun x y↦(3:ℝ)•inverse a T H (U∪E) (projection U x)
      (projection U y+(2:ℝ)•projection E y))
    (by intro x y z;simp [map_add,add_smul];module)
    (by intro r x y;simp [map_smul,smul_smul,mul_comm];module)
    (by intro x y z;simp [map_add,smul_add];module)
    (by intro r x y;simp [map_smul,smul_add,smul_smul];module)

def lastMap (a : ι → ℝ) (T : Tri (Point ι)) : IndexTree ι→Finset ι→Bilin (ι:=ι)
  | .leaf _,_=>0
  | .node hi lo,E=>lastMap a T hi (support lo∪E)+lastMap a T lo E+
      nodeMap a T (support hi) (support lo) E

def leafMap (a : ι → ℝ) (T : Tri (Point ι)) (i : ι) (E : Finset ι) : Bilin (ι:=ι) :=
  LinearMap.mk₂ ℝ
    (fun x y↦((T (coordinateAxis i) (coordinateAxis i) (coordinateAxis i)*x i*y i+
      3*x i*T (coordinateAxis i) (coordinateAxis i) (projection E y))/a i)•coordinateAxis i)
    (by intro x y z;simp [add_mul,add_div,add_smul];module)
    (by intro r x y;simp [mul_add,mul_div_assoc,smul_smul];module)
    (by intro x y z;simp [map_add,mul_add,add_div,add_smul];module)
    (by intro r x y;simp [map_smul,mul_add,mul_div_assoc,smul_smul];module)

def leavesMap (a : ι → ℝ) (T : Tri (Point ι)) : IndexTree ι→Finset ι→Bilin (ι:=ι)
  | .leaf i,E=>leafMap a T i E
  | .node hi lo,E=>leavesMap a T hi (support lo∪E)+leavesMap a T lo E

def divisionMap (a : ι → ℝ) (T : Tri (Point ι)) (tr : IndexTree ι) (E : Finset ι) : Bilin (ι:=ι) :=
  leavesMap a T tr E+lastMap a T tr E

/-- An explicit actual quadratic polynomial for every component of any
finite-coordinate bilinear map. -/
def bilinearPolynomial (B : Bilin (ι := ι)) (i : ι) : MvPolynomial ι ℝ :=
  ∑ j,∑ k,C (B (coordinateAxis j) (coordinateAxis k) i)*X j*X k

theorem bilinearPolynomial_homogeneous (B : Bilin (ι := ι)) (i : ι) :
    (bilinearPolynomial B i).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro j _
  apply IsHomogeneous.sum
  intro k _
  exact ((isHomogeneous_X ℝ j).C_mul _).mul (isHomogeneous_X ℝ k)

theorem bilinearPolynomial_eval (B : Bilin (ι := ι)) (i : ι) (h : Point ι) :
    eval (fun j↦h j) (bilinearPolynomial B i)=B h h i := by
  have heq : B h h=∑ j,∑ k,(h j*h k)•B (coordinateAxis j) (coordinateAxis k) := by
    conv_lhs=>rw [←sum_coordinatePiece h]
    simp only [map_sum,LinearMap.sum_apply,coordinatePiece,map_smul,
      LinearMap.smul_apply,smul_smul,Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_comm]
  rw [heq]
  change eval (fun j↦h j) (bilinearPolynomial B i)=
    (EuclideanSpace.proj i) (∑ j,∑ k,(h j*h k)•B (coordinateAxis j) (coordinateAxis k))
  simp [bilinearPolynomial,map_sum,map_smul,mul_assoc,mul_comm,mul_left_comm]

def divisionPolynomial (a : ι → ℝ) (T : Tri (Point ι)) (tr : IndexTree ι) (E : Finset ι) (i : ι) :
    MvPolynomial ι ℝ := bilinearPolynomial (divisionMap a T tr E) i

theorem divisionPolynomial_homogeneous (a : ι → ℝ) (T : Tri (Point ι))
    (tr : IndexTree ι) (E : Finset ι) (i : ι) :
    (divisionPolynomial a T tr E i).IsHomogeneous 2 := bilinearPolynomial_homogeneous _ _

theorem divisionPolynomial_eval (a : ι → ℝ) (T : Tri (Point ι))
    (tr : IndexTree ι) (E : Finset ι) (i : ι) (h : Point ι) :
    eval (fun j↦h j) (divisionPolynomial a T tr E i)=divisionMap a T tr E h h i :=
  bilinearPolynomial_eval _ _ _

theorem project_union (s t : Finset ι) (hst : Disjoint s t) (h : Point ι) :
    project (s∪t) h=project s h+project t h := by
  ext i
  by_cases hs:i∈s
  · have ht:i∉t:=fun ht↦(Finset.disjoint_left.mp hst) hs ht
    simp [project_apply,hs,ht]
  · by_cases ht:i∈t <;> simp [project_apply,hs,ht]

omit [Fintype ι] in
theorem project_project_of_subset {s t : Finset ι} (hst : s ⊆ t) (h : Point ι) :
    project t (project s h)=project s h := by
  ext i
  by_cases hs:i∈s
  · simp [project_apply,hs,hst hs]
  · simp [project_apply,hs]

omit [Fintype ι] in
theorem project_singleton (i : ι) (h : Point ι) : project {i} h=coordinatePiece h i := by
  ext j
  by_cases hj:j=i
  · subst j;simp [project_apply,coordinatePiece,coordinateAxis,Pi.single_apply]
  · simp [project_apply,coordinatePiece,coordinateAxis,Pi.single_apply,hj]

omit [Fintype ι] in
theorem valid_pos (a : ι → ℝ) (tr : IndexTree ι) (E : Finset ι) (hv : Valid a tr E) :
    ∀ i∈support tr,0<a i := by
  induction tr generalizing E with
  | leaf j=>intro i hi;simpa only [support,Finset.mem_singleton.mp hi] using hv.1
  | node hi lo ihh ihl=>
    intro i hi
    rcases Finset.mem_union.mp hi with hh|hl
    · exact ihh _ hv.2.2.1 i hh
    · exact ihl _ hv.2.2.2.1 i hl

omit [Fintype ι] in
theorem valid_external_disjoint (a : ι → ℝ) (tr : IndexTree ι) (E : Finset ι)
    (hv : Valid a tr E) : Disjoint E (support tr) := by
  cases tr with
  | leaf i=>simpa only [support,Finset.disjoint_singleton_right] using hv.2.1
  | node hi lo=>exact hv.2.1

theorem nodeMap_pair (a : ι → ℝ) (T : Tri (Point ι)) (H U E : Finset ι)
    (ha : ∀ i ∈ H, a i ≠ 0) (h : Point ι) :
    ⟪diagonal a h,nodeMap a T H U E h h⟫_ℝ=
      3*T (project H h) (project U h) (project U h+(2:ℝ)•project E h) := by
  have hu:=project_project_of_subset (Finset.subset_union_left : U⊆U∪E) h
  have he:=project_project_of_subset (Finset.subset_union_right : E⊆U∪E) h
  have hsum : project (U∪E) (project U h+(2:ℝ)•project E h)=
      project U h+(2:ℝ)•project E h := by
    change projection (U∪E) (project U h+(2:ℝ)•project E h)=_
    rw [map_add,map_smul]
    exact congrArg₂ (fun x y↦x+(2:ℝ)•y) hu he
  change ⟪diagonal a h,(3:ℝ)•inverse a T H (U∪E)
    (project U h) (project U h+(2:ℝ)•project E h)⟫_ℝ=_
  rw [inner_smul_right,inverse_pair a T H (U∪E) ha,hu,hsum]

theorem leafMap_pair (a : ι → ℝ) (T : Tri (Point ι)) (i : ι) (E : Finset ι)
    (ha : a i ≠ 0) (h : Point ι) :
    ⟪diagonal a h,leafMap a T i E h h⟫_ℝ=
      assignedRemainder T (project {i} h) (project E h) := by
  have hi : ⟪diagonal a h,coordinateAxis i⟫_ℝ=a i*h i := by
    simp [coordinateAxis,PiLp.inner_apply,Pi.single_apply,diagonal_apply]
  rw [project_singleton]
  simp only [leafMap,LinearMap.mk₂_apply,projection_apply,inner_smul_right,hi,
    assignedRemainder,diagonalCubic,coordinatePiece,map_smul,LinearMap.smul_apply,smul_eq_mul]
  field_simp [ha]

/-- The constructed vector has the exact weighted pairing of the actual
prefix-tree cubic expansion. No norm or completion premise is used. -/
theorem divisionMap_pair (a : ι → ℝ) (T : Tri (Point ι))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (tr : IndexTree ι) (E : Finset ι) (hv : Valid a tr E) (h : Point ι) :
    ⟪diagonal a h,divisionMap a T tr E h h⟫_ℝ=
      assignedRemainder T (project (support tr) h) (project E h) := by
  have hm : ⟪diagonal a h,leavesMap a T tr E h h⟫_ℝ+
      ⟪diagonal a h,lastMap a T tr E h h⟫_ℝ=
      assignedRemainder T (project (support tr) h) (project E h) := by
    induction tr generalizing E with
    | leaf i=>
      simp only [leavesMap,lastMap,LinearMap.zero_apply,inner_zero_right,add_zero,support]
      exact leafMap_pair a T i E hv.1.ne' h
    | node hi lo ihh ihl=>
      have hhigh:=ihh _ hv.2.2.1
      have hlow:=ihl _ hv.2.2.2.1
      have hpos:=valid_pos a hi (support lo∪E) hv.2.2.1
      have hnode:=nodeMap_pair a T (support hi) (support lo) E (fun i hi↦(hpos i hi).ne') h
      have hloE:Disjoint (support lo) E:=by
        apply Finset.disjoint_left.mpr
        intro i hi he
        exact (Finset.disjoint_left.mp hv.2.1) he (Finset.mem_union_right _ hi)
      have hexp:=assignedRemainder_split T h12 h23 (project (support hi) h)
        (project (support lo) h) (project E h)
      rw [project_union (support lo) E hloE,add_comm (project (support lo) h)] at hhigh
      rw [←project_union (support hi) (support lo) hv.1] at hexp
      simp only [leavesMap,lastMap,LinearMap.add_apply,inner_add_right]
      dsimp only [support]
      linear_combination hhigh+hlow+hnode-hexp
  simpa only [divisionMap,LinearMap.add_apply,inner_add_right] using hm

/-- A full coordinate tree therefore gives the exact original cubic. -/
theorem full_divisionMap_pair (a : ι → ℝ) (T : Tri (Point ι))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (tr : IndexTree ι) (hv : Valid a tr ∅) (hs : support tr = Finset.univ) (h : Point ι) :
    ⟪diagonal a h,divisionMap a T tr ∅ h h⟫_ℝ=diagonalCubic T h := by
  have hh:=divisionMap_pair a T h12 h23 tr ∅ hv h
  have hu:project (Finset.univ:Finset ι) h=h:=project_eq_self (by simp)
  have he:project (∅:Finset ι) h=0:=by ext i;simp [project_apply]
  rw [hs,hu,he,assignedRemainder_zero] at hh
  exact hh

/-- The fixed constructed output is an exact identity of actual
polynomials with homogeneous quadratic roots. -/
theorem full_divisionPolynomial_identity (a : ι → ℝ) (T : Tri (Point ι))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (tr : IndexTree ι) (hv : Valid a tr ∅) (hs : support tr = Finset.univ) :
    (∑ i,C (a i)*X i*divisionPolynomial a T tr ∅ i)=cubicFromTri T := by
  apply MvPolynomial.funext
  intro x
  let h : Point ι := evaluationPoint x
  have hh:=full_divisionMap_pair a T h12 h23 tr hv hs h
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,diagonal_apply] at hh
  simp only [map_sum,map_mul,eval_C,eval_X,cubicFromTri_eval]
  change (∑ i,a i*h i*eval (fun j↦h j) (divisionPolynomial a T tr ∅ i))=diagonalCubic T h
  simp only [divisionPolynomial_eval]
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fintype ι] in
theorem project_small_large {s t : Finset ι} (hst : s ⊆ t) (h : Point ι) :
    project s (project t h)=project s h := by
  ext i
  by_cases hs:i∈s
  · simp [project_apply,hs,hst hs]
  · simp [project_apply,hs]

theorem project_mono_norm {s t : Finset ι} (hst : s ⊆ t) (h : Point ι) :
    ‖project s h‖≤‖project t h‖ := by
  have hh:=project_norm_le s (project t h)
  rwa [project_small_large hst] at hh

omit [Fintype ι] in
theorem project_supported (s : Finset ι) (h : Point ι) : ∀ i,i∉s→project s h i=0 := by
  intro i hi;simp [project_apply,hi]

theorem project_disjoint_inner (s t : Finset ι) (hst : Disjoint s t) (h : Point ι) :
    ⟪project s h,project t h⟫_ℝ=0 :=
  inner_zero_of_support hst _ _ (project_supported _ _) (project_supported _ _)

theorem project_disjoint_norm_sq (s t : Finset ι) (hst : Disjoint s t) (h : Point ι) :
    ‖project (s∪t) h‖^2=‖project s h‖^2+‖project t h‖^2 := by
  rw [project_union s t hst,norm_add_sq_real,project_disjoint_inner s t hst]
  ring

theorem nodeMap_support (a : ι → ℝ) (T : Tri (Point ι)) (H U E : Finset ι)
    (h : Point ι) (i : ι) (hi : i ∉ H) : nodeMap a T H U E h h i=0 := by
  change 3*(inverse a T H (U∪E) (project U h) (project U h+(2:ℝ)•project E h) i)=0
  rw [inverse_support a T H (U∪E) _ _ i hi,mul_zero]

theorem lastMap_support (a : ι → ℝ) (T : Tri (Point ι)) (tr : IndexTree ι) (E : Finset ι)
    (h : Point ι) : ∀ i,i∉support tr→lastMap a T tr E h h i=0 := by
  induction tr generalizing E with
  | leaf j=>simp [lastMap]
  | node hi lo ihh ihl=>
    intro i hni
    have hin:i∉support hi:=fun hh↦hni (Finset.mem_union_left _ hh)
    have hil:i∉support lo:=fun hh↦hni (Finset.mem_union_right _ hh)
    change lastMap a T hi (support lo∪E) h h i+lastMap a T lo E h h i+
      nodeMap a T (support hi) (support lo) E h h i=0
    rw [ihh _ i hin,ihl _ i hil,nodeMap_support a T _ _ E h i hin]
    ring

theorem leavesMap_support (a : ι → ℝ) (T : Tri (Point ι)) (tr : IndexTree ι) (E : Finset ι)
    (h : Point ι) : ∀ i,i∉support tr→leavesMap a T tr E h h i=0 := by
  induction tr generalizing E with
  | leaf j=>
    intro i hi
    have hij:i≠j:=by simpa only [support,Finset.mem_singleton] using hi
    simp [leavesMap,leafMap,coordinateAxis,Pi.single_apply,hij]
  | node hi lo ihh ihl=>
    intro i hni
    have hin:i∉support hi:=fun hh↦hni (Finset.mem_union_left _ hh)
    have hil:i∉support lo:=fun hh↦hni (Finset.mem_union_right _ hh)
    change leavesMap a T hi (support lo∪E) h h i+leavesMap a T lo E h h i=0
    rw [ihh _ i hin,ihl _ i hil]
    ring

/-- Actual source domination bounds the explicit node, with no node-count
factor and no assumed mixed estimate. -/
theorem nodeMap_norm_le (a : ι → ℝ) (T : Tri (Point ι)) (H U E : Finset ι)
    {tau : ℝ} (htau : 0 < tau) (haH : ∀ i ∈ H, tau ≤ a i)
    (haU : ∀ i ∈ U ∪ E, 0 ≤ a i ∧ a i ≤ tau)
    (hHU : Disjoint H (U ∪ E)) (hUE : Disjoint U E)
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2) (h : Point ι) :
    ‖nodeMap a T H U E h h‖≤24*‖project (H∪U∪E) h‖*‖project U h‖ := by
  have hn:=inverse_norm_le a T H (U∪E) htau haH haU hHU h12 h23 hdom
    (project U h) (project U h+(2:ℝ)•project E h)
  have hor:=project_disjoint_inner U E hUE h
  have hnorm : ‖project U h+(2:ℝ)•project E h‖^2=
      ‖project U h‖^2+4*‖project E h‖^2 := by
    rw [norm_add_sq_real]
    simp only [inner_smul_right,hor,mul_zero,add_zero,norm_smul]
    norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
    ring
  have hsub:U∪E⊆H∪U∪E:=by
    intro i hi
    rcases Finset.mem_union.mp hi with hU|hE
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hU)
    · exact Finset.mem_union_right _ hE
  have hgn:=project_mono_norm hsub h
  have hgsq:‖project U h‖^2+‖project E h‖^2≤‖project (H∪U∪E) h‖^2:=by
    rw [←project_disjoint_norm_sq U E hUE]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hgn
  have harg:‖project U h+(2:ℝ)•project E h‖≤2*‖project (H∪U∪E) h‖:=by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤2*‖project (H∪U∪E) h‖)).mp
    rw [hnorm]
    nlinarith [sq_nonneg ‖project U h‖]
  have hh : ‖nodeMap a T H U E h h‖=3*‖inverse a T H (U∪E)
      (project U h) (project U h+(2:ℝ)•project E h)‖ := by
    change ‖(3:ℝ)•inverse a T H (U∪E) (project U h) (project U h+(2:ℝ)•project E h)‖=_
    rw [norm_smul]
    norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<3)]
  rw [hh]
  nlinarith [mul_le_mul_of_nonneg_left harg (mul_nonneg (by norm_num : (0:ℝ)≤4) (norm_nonneg
    (project U h)))]

theorem coordinate_abs_le_project (h : Point ι) (i : ι) (s : Finset ι) (hi : i ∈ s) :
    |h i|≤‖project s h‖ := by
  have hh:=OrderedCubicLeafBounds.coordinate_abs_le_norm (project s h) i
  simpa only [project_apply,ite_eq_left hi] using hh

/-- The actual terminal polynomial vector costs14 times the product of
its local radius and its combined local/external radius. -/
theorem leafMap_norm_le (a : ι → ℝ) (T : Tri (Point ι)) (i : ι) (E : Finset ι)
    (hv : Valid a (.leaf i) E)
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2) (h : Point ι) :
    ‖leafMap a T i E h h‖≤14*‖project ({i}∪E) h‖*‖project {i} h‖ := by
  have hai:0<a i:=hv.1
  have hn:‖coordinateAxis i‖=1:=by simp [coordinateAxis,PiLp.norm_single]
  have hd:‖diagonal a (coordinateAxis i)‖=a i:=by
    simp [coordinateAxis,diagonal_single,PiLp.norm_single,abs_of_pos hai]
  have hdiag:=hdom (coordinateAxis i)
  simp only [diagonalCubic,hn,hd,one_pow,mul_one] at hdiag
  have hdc:|T (coordinateAxis i) (coordinateAxis i) (coordinateAxis i)/a i|≤2:=by
    rw [abs_div,abs_of_pos hai]
    exact (div_le_iff₀ hai).mpr (by linarith)
  have hlow:=supported_diagonal_norm_le a E hai.le hv.2.2 (project E h) (project_supported E h)
  have horth:⟪coordinateAxis i,project E h⟫_ℝ=0:=by
    simp [coordinateAxis,EuclideanSpace.inner_single_left,project_apply,hv.2.1]
  have hm:=(mixed_bounds T (diagonal a) h12 h23 hdom horth (by simpa [hn,hd] using hlow)).2
  rw [hn,hd,mul_one] at hm
  have hmc:|T (coordinateAxis i) (coordinateAxis i) (project E h)/a i|≤4*‖project E h‖:=by
    rw [abs_div,abs_of_pos hai]
    exact (div_le_iff₀ hai).mpr (by nlinarith)
  have hlocal:‖project {i} h‖=|h i|:=by
    rw [project_singleton]
    simp [coordinatePiece,norm_smul,Real.norm_eq_abs,hn]
  have hglob:=coordinate_abs_le_project h i ({i}∪E) (by simp)
  have hpre:=project_mono_norm (Finset.subset_union_right : E⊆{i}∪E) h
  have hid:
      (T (coordinateAxis i) (coordinateAxis i) (coordinateAxis i)*h i*h i+
        3*h i*T (coordinateAxis i) (coordinateAxis i) (project E h))/a i=
      (T (coordinateAxis i) (coordinateAxis i) (coordinateAxis i)/a i)*(h i)^2+
        3*h i*(T (coordinateAxis i) (coordinateAxis i) (project E h)/a i):=by
    field_simp [hai.ne']
  change ‖(_ : ℝ)•coordinateAxis i‖≤_
  rw [norm_smul,Real.norm_eq_abs,hn,mul_one,hlocal,projection_apply,hid]
  calc
    _ ≤ |T (coordinateAxis i) (coordinateAxis i) (coordinateAxis i)/a i| * |h i|^2+
        3* |h i| * |T (coordinateAxis i) (coordinateAxis i) (project E h)/a i|:=by
      have hh:=abs_add_le ((T (coordinateAxis i) (coordinateAxis i) (coordinateAxis i)/a i)*(h i)^2)
        (3*h i*(T (coordinateAxis i) (coordinateAxis i) (project E h)/a i))
      rw [abs_mul,abs_pow,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3)] at hh
      exact hh
    _ ≤ 2* |h i|^2+12* |h i| * ‖project E h‖:=by
      nlinarith [mul_le_mul_of_nonneg_right hdc (sq_nonneg |h i|),
        mul_le_mul_of_nonneg_left hmc (by positivity : 0≤3* |h i|)]
    _ ≤ 14*‖project ({i}∪E) h‖* |h i|:=by
      nlinarith [mul_le_mul_of_nonneg_right hglob (abs_nonneg (h i)),
        mul_le_mul_of_nonneg_right hpre (abs_nonneg (h i))]

/-- Pythagoras transports a common multiplicative norm bound through two
orthogonal children without adding their constants. -/
theorem orthogonal_norm_bound {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (x y u v : X) (hxy : ⟪x, y⟫_ℝ = 0) (huv : ⟪u, v⟫_ℝ = 0)
    {K : ℝ} (hK : 0 ≤ K) (hx : ‖x‖ ≤ K*‖u‖) (hy : ‖y‖ ≤ K*‖v‖) :
    ‖x+y‖≤K*‖u+v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mp
  rw [norm_add_sq_real,hxy,mul_zero,add_zero,mul_pow,norm_add_sq_real,huv,mul_zero,add_zero]
  have hx2:‖x‖^2≤K^2*‖u‖^2:=by simpa only [mul_pow] using
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mpr hx
  have hy2:‖y‖^2≤K^2*‖v‖^2:=by simpa only [mul_pow] using
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mpr hy
  nlinarith

/-- The leaf outputs have disjoint supports; their14 bound is preserved
through the complete actual tree rather than added over its leaves. -/
theorem leavesMap_norm_le (a : ι → ℝ) (T : Tri (Point ι))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2)
    (tr : IndexTree ι) (E : Finset ι) (hv : Valid a tr E) (h : Point ι) :
    ‖leavesMap a T tr E h h‖≤14*‖project (support tr∪E) h‖*‖project (support tr) h‖ := by
  induction tr generalizing E with
  | leaf i=>exact leafMap_norm_le a T i E hv h12 h23 hdom h
  | node hi lo ihh ihl=>
    have hh:=ihh _ hv.2.2.1
    rw [←Finset.union_assoc] at hh
    have hl:=ihl _ hv.2.2.2.1
    have hgn:=project_mono_norm
      (Finset.union_subset_union (Finset.subset_union_right : support lo⊆support hi∪support lo)
        (Finset.Subset.refl E)) h
    have hl':‖leavesMap a T lo E h h‖≤
        14*‖project ((support hi∪support lo)∪E) h‖*‖project (support lo) h‖:=by
      exact hl.trans (by gcongr)
    have ho:=inner_zero_of_support hv.1 _ _
      (leavesMap_support a T hi (support lo∪E) h) (leavesMap_support a T lo E h)
    have hin:=project_disjoint_inner (support hi) (support lo) hv.1 h
    have hb:=orthogonal_norm_bound _ _ _ _ ho hin
      (by positivity : 0≤14*‖project ((support hi∪support lo)∪E) h‖) hh hl'
    rw [←project_union (support hi) (support lo) hv.1] at hb
    exact hb

/-- The constructed last part costs24 per actual tree depth. At each
split the two child outputs combine by Pythagoras. -/
theorem lastMap_norm_le (a : ι → ℝ) (T : Tri (Point ι))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2)
    (tr : IndexTree ι) (E : Finset ι) (hv : Valid a tr E) (h : Point ι) :
    ‖lastMap a T tr E h h‖≤24*(depth tr:ℝ)*‖project (support tr∪E) h‖*‖project (support tr) h‖ := by
  induction tr generalizing E with
  | leaf i=>simp [lastMap,depth]
  | node hi lo ihh ihl=>
    let d:=max (depth hi) (depth lo)
    let G:=‖project ((support hi∪support lo)∪E) h‖
    let K:=24*(d:ℝ)*G
    have hdhi:(depth hi:ℝ)≤(d:ℝ):=by exact_mod_cast Nat.le_max_left (depth hi) (depth lo)
    have hdlo:(depth lo:ℝ)≤(d:ℝ):=by exact_mod_cast Nat.le_max_right (depth hi) (depth lo)
    have hh:=ihh _ hv.2.2.1
    rw [←Finset.union_assoc] at hh
    have hh':‖lastMap a T hi (support lo∪E) h h‖≤K*‖project (support hi) h‖:=by
      exact hh.trans (by dsimp [K,G];gcongr)
    have hl:=ihl _ hv.2.2.2.1
    have hgn:=project_mono_norm
      (Finset.union_subset_union (Finset.subset_union_right : support lo⊆support hi∪support lo)
        (Finset.Subset.refl E)) h
    have hl':‖lastMap a T lo E h h‖≤K*‖project (support lo) h‖:=by
      exact hl.trans (by dsimp [K,G];gcongr)
    have ho:=inner_zero_of_support hv.1 _ _
      (lastMap_support a T hi (support lo∪E) h) (lastMap_support a T lo E h)
    have hin:=project_disjoint_inner (support hi) (support lo) hv.1 h
    have hchild:=orthogonal_norm_bound _ _ _ _ ho hin (by dsimp [K,G];positivity) hh' hl'
    rw [←project_union (support hi) (support lo) hv.1] at hchild
    have hHU:Disjoint (support hi) (support lo∪E):=by
      apply Finset.disjoint_left.mpr
      intro i hi hU
      rcases Finset.mem_union.mp hU with hlo|he
      · exact (Finset.disjoint_left.mp hv.1) hi hlo
      · exact (Finset.disjoint_left.mp hv.2.1) he (Finset.mem_union_left _ hi)
    have hUE:Disjoint (support lo) E:=by
      apply Finset.disjoint_left.mpr
      intro i hi he
      exact (Finset.disjoint_left.mp hv.2.1) he (Finset.mem_union_right _ hi)
    obtain ⟨tau,htau,haH,haU⟩:=hv.2.2.2.2
    have hnode:=nodeMap_norm_le a T (support hi) (support lo) E htau haH haU hHU hUE h12 h23 hdom h
    have hlocal:=project_mono_norm (Finset.subset_union_right : support lo⊆support hi∪support lo) h
    have hnode':‖nodeMap a T (support hi) (support lo) E h h‖≤
        24*G*‖project (support hi∪support lo) h‖:=hnode.trans (by dsimp [G];gcongr)
    change ‖lastMap a T hi (support lo∪E) h h+lastMap a T lo E h h+
      nodeMap a T (support hi) (support lo) E h h‖≤_
    calc
      _ ≤ ‖lastMap a T hi (support lo∪E) h h+lastMap a T lo E h h‖+
          ‖nodeMap a T (support hi) (support lo) E h h‖:=norm_add_le _ _
      _ ≤ K*‖project (support hi∪support lo) h‖+24*G*‖project (support hi∪support lo)
        h‖:=add_le_add hchild hnode'
      _ = _:=by simp only [depth,support,Nat.cast_add,Nat.cast_one];dsimp [K,d,G];ring

theorem divisionMap_norm_le (a : ι → ℝ) (T : Tri (Point ι))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2)
    (tr : IndexTree ι) (E : Finset ι) (hv : Valid a tr E) (h : Point ι) :
    ‖divisionMap a T tr E h h‖≤(14+24*(depth tr:ℝ))*
      ‖project (support tr∪E) h‖*‖project (support tr) h‖ := by
  have hl:=leavesMap_norm_le a T h12 h23 hdom tr E hv h
  have hr:=lastMap_norm_le a T h12 h23 hdom tr E hv h
  change ‖leavesMap a T tr E h h+lastMap a T tr E h h‖≤_
  exact (norm_add_le _ _).trans (by nlinarith)

/-- Full actual quadratic-polynomial division for a valid coordinate
tree, with the norm cost14+24 times its depth. -/
theorem full_divisionPolynomial_norm_le (a : ι → ℝ) (T : Tri (Point ι))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2)
    (tr : IndexTree ι) (hv : Valid a tr ∅) (hs : support tr = Finset.univ) (h : Point ι) :
    ‖(WithLp.equiv 2 (ι→ℝ)).symm (fun i↦eval (fun j↦h j) (divisionPolynomial a T tr ∅ i))‖≤
      (14+24*(depth tr:ℝ))*‖h‖^2 := by
  have heq:(WithLp.equiv 2 (ι→ℝ)).symm (fun i↦eval (fun j↦h j) (divisionPolynomial a T tr ∅ i))=
      divisionMap a T tr ∅ h h:=by ext i;exact divisionPolynomial_eval _ _ _ _ _ _
  rw [heq]
  have hh:=divisionMap_norm_le a T h12 h23 hdom tr ∅ hv h
  have hu:project (Finset.univ:Finset ι) h=h:=project_eq_self (by simp)
  simpa only [hs,Finset.union_empty,hu,pow_two,mul_assoc] using hh

theorem full_divisionPolynomial_norm_le_eighty (a : ι → ℝ) (T : Tri (Point ι))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2)
    (tr : IndexTree ι) (hv : Valid a tr ∅) (hs : support tr = Finset.univ) (h : Point ι) :
    ‖(WithLp.equiv 2 (ι→ℝ)).symm (fun i↦eval (fun j↦h j) (divisionPolynomial a T tr ∅ i))‖≤
      80*((depth tr:ℝ)+1)*‖h‖^2 := by
  have hh:=full_divisionPolynomial_norm_le a T h12 h23 hdom tr hv hs h
  have hd:0≤(depth tr:ℝ):=by positivity
  exact hh.trans (by nlinarith [sq_nonneg ‖h‖])

/-- Actual homogeneous quadratic division constructed from a spectrally
ordered coordinate tree. No mixed-norm or completion premise is assumed. -/
theorem exists_quadratic_division (a : ι → ℝ) (T : Tri (Point ι))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2)
    (tr : IndexTree ι) (hv : Valid a tr ∅) (hs : support tr = Finset.univ) :
    ∃ b : ι→MvPolynomial ι ℝ,(∀ i,(b i).IsHomogeneous 2) ∧
      (∑ i,C (a i)*X i*b i)=cubicFromTri T ∧
      ∀ h : Point ι,‖(WithLp.equiv 2 (ι→ℝ)).symm (fun i↦eval (fun j↦h j) (b i))‖≤
        80*((depth tr:ℝ)+1)*‖h‖^2 := by
  exact ⟨divisionPolynomial a T tr ∅,divisionPolynomial_homogeneous a T tr ∅,
    full_divisionPolynomial_identity a T h12 h23 tr hv hs,
    full_divisionPolynomial_norm_le_eighty a T h12 h23 hdom tr hv hs⟩

end CubicPrefixTree
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
