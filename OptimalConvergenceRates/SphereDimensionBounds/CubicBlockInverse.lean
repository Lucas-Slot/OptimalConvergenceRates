import OptimalConvergenceRates.SphereDimensionBounds.OrderedCubicLeafBounds

/-! An actual inverse cubic vector on arbitrary disjoint coordinate blocks.
The source estimate is the original weighted cubic domination. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.CubicBlockInverse
open scoped BigOperators InnerProductSpace
open WeightedQuadraticSplit WeightedCubicSplit WeightedCubicBilinear
  OrderedCubicExpansion OrthogonalDepthAggregation

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def projection (s : Finset ι) : Point ι →ₗ[ℝ] Point ι where
  toFun := project s
  map_add' x y := by ext i;by_cases hi:i∈s <;> simp [project_apply,hi]
  map_smul' r x := by ext i;by_cases hi:i∈s <;> simp [project_apply,hi]

@[simp] theorem projection_apply (s : Finset ι) (x : Point ι) : projection s x=project s x := rfl

omit [Fintype ι] in
theorem project_eq_self {s : Finset ι} {x : Point ι} (hx : ∀ i, i ∉ s → x i = 0) : project s x=x := by
  ext i
  by_cases hi:i∈s
  · simp [project_apply,hi]
  · simp [project_apply,hi,hx i hi]

theorem project_norm_le (s : Finset ι) (x : Point ι) : ‖project s x‖≤‖x‖ := by
  have hh:=disjoint_project_norm_sq_sum_le (fun _:Unit=>s)
    (by intro i j hij;exact (hij (Subsingleton.elim _ _)).elim) x
  simp only [Fintype.sum_unique] at hh
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hh

theorem inner_zero_of_support {s t : Finset ι} (hst : Disjoint s t) (x y : Point ι)
    (hx : ∀ i, i ∉ s → x i = 0) (hy : ∀ i, i ∉ t → y i = 0) : ⟪x,y⟫_ℝ=0 := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi:i∈s
  · have hit : i∉t := fun hit=>(Finset.disjoint_left.mp hst) hi hit
    rw [hy i hit]
    simp
  · rw [hx i hi]
    simp

theorem supported_diagonal_norm_le (a : ι → ℝ) (s : Finset ι) {tau : ℝ} (htau : 0 ≤ tau)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ tau) (x : Point ι) (hx : ∀ i, i ∉ s → x i = 0) :
    ‖diagonal a x‖≤tau*‖x‖ := by
  let c : ι→ℝ := fun i=>if i∈s then a i else 0
  have hc0 : ∀ i,0≤c i := by
    intro i;dsimp [c];split_ifs with hi
    · exact (ha i hi).1
    · norm_num
  have hc : ∀ i,c i≤tau := by
    intro i;dsimp [c];split_ifs with hi
    · exact (ha i hi).2
    · exact htau
  have heq : diagonal a x=diagonal c x := by
    ext i
    by_cases hi:i∈s
    · simp [diagonal_apply,c,hi]
    · simp [diagonal_apply,c,hi,hx i hi]
  rw [heq]
  exact diagonal_norm_le htau hc0 hc x

theorem supported_le_diagonal_norm (a : ι → ℝ) (s : Finset ι) {tau : ℝ} (htau : 0 ≤ tau)
    (ha : ∀ i ∈ s, tau ≤ a i) (x : Point ι) (hx : ∀ i, i ∉ s → x i = 0) :
    tau*‖x‖≤‖diagonal a x‖ := by
  let c : ι→ℝ := fun i=>if i∈s then a i else tau
  have hc : ∀ i,tau≤c i := by
    intro i;dsimp [c];split_ifs with hi
    · exact ha i hi
    · rfl
  have heq : diagonal a x=diagonal c x := by
    ext i
    by_cases hi:i∈s
    · simp [diagonal_apply,c,hi]
    · simp [diagonal_apply,c,hi,hx i hi]
  rw [heq]
  exact le_diagonal_norm htau hc x

/-- Zero outside the actual high block, with both lower arguments
projected onto the actual lower-coordinate block. -/
def inverse (a : ι → ℝ) (T : Tri (Point ι)) (H U : Finset ι) :
    Point ι →ₗ[ℝ] Point ι →ₗ[ℝ] Point ι :=
  LinearMap.mk₂ ℝ
    (fun y z=>(WithLp.equiv 2 (ι→ℝ)).symm (fun i=>if i∈H then
      T (coordinateAxis i) (projection U y) (projection U z)/a i else 0))
    (by intro x y z;ext i;by_cases hi:i∈H <;> simp [hi,map_add,add_div])
    (by intro r x y;ext i;by_cases hi:i∈H <;> simp [hi,map_smul,mul_div_assoc])
    (by intro x y z;ext i;by_cases hi:i∈H <;> simp [hi,map_add,add_div])
    (by intro r x y;ext i;by_cases hi:i∈H <;> simp [hi,map_smul,mul_div_assoc])

@[simp] theorem inverse_apply (a : ι → ℝ) (T : Tri (Point ι)) (H U : Finset ι)
    (y z : Point ι) (i : ι) :
    inverse a T H U y z i=if i∈H then T (coordinateAxis i) (project U y) (project U z)/a i else 0 := rfl

theorem inverse_support (a : ι → ℝ) (T : Tri (Point ι)) (H U : Finset ι)
    (y z : Point ι) (i : ι) (hi : i ∉ H) : inverse a T H U y z i=0 := by
  simp [inverse_apply,hi]

theorem inverse_symm (a : ι → ℝ) (T : Tri (Point ι)) (H U : Finset ι)
    (h23 : ∀ x y z, T x y z = T x z y) (y z : Point ι) :
    inverse a T H U y z=inverse a T H U z y := by
  ext i
  simp only [inverse_apply,h23]

theorem first_slot_expansion (T : Tri (Point ι)) (x y z : Point ι) :
    T x y z=∑ i,x i*T (coordinateAxis i) y z := by
  conv_lhs => rw [←sum_coordinatePiece x]
  simp only [map_sum,LinearMap.sum_apply,coordinatePiece,map_smul,
    LinearMap.smul_apply,smul_eq_mul]

theorem inverse_pair (a : ι → ℝ) (T : Tri (Point ι)) (H U : Finset ι)
    (ha : ∀ i ∈ H, a i ≠ 0) (x y z : Point ι) :
    ⟪diagonal a x,inverse a T H U y z⟫_ℝ=T (project H x) (project U y) (project U z) := by
  rw [first_slot_expansion]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,diagonal_apply,inverse_apply,project_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi:i∈H
  · simp only [ite_eq_left hi]
    field_simp [ha i hi]
  · simp [hi]

/-- The actual inverse vector is bounded on arbitrary ordered blocks.
Only the original cubic inequality is assumed. -/
theorem inverse_norm_le (a : ι → ℝ) (T : Tri (Point ι)) (H U : Finset ι)
    {tau : ℝ} (htau : 0 < tau) (haH : ∀ i ∈ H, tau ≤ a i)
    (haU : ∀ i ∈ U, 0 ≤ a i ∧ a i ≤ tau) (hHU : Disjoint H U)
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2) (u w : Point ι) :
    ‖inverse a T H U u w‖≤4*‖u‖*‖w‖ := by
  apply bilinear_norm_le (inverse a T H U) (inverse_symm a T H U h23) (by norm_num : (0:ℝ)≤4)
  intro x
  let c := inverse a T H U x x
  let v := diagonal (fun i=>(a i)⁻¹) c
  let y := project U x
  have ha0 : ∀ i∈H,a i≠0 := fun i hi=>(htau.trans_le (haH i hi)).ne'
  have hc : ∀ i,i∉H→c i=0 := inverse_support a T H U x x
  have hv : ∀ i,i∉H→v i=0 := by
    intro i hi
    simp only [v,diagonal_apply,hc i hi,mul_zero]
  have hy : ∀ i,i∉U→y i=0 := by intro i hi;simp [y,project_apply,hi]
  have hLv : diagonal a v=c := by
    ext i
    by_cases hi:i∈H
    · simp only [v,diagonal_apply]
      field_simp [ha0 i hi]
    · simp only [diagonal_apply,hv i hi,hc i hi,mul_zero]
  have hpair : ‖c‖^2=T v y y := by
    have hp:=inverse_pair a T H U ha0 v x x
    rw [project_eq_self hv,hLv] at hp
    change ⟪c,c⟫_ℝ=T v y y at hp
    exact (real_inner_self_eq_norm_sq c).symm.trans hp
  have horth:=inner_zero_of_support hHU v y hv hy
  have hlow:=supported_diagonal_norm_le a U htau.le haU y hy
  have hhigh:=supported_le_diagonal_norm a H htau.le haH v hv
  have horder : ‖diagonal a y‖*‖v‖≤‖diagonal a v‖*‖y‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hlow (norm_nonneg v),
      mul_le_mul_of_nonneg_right hhigh (norm_nonneg y)]
  have hm:=(mixed_bounds T (diagonal a) h12 h23 hdom horth horder).1
  rw [hLv] at hm
  have hn : ‖c‖≤4*‖y‖^2 := by
    by_cases hc0:c=0
    · simp only [hc0,norm_zero];positivity
    have hcp:=norm_pos_iff.mpr hc0
    have hh : ‖c‖*‖c‖≤‖c‖*(4*‖y‖^2) := by
      nlinarith [le_abs_self (T v y y)]
    exact (mul_le_mul_iff_right₀ hcp).mp hh
  have hyx:‖y‖≤‖x‖:=project_norm_le U x
  exact hn.trans (by nlinarith [norm_nonneg y,norm_nonneg x])

end OptimalConvergenceRates.SphereDimensionBounds.CubicBlockInverse
