import OptimalConvergenceRates.SphereDimensionBounds.CubicBlockInverse

/-! The same actual inverse cubic vector on nonnegative ordered blocks,
including zero high eigenvalues. No boundary completion is chosen. -/
noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.CubicBlockSemidefinite
open scoped BigOperators InnerProductSpace
open WeightedQuadraticSplit WeightedCubicSplit OrderedCubicExpansion
  OrthogonalDepthAggregation CubicBlockInverse
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem inverse_positive_filter (a : ι→ℝ) (ha : ∀ i, 0 ≤ a i) (T : Tri (Point ι)) (H U : Finset ι)
    (y z : Point ι) :inverse a T H U y z=inverse a T (H.filter (fun i=>0<a i)) U y z:=by
  ext i
  simp only [inverse_apply,Finset.mem_filter]
  by_cases hi:i∈H
  · by_cases hp:0<a i
    · simp [hi,hp]
    · have hzero:a i=0:=le_antisymm (le_of_not_gt hp) (ha i)
      simp [hi,hp,hzero]
  · simp [hi]

/-- The positive subblock has the old strict-gap bound. Zero high
coordinates are identically zero in the SAME inverse formula. -/
theorem inverse_norm_le_semidefinite (a : ι→ℝ) (ha : ∀ i, 0 ≤ a i) (T : Tri (Point ι)) (H U : Finset ι)
    {tau : ℝ} (htau : 0 ≤ tau) (haH : ∀ i ∈ H, tau ≤ a i) (haU : ∀ i ∈ U, 0 ≤ a i ∧ a i ≤ tau)
    (hHU : Disjoint H U) (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2) (u w : Point ι) :
    ‖inverse a T H U u w‖≤4*‖u‖*‖w‖:=by
  by_cases hp:0<tau
  · exact inverse_norm_le a T H U hp haH haU hHU h12 h23 hdom u w
  have ht:tau=0:=le_antisymm (le_of_not_gt hp) htau
  let K:=H.filter (fun i=>0<a i)
  rw [inverse_positive_filter a ha T H U]
  change ‖inverse a T K U u w‖≤4*‖u‖*‖w‖
  by_cases hk:K.Nonempty
  · obtain ⟨i,hi,hmin⟩:=Finset.exists_min_image K a hk
    have hi0:0<a i:=(Finset.mem_filter.mp hi).2
    have hKU:Disjoint K U:=Finset.disjoint_left.mpr (by
      intro j hj hu;exact (Finset.disjoint_left.mp hHU) (Finset.mem_filter.mp hj).1 hu)
    apply inverse_norm_le a T K U hi0 (fun j hj=>hmin j hj) _ hKU h12 h23 hdom u w
    intro j hj
    have hz:a j=0:=le_antisymm (by simpa only [ht] using (haU j hj).2) (ha j)
    exact ⟨ha j,by rw [hz];exact hi0.le⟩
  · have he:K=∅:=Finset.not_nonempty_iff_eq_empty.mp hk
    have hv:inverse a T K U u w=0:=by ext i;simp [inverse_apply,he]
    rw [hv,norm_zero]
    positivity

/-- The source forces every numerator at a zero high weight to vanish,
including genuinely bilinear lower arguments. -/
theorem zero_high_numerator (a : ι→ℝ) (ha : ∀ i, 0 ≤ a i) (T : Tri (Point ι)) (H U : Finset ι)
    {tau : ℝ} (htau : 0 ≤ tau) (haH : ∀ i ∈ H, tau ≤ a i) (haU : ∀ i ∈ U, 0 ≤ a i ∧ a i ≤ tau)
    (hHU : Disjoint H U) (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2)
    (i : ι) (hi : i ∈ H) (hi0 : a i = 0) (y z : Point ι) :
    T (coordinateAxis i) (project U y) (project U z)=0:=by
  have ht:tau=0:=le_antisymm (by simpa only [hi0] using haH i hi) htau
  have hU:∀j∈U,a j=0:=fun j hj=>le_antisymm (by simpa only [ht] using (haU j hj).2) (ha j)
  have hLv:diagonal a (coordinateAxis i)=0:=by
    ext j
    by_cases hj:j=i
    · subst j;simp [diagonal_apply,coordinateAxis,hi0]
    · simp [diagonal_apply,coordinateAxis,Pi.single_apply,hj]
  have hdiag:∀u:Point ι,T (coordinateAxis i) (project U u) (project U u)=0:=by
    intro u
    have hv:∀j,j∉H→coordinateAxis i j=0:=by
      intro j hj
      have hji:j≠i:=by intro h;subst j;exact hj hi
      simp [coordinateAxis,Pi.single_apply,hji]
    have hu:∀j,j∉U→project U u j=0:=by intro j hj;simp [project_apply,hj]
    have horth:=inner_zero_of_support hHU (coordinateAxis i) (project U u) hv hu
    have hLu:diagonal a (project U u)=0:=by
      ext j
      by_cases hj:j∈U
      · simp [diagonal_apply,project_apply,hj,hU j hj]
      · simp [diagonal_apply,project_apply,hj]
    have hh:=(mixed_bounds T (diagonal a) h12 h23 hdom horth
      (by rw [hLu,hLv];simp)).1
    have hzero:|T (coordinateAxis i) (project U u) (project U u)|≤0:=by
      simpa only [hLv,norm_zero,mul_zero,zero_mul] using hh
    exact abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))
  have hh:=hdiag (y+z)
  change T (coordinateAxis i) (projection U (y+z)) (projection U (y+z))=0 at hh
  simp only [map_add,LinearMap.add_apply] at hh
  have hy:=hdiag y
  have hz:=hdiag z
  have hs:=h23 (coordinateAxis i) (project U z) (project U y)
  change T (coordinateAxis i) (projection U y) (projection U y)=0 at hy
  change T (coordinateAxis i) (projection U z) (projection U z)=0 at hz
  change T (coordinateAxis i) (projection U z) (projection U y)=
    T (coordinateAxis i) (projection U y) (projection U z) at hs
  change T (coordinateAxis i) (projection U y) (projection U z)=0
  linarith

/-- Exact weighted pairing survives every zero eigenvalue on the same
explicit finite bilinear map. -/
theorem inverse_pair_semidefinite (a : ι→ℝ) (ha : ∀ i, 0 ≤ a i) (T : Tri (Point ι)) (H U : Finset ι)
    {tau : ℝ} (htau : 0 ≤ tau) (haH : ∀ i ∈ H, tau ≤ a i) (haU : ∀ i ∈ U, 0 ≤ a i ∧ a i ≤ tau)
    (hHU : Disjoint H U) (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2) (x y z : Point ι) :
    ⟪diagonal a x,inverse a T H U y z⟫_ℝ=T (project H x) (project U y) (project U z):=by
  rw [first_slot_expansion]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,diagonal_apply,inverse_apply,project_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi:i∈H
  · simp only [ite_eq_left hi]
    by_cases hi0:a i=0
    · have hh:=zero_high_numerator a ha T H U htau haH haU hHU h12 h23 hdom i hi hi0 y z
      rw [hh]
      simp
    · field_simp [hi0]
  · simp [hi]

end OptimalConvergenceRates.SphereDimensionBounds.CubicBlockSemidefinite
