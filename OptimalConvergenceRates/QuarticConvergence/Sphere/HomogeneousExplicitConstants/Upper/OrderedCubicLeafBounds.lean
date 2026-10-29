import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.OrderedCubicExpansion
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.OrthogonalDepthAggregation

/-! Actual diagonal and middle-part bounds for the largest-index cubic
vector. The estimates follow from the original cubic domination. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace OrderedCubicLeafBounds
open scoped BigOperators InnerProductSpace
open WeightedQuadraticSplit WeightedCubicSplit OrderedCubicExpansion OrthogonalDepthAggregation

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

@[simp] theorem coordinatePrefix_apply (h : Point ι) (i j : ι) :
    coordinatePrefix h i j=if j < i then h j else 0 := by
  change (EuclideanSpace.proj j).toLinearMap
    (∑ k ∈ Finset.univ.filter (fun k↦k < i),coordinatePiece h k)=_
  rw [map_sum]
  simp [coordinatePiece,coordinateAxis,PiLp.single_apply,Pi.single_apply,eq_comm]

theorem coordinatePrefix_eq_project (h : Point ι) (i : ι) :
    coordinatePrefix h i=project (Finset.univ.filter (fun j↦j < i)) h := by
  ext j
  simp [coordinatePrefix_apply,project_apply]

theorem coordinatePrefix_norm_le (h : Point ι) (i : ι) :
    ‖coordinatePrefix h i‖≤‖h‖ := by
  have hh := disjoint_project_norm_sq_sum_le
    (fun _ : Unit↦Finset.univ.filter (fun j↦j < i)) (by intro j k hjk;exact (hjk
      (Subsingleton.elim _ _)).elim) h
  simp only [Fintype.sum_unique] at hh
  rw [←coordinatePrefix_eq_project] at hh
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hh

theorem coordinatePrefix_diagonal_norm_le (a : ι → ℝ) (ha0 : ∀ i, 0 ≤ a i)
    (ha : Monotone a) (h : Point ι) (i : ι) :
    ‖diagonal a (coordinatePrefix h i)‖≤a i*‖coordinatePrefix h i‖ := by
  let c : ι→ℝ := fun j↦if j < i then a j else 0
  have hc0 : ∀ j,0≤c j := by
    intro j
    dsimp [c]
    split_ifs
    · exact ha0 j
    · norm_num
  have hc : ∀ j,c j≤a i := by
    intro j
    dsimp [c]
    split_ifs with hj
    · exact ha hj.le
    · exact ha0 i
  have heq : diagonal a (coordinatePrefix h i)=diagonal c (coordinatePrefix h i) := by
    ext j
    by_cases hj : j < i <;> simp [diagonal_apply,coordinatePrefix_apply,c,hj]
  rw [heq]
  exact diagonal_norm_le (ha0 i) hc0 hc _

/-- The first coefficient has the source bound2 even before summing any
coordinates. Strict positivity is used only to define its inverse. -/
theorem diagonal_coefficient_abs_le (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (T : Tri (Point ι))
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2) (i : ι) :
    |T (coordinateAxis i) (coordinateAxis i) (coordinateAxis i)/a i|≤2 := by
  have hh:=hdom (coordinateAxis i)
  have hn : ‖coordinateAxis i‖=1 := by simp [coordinateAxis,PiLp.norm_single]
  have hdn : ‖diagonal a (coordinateAxis i)‖=a i := by
    simp [coordinateAxis,diagonal_single,PiLp.norm_single,abs_of_pos (ha i)]
  simp only [diagonalCubic,hn,hdn,one_pow,mul_one] at hh
  rw [abs_div,abs_of_pos (ha i)]
  exact (div_le_iff₀ (ha i)).mpr (by linarith)

/-- The middle inverse coefficient is controlled by the actual lower
prefix norm, derived from the full original cubic and spectral order. -/
theorem middle_coefficient_abs_le (a : ι → ℝ) (ha0 : ∀ i, 0 < a i)
    (ha : Monotone a) (T : Tri (Point ι))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2)
    (h : Point ι) (i : ι) :
    |T (coordinateAxis i) (coordinateAxis i) (coordinatePrefix h i)/a i|≤
      4*‖coordinatePrefix h i‖ := by
  have hn : ‖coordinateAxis i‖=1 := by simp [coordinateAxis,PiLp.norm_single]
  have hdn : ‖diagonal a (coordinateAxis i)‖=a i := by
    simp [coordinateAxis,diagonal_single,PiLp.norm_single,abs_of_pos (ha0 i)]
  have ho : ⟪coordinateAxis i,coordinatePrefix h i⟫_ℝ=0 := by
    simp [coordinateAxis,EuclideanSpace.inner_single_left,coordinatePrefix_apply]
  have hord := coordinatePrefix_diagonal_norm_le a (fun i↦(ha0 i).le) ha h i
  have hm := (mixed_bounds T (diagonal a) h12 h23 hdom ho (by simpa [hn,hdn] using hord)).2
  rw [hn,hdn,mul_one] at hm
  rw [abs_div,abs_of_pos (ha0 i)]
  exact (div_le_iff₀ (ha0 i)).mpr (by nlinarith)

/-- Absolute coefficient bounds suffice for the Euclidean norm of an
actual signed diagonal operator. -/
theorem signed_diagonal_norm_le (c : ι → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hc : ∀ i, |c i| ≤ K) (h : Point ι) : ‖diagonal c h‖≤K*‖h‖ := by
  have heq : ‖diagonal c h‖=‖diagonal (fun i↦|c i|) h‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [norm_sq,diagonal_apply,mul_pow,sq_abs]
  rw [heq]
  exact diagonal_norm_le hK (fun _↦abs_nonneg _) hc h

omit [LinearOrder ι] in
theorem coordinate_abs_le_norm (h : Point ι) (i : ι) : |h i|≤‖h‖ := by
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [sq_abs,norm_sq]
  exact Finset.single_le_sum (fun j _↦sq_nonneg (h j)) (Finset.mem_univ i)

def diagonalPart (a : ι → ℝ) (T : Tri (Point ι)) (h : Point ι) : Point ι :=
  diagonal (fun i↦T (coordinateAxis i) (coordinateAxis i) (coordinateAxis i)/a i*h i) h

def middlePart (a : ι → ℝ) (T : Tri (Point ι)) (h : Point ι) : Point ι :=
  diagonal (fun i↦3*(T (coordinateAxis i) (coordinateAxis i) (coordinatePrefix h i)/a i)) h

/-- The actual diagonal part of the division vector costs at most2R. -/
theorem diagonalPart_norm_le (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (T : Tri (Point ι))
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2) (h : Point ι) :
    ‖diagonalPart a T h‖≤2*‖h‖^2 := by
  have hc (i : ι) :
      |T (coordinateAxis i) (coordinateAxis i) (coordinateAxis i)/a i*h i|≤2*‖h‖ := by
    rw [abs_mul]
    calc
      _ ≤ 2*|h i| := mul_le_mul_of_nonneg_right (diagonal_coefficient_abs_le a ha T hdom i)
        (abs_nonneg _)
      _ ≤ 2*‖h‖ := mul_le_mul_of_nonneg_left (coordinate_abs_le_norm h i) (by norm_num)
  have hh := signed_diagonal_norm_le _ (by positivity : 0≤2*‖h‖) hc h
  simpa only [diagonalPart,pow_two,mul_assoc] using hh

/-- The actual middle part costs12R, uniformly in the dimension and all
eigenvalues, deduced from the original cubic source. -/
theorem middlePart_norm_le (a : ι → ℝ) (ha0 : ∀ i, 0 < a i) (ha : Monotone a)
    (T : Tri (Point ι))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2) (h : Point ι) :
    ‖middlePart a T h‖≤12*‖h‖^2 := by
  have hc (i : ι) :
      |3*(T (coordinateAxis i) (coordinateAxis i) (coordinatePrefix h i)/a i)|≤12*‖h‖ := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3)]
    calc
      _ ≤ 3*(4*‖coordinatePrefix h i‖) := mul_le_mul_of_nonneg_left
        (middle_coefficient_abs_le a ha0 ha T h12 h23 hdom h i) (by norm_num)
      _ ≤ 12*‖h‖ := by nlinarith [coordinatePrefix_norm_le h i]
  have hh := signed_diagonal_norm_le _ (by positivity : 0≤12*‖h‖) hc h
  simpa only [middlePart,pow_two,mul_assoc] using hh

theorem leafParts_norm_le (a : ι → ℝ) (ha0 : ∀ i, 0 < a i) (ha : Monotone a)
    (T : Tri (Point ι))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2) (h : Point ι) :
    ‖diagonalPart a T h+middlePart a T h‖≤14*‖h‖^2 := by
  have hd:=diagonalPart_norm_le a ha0 T hdom h
  have hm:=middlePart_norm_le a ha0 ha T h12 h23 hdom h
  exact (norm_add_le _ _).trans (by linarith)

end OrderedCubicLeafBounds
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
