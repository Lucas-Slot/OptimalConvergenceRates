import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.WeightedCubicSplit
import Mathlib.Data.Finset.Max

/-! Actual ordered cubic expansion and the external-prefix split.
These are polynomial identities; no norm bound or division oracle is assumed. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace OrderedCubicExpansion

open scoped BigOperators
open WeightedCubicSplit WeightedQuadraticSplit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def assignedRemainder (T : Tri E) (x w : E) : ℝ :=
  diagonalCubic T x + 3 * T x x w

def cubicIncrement (T : Tri E) (x w : E) : ℝ :=
  assignedRemainder T x w + 3 * T x w w

theorem assignedRemainder_zero (T : Tri E) (x : E) :
    assignedRemainder T x 0 = diagonalCubic T x := by
  simp [assignedRemainder]

theorem cubicIncrement_add (T : Tri E)
    (h12 : ∀ x y z, T x y z = T y x z)
    (h23 : ∀ x y z, T x y z = T x z y) (x w : E) :
    diagonalCubic T (w+x) = diagonalCubic T w + cubicIncrement T x w := by
  have h := cubic_split_identity T h12 h23 x w
  rw [add_comm w x]
  dsimp [cubicIncrement, assignedRemainder]
  linarith

/-- The high child inherits the lower child in its external prefix.
The leaf term excludes the pure external-square contribution. -/
theorem assignedRemainder_split (T : Tri E)
    (h12 : ∀ x y z, T x y z = T y x z)
    (h23 : ∀ x y z, T x y z = T x z y) (v u w : E) :
    assignedRemainder T (v+u) w =
      assignedRemainder T v (w+u) + assignedRemainder T u w +
        3 * T v u (u+(2:ℝ) • w) := by
  have h1 : T u v v = T v v u := by rw [h12 u v v, h23 v u v]
  have h2 : T u v u = T v u u := h12 u v u
  have h3 : T u u v = T v u u := by rw [h23 u u v, h2]
  simp only [assignedRemainder, diagonalCubic, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    h1, h2, h3, h23 v u v, h12 u v w]
  ring

def orderedPrefix {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (x : ι → E) (i : ι) : E :=
  ∑ j ∈ s.filter (fun j ↦ j < i), x j

/-- Telescoping by increasing indices gives the actual largest-index
assignment, including multiplicities three and six. -/
theorem ordered_sum_expansion {ι : Type*} [LinearOrder ι]
    (T : Tri E) (h12 : ∀ x y z, T x y z = T y x z)
    (h23 : ∀ x y z, T x y z = T x z y) (s : Finset ι) (x : ι → E) :
    diagonalCubic T (∑ i ∈ s, x i) =
      ∑ i ∈ s, cubicIncrement T (x i) (orderedPrefix s x i) := by
  induction s using Finset.induction_on_max with
  | empty => simp [diagonalCubic]
  | @insert a s hmax ih =>
    have ha : a ∉ s := by
      intro hs
      exact (lt_irrefl a) (hmax a hs)
    have hpa : orderedPrefix (insert a s) x a = ∑ j ∈ s, x j := by
      have hf : s.filter (fun j ↦ j < a) = s := Finset.filter_eq_self.mpr hmax
      simp [orderedPrefix, Finset.filter_insert, hf]
    have hpi (i : ι) (hi : i ∈ s) :
        orderedPrefix (insert a s) x i = orderedPrefix s x i := by
      have hn : ¬ a < i := not_lt.mpr (le_of_lt (hmax i hi))
      simp [orderedPrefix, Finset.filter_insert, hn]
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hpa]
    rw [add_comm (x a), cubicIncrement_add T h12 h23, ih]
    have hs : (∑ i ∈ s, cubicIncrement T (x i) (orderedPrefix (insert a s) x i)) =
        ∑ i ∈ s, cubicIncrement T (x i) (orderedPrefix s x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hpi i hi]
    rw [hs]
    ring

inductive CubicTree (E : Type*)
  | leaf : E → CubicTree E
  | node : CubicTree E → CubicTree E → CubicTree E

def treeSum : CubicTree E → E
  | .leaf x => x
  | .node hi lo => treeSum hi + treeSum lo

def treeLeafSum (T : Tri E) (w : E) : CubicTree E → ℝ
  | .leaf x => assignedRemainder T x w
  | .node hi lo => treeLeafSum T (w+treeSum lo) hi + treeLeafSum T w lo

def treeCrossSum (T : Tri E) (w : E) : CubicTree E → ℝ
  | .leaf _ => 0
  | .node hi lo => treeCrossSum T (w+treeSum lo) hi + treeCrossSum T w lo +
      3 * T (treeSum hi) (treeSum lo) (treeSum lo+(2:ℝ) • w)

/-- Exact coverage for every actual recursive high/low tree, with its
external prefixes. Balancing and spectral norm estimates are separate. -/
theorem tree_expansion (T : Tri E)
    (h12 : ∀ x y z, T x y z = T y x z)
    (h23 : ∀ x y z, T x y z = T x z y) (tr : CubicTree E) (w : E) :
    treeLeafSum T w tr + treeCrossSum T w tr = assignedRemainder T (treeSum tr) w := by
  induction tr generalizing w with
  | leaf x => simp [treeLeafSum, treeCrossSum, treeSum]
  | node hi lo ihH ihL =>
    simp only [treeLeafSum, treeCrossSum, treeSum]
    rw [assignedRemainder_split T h12 h23]
    linarith [ihH (w+treeSum lo), ihL w]

theorem tree_expansion_zero (T : Tri E)
    (h12 : ∀ x y z, T x y z = T y x z)
    (h23 : ∀ x y z, T x y z = T x z y) (tr : CubicTree E) :
    treeLeafSum T 0 tr + treeCrossSum T 0 tr = diagonalCubic T (treeSum tr) := by
  rw [tree_expansion T h12 h23, assignedRemainder_zero]

section Coordinates

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def coordinateAxis (i : ι) : Point ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm (Pi.single i 1)

def coordinatePiece (h : Point ι) (i : ι) : Point ι :=
  (h i) • coordinateAxis i

def coordinatePrefix (h : Point ι) (i : ι) : Point ι :=
  orderedPrefix Finset.univ (coordinatePiece h) i

theorem sum_coordinatePiece (h : Point ι) : ∑ i, coordinatePiece h i = h := by
  ext j
  change (EuclideanSpace.proj j).toLinearMap (∑ i, coordinatePiece h i) = h j
  rw [map_sum]
  simp [coordinatePiece, coordinateAxis, Pi.single_apply]

def coordinateNumerator (T : Tri (Point ι)) (h : Point ι) (i : ι) : ℝ :=
  T (coordinateAxis i) (coordinateAxis i) (coordinateAxis i) * (h i)^2 +
    3 * h i * T (coordinateAxis i) (coordinateAxis i) (coordinatePrefix h i) +
    3 * T (coordinateAxis i) (coordinatePrefix h i) (coordinatePrefix h i)

theorem coordinate_increment (T : Tri (Point ι)) (h : Point ι) (i : ι) :
    cubicIncrement T (coordinatePiece h i) (coordinatePrefix h i) =
      h i * coordinateNumerator T h i := by
  simp only [cubicIncrement, assignedRemainder, diagonalCubic, coordinatePiece,
    coordinateNumerator, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem coordinate_numerator_identity (T : Tri (Point ι))
    (h12 : ∀ x y z, T x y z = T y x z)
    (h23 : ∀ x y z, T x y z = T x z y) (h : Point ι) :
    (∑ i, h i * coordinateNumerator T h i) = diagonalCubic T h := by
  have he := ordered_sum_expansion T h12 h23 Finset.univ (coordinatePiece h)
  simp only [sum_coordinatePiece, coordinatePrefix, ← coordinate_increment] at he ⊢
  exact he.symm

def coordinateDivision (a : ι → ℝ) (T : Tri (Point ι)) (h : Point ι) (i : ι) : ℝ :=
  coordinateNumerator T h i / a i

theorem coordinate_division_identity (a : ι → ℝ) (T : Tri (Point ι))
    (h12 : ∀ x y z, T x y z = T y x z)
    (h23 : ∀ x y z, T x y z = T x z y) (h : Point ι)
    (hkernel : ∀ i, a i = 0 → coordinateNumerator T h i = 0) :
    (∑ i, a i * h i * coordinateDivision a T h i) = diagonalCubic T h := by
  rw [← coordinate_numerator_identity T h12 h23 h]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : a i = 0
  · simp [coordinateDivision, hi, hkernel i hi]
  · dsimp [coordinateDivision]
    field_simp

theorem coordinate_division_identity_of_nonzero (a : ι → ℝ) (T : Tri (Point ι))
    (h12 : ∀ x y z, T x y z = T y x z)
    (h23 : ∀ x y z, T x y z = T x z y) (h : Point ι) (ha : ∀ i, a i ≠ 0) :
    (∑ i, a i * h i * coordinateDivision a T h i) = diagonalCubic T h := by
  exact coordinate_division_identity a T h12 h23 h (fun i hi ↦ (ha i hi).elim)

theorem tri_apply_coordinates (T : Tri (Point ι)) (x y z : Point ι) :
    T x y z = ∑ i, ∑ j, ∑ k,
      T (coordinateAxis i) (coordinateAxis j) (coordinateAxis k) * x i * y j * z k := by
  calc
    T x y z = T (∑ i, coordinatePiece x i) (∑ j, coordinatePiece y j)
        (∑ k, coordinatePiece z k) := by rw [sum_coordinatePiece, sum_coordinatePiece,
          sum_coordinatePiece]
    _ = ∑ k, ∑ j, ∑ i,
        T (coordinateAxis i) (coordinateAxis j) (coordinateAxis k) * x i * y j * z k := by
      simp [coordinatePiece, map_sum, map_smul, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
        mul_comm, mul_left_comm, mul_assoc]
    _ = ∑ j, ∑ k, ∑ i,
        T (coordinateAxis i) (coordinateAxis j) (coordinateAxis k) * x i * y j * z k :=
      Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ k,
        T (coordinateAxis i) (coordinateAxis j) (coordinateAxis k) * x i * y j * z k := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

section Polynomials

open MvPolynomial

def prefixLinearPolynomial (T : Tri (Point ι)) (i : ι) : MvPolynomial ι ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j ↦ j < i),
    C (T (coordinateAxis i) (coordinateAxis i) (coordinateAxis j)) * X j

def prefixQuadraticPolynomial (T : Tri (Point ι)) (i : ι) : MvPolynomial ι ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j ↦ j < i),
    ∑ k ∈ Finset.univ.filter (fun k ↦ k < i),
      C (T (coordinateAxis i) (coordinateAxis j) (coordinateAxis k)) * X j * X k

/-- The actual degree-two numerator in equation (1.36). -/
def numeratorPolynomial (T : Tri (Point ι)) (i : ι) : MvPolynomial ι ℝ :=
  C (T (coordinateAxis i) (coordinateAxis i) (coordinateAxis i)) * (X i)^2 +
    C 3 * X i * prefixLinearPolynomial T i + C 3 * prefixQuadraticPolynomial T i

def divisionPolynomial (a : ι → ℝ) (T : Tri (Point ι)) (i : ι) : MvPolynomial ι ℝ :=
  C ((a i)⁻¹) * numeratorPolynomial T i

def cubicFromTri (T : Tri (Point ι)) : MvPolynomial ι ℝ :=
  cubicPolynomial (fun i j k ↦ T (coordinateAxis i) (coordinateAxis j) (coordinateAxis k))

def evaluationPoint (x : ι → ℝ) : Point ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm x

theorem prefixLinearPolynomial_eval (T : Tri (Point ι)) (i : ι) (x : ι → ℝ) :
    eval x (prefixLinearPolynomial T i) =
      T (coordinateAxis i) (coordinateAxis i) (coordinatePrefix (evaluationPoint x) i) := by
  simp [prefixLinearPolynomial, coordinatePrefix, orderedPrefix, coordinatePiece,
    evaluationPoint, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, mul_comm]

theorem prefixQuadraticPolynomial_eval (T : Tri (Point ι)) (i : ι) (x : ι → ℝ) :
    eval x (prefixQuadraticPolynomial T i) =
      T (coordinateAxis i) (coordinatePrefix (evaluationPoint x) i)
        (coordinatePrefix (evaluationPoint x) i) := by
  simp [prefixQuadraticPolynomial, coordinatePrefix, orderedPrefix, coordinatePiece,
    evaluationPoint, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem numeratorPolynomial_eval (T : Tri (Point ι)) (i : ι) (x : ι → ℝ) :
    eval x (numeratorPolynomial T i) = coordinateNumerator T (evaluationPoint x) i := by
  simp [numeratorPolynomial, prefixLinearPolynomial_eval, prefixQuadraticPolynomial_eval,
    coordinateNumerator, evaluationPoint]

theorem divisionPolynomial_eval (a : ι → ℝ) (T : Tri (Point ι)) (i : ι) (x : ι → ℝ) :
    eval x (divisionPolynomial a T i) = coordinateDivision a T (evaluationPoint x) i := by
  simp [divisionPolynomial, numeratorPolynomial_eval, coordinateDivision, div_eq_mul_inv, mul_comm]

theorem cubicFromTri_eval (T : Tri (Point ι)) (x : ι → ℝ) :
    eval x (cubicFromTri T) = diagonalCubic T (evaluationPoint x) := by
  rw [diagonalCubic, tri_apply_coordinates]
  simp [cubicFromTri, cubicPolynomial, evaluationPoint]

theorem prefixLinearPolynomial_homogeneous (T : Tri (Point ι)) (i : ι) :
    (prefixLinearPolynomial T i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact (MvPolynomial.isHomogeneous_X ℝ j).C_mul _

theorem prefixQuadraticPolynomial_homogeneous (T : Tri (Point ι)) (i : ι) :
    (prefixQuadraticPolynomial T i).IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  apply MvPolynomial.IsHomogeneous.sum
  intro k _
  exact ((MvPolynomial.isHomogeneous_X ℝ j).C_mul _).mul (MvPolynomial.isHomogeneous_X ℝ k)

theorem numeratorPolynomial_homogeneous (T : Tri (Point ι)) (i : ι) :
    (numeratorPolynomial T i).IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.add
  · apply MvPolynomial.IsHomogeneous.add
    · exact ((MvPolynomial.isHomogeneous_X ℝ i).pow 2).C_mul _
    · exact ((MvPolynomial.isHomogeneous_X ℝ i).C_mul _).mul
        (prefixLinearPolynomial_homogeneous T i)
  · exact (prefixQuadraticPolynomial_homogeneous T i).C_mul _

theorem divisionPolynomial_homogeneous (a : ι → ℝ) (T : Tri (Point ι)) (i : ι) :
    (divisionPolynomial a T i).IsHomogeneous 2 :=
  (numeratorPolynomial_homogeneous T i).C_mul _

theorem numeratorPolynomial_degree_le (T : Tri (Point ι)) (i : ι) :
    (numeratorPolynomial T i).totalDegree ≤ 2 :=
  (numeratorPolynomial_homogeneous T i).totalDegree_le

theorem divisionPolynomial_degree_le (a : ι → ℝ) (T : Tri (Point ι)) (i : ι) :
    (divisionPolynomial a T i).totalDegree ≤ 2 :=
  (divisionPolynomial_homogeneous a T i).totalDegree_le

theorem cubicFromTri_homogeneous (T : Tri (Point ι)) :
    (cubicFromTri T).IsHomogeneous 3 :=
  cubicPolynomial_homogeneous _

theorem numerator_polynomial_identity (T : Tri (Point ι))
    (h12 : ∀ x y z, T x y z = T y x z)
    (h23 : ∀ x y z, T x y z = T x z y) :
    (∑ i, X i * numeratorPolynomial T i) = cubicFromTri T := by
  apply MvPolynomial.funext
  intro x
  simp only [map_sum, map_mul, eval_X, numeratorPolynomial_eval, cubicFromTri_eval]
  exact coordinate_numerator_identity T h12 h23 (evaluationPoint x)

theorem division_polynomial_identity (a : ι → ℝ) (T : Tri (Point ι))
    (h12 : ∀ x y z, T x y z = T y x z)
    (h23 : ∀ x y z, T x y z = T x z y)
    (hkernel : ∀ i, a i = 0 → numeratorPolynomial T i = 0) :
    (∑ i, C (a i) * X i * divisionPolynomial a T i) = cubicFromTri T := by
  apply MvPolynomial.funext
  intro x
  simp only [map_sum, map_mul, eval_C, eval_X, divisionPolynomial_eval, cubicFromTri_eval]
  apply coordinate_division_identity a T h12 h23 (evaluationPoint x)
  intro i hi
  rw [← numeratorPolynomial_eval, hkernel i hi, map_zero]

theorem division_polynomial_identity_of_nonzero (a : ι → ℝ) (T : Tri (Point ι))
    (h12 : ∀ x y z, T x y z = T y x z)
    (h23 : ∀ x y z, T x y z = T x z y) (ha : ∀ i, a i ≠ 0) :
    (∑ i, C (a i) * X i * divisionPolynomial a T i) = cubicFromTri T :=
  division_polynomial_identity a T h12 h23 (fun i hi ↦ (ha i hi).elim)

end Polynomials

end Coordinates

end OrderedCubicExpansion
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
