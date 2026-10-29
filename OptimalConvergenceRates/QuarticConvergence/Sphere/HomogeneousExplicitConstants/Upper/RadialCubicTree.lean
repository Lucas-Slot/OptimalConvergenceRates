import Mathlib.Algebra.MvPolynomial.Funext
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.CubicQuadraticMatrix
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.OrderedBalancedTree

/-! Exact original-coordinate cubic expansion across the actual ordered
balanced tree, with semidefinite source-derived leaf coefficients. -/
noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace RadialCubicTree
open scoped BigOperators InnerProductSpace
open MvPolynomial WeightedQuadraticSplit WeightedCubicSplit OrderedCubicExpansion
  OrthogonalDepthAggregation CubicBlockInverse CubicPrefixTree RadialTreeSOS RadialAssemblySOS
abbrev Poly (n : ℕ):=MvPolynomial (Fin n) ℝ
local instance (priority := 2000) finOrderDecidableEq (n : ℕ):DecidableEq (Fin n):=
  (inferInstance : LinearOrder (Fin n)).toDecidableEq

def blockCubic {n : ℕ} (T : Tri (Point (Fin n))) (H : Finset (Fin n)):Poly n:=
  cubicFromTri (CubicLinearMatrix.projectedTri T H H H)

def crossCubic {n : ℕ} (T : Tri (Point (Fin n))) (H U : Finset (Fin n)):Poly n:=
  3*CubicQuadraticMatrix.mixedPolynomial T H U+3*CubicLinearMatrix.mixedPolynomial T H U

theorem blockCubic_eval {n : ℕ} (T : Tri (Point (Fin n))) (H : Finset (Fin n)) (x : Point (Fin n)) :
    eval (fun i↦x i) (blockCubic T H)=diagonalCubic T (project H x):=by
  rw [blockCubic,cubicFromTri_eval]
  rfl

theorem blockCubic_union {n : ℕ} (T : Tri (Point (Fin n)))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (H U : Finset (Fin n)) (hHU : Disjoint H U) :
    blockCubic T (H∪U)=blockCubic T H+blockCubic T U+crossCubic T H U:=by
  apply MvPolynomial.funext
  intro y
  let x:Point (Fin n):=evaluationPoint y
  rw [show y=(fun i↦x i) from rfl]
  simp only [eval_add,blockCubic_eval,crossCubic,eval_mul,eval_ofNat,
    CubicQuadraticMatrix.mixedPolynomial_eval,CubicLinearMatrix.mixedPolynomial_eval]
  rw [CubicPrefixTree.project_union H U hHU x,cubic_split_identity T h12 h23]
  ring

theorem blockCubic_singleton {n : ℕ} (T : Tri (Point (Fin n))) (i : Fin n) :
    blockCubic T {i}=C (T (coordinateAxis i) (coordinateAxis i) (coordinateAxis i))*X i^3:=by
  apply MvPolynomial.funext
  intro y
  let x:Point (Fin n):=evaluationPoint y
  rw [show y=(fun i↦x i) from rfl]
  simp only [blockCubic_eval,eval_mul,eval_C,eval_pow,eval_X,diagonalCubic,
    CubicPrefixTree.project_singleton,coordinatePiece,map_smul,LinearMap.smul_apply,smul_eq_mul]
  ring

theorem blockCubic_univ {n : ℕ} (T : Tri (Point (Fin n))):blockCubic T Finset.univ=cubicFromTri
  T:=by
  apply MvPolynomial.funext
  intro y
  let x:Point (Fin n):=evaluationPoint y
  rw [show y=(fun i↦x i) from rfl,blockCubic_eval,cubicFromTri_eval]
  have hp:project (Finset.univ:Finset (Fin n)) x=x:=project_eq_self (by simp)
  rw [hp]
  congr 1

/-- Every cubic term, including repeated-index monomials, is retained
by the exact binary split identity. -/
theorem tree_cubic_identity {n : ℕ} (T : Tri (Point (Fin n)))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (tr : IndexTree (Fin n)) (hp : Proper tr) :
    blockCubic T (CubicPrefixTree.support tr)=nodeSum (crossCubic T) tr+
      ∑i∈CubicPrefixTree.support tr,C (T (coordinateAxis i) (coordinateAxis i) (coordinateAxis
        i))*X i^3:=by
  induction tr with
  | leaf i=>simpa only [CubicPrefixTree.support,nodeSum,Finset.sum_singleton,zero_add] using
    blockCubic_singleton T i
  | node hi lo ihh ihl=>
    simp only [CubicPrefixTree.support,nodeSum]
    rw [blockCubic_union T h12 h23 _ _ hp.1,Finset.sum_union hp.1,ihh hp.2.1,ihl hp.2.2]
    ring

theorem full_tree_cubic_identity {n : ℕ} (T : Tri (Point (Fin n)))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (tr : IndexTree (Fin n)) (hp : Proper tr) (hfull : CubicPrefixTree.support tr = Finset.univ) :
    nodeSum (crossCubic T) tr+
      ∑i,C (T (coordinateAxis i) (coordinateAxis i) (coordinateAxis i))*X i^3=cubicFromTri T:=by
  have hh:=tree_cubic_identity T h12 h23 tr hp
  rw [hfull,blockCubic_univ] at hh
  exact hh.symm

def gamma {n : ℕ} (a : Fin n → ℝ) (T : Tri (Point (Fin n))) (i : Fin n):ℝ:=
  T (coordinateAxis i) (coordinateAxis i) (coordinateAxis i)/a i

theorem diagonal_bound {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (T : Tri (Point (Fin n)))
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖WeightedQuadraticSplit.diagonal a x‖ * ‖x‖ ^ 2) (i : Fin
      n) :
    |T (coordinateAxis i) (coordinateAxis i) (coordinateAxis i)|≤2*a i:=by
  have hh:=hdom (coordinateAxis i)
  have hn:‖coordinateAxis i‖=1:=by simp [coordinateAxis,PiLp.norm_single]
  have hdn:‖WeightedQuadraticSplit.diagonal a (coordinateAxis i)‖=a i:=by
    simp [coordinateAxis,diagonal_single,PiLp.norm_single,abs_of_nonneg (ha i)]
  simpa only [diagonalCubic,hn,hdn,one_pow,mul_one] using hh

theorem gamma_bound {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (T : Tri (Point (Fin n)))
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖WeightedQuadraticSplit.diagonal a x‖ * ‖x‖ ^ 2) (i : Fin
      n) :
    |gamma a T i|≤2:=by
  by_cases hi:a i=0
  · simp [gamma,hi]
  · have hp:0<a i:=lt_of_le_of_ne (ha i) (Ne.symm hi)
    rw [gamma,abs_div,abs_of_pos hp]
    exact (div_le_iff₀ hp).mpr (diagonal_bound a ha T hdom i)

theorem mul_gamma {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (T : Tri (Point (Fin n)))
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖WeightedQuadraticSplit.diagonal a x‖ * ‖x‖ ^ 2) (i : Fin
      n) :
    a i*gamma a T i=T (coordinateAxis i) (coordinateAxis i) (coordinateAxis i):=by
  by_cases hi:a i=0
  · have hb:=diagonal_bound a ha T hdom i
    rw [hi,mul_zero] at hb
    have hz:=abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
    simp [hi,hz]
  · unfold gamma
    field_simp [hi]

end RadialCubicTree
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
