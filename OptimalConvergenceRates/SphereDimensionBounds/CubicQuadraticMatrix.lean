import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.SphereDimensionBounds.CubicLinearMatrix

/-! The actual symmetric linear matrix family for the high-high mixed
cubic, with domination derived from the original cubic source. -/
noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.CubicQuadraticMatrix

set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
open MvPolynomial WeightedQuadraticSplit WeightedCubicSplit OrderedCubicExpansion
  OrthogonalDepthAggregation CubicBlockInverse CubicLinearMatrix
open WeightedQuadraticExistence MatrixSmoothingConstraint
abbrev Poly (n : ℕ):=MvPolynomial (Fin n) ℝ
local instance (priority := 2000) finOrderDecidableEq (n : ℕ):DecidableEq (Fin n):=
  (inferInstance : LinearOrder (Fin n)).toDecidableEq

def maskedMatrix {n : ℕ} (a : Fin n → ℝ) (H : Finset (Fin n)):Matrix (Fin n) (Fin n) ℝ:=
  Matrix.diagonal (fun i=>if i∈H then a i else 0)

theorem maskedMatrix_psd {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (H : Finset (Fin n)) :
    (maskedMatrix a H).PosSemidef:=by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  split_ifs
  · exact ha i
  · exact le_rfl

theorem maskedMatrix_apply {n : ℕ} (a : Fin n → ℝ) (H : Finset (Fin n)) (x : Point (Fin n)) :
    Matrix.toEuclideanLin (maskedMatrix a H) x=WeightedQuadraticSplit.diagonal a (project H x):=by
  ext i
  simp [maskedMatrix,Matrix.toLpLin_apply,Matrix.mulVec,dotProduct,
    Matrix.diagonal_apply,WeightedQuadraticSplit.diagonal_apply,project_apply,mul_ite,ite_mul]

def quadraticFamily {n : ℕ} (T : Tri (Point (Fin n))) (H U : Finset (Fin n)) :
    Point (Fin n)→ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun u:=fun i j=>T (projection H (coordinateAxis i)) (projection H (coordinateAxis j)) (projection U u)
  map_add' u v:=by ext i j;simp [map_add]
  map_smul' r u:=by ext i j;simp [map_smul]

theorem quadraticFamily_symm {n : ℕ} (T : Tri (Point (Fin n)))
    (h12 : ∀ x y z, T x y z = T y x z) (H U : Finset (Fin n)) (u : Point (Fin n)) :
    (quadraticFamily T H U u).transpose=quadraticFamily T H U u:=by
  ext i j
  exact h12 _ _ _

theorem quadraticFamily_value {n : ℕ} (T : Tri (Point (Fin n))) (H U : Finset (Fin n))
    (u x : Point (Fin n)) :
    quadraticValue (quadraticFamily T H U u) x=T (project H x) (project H x) (project U u):=by
  have hx:project H x=∑i,x i•project H (coordinateAxis i):=by
    change projection H x=∑i,x i•projection H (coordinateAxis i)
    conv_lhs=>rw [←sum_coordinatePiece x]
    simp [coordinatePiece,map_sum,map_smul]
  rw [hx]
  simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,Finset.mul_sum]
  conv_rhs=>rw [Finset.sum_comm]
  change (∑i,∑j,T (projection H (coordinateAxis i)) (projection H (coordinateAxis j)) (projection U u)*x i*x j)=_
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change T (project H (coordinateAxis i)) (project H (coordinateAxis j)) (project U u)*x i*x j=
    x j*(x i*T (project H (coordinateAxis i)) (project H (coordinateAxis j)) (project U u))
  ring

/-- Both the domain orthogonality and image ordering follow from the
actual disjoint ordered coordinate blocks, even at a zero gap. -/
theorem quadraticFamily_domination {n : ℕ} (a : Fin n → ℝ) (T : Tri (Point (Fin n)))
    (H U : Finset (Fin n)) {tau : ℝ} (htau : 0 ≤ tau)
    (haH : ∀ i ∈ H, tau ≤ a i) (haU : ∀ i ∈ U, 0 ≤ a i ∧ a i ≤ tau) (hHU : Disjoint H U)
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖WeightedQuadraticSplit.diagonal a x‖ * ‖x‖ ^ 2)
    (u x : Point (Fin n)) :
    |quadraticValue (quadraticFamily T H U u) x|≤
      (13*‖u‖)*‖Matrix.toEuclideanLin (maskedMatrix a H) x‖*‖x‖:=by
  let v:=project H x
  let w:=project U u
  have hv:∀i,i∉H→v i=0:=by intro i hi;simp [v,project_apply,hi]
  have hw:∀i,i∉U→w i=0:=by intro i hi;simp [w,project_apply,hi]
  have horth:=inner_zero_of_support hHU v w hv hw
  have hlo:=supported_diagonal_norm_le a U htau haU w hw
  have hhi:=supported_le_diagonal_norm a H htau haH v hv
  have hord:‖WeightedQuadraticSplit.diagonal a w‖*‖v‖≤‖WeightedQuadraticSplit.diagonal a v‖*‖w‖:=by
    nlinarith [mul_le_mul_of_nonneg_right hlo (norm_nonneg v),
      mul_le_mul_of_nonneg_right hhi (norm_nonneg w)]
  have hm:=(mixed_bounds T (WeightedQuadraticSplit.diagonal a) h12 h23 hdom horth hord).2
  rw [quadraticFamily_value,maskedMatrix_apply]
  change |T v v w|≤(13*‖u‖)*‖WeightedQuadraticSplit.diagonal a v‖*‖x‖
  have hvx:‖v‖≤‖x‖:=project_norm_le H x
  have hwu:‖w‖≤‖u‖:=project_norm_le U u
  calc
    |T v v w|≤4*‖WeightedQuadraticSplit.diagonal a v‖*‖v‖*‖w‖:=hm
    _≤4*‖WeightedQuadraticSplit.diagonal a v‖*‖x‖*‖u‖:=by gcongr
    _≤(13*‖u‖)*‖WeightedQuadraticSplit.diagonal a v‖*‖x‖:=by
      have hn:0≤‖WeightedQuadraticSplit.diagonal a v‖*‖x‖*‖u‖:=by positivity
      nlinarith

def mixedPolynomial {n : ℕ} (T : Tri (Point (Fin n))) (H U : Finset (Fin n)):Poly n:=
  cubicFromTri (projectedTri T H H U)

theorem mixedPolynomial_homogeneous {n : ℕ} (T : Tri (Point (Fin n))) (H U : Finset (Fin n)) :
    (mixedPolynomial T H U).IsHomogeneous 3:=cubicFromTri_homogeneous _

theorem mixedPolynomial_eval {n : ℕ} (T : Tri (Point (Fin n))) (H U : Finset (Fin n)) (x : Point (Fin n)) :
    eval (fun i=>x i) (mixedPolynomial T H U)=T (project H x) (project H x) (project U x):=by
  rw [mixedPolynomial,cubicFromTri_eval]
  rfl

/-- The quadratic matrix family produces the actual high-high cubic
when contracted with the actual high-coordinate polynomials. -/
theorem family_polynomial_pair {n : ℕ} (T : Tri (Point (Fin n))) (H U : Finset (Fin n)) :
    FiniteMatrixVariance.quadraticForm
      (familyPolynomial ((quadraticFamily T H U).comp (projection U)))
      (fun i=>if i∈H then X i else 0)=mixedPolynomial T H U:=by
  apply MvPolynomial.funext
  intro y
  let x:Point (Fin n):=evaluationPoint y
  have hH:project H (project H x)=project H x:=project_eq_self (by intro i hi;simp [project_apply,hi])
  have hU:project U (project U x)=project U x:=project_eq_self (by intro i hi;simp [project_apply,hi])
  rw [show y=(fun i=>x i) from rfl,mixedPolynomial_eval]
  simp only [FiniteMatrixVariance.quadraticForm,eval_sum,eval_mul,familyPolynomial_eval,apply_ite,eval_X,map_zero]
  have hh:=quadraticFamily_value T H U (project U x) (project H x)
  rw [hH,hU] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [LinearMap.comp_apply,projection_apply,quadraticValue,project_apply,
    mul_ite,ite_mul,mul_zero,zero_mul]
  ring

end OptimalConvergenceRates.SphereDimensionBounds.CubicQuadraticMatrix
