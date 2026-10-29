import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.CubicBlockSemidefinite
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.MixedMatrixSupplier

/-! The actual linear matrix field for the lower-lower mixed cubic,
including singular spectra, constructed from the original cubic source. -/
noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace CubicLinearMatrix
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
open Matrix MvPolynomial WeightedQuadraticSplit WeightedCubicSplit OrderedCubicExpansion
  CubicBlockInverse CubicBlockSemidefinite MatrixSmoothingConstraint OrthogonalDepthAggregation
abbrev Poly (n : ℕ):=MvPolynomial (Fin n) ℝ
local instance (priority := 2000) finOrderDecidableEq (n : ℕ):DecidableEq (Fin n):=
  (inferInstance : LinearOrder (Fin n)).toDecidableEq

def inverseFamily {n : ℕ} (a : Fin n → ℝ) (T : Tri (Point (Fin n))) (H U : Finset (Fin n)) :
    Point (Fin n)→ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun u:=fun i j↦inverse a T H U u (coordinateAxis j) i
  map_add' u v:=by
    ext i j
    change inverse a T H U (u+v) (coordinateAxis j) i=_
    rw [map_add,LinearMap.add_apply]
    rfl
  map_smul' r u:=by
    ext i j
    change inverse a T H U (r•u) (coordinateAxis j) i=_
    rw [map_smul,LinearMap.smul_apply]
    rfl

theorem inverseFamily_apply {n : ℕ} (a : Fin n → ℝ) (T : Tri (Point (Fin n))) (H U : Finset (Fin n))
    (u x : Point (Fin n)) : Matrix.toEuclideanLin (inverseFamily a T H U u) x=inverse a T H U u
      x:=by
  conv_rhs=>rw [←sum_coordinatePiece x]
  simp only [map_sum,coordinatePiece,map_smul]
  ext i
  simp only [Matrix.toLpLin_apply,WithLp.equiv_symm_apply, PiLp.toLp_apply,WithLp.equiv_apply,
    Matrix.mulVec,dotProduct,inverseFamily,LinearMap.coe_mk,AddHom.coe_mk]
  change (∑j,inverse a T H U u (coordinateAxis j) i*x j)=
    (EuclideanSpace.proj i) (∑j,x j•inverse a T H U u (coordinateAxis j))
  simp only [map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  change inverse a T H U u (coordinateAxis j) i*x j=x j*inverse a T H U u (coordinateAxis j) i
  ring

theorem inverse_first_projection {n : ℕ} (a : Fin n → ℝ) (T : Tri (Point (Fin n))) (H U : Finset
  (Fin n))
    (u x : Point (Fin n)):inverse a T H U (project U u) x=inverse a T H U u x:=by
  have hproj:project U (project U u)=project U u:=project_eq_self (by
    intro i hi;simp [OrthogonalDepthAggregation.project_apply,hi])
  ext i
  simp only [inverse_apply,hproj]

/-- Operator norm of the actual finite matrix, with the original lower
block radius and the source-derived constant four. -/
theorem inverseFamily_norm {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (T : Tri (Point (Fin n)))
    (H U : Finset (Fin n)) {tau : ℝ} (htau : 0 ≤ tau)
    (haH : ∀ i ∈ H, tau ≤ a i) (haU : ∀ i ∈ U, 0 ≤ a i ∧ a i ≤ tau) (hHU : Disjoint H U)
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖WeightedQuadraticSplit.diagonal a x‖ * ‖x‖ ^ 2) (u :
      Point (Fin n)) :
    ‖inverseFamily a T H U u‖≤4*‖project U u‖:=by
  change ‖Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ) (inverseFamily a T H U u)‖≤_
  refine (Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ) (inverseFamily a T H U u)).opNorm_le_bound
    (show 0≤4*‖project U u‖ by positivity) ?_
  intro x
  change ‖Matrix.toEuclideanLin (inverseFamily a T H U u) x‖≤_
  rw [inverseFamily_apply,←inverse_first_projection a T H U u x]
  exact inverse_norm_le_semidefinite a ha T H U htau haH haU hHU h12 h23 hdom _ _

def projectedTri {n : ℕ} (T : Tri (Point (Fin n))) (H U V : Finset (Fin n)):Tri (Point (Fin n)):=
  LinearMap.mk₂ ℝ (fun x y↦(T (projection H x) (projection U y)).comp (projection V))
    (by intro x y z;ext w;simp [map_add])
    (by intro r x y;ext w;simp [map_smul])
    (by intro x y z;ext w;simp [map_add])
    (by intro r x y;ext w;simp [map_smul])

def mixedPolynomial {n : ℕ} (T : Tri (Point (Fin n))) (H U : Finset (Fin n)):Poly n:=
  cubicFromTri (projectedTri T H U U)

theorem mixedPolynomial_homogeneous {n : ℕ} (T : Tri (Point (Fin n))) (H U : Finset (Fin n)) :
    (mixedPolynomial T H U).IsHomogeneous 3:=cubicFromTri_homogeneous _

theorem mixedPolynomial_eval {n : ℕ} (T : Tri (Point (Fin n))) (H U : Finset (Fin n)) (x : Point
  (Fin n)) :
    eval (fun i↦x i) (mixedPolynomial T H U)=T (project H x) (project U x) (project U x):=by
  rw [mixedPolynomial,cubicFromTri_eval]
  rfl

theorem inverseFamily_pair {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (T : Tri (Point (Fin n)))
    (H U : Finset (Fin n)) {tau : ℝ} (htau : 0 ≤ tau)
    (haH : ∀ i ∈ H, tau ≤ a i) (haU : ∀ i ∈ U, 0 ≤ a i ∧ a i ≤ tau) (hHU : Disjoint H U)
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖WeightedQuadraticSplit.diagonal a x‖ * ‖x‖ ^ 2) (x :
      Point (Fin n)) :
    ⟪WeightedQuadraticSplit.diagonal a (project H x),Matrix.toEuclideanLin (inverseFamily a T H U
      x) (project U x)⟫_ℝ=
      T (project H x) (project U x) (project U x):=by
  rw [inverseFamily_apply,inverse_pair_semidefinite a ha T H U htau haH haU hHU h12 h23 hdom]
  have hH:project H (project H x)=project H x:=project_eq_self (by
    intro i hi;simp [OrthogonalDepthAggregation.project_apply,hi])
  have hU:project U (project U x)=project U x:=project_eq_self (by
    intro i hi;simp [OrthogonalDepthAggregation.project_apply,hi])
  rw [hH,hU]

/-- Literal weighted polynomial pairing for the actual lower-lower
linear matrix family, with no inverse compatibility assumption. -/
theorem inverseFamily_polynomial_pair {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (T : Tri (Point
  (Fin n)))
    (H U : Finset (Fin n)) {tau : ℝ} (htau : 0 ≤ tau)
    (haH : ∀ i ∈ H, tau ≤ a i) (haU : ∀ i ∈ U, 0 ≤ a i ∧ a i ≤ tau) (hHU : Disjoint H U)
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖WeightedQuadraticSplit.diagonal a x‖ * ‖x‖ ^ 2) :
    (∑i,(C (a i)*(if i∈H then X i else 0))*
      (∑j,familyPolynomial (inverseFamily a T H U) i j*(if j∈U then X j else 0)))=
      mixedPolynomial T H U:=by
  apply MvPolynomial.funext
  intro y
  let x:Point (Fin n):=evaluationPoint y
  have hp:=inverseFamily_pair a ha T H U htau haH haU hHU h12 h23 hdom x
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,WeightedQuadraticSplit.diagonal_apply,
    Matrix.toLpLin_apply,WithLp.equiv_symm_apply, PiLp.toLp_apply,WithLp.equiv_apply,
    Matrix.mulVec,dotProduct] at hp
  rw [show y=(fun i↦x i) from rfl,mixedPolynomial_eval]
  simp only [eval_sum,eval_mul,eval_C,apply_ite,eval_X,map_zero,familyPolynomial_eval]
  convert hp using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [WeightedQuadraticSplit.diagonal_apply,OrthogonalDepthAggregation.project_apply,
    mul_ite,ite_mul,mul_zero,zero_mul]
  ring

end CubicLinearMatrix
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
