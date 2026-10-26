import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.SphereDimensionBounds.CubicQuadraticMatrix
import OptimalConvergenceRates.SphereDimensionBounds.LinearMatrixSmoothing
import OptimalConvergenceRates.SphereDimensionBounds.RadialNodeSOS

/-! Both actual homogeneous mixed-node matrix certificates, with all
completion, smoothing and singular inverse inputs derived from the
original scalar cubic source. -/
noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.MixedCubicSupplier
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
open MvPolynomial WeightedQuadraticSplit WeightedCubicSplit OrderedCubicExpansion
  OrthogonalDepthAggregation CubicBlockInverse HomogeneousMatrixBound FiniteMatrixVariance
abbrev Poly (n : ℕ):=MvPolynomial (Fin n) ℝ
local instance (priority := 2000) finOrderDecidableEq (n : ℕ):DecidableEq (Fin n):=
  (inferInstance : LinearOrder (Fin n)).toDecidableEq

def coordinateBlock {n : ℕ} (H : Finset (Fin n)) (i : Fin n):Poly n:=if i∈H then X i else 0

theorem coordinateBlock_homogeneous {n : ℕ} (H : Finset (Fin n)) (i : Fin n) :
    (coordinateBlock H i).IsHomogeneous 1:=by
  unfold coordinateBlock
  split_ifs
  · exact isHomogeneous_X ℝ i
  · exact isHomogeneous_zero _ _ _

/-- The actual homogeneous smoothing bound is exactly the rectangular
matrix expression used by the scalar square completion. -/
theorem radialBound_eq {n d e s : ℕ} (beta : ℝ) (w : Poly n)
    (M : Matrix (Fin d) (Fin e) (Poly n)) :
    radialBound s beta w M=(OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n)^(s+1)•
      ((C beta*(OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n)^(2*s-2)*w)•
        (1:Matrix (Fin d) (Fin d) (Poly n))-M*M.transpose):=by
  apply Matrix.ext
  intro i j
  simp [radialBound,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Matrix.sub_apply,
    Matrix.mul_apply,Matrix.transpose_apply]

/-- Actual high-high matrix supplier; neither a matrix completion nor a
mixed norm bound is supplied as a premise. -/
theorem exists_hhl_supplier {n s : ℕ} (hn : 2 ≤ n) (hs : n ≤ 2 * s)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (T : Tri (Point (Fin n))) (H U : Finset (Fin n))
    {tau : ℝ} (htau : 0 ≤ tau) (haH : ∀ i ∈ H, tau ≤ a i) (haU : ∀ i ∈ U, 0 ≤ a i ∧ a i ≤ tau)
    (hHU : Disjoint H U) (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖WeightedQuadraticSplit.diagonal a x‖ * ‖x‖ ^ 2) :
    ∃M:Matrix (Fin n) (Fin n) (Poly n),
      (∀i j,(M i j).IsHomogeneous (2*s-1)) ∧
      BoundedMatrixSOS (3*s) (radialBound s 2704 (blockWeight U) M) ∧
      (∑i,(C (a i)*coordinateBlock H i)*(∑j,M i j*coordinateBlock H j))=
        (OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n)^(s-1)*CubicQuadraticMatrix.mixedPolynomial T H U:=by
  obtain ⟨M,hm,hmat,hconstraint,hpair⟩:=MixedMatrixSupplier.exists_homogeneous_matrix_supplier
    (s:=s) hn hs (CubicQuadraticMatrix.maskedMatrix a H) (CubicQuadraticMatrix.maskedMatrix_psd a ha H)
    (CubicQuadraticMatrix.quadraticFamily T H U) (CubicQuadraticMatrix.quadraticFamily_symm T h12 H U)
    (D:=13) (by norm_num) (CubicQuadraticMatrix.quadraticFamily_domination a T H U htau haH haU hHU h12 h23 hdom) U
  refine ⟨M,hm,?_,?_⟩
  · norm_num at hmat
    exact hmat
  · have hv:=hpair (coordinateBlock H)
    have hD(i:Fin n):(∑j,C (CubicQuadraticMatrix.maskedMatrix a H i j)*coordinateBlock H j)=
        C (a i)*coordinateBlock H i:=by
      simp only [CubicQuadraticMatrix.maskedMatrix,Matrix.diagonal_apply]
      rw [Finset.sum_eq_single i]
      · by_cases hi:i∈H <;> simp [coordinateBlock,hi]
      · intro j _ hji
        simp [Ne.symm hji]
      · simp
    simp_rw [hD] at hv
    change _=(OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n)^(s-1)*FiniteMatrixVariance.quadraticForm
      (MatrixSmoothingConstraint.familyPolynomial ((CubicQuadraticMatrix.quadraticFamily T H U).comp (projection U)))
      (fun i=>if i∈H then X i else 0) at hv
    rw [CubicQuadraticMatrix.family_polynomial_pair] at hv
    exact hv

/-- Actual low-low matrix supplier: the same semidefinite inverse gives a
linear field, and the true sphere smoothing bound supplies its matrix SOS. -/
theorem exists_hll_supplier {n s : ℕ} (hn : 2 ≤ n) (hs : n ≤ 2 * s)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (T : Tri (Point (Fin n))) (H U : Finset (Fin n))
    {tau : ℝ} (htau : 0 ≤ tau) (haH : ∀ i ∈ H, tau ≤ a i) (haU : ∀ i ∈ U, 0 ≤ a i ∧ a i ≤ tau)
    (hHU : Disjoint H U) (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖WeightedQuadraticSplit.diagonal a x‖ * ‖x‖ ^ 2) :
    ∃M:Matrix (Fin n) (Fin n) (Poly n),
      (∀i j,(M i j).IsHomogeneous (2*s-1)) ∧
      BoundedMatrixSOS (3*s) (radialBound s 676 (blockWeight U) M) ∧
      (∑i,(C (a i)*coordinateBlock H i)*(∑j,M i j*coordinateBlock U j))=
        (OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n)^(s-1)*CubicLinearMatrix.mixedPolynomial T H U:=by
  let F:=CubicLinearMatrix.inverseFamily a T H U
  have hF:∀x,‖F x‖≤13*‖projection U x‖:=by
    intro x
    have hh:=CubicLinearMatrix.inverseFamily_norm a ha T H U htau haH haU hHU h12 h23 hdom x
    change ‖F x‖≤13*‖project U x‖
    exact hh.trans (by nlinarith [norm_nonneg (project U x)])
  let M:=LinearMatrixSmoothing.radialFamily (s:=s) F
  refine ⟨M,LinearMatrixSmoothing.radialFamily_homogeneous (by omega : 1≤s) F,?_,?_⟩
  · have hm:=LinearMatrixSmoothing.linear_matrix_smoothing_bound (s:=s) hn hs (by norm_num : (0:ℝ)≤13) U F hF
    norm_num at hm
    exact hm
  · have hp:=CubicLinearMatrix.inverseFamily_polynomial_pair a ha T H U htau haH haU hHU h12 h23 hdom
    have hmij(i j:Fin n):M i j=(OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n)^(s-1)*
        MatrixSmoothingConstraint.familyPolynomial (CubicLinearMatrix.inverseFamily a T H U) i j:=rfl
    simp_rw [hmij]
    rw [←hp]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [coordinateBlock]
    ring

end OptimalConvergenceRates.SphereDimensionBounds.MixedCubicSupplier
