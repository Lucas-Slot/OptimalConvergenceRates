import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.MixedCubicSupplier

/-! A true scalar spectral-node SOS from the original cubic source,
with smoothing on the ORIGINAL transverse sphere dimension. -/
noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace RadialSpectralNode

set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators InnerProductSpace
open MvPolynomial ChebyshevSOSKernel WeightedQuadraticSplit WeightedCubicSplit
  OrderedCubicExpansion OrthogonalDepthAggregation CubicBlockInverse
  HomogeneousMatrixBound FiniteMatrixVariance MixedCubicSupplier
abbrev Poly (n : ℕ):=MvPolynomial (Fin n) ℝ

def lift {n : ℕ}:Poly n→+*Poly (n+1):=(rename Fin.succ).toRingHom

def radiusBlock {n : ℕ} (H : Finset (Fin n)):Poly n:=∑i∈H,X i^2

def energyBlock {n : ℕ} (a : Fin n → ℝ) (H : Finset (Fin n)):Poly n:=∑i∈H,C (a i)^2*X i^2

theorem sum_block_ite {n : ℕ} (H : Finset (Fin n)) (f : Fin n → Poly n) :
    (∑i,if i∈H then f i else 0)=∑i∈H,f i:=by
  calc
    (∑i,if i∈H then f i else 0)=∑i∈H,if i∈H then f i else 0:=
      (Finset.sum_subset (Finset.subset_univ H) (by intro i _ hi;simp [hi])).symm
    _=_:=by apply Finset.sum_congr rfl;intro i hi;simp [hi]

theorem coordinateBlock_squares {n : ℕ} (H : Finset (Fin n)) :
    (∑i,coordinateBlock H i^2)=radiusBlock H:=by
  simp only [coordinateBlock,ite_pow,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,ite_false]
  exact sum_block_ite H _

theorem weightedBlock_squares {n : ℕ} (a : Fin n → ℝ) (H : Finset (Fin n)) :
    (∑i,(C (a i)*coordinateBlock H i)^2)=energyBlock a H:=by
  simp only [coordinateBlock,mul_pow,ite_pow,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,
    ite_false,mul_ite,mul_zero]
  exact sum_block_ite H _

theorem blockWeight_eq {n : ℕ} (U : Finset (Fin n)) :
    blockWeight U=radiusBlock U+C (rho U)*Foundation.radiusPolynomial n:=by
  unfold blockWeight weightedSquares
  simp only [map_add,apply_ite,map_one,map_zero,add_mul,one_mul,zero_mul,Finset.sum_add_distrib,
    ←Finset.mul_sum]
  simp only [ite_mul,one_mul,zero_mul]
  rw [sum_block_ite]
  rfl

theorem lift_radius_sos {n : ℕ}:BoundedSOS 1 (lift (Foundation.radiusPolynomial n)):=by
  apply BoundedSOS.rename
  exact BoundedSOS.of_family (fun i:Fin n↦X i) (by intro i;simp)

theorem lift_matrix_bound {n d e s : ℕ} {beta : ℝ} {w : Poly n}
    {M : Matrix (Fin d) (Fin e) (Poly n)}
    (hM : BoundedMatrixSOS (3 * s) (radialBound s beta w M)) :
    BoundedMatrixSOS (3*s) ((lift (Foundation.radiusPolynomial n))^(s+1)•
      ((C beta*(lift (Foundation.radiusPolynomial n))^(2*s-2)*lift w)•
        (1:Matrix (Fin d) (Fin d) (Poly (n+1)))-
        (M.map lift)*(M.map lift).transpose)):=by
  rw [radialBound_eq] at hM
  have hh:=RadialNodeSOS.matrixSOS_rename hM Fin.succ
  convert hh using 1
  apply Matrix.ext
  intro i j
  by_cases hij:i=j <;> simp [lift,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Matrix.sub_apply,
    Matrix.mul_apply,Matrix.transpose_apply,map_sum,map_mul,map_pow,map_sub,hij]

theorem lift_pairing {n d e s : ℕ} (M : Matrix (Fin d) (Fin e) (Poly n))
    (D : Fin d → Poly n) (v : Fin e → Poly n) (q : Poly n)
    (hp : (∑ i, D i * (∑ j, M i j * v j)) = (Foundation.radiusPolynomial n) ^ (s - 1) * q) :
    (∑i,lift (D i)*(∑j,lift (M i j)*lift (v j)))=
      (lift (Foundation.radiusPolynomial n))^(s-1)*lift q:=by
  simpa only [map_sum,map_mul,map_pow] using congrArg (lift (n:=n)) hp

local instance (priority := 2000) finOrderDecidableEq (n : ℕ):DecidableEq (Fin n):=
  (inferInstance : LinearOrder (Fin n)).toDecidableEq

set_option maxHeartbeats 1500000 in
/-- Both actual mixed-node certificates are discharged internally from
original source domination. No matrix or pairing premise remains. -/
theorem spectral_node_boundedSOS {n s : ℕ} (hn : 2 ≤ n) (hs : n ≤ 2 * s)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (T : Tri (Point (Fin n))) (H U : Finset (Fin n))
    {tau : ℝ} (htau : 0 ≤ tau) (haH : ∀ i ∈ H, tau ≤ a i) (haU : ∀ i ∈ U, 0 ≤ a i ∧ a i ≤ tau)
    (hHU : Disjoint H U) (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖WeightedQuadraticSplit.diagonal a x‖ * ‖x‖ ^ 2) :
    BoundedSOS (3*s+2)
      (C 7605*(X (0:Fin (n+1)))^2*(lift (Foundation.radiusPolynomial n))^(3*s-1)*
        lift (radiusBlock U+C (rho U)*Foundation.radiusPolynomial n)*lift (energyBlock a H)+
       X (0:Fin (n+1))*(lift (Foundation.radiusPolynomial n))^(3*s)*
        (3*lift (CubicQuadraticMatrix.mixedPolynomial T H U)+3*lift
          (CubicLinearMatrix.mixedPolynomial T H U))+
       (lift (Foundation.radiusPolynomial n))^(3*s+1)*(lift (radiusBlock H)+lift (radiusBlock
         U))):=by
  have hspos:1≤s:=by omega
  obtain ⟨M,hm,hM,hpq⟩:=exists_hhl_supplier hn hs a ha T H U htau haH haU hHU h12 h23 hdom
  obtain ⟨N,hnh,hN,hpt⟩:=exists_hll_supplier hn hs a ha T H U htau haH haU hHU h12 h23 hdom
  have hRdeg:(lift (Foundation.radiusPolynomial n)).totalDegree≤2:=
    (totalDegree_rename_le _ _).trans (HomogeneousSphereBounds.radius_homogeneous n).totalDegree_le
  have hMdeg:∀i j,(lift (M i j)).totalDegree≤2*s-1:=fun i j↦
    (totalDegree_rename_le _ _).trans (hm i j).totalDegree_le
  have hNdeg:∀i j,(lift (N i j)).totalDegree≤2*s-1:=fun i j↦
    (totalDegree_rename_le _ _).trans (hnh i j).totalDegree_le
  have hDdeg:∀i,(lift (C (a i)*coordinateBlock H i)).totalDegree≤1:=fun i↦
    (totalDegree_rename_le _ _).trans ((coordinateBlock_homogeneous H i).C_mul (a i)).totalDegree_le
  have hVdeg:∀i,(lift (coordinateBlock H i)).totalDegree≤1:=fun i↦
    (totalDegree_rename_le _ _).trans (coordinateBlock_homogeneous H i).totalDegree_le
  have hUdeg:∀i,(lift (coordinateBlock U i)).totalDegree≤1:=fun i↦
    (totalDegree_rename_le _ _).trans (coordinateBlock_homogeneous U i).totalDegree_le
  have hpq':=lift_pairing (s:=s) M (fun i↦C (a i)*coordinateBlock H i) (coordinateBlock H) _ hpq
  have hpt':=lift_pairing (s:=s) N (fun i↦C (a i)*coordinateBlock H i) (coordinateBlock U) _ hpt
  have hh:=RadialNodeSOS.radial_node_pair_boundedSOS hspos
    (lift (Foundation.radiusPolynomial n)) (X (0:Fin (n+1))) (lift (blockWeight U))
    (lift (CubicQuadraticMatrix.mixedPolynomial T H U)) (lift (CubicLinearMatrix.mixedPolynomial T
      H U))
    hRdeg lift_radius_sos (by simp) (fun i j↦lift (M i j)) hMdeg (fun i j↦lift (N i j)) hNdeg
    (fun i↦lift (C (a i)*coordinateBlock H i)) hDdeg (fun i↦lift (coordinateBlock H i)) hVdeg
    (fun i↦lift (coordinateBlock U i)) hUdeg hpq' hpt' (lift_matrix_bound hM) (lift_matrix_bound hN)
  have henergy:(∑i,(lift (C (a i)*coordinateBlock H i))^2)=lift (energyBlock a H):=by
    simp only [←map_pow,←map_sum,weightedBlock_squares]
  have hhigh:(∑i,lift (coordinateBlock H i)^2)=lift (radiusBlock H):=by
    simp only [←map_pow,←map_sum,coordinateBlock_squares]
  have hlow:(∑i,lift (coordinateBlock U i)^2)=lift (radiusBlock U):=by
    simp only [←map_pow,←map_sum,coordinateBlock_squares]
  simpa only [henergy,hhigh,hlow,blockWeight_eq] using hh

end RadialSpectralNode
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
