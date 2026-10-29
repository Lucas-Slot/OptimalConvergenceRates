import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.RadialSpectralNode
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.RadialCubicTree
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.RadialLongitudinalScale

/-! Actual spectral-tree radial certificate from the original cubic
source in every original transverse dimension. -/
noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace SortedRadialCertificate
open scoped BigOperators InnerProductSpace
open MvPolynomial ChebyshevSOSKernel WeightedQuadraticSplit WeightedCubicSplit
  OrderedCubicExpansion OrthogonalDepthAggregation CubicBlockInverse CubicPrefixTree
  RadialTreeSOS RadialAssemblySOS RadialSpectralNode RadialCubicTree
abbrev Poly (n : ℕ):=MvPolynomial (Fin n) ℝ
local instance (priority := 2000) finOrderDecidableEq (n : ℕ):DecidableEq (Fin n):=
  (inferInstance : LinearOrder (Fin n)).toDecidableEq

theorem lift_constant {n : ℕ} (c : ℝ):lift (C c:Poly n)=C c:=by simp [lift]

theorem support_nonempty {n : ℕ} (tr : IndexTree (Fin n)):(CubicPrefixTree.support tr).Nonempty:=by
  induction tr with
  | leaf i=>exact Finset.singleton_nonempty _
  | node hi lo ihh _=>exact ihh.mono Finset.subset_union_left

theorem ordered_gap {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a)
    (H U : Finset (Fin n)) (hne : H.Nonempty) (horder : ∀ i ∈ H, ∀ j ∈ U, i < j) :
    ∃tau:ℝ,0≤tau ∧ (∀i∈H,tau≤a i) ∧ ∀j∈U,0≤a j ∧ a j≤tau:=by
  obtain ⟨i,hi,hmin⟩:=Finset.exists_min_image H a hne
  exact ⟨a i,ha i,hmin,fun j hj↦⟨ha j,hmono (horder i hi j hj).le⟩⟩

def nodePolynomial {n s : ℕ} (a : Fin n → ℝ) (T : Tri (Point (Fin n))) (H U : Finset (Fin n)):Poly
  (n+1):=
  C 7605*(X (0:Fin (n+1)))^2*(lift (Foundation.radiusPolynomial n))^(3*s-1)*
    lift (radiusBlock U+C (HomogeneousMatrixBound.rho U)*Foundation.radiusPolynomial n)*lift
      (energyBlock a H)+
  X (0:Fin (n+1))*(lift (Foundation.radiusPolynomial n))^(3*s)*lift (crossCubic T H U)+
  (lift (Foundation.radiusPolynomial n))^(3*s+1)*(lift (radiusBlock H)+lift (radiusBlock U))

/-- Every node of the actual tree receives a true source-derived scalar
certificate, including nodes whose high spectrum has zero eigenvalues. -/
theorem every_node_certificate {n s : ℕ} (hn : 2 ≤ n) (hs : n ≤ 2 * s)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a) (T : Tri (Point (Fin n)))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖WeightedQuadraticSplit.diagonal a x‖ * ‖x‖ ^ 2)
    (tr : IndexTree (Fin n)) (hp : Proper tr)
    (ho : EveryNode (fun H U ↦ ∀ i ∈ H, ∀ j ∈ U, i < j) tr) :
    EveryNode (fun H U↦BoundedSOS (3*s+2) (nodePolynomial (s:=s) a T H U)) tr:=by
  induction tr with
  | leaf i=>trivial
  | node hi lo ihh ihl=>
    refine ⟨ihh hp.2.1 ho.1,ihl hp.2.2 ho.2.1,?_⟩
    obtain ⟨tau,ht,hH,hU⟩:=ordered_gap a ha hmono _ _ (support_nonempty hi) ho.2.2
    have hh:=spectral_node_boundedSOS hn hs a ha T _ _ ht hH hU hp.1 h12 h23 hdom
    simpa only [nodePolynomial,crossCubic,map_add,map_mul,map_ofNat] using hh

theorem radius_block_lift {n : ℕ} (H : Finset (Fin n)) :
    blockRadius (fun i↦lift (X i:Poly n)) H=lift (radiusBlock H):=by
  simp only [blockRadius,radiusBlock,map_sum,map_pow]

theorem energy_block_lift {n : ℕ} (a : Fin n → ℝ) (H : Finset (Fin n)) :
    blockEnergy a (fun i↦lift (X i:Poly n)) H=lift (energyBlock a H):=by
  simp only [blockEnergy,energyBlock,map_sum,map_mul,map_pow,lift_constant]

theorem dimension_mass {n : ℕ} (U : Finset (Fin n)) :
    mass (fun _↦(1:ℝ)/(n:ℝ)) U=HomogeneousMatrixBound.rho U:=by
  simp [mass,HomogeneousMatrixBound.rho,div_eq_mul_inv]

theorem nodeSum_lift {n : ℕ} (F : Finset (Fin n) → Finset (Fin n) → Poly n) (tr : IndexTree (Fin
  n)) :
    nodeSum (fun H U↦lift (F H U)) tr=lift (nodeSum F tr):=by
  induction tr with
  | leaf i=>simp [nodeSum]
  | node hi lo ihh ihl=>simp only [nodeSum,ihh,ihl,map_add]

/-- The actual full node and leaf sum, before the harmless longitudinal
rescaling. All analytic source inputs have been discharged. -/
theorem exists_unscaled_radial_certificate {n s : ℕ} (hn : 2 ≤ n) (hs : n ≤ 2 * s)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a) (T : Tri (Point (Fin n)))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖WeightedQuadraticSplit.diagonal a x‖ * ‖x‖ ^ 2) :
    ∃d:ℕ,d≤Nat.clog 2 n ∧ BoundedSOS (3*s+2)
      ((lift (Foundation.radiusPolynomial n))^(3*s)*
        (C 15211*(X (0:Fin (n+1)))^2*lift (energyBlock a Finset.univ)+
         X (0:Fin (n+1))*lift (cubicFromTri T)+C ((d:ℝ)+1)*(lift (Foundation.radiusPolynomial
           n))^2)):=by
  obtain ⟨tr,hp,hfull,hd,ho⟩:=OrderedBalancedTree.exists_full_tree (by omega : 0<n)
  let x:Fin n→Poly (n+1):=fun i↦lift (X i)
  let c:Fin n→ℝ:=fun _↦1/(n:ℝ)
  have hx:∀i,(x i).totalDegree≤1:=by
    intro i
    exact (totalDegree_rename_le _ _).trans (by simp)
  have hc:∀i,0≤c i:=by intro i;dsimp [c];positivity
  have hm:(∑i,c i)=1:=by
    simp only [c,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hn0:(n:ℝ)≠0:=by exact_mod_cast (by omega : n≠0)
    field_simp
  have hR:(∑i,x i^2)=lift (Foundation.radiusPolynomial n):=by
    simp only [x,←map_pow,←map_sum]
    rfl
  have hA:(∑i,C (a i)^2*x i^2)=lift (energyBlock a Finset.univ):=by
    change blockEnergy a x Finset.univ=_
    exact energy_block_lift a _
  have hnodes:=every_node_certificate hn hs a ha hmono T h12 h23 hdom tr hp ho
  have hevery:EveryNode (fun H U↦BoundedSOS (3*s+2)
    (C 7605*(X (0:Fin (n+1)))^2*(∑i,x i^2)^(3*s-1)*
      (blockRadius x U+C (mass c U)*(∑i,x i^2))*blockEnergy a x H+
     X (0:Fin (n+1))*(∑i,x i^2)^(3*s)*lift (crossCubic T H U)+
     (∑i,x i^2)^(3*s+1)*(blockRadius x H+blockRadius x U))) tr:=by
    simpa only [nodePolynomial,hR,x,c,radius_block_lift,energy_block_lift,
      dimension_mass,map_add,map_mul,lift_constant] using! hnodes
  have hh:=tree_and_leaf_boundedSOS (by omega : 1≤s) a c (gamma a T) hc
    (gamma_bound a ha T hdom) x hx (X (0:Fin (n+1))) (by simp) tr hp hfull hm
    (fun H U↦lift (crossCubic T H U)) hevery
  have hQ:nodeSum (fun H U↦lift (crossCubic T H U)) tr+
      (∑i,C (a i*gamma a T i)*x i^3)=lift (cubicFromTri T):=by
    rw [nodeSum_lift]
    have hleaf:(∑i,C (a i*gamma a T i)*x i^3)=
        lift (∑i,C (T (coordinateAxis i) (coordinateAxis i) (coordinateAxis i))*X i^3):=by
      simp only [x,map_sum,map_mul,map_pow,mul_gamma a ha T hdom,lift_constant]
    rw [hleaf,←map_add,full_tree_cubic_identity T h12 h23 tr hp hfull]
  rw [hR,hA,hQ] at hh
  exact ⟨depth tr,hd,hh⟩

/-- The actual normalized radial certificate in every original dimension,
with the published15211*(clog2n+2) budget and full3s+2 root bound. -/
theorem sorted_radial_boundedSOS {n s : ℕ} (hn : 2 ≤ n) (hs : n ≤ 2 * s)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a) (T : Tri (Point (Fin n)))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖WeightedQuadraticSplit.diagonal a x‖ * ‖x‖ ^ 2) :
    BoundedSOS (3*s+2) ((lift (Foundation.radiusPolynomial n))^(3*s)*
      ((X (0:Fin (n+1)))^2*lift (energyBlock a Finset.univ)+
       X (0:Fin (n+1))*lift (cubicFromTri T)+
       C (15211*((Nat.clog 2 n:ℝ)+2))*(lift (Foundation.radiusPolynomial n))^2)):=by
  obtain ⟨d,hd,hpre⟩:=exists_unscaled_radial_certificate hn hs a ha hmono T h12 h23 hdom
  have hnorm:=RadialLongitudinalScale.normalize_boundedSOS
    (Foundation.radiusPolynomial n) (energyBlock a Finset.univ) (cubicFromTri T) ((d:ℝ)+1) hpre
  let delta:ℝ:=15211*((Nat.clog 2 n:ℝ)+2-((d:ℝ)+1))
  have hdelta:0≤delta:=by
    have hcast:(d:ℝ)≤(Nat.clog 2 n:ℝ):=by exact_mod_cast hd
    dsimp [delta]
    linarith
  have hpad:BoundedSOS (3*s+2) (C delta*(lift (Foundation.radiusPolynomial n))^(3*s+2)):=
    (RadialNodeSOS.radius_power_boundedSOS (s:=3*s+2) lift_radius_sos).scale delta hdelta
  have hcoeff:(C (15211*((Nat.clog 2 n:ℝ)+2)):Poly (n+1))=C (15211*((d:ℝ)+1))+C delta:=by
    rw [←map_add]
    congr 1
    dsimp [delta]
    ring
  have hpow:(lift (Foundation.radiusPolynomial n))^(3*s+2)=
      (lift (Foundation.radiusPolynomial n))^(3*s)*(lift (Foundation.radiusPolynomial
        n))^2:=pow_add _ _ _
  convert hnorm.add hpad using 1
  rw [hcoeff,hpow]
  ring

end SortedRadialCertificate
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
