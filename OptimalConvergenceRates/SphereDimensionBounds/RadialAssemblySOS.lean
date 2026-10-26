import OptimalConvergenceRates.SphereDimensionBounds.RadialTreeSOS
import OptimalConvergenceRates.SphereDimensionBounds.RadialLeafSOS

/-! Exact degree-preserving summation of the spectral-node and leaf
certificates. The analytic mixed-node construction is a separate input
supplier, not replaced by pointwise nonnegativity. -/
noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.RadialAssemblySOS
open scoped BigOperators
open MvPolynomial ChebyshevSOSKernel CubicPrefixTree RadialTreeSOS
abbrev Poly (n : ℕ):=MvPolynomial (Fin n) ℝ
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def EveryNode (P : Finset ι → Finset ι → Prop):IndexTree ι→Prop
  | .leaf _=>True
  | .node hi lo=>EveryNode P hi ∧ EveryNode P lo ∧ P (CubicPrefixTree.support hi) (CubicPrefixTree.support lo)

omit [Fintype ι] in
theorem nodeSum_boundedSOS {n r : ℕ} (F : Finset ι → Finset ι → Poly n) (tr : IndexTree ι)
    (h : EveryNode (fun H U => BoundedSOS r (F H U)) tr):BoundedSOS r (nodeSum F tr):=by
  induction tr with
  | leaf i=>exact BoundedSOS.zero
  | node hi lo ihh ihl=>exact ((ihh h.1).add (ihl h.2.1)).add h.2.2

omit [Fintype ι] in
theorem nodeSum_three_terms {n : ℕ} (F G H : Finset ι → Finset ι → Poly n) (p q r : Poly n) (tr : IndexTree ι) :
    nodeSum (fun A B=>p*F A B+q*G A B+r*H A B) tr=
      p*nodeSum F tr+q*nodeSum G tr+r*nodeSum H tr:=by
  induction tr with
  | leaf i=>simp [nodeSum]
  | node hi lo ihh ihl=>simp only [nodeSum,ihh,ihl];ring

omit [Fintype ι] in
/-- The exact two sibling slacks and the depth slack turn actual node
certificates into the common top coefficient15210. -/
theorem tree_node_sum_boundedSOS {n s : ℕ} (hs : 1 ≤ s) (a c : ι→ℝ) (hc : ∀ i, 0 ≤ c i)
    (x : ι → Poly n) (hx : ∀ i, (x i).totalDegree ≤ 1) (z : Poly n) (hz : z.totalDegree ≤ 1)
    (tr : IndexTree ι) (hp : Proper tr) (hm : mass c (CubicPrefixTree.support tr) = 1)
    (Q : Finset ι → Finset ι → Poly n)
    (hnode : EveryNode (fun H U => BoundedSOS (3 * s + 2)
      (C 7605 * z ^ 2 * (blockRadius x (CubicPrefixTree.support tr)) ^ (3 * s - 1) *
        (blockRadius x U + C (mass c U) * blockRadius x (CubicPrefixTree.support tr)) * blockEnergy a x H +
       z * (blockRadius x (CubicPrefixTree.support tr)) ^ (3 * s) * Q H U +
       (blockRadius x (CubicPrefixTree.support tr)) ^ (3 * s + 1) * (blockRadius x H + blockRadius x U))) tr) :
    BoundedSOS (3*s+2) ((blockRadius x (CubicPrefixTree.support tr))^(3*s)*
      (C 15210*z^2*blockEnergy a x (CubicPrefixTree.support tr)+z*nodeSum Q tr+
       C (depth tr:ℝ)*(blockRadius x (CubicPrefixTree.support tr))^2)):=by
  let R:=blockRadius x (CubicPrefixTree.support tr)
  let A:=blockEnergy a x (CubicPrefixTree.support tr)
  let W:=fun H U=>(blockRadius x U+C (mass c U)*R)*blockEnergy a x H
  let V:=fun H U=>blockRadius x H+blockRadius x U
  have hR:BoundedSOS 1 R:=blockRadius_sos x hx _
  have hfold:BoundedSOS (3*s+2) (C 7605*z^2*R^(3*s-1)*nodeSum W tr+
      z*R^(3*s)*nodeSum Q tr+R^(3*s+1)*nodeSum V tr):=by
    rw [←nodeSum_three_terms W Q V (C 7605*z^2*R^(3*s-1)) (z*R^(3*s)) (R^(3*s+1)) tr]
    apply nodeSum_boundedSOS
    simpa only [W,V,R,mul_assoc] using! hnode
  have hw:BoundedSOS 2 (2*R*A-nodeSum W tr):=weighted_slack_sos a c hc x hx tr hp hm
  have hfactor:BoundedSOS (3*s) (z^2*R^(3*s-1)):=by
    have hh:=(BoundedSOS.square z hz).mul (RadialNodeSOS.radius_power_boundedSOS (s:=3*s-1) hR)
    convert hh using 1
    omega
  have hw':BoundedSOS (3*s+2) (C 7605*(z^2*R^(3*s-1)*(2*R*A-nodeSum W tr))):=
    (hfactor.mul hw).scale 7605 (by norm_num)
  have hv:BoundedSOS 1 (C (depth tr:ℝ)*R-nodeSum V tr):=depth_radius_slack_sos x hx tr hp
  have hv':BoundedSOS (3*s+2) (R^(3*s+1)*(C (depth tr:ℝ)*R-nodeSum V tr)):=by
    exact (RadialNodeSOS.radius_power_boundedSOS (s:=3*s+1) hR).mul hv
  have hid:R^(3*s)*(C 15210*z^2*A+z*nodeSum Q tr+C (depth tr:ℝ)*R^2)=
      (C 7605*z^2*R^(3*s-1)*nodeSum W tr+z*R^(3*s)*nodeSum Q tr+R^(3*s+1)*nodeSum V tr)+
      C 7605*(z^2*R^(3*s-1)*(2*R*A-nodeSum W tr))+
      R^(3*s+1)*(C (depth tr:ℝ)*R-nodeSum V tr):=by
    have hpow:R^(3*s-1)*R=R^(3*s):=by rw [←pow_succ];congr 1;omega
    have hpow':R^(3*s+1)=R^(3*s)*R:=pow_succ _ _
    have hnumber:(C 15210:Poly n)=2*C 7605:=by
      change C (15210:ℝ)=C (2:ℝ)*C (7605:ℝ)
      rw [←map_mul]
      norm_num
    rw [hnumber,hpow']
    linear_combination -(2*C 7605*z^2*A)*hpow
  change BoundedSOS (3*s+2) (R^(3*s)*(C 15210*z^2*A+z*nodeSum Q tr+C (depth tr:ℝ)*R^2))
  rw [hid]
  exact (hfold.add hw').add hv'

/-- Adding the actual leaf squares costs one top coefficient and one
radius square, with no degree loss. -/
theorem tree_and_leaf_boundedSOS {n s : ℕ} (hs : 1 ≤ s) (a c gamma : ι→ℝ) (hc : ∀ i, 0 ≤ c i)
    (hg : ∀ i, |gamma i| ≤ 2) (x : ι → Poly n) (hx : ∀ i, (x i).totalDegree ≤ 1)
    (z : Poly n) (hz : z.totalDegree ≤ 1) (tr : IndexTree ι) (hp : Proper tr)
    (hfull : CubicPrefixTree.support tr = Finset.univ) (hm : ∑ i, c i = 1)
    (Q : Finset ι → Finset ι → Poly n)
    (hnode : EveryNode (fun H U => BoundedSOS (3 * s + 2)
      (C 7605 * z ^ 2 * (∑ i, x i ^ 2) ^ (3 * s - 1) * (blockRadius x U + C (mass c U) * (∑ i, x i ^ 2)) * blockEnergy a x H +
       z * (∑ i, x i ^ 2) ^ (3 * s) * Q H U + (∑ i, x i ^ 2) ^ (3 * s + 1) * (blockRadius x H + blockRadius x U))) tr) :
    BoundedSOS (3*s+2) ((∑i,x i^2)^(3*s)*
      (C 15211*z^2*(∑i,C (a i)^2*x i^2)+z*(nodeSum Q tr+∑i,C (a i*gamma i)*x i^3)+
       C ((depth tr:ℝ)+1)*(∑i,x i^2)^2)):=by
  have hnodes:BoundedSOS (3*s+2) ((∑i,x i^2)^(3*s)*
      (C 15210*z^2*(∑i,C (a i)^2*x i^2)+z*nodeSum Q tr+C (depth tr:ℝ)*(∑i,x i^2)^2)):=by
    apply (by simpa only [hfull,blockRadius,blockEnergy] using
      (tree_node_sum_boundedSOS hs a c hc x hx z hz tr hp
        (by simpa only [hfull,mass] using hm) Q (by simpa only [hfull,blockRadius] using hnode)))
  have hleaf:=RadialLeafSOS.leaf_boundedSOS x hx z hz a gamma hg
  have hR:BoundedSOS 1 (∑i,x i^2):=BoundedSOS.of_family _ hx
  have hl:BoundedSOS (3*s+2) ((∑i,x i^2)^(3*s)*
      (z^2*(∑i,C (a i)^2*x i^2)+z*(∑i,C (a i*gamma i)*x i^3)+(∑i,x i^2)^2)):=
    (RadialNodeSOS.radius_power_boundedSOS (s:=3*s) hR).mul hleaf
  convert hnodes.add hl using 1
  simp only [map_add,map_one]
  have hn:(C 15211:Poly n)=C 15210+1:=by
    change C (15211:ℝ)=C (15210:ℝ)+C (1:ℝ)
    rw [←map_add]
    norm_num
  rw [hn]
  ring

end OptimalConvergenceRates.SphereDimensionBounds.RadialAssemblySOS
