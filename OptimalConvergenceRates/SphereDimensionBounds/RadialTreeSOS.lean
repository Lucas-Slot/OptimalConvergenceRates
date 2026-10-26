import OptimalConvergenceRates.SphereDimensionBounds.RadialNodeSOS
import OptimalConvergenceRates.SphereDimensionBounds.BalancedCubicTree

/-! Exact SOS slacks for the spectral-node sums. The coordinate tree and
its root families are finite constructions; no coefficientwise positivity
is converted to SOS without explicit factors. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.RadialTreeSOS
open scoped BigOperators
open MvPolynomial ChebyshevSOSKernel CubicPrefixTree

abbrev Poly (n : ℕ):=MvPolynomial (Fin n) ℝ
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def Proper : IndexTree ι→Prop
  | .leaf _=>True
  | .node hi lo=>Disjoint (CubicPrefixTree.support hi) (CubicPrefixTree.support lo) ∧ Proper hi ∧ Proper lo

omit [Fintype ι] in
theorem proper_of_valid (a : ι→ℝ) (tr : IndexTree ι) (E : Finset ι) (hv : Valid a tr E) : Proper tr:=by
  induction tr generalizing E with
  | leaf i=>trivial
  | node hi lo ihh ihl=>exact ⟨hv.1,ihh _ hv.2.2.1,ihl _ hv.2.2.2.1⟩

def blockRadius {n : ℕ} (x : ι → Poly n) (s : Finset ι):Poly n:=∑i∈s,x i^2

def blockEnergy {n : ℕ} (a : ι→ℝ) (x : ι → Poly n) (s : Finset ι):Poly n:=∑i∈s,C (a i)^2*x i^2

def mass (c : ι→ℝ) (s : Finset ι):ℝ:=∑i∈s,c i

def nodeSum {n : ℕ} (F : Finset ι → Finset ι → Poly n):IndexTree ι→Poly n
  | .leaf _=>0
  | .node hi lo=>nodeSum F hi+nodeSum F lo+F (CubicPrefixTree.support hi) (CubicPrefixTree.support lo)

omit [Fintype ι] in
theorem blockRadius_union {n : ℕ} (x : ι → Poly n) (H U : Finset ι) (h : Disjoint H U) :
    blockRadius x (H∪U)=blockRadius x H+blockRadius x U:=Finset.sum_union h

omit [Fintype ι] in
theorem blockEnergy_union {n : ℕ} (a : ι→ℝ) (x : ι → Poly n) (H U : Finset ι) (h : Disjoint H U) :
    blockEnergy a x (H∪U)=blockEnergy a x H+blockEnergy a x U:=Finset.sum_union h

omit [Fintype ι] in
theorem mass_union (c : ι→ℝ) (H U : Finset ι) (h : Disjoint H U) :
    mass c (H∪U)=mass c H+mass c U:=Finset.sum_union h

omit [Fintype ι] [LinearOrder ι] in
theorem blockRadius_sos {n : ℕ} (x : ι → Poly n) (hx : ∀ i, (x i).totalDegree ≤ 1) (s : Finset ι) :
    BoundedSOS 1 (blockRadius x s):=by
  apply BoundedSOS.sum
  intro i _
  exact BoundedSOS.square _ (hx i)

omit [Fintype ι] [LinearOrder ι] in
theorem blockEnergy_sos {n : ℕ} (a : ι→ℝ) (x : ι → Poly n) (hx : ∀ i, (x i).totalDegree ≤ 1) (s : Finset ι) :
    BoundedSOS 1 (blockEnergy a x s):=by
  apply BoundedSOS.sum
  intro i _
  simpa only [map_pow] using (BoundedSOS.square _ (hx i)).scale (a i^2) (sq_nonneg _)

omit [Fintype ι] [LinearOrder ι] in
theorem mass_nonnegative (c : ι→ℝ) (hc : ∀ i, 0 ≤ c i) (s : Finset ι) : 0 ≤ mass c s:=
  Finset.sum_nonneg (fun i _=>hc i)

omit [Fintype ι] in
/-- The lower siblings consume a radius only once along any fixed high
coordinate. This exact recursive slack already has quadratic roots. -/
theorem energy_radius_slack_sos {n : ℕ} (a : ι→ℝ) (x : ι → Poly n)
    (hx : ∀ i, (x i).totalDegree ≤ 1) (tr : IndexTree ι) (hp : Proper tr) :
    BoundedSOS 2 (blockEnergy a x (CubicPrefixTree.support tr)*blockRadius x (CubicPrefixTree.support tr)-
      nodeSum (fun H U=>blockEnergy a x H*blockRadius x U) tr):=by
  induction tr with
  | leaf i=>
    simp only [CubicPrefixTree.support,nodeSum,sub_zero]
    exact (blockEnergy_sos a x hx {i}).mul (blockRadius_sos x hx {i})
  | node hi lo ihh ihl=>
    have hh:=ihh hp.2.1
    have hl:=ihl hp.2.2
    have hc:BoundedSOS 2 (blockEnergy a x (CubicPrefixTree.support lo)*blockRadius x (CubicPrefixTree.support hi)):=
      (blockEnergy_sos a x hx _).mul (blockRadius_sos x hx _)
    have he:(blockEnergy a x (CubicPrefixTree.support (.node hi lo))*blockRadius x (CubicPrefixTree.support (.node hi lo))-
        nodeSum (fun H U=>blockEnergy a x H*blockRadius x U) (.node hi lo))=
        (blockEnergy a x (CubicPrefixTree.support hi)*blockRadius x (CubicPrefixTree.support hi)-nodeSum (fun H U=>blockEnergy a x H*blockRadius x U) hi)+
        (blockEnergy a x (CubicPrefixTree.support lo)*blockRadius x (CubicPrefixTree.support lo)-nodeSum (fun H U=>blockEnergy a x H*blockRadius x U) lo)+
        blockEnergy a x (CubicPrefixTree.support lo)*blockRadius x (CubicPrefixTree.support hi):=by
      simp only [CubicPrefixTree.support,nodeSum,blockEnergy_union a x _ _ hp.1,blockRadius_union x _ _ hp.1]
      ring
    rw [he]
    exact (hh.add hl).add hc

omit [Fintype ι] in
/-- Dimension ratios consume at most their total mass, with a genuinely
linear-square slack even for zero coefficients. -/
theorem mass_energy_slack_sos {n : ℕ} (a c : ι→ℝ) (hc : ∀ i, 0 ≤ c i) (x : ι → Poly n)
    (hx : ∀ i, (x i).totalDegree ≤ 1) (tr : IndexTree ι) (hp : Proper tr) :
    BoundedSOS 1 (C (mass c (CubicPrefixTree.support tr))*blockEnergy a x (CubicPrefixTree.support tr)-
      nodeSum (fun H U=>C (mass c U)*blockEnergy a x H) tr):=by
  induction tr with
  | leaf i=>
    simp only [nodeSum,sub_zero]
    exact (blockEnergy_sos a x hx _).scale _ (mass_nonnegative c hc _)
  | node hi lo ihh ihl=>
    have hh:=ihh hp.2.1
    have hl:=ihl hp.2.2
    have hs:BoundedSOS 1 (C (mass c (CubicPrefixTree.support hi))*blockEnergy a x (CubicPrefixTree.support lo)):=
      (blockEnergy_sos a x hx _).scale _ (mass_nonnegative c hc _)
    have he:(C (mass c (CubicPrefixTree.support (.node hi lo)))*blockEnergy a x (CubicPrefixTree.support (.node hi lo))-
        nodeSum (fun H U=>C (mass c U)*blockEnergy a x H) (.node hi lo))=
        (C (mass c (CubicPrefixTree.support hi))*blockEnergy a x (CubicPrefixTree.support hi)-nodeSum (fun H U=>C (mass c U)*blockEnergy a x H) hi)+
        (C (mass c (CubicPrefixTree.support lo))*blockEnergy a x (CubicPrefixTree.support lo)-nodeSum (fun H U=>C (mass c U)*blockEnergy a x H) lo)+
        C (mass c (CubicPrefixTree.support hi))*blockEnergy a x (CubicPrefixTree.support lo):=by
      simp only [CubicPrefixTree.support,nodeSum,mass_union c _ _ hp.1,blockEnergy_union a x _ _ hp.1,map_add]
      ring
    rw [he]
    exact (hh.add hl).add hs

omit [Fintype ι] in
/-- Each coordinate appears at most once at any tree depth. The proof
constructs the difference from child slacks and nonnegative radius terms. -/
theorem depth_radius_slack_sos {n : ℕ} (x : ι → Poly n) (hx : ∀ i, (x i).totalDegree ≤ 1)
    (tr : IndexTree ι) (hp : Proper tr) :
    BoundedSOS 1 (C (depth tr:ℝ)*blockRadius x (CubicPrefixTree.support tr)-
      nodeSum (fun H U=>blockRadius x H+blockRadius x U) tr):=by
  induction tr with
  | leaf i=>simp [depth,nodeSum,BoundedSOS.zero]
  | node hi lo ihh ihl=>
    have hh:=ihh hp.2.1
    have hl:=ihl hp.2.2
    have dh:0≤((max (depth hi) (depth lo)-depth hi:ℕ):ℝ):=Nat.cast_nonneg _
    have dl:0≤((max (depth hi) (depth lo)-depth lo:ℕ):ℝ):=Nat.cast_nonneg _
    have hhs:BoundedSOS 1 (C ((max (depth hi) (depth lo)-depth hi:ℕ):ℝ)*blockRadius x (CubicPrefixTree.support hi)):=
      (blockRadius_sos x hx _).scale _ dh
    have hls:BoundedSOS 1 (C ((max (depth hi) (depth lo)-depth lo:ℕ):ℝ)*blockRadius x (CubicPrefixTree.support lo)):=
      (blockRadius_sos x hx _).scale _ dl
    have hcH:((max (depth hi) (depth lo)-depth hi:ℕ):ℝ)=((max (depth hi) (depth lo):ℕ):ℝ)-(depth hi:ℝ):=by
      exact Nat.cast_sub (le_max_left _ _)
    have hcL:((max (depth hi) (depth lo)-depth lo:ℕ):ℝ)=((max (depth hi) (depth lo):ℕ):ℝ)-(depth lo:ℝ):=by
      exact Nat.cast_sub (le_max_right _ _)
    have he:(C (depth (.node hi lo):ℝ)*blockRadius x (CubicPrefixTree.support (.node hi lo))-
        nodeSum (fun H U=>blockRadius x H+blockRadius x U) (.node hi lo))=
        ((C (depth hi:ℝ)*blockRadius x (CubicPrefixTree.support hi)-nodeSum (fun H U=>blockRadius x H+blockRadius x U) hi)+
        (C (depth lo:ℝ)*blockRadius x (CubicPrefixTree.support lo)-nodeSum (fun H U=>blockRadius x H+blockRadius x U) lo))+
        (C ((max (depth hi) (depth lo)-depth hi:ℕ):ℝ)*blockRadius x (CubicPrefixTree.support hi)+
        C ((max (depth hi) (depth lo)-depth lo:ℕ):ℝ)*blockRadius x (CubicPrefixTree.support lo)):=by
      simp only [CubicPrefixTree.support,depth,nodeSum,blockRadius_union x _ _ hp.1,Nat.cast_add,Nat.cast_one,hcH,hcL,map_add,map_sub,map_one]
      ring
    rw [he]
    exact (hh.add hl).add (hhs.add hls)

omit [Fintype ι] in
theorem nodeSum_weighted_identity {n : ℕ} (a c : ι→ℝ) (x : ι → Poly n) (R : Poly n) (tr : IndexTree ι) :
    nodeSum (fun H U=>(blockRadius x U+C (mass c U)*R)*blockEnergy a x H) tr=
      nodeSum (fun H U=>blockEnergy a x H*blockRadius x U) tr+
      R*nodeSum (fun H U=>C (mass c U)*blockEnergy a x H) tr:=by
  induction tr with
  | leaf i=>simp [nodeSum]
  | node hi lo ihh ihl=>simp only [nodeSum,ihh,ihl];ring

omit [Fintype ι] in
/-- The two actual sibling budgets combine with total coefficient two. -/
theorem weighted_slack_sos {n : ℕ} (a c : ι→ℝ) (hc : ∀ i, 0 ≤ c i) (x : ι → Poly n)
    (hx : ∀ i, (x i).totalDegree ≤ 1) (tr : IndexTree ι) (hp : Proper tr)
    (hm : mass c (CubicPrefixTree.support tr) = 1) :
    BoundedSOS 2 (2*blockRadius x (CubicPrefixTree.support tr)*blockEnergy a x (CubicPrefixTree.support tr)-
      nodeSum (fun H U=>(blockRadius x U+C (mass c U)*blockRadius x (CubicPrefixTree.support tr))*blockEnergy a x H) tr):=by
  have h1:=energy_radius_slack_sos a x hx tr hp
  have h2:BoundedSOS 2 (blockRadius x (CubicPrefixTree.support tr)*
      (C (mass c (CubicPrefixTree.support tr))*blockEnergy a x (CubicPrefixTree.support tr)-
        nodeSum (fun H U=>C (mass c U)*blockEnergy a x H) tr)):=
    (blockRadius_sos x hx _).mul (mass_energy_slack_sos a c hc x hx tr hp)
  rw [hm,map_one] at h2
  have hid:(2*blockRadius x (CubicPrefixTree.support tr)*blockEnergy a x (CubicPrefixTree.support tr)-
      nodeSum (fun H U=>(blockRadius x U+C (mass c U)*blockRadius x (CubicPrefixTree.support tr))*blockEnergy a x H) tr)=
      (blockEnergy a x (CubicPrefixTree.support tr)*blockRadius x (CubicPrefixTree.support tr)-
        nodeSum (fun H U=>blockEnergy a x H*blockRadius x U) tr)+
      blockRadius x (CubicPrefixTree.support tr)*(blockEnergy a x (CubicPrefixTree.support tr)-
        nodeSum (fun H U=>C (mass c U)*blockEnergy a x H) tr):=by
    rw [nodeSum_weighted_identity]
    ring
  rw [hid]
  simpa only [one_mul] using h1.add h2

local instance (priority := 2000) finOrderDecidableEq (n : ℕ) : DecidableEq (Fin n) :=
  (inferInstance : LinearOrder (Fin n)).toDecidableEq

theorem fullTree_proper (d : ℕ) : Proper (BalancedCubicTree.fullTree d):=by
  apply proper_of_valid (fun _=>1) _ ∅
  apply BalancedCubicTree.fullTree_valid
  · intro i;norm_num
  · intro i j _;exact le_rfl

/-- A complete balanced tree is supplied explicitly; its variables may
be zero padding in a smaller original ambient polynomial ring. -/
theorem fullTree_weighted_slack_sos {n : ℕ} (d : ℕ) (a c : Fin (2 ^ d) → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hm : ∑ i, c i = 1) (x : Fin (2 ^ d) → Poly n)
    (hx : ∀ i, (x i).totalDegree ≤ 1) :
    BoundedSOS 2 (2*(∑i,x i^2)*(∑i,C (a i)^2*x i^2)-
      nodeSum (fun H U=>(blockRadius x U+C (mass c U)*(∑i,x i^2))*blockEnergy a x H) (BalancedCubicTree.fullTree d)):=by
  have hh:=weighted_slack_sos a c hc x hx (BalancedCubicTree.fullTree d) (fullTree_proper d)
  simpa only [BalancedCubicTree.fullTree_support,blockRadius,blockEnergy,mass,hm] using hh (by
    simpa only [BalancedCubicTree.fullTree_support,mass] using hm)

theorem fullTree_depth_slack_sos {n : ℕ} (d : ℕ) (x : Fin (2 ^ d) → Poly n)
    (hx : ∀ i, (x i).totalDegree ≤ 1) :
    BoundedSOS 1 (C (d:ℝ)*(∑i,x i^2)-nodeSum (fun H U=>blockRadius x H+blockRadius x U) (BalancedCubicTree.fullTree d)):=by
  simpa only [BalancedCubicTree.fullTree_support,BalancedCubicTree.fullTree_depth,blockRadius] using
    depth_radius_slack_sos x hx (BalancedCubicTree.fullTree d) (fullTree_proper d)

end OptimalConvergenceRates.SphereDimensionBounds.RadialTreeSOS
