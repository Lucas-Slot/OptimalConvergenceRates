import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.RadialAssemblySOS

/-! An actual balanced ordered coordinate tree in every positive dimension.
No sphere or polynomial ambient dimension is padded. -/
noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace OrderedBalancedTree
open scoped BigOperators
open CubicPrefixTree RadialTreeSOS RadialAssemblySOS
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

omit [Fintype ι] in
/-- Every finite strictly ordered list with at most2^d entries has a
proper ordered coordinate tree of depth at mostd. -/
theorem exists_tree_of_list (d : ℕ) (l : List ι) (hne : l ≠ []) (hcap : l.length ≤ 2 ^ d)
    (hl : l.Pairwise (· < ·)) :
    ∃tr:IndexTree ι,Proper tr ∧ CubicPrefixTree.support tr=l.toFinset ∧ depth tr≤d ∧
      EveryNode (fun H U↦∀i∈H,∀j∈U,i<j) tr:=by
  induction d generalizing l with
  | zero=>
    have hlen:l.length=1:=by have hh:=List.length_pos_iff.mpr hne;norm_num at hcap;omega
    obtain ⟨i,hi⟩:=List.length_eq_one_iff.mp hlen
    subst l
    exact ⟨.leaf i,trivial,by simp [CubicPrefixTree.support],by simp [depth],trivial⟩
  | succ d ih=>
    by_cases hsmall:l.length≤2^d
    · obtain ⟨tr,hp,hs,hd,ho⟩:=ih l hne hsmall hl
      exact ⟨tr,hp,hs,by omega,ho⟩
    let cap:=2^d
    have hcap0:0<cap:=pow_pos (by norm_num) d
    have hlong:cap<l.length:=lt_of_not_ge hsmall
    have hlen:l.length≤2*cap:=by simpa only [pow_succ,mul_comm] using hcap
    have hsplit:(l.take cap++l.drop cap).Pairwise (·<·):=by simpa only [List.take_append_drop]
      using hl
    obtain ⟨hh,hu,hcross⟩:=List.pairwise_append.mp hsplit
    have hHlen:(l.take cap).length=cap:=by rw [List.length_take,Nat.min_eq_left hlong.le]
    have hUlen:(l.drop cap).length=l.length-cap:=List.length_drop
    have hHne:l.take cap≠[]:=by intro hz;rw [hz,List.length_nil] at hHlen;omega
    have hUne:l.drop cap≠[]:=by intro hz;rw [hz,List.length_nil] at hUlen;omega
    obtain ⟨H,hHp,hHs,hHd,hHo⟩:=ih (l.take cap) hHne (by rw [hHlen]) hh
    obtain ⟨U,hUp,hUs,hUd,hUo⟩:=ih (l.drop cap) hUne (by rw [hUlen];omega) hu
    have hdisj:Disjoint (CubicPrefixTree.support H) (CubicPrefixTree.support U):=by
      rw [hHs,hUs]
      apply Finset.disjoint_left.mpr
      intro i hi hu
      exact (lt_irrefl i) (hcross i (List.mem_toFinset.mp hi) i (List.mem_toFinset.mp hu))
    refine ⟨.node H U,⟨hdisj,hHp,hUp⟩,?_,?_,⟨hHo,hUo,?_⟩⟩
    · simp only [CubicPrefixTree.support,hHs,hUs,←List.toFinset_append,List.take_append_drop]
    · simp only [depth]
      omega
    · intro i hi j hj
      rw [hHs] at hi
      rw [hUs] at hj
      exact hcross i (List.mem_toFinset.mp hi) j (List.mem_toFinset.mp hj)

local instance (priority := 2000) finOrderDecidableEq (n : ℕ):DecidableEq (Fin n):=
  (inferInstance : LinearOrder (Fin n)).toDecidableEq

/-- A balanced ordered tree on precisely the ORIGINAL n coordinates,
with no dummy coordinates, is constructed rather than assumed. -/
theorem exists_full_tree {n : ℕ} (hn : 0 < n) :
    ∃tr:IndexTree (Fin n),Proper tr ∧ CubicPrefixTree.support tr=Finset.univ ∧
      depth tr≤Nat.clog 2 n ∧ EveryNode (fun H U↦∀i∈H,∀j∈U,i<j) tr:=by
  have hne:List.finRange n≠[]:=by
    intro hz
    have hh:=congrArg List.length hz
    simp only [List.length_finRange,List.length_nil] at hh
    omega
  obtain ⟨tr,hp,hs,hd,ho⟩:=exists_tree_of_list (Nat.clog 2 n) (List.finRange n) hne
    (by simpa only [List.length_finRange] using Nat.le_pow_clog (by norm_num : 1<2) n)
    (List.pairwise_lt_finRange n)
  refine ⟨tr,hp,?_,hd,ho⟩
  rw [hs]
  ext i
  simp

end OrderedBalancedTree
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
