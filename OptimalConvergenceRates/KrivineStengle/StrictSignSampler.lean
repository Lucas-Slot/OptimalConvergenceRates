/-
  OptimalConvergenceRates/KrivineStengle/StrictSignSampler.lean

  The algebraic sign-cell lemma underlying the finite strict sampler.
-/
import OptimalConvergenceRates.KrivineStengle.AlgebraicRolle
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

noncomputable section

open Polynomial Set

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-- If a finite strict sign cell has a product root on both sides of one
of its points, a root of the product derivative samples that same cell. -/
theorem exists_derivative_isRoot_with_all_pos_of_roots_on_both_sides
    (fs : List R[X]) (y : R)
    (hpos : ∀ f ∈ fs, 0 < f.eval y)
    (hleft : ∃ a, a < y ∧ fs.prod.IsRoot a)
    (hright : ∃ b, y < b ∧ fs.prod.IsRoot b) :
    ∃ z, fs.prod.derivative.IsRoot z ∧ ∀ f ∈ fs, 0 < f.eval z := by
  classical
  let p : R[X] := fs.prod
  have hpEvalY : 0 < p.eval y := by
    change 0 < fs.prod.eval y
    rw [eval_list_prod]
    apply List.prod_pos
    intro v hv
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hv
    exact hpos f hf
  have hp0 : p ≠ 0 := by
    intro hp
    simp [hp] at hpEvalY
  obtain ⟨a0, ha0y, ha0Root⟩ := hleft
  obtain ⟨b0, hyb0, hb0Root⟩ := hright
  let leftRoots : Finset R := p.roots.toFinset.filter (fun t ↦ t < y)
  let rightRoots : Finset R := p.roots.toFinset.filter (fun t ↦ y < t)
  have hleftNonempty : leftRoots.Nonempty := by
    refine ⟨a0, Finset.mem_filter.mpr ⟨?_, ha0y⟩⟩
    exact Multiset.mem_toFinset.mpr ((mem_roots hp0).2 ha0Root)
  have hrightNonempty : rightRoots.Nonempty := by
    refine ⟨b0, Finset.mem_filter.mpr ⟨?_, hyb0⟩⟩
    exact Multiset.mem_toFinset.mpr ((mem_roots hp0).2 hb0Root)
  let a := leftRoots.max' hleftNonempty
  let b := rightRoots.min' hrightNonempty
  have haData := Finset.mem_filter.mp (leftRoots.max'_mem hleftNonempty)
  have hbData := Finset.mem_filter.mp (rightRoots.min'_mem hrightNonempty)
  have haRoot : p.IsRoot a :=
    (mem_roots hp0).1 (Multiset.mem_toFinset.mp haData.1)
  have hbRoot : p.IsRoot b :=
    (mem_roots hp0).1 (Multiset.mem_toFinset.mp hbData.1)
  have hay : a < y := haData.2
  have hyb : y < b := hbData.2
  have hconsecutive : ∀ t ∈ Ioo a b, ¬p.IsRoot t := by
    intro t ht htRoot
    by_cases hty : t < y
    · have htMem : t ∈ leftRoots := Finset.mem_filter.mpr ⟨
        Multiset.mem_toFinset.mpr ((mem_roots hp0).2 htRoot), hty⟩
      have hta : t ≤ a := leftRoots.le_max' t htMem
      exact (not_lt_of_ge hta) ht.1
    by_cases hyt : y < t
    · have htMem : t ∈ rightRoots := Finset.mem_filter.mpr ⟨
        Multiset.mem_toFinset.mpr ((mem_roots hp0).2 htRoot), hyt⟩
      have hbt : b ≤ t := rightRoots.min'_le t htMem
      exact (not_lt_of_ge hbt) ht.2
    · have htyEq : t = y := le_antisymm (le_of_not_gt hyt) (le_of_not_gt hty)
      exact hpEvalY.ne' (by simpa [htyEq] using htRoot.eq_zero)
  obtain ⟨z, hz, hzRoot⟩ :=
    exists_derivative_isRoot_mem_Ioo_of_consecutive_roots hp0 (hay.trans hyb)
      haRoot hbRoot hconsecutive
  refine ⟨z, ?_, ?_⟩
  · simpa [p] using hzRoot
  · intro f hf
    have hf0 : f ≠ 0 := by
      intro hfzero
      simpa [hfzero] using hpos f hf
    have hfRootToP {t : R} (ht : f.IsRoot t) : p.IsRoot t := by
      exact ht.dvd (by simpa [p] using List.dvd_prod hf)
    by_cases hyz : y ≤ z
    · have hfNoRoot : ∀ t ∈ Icc y z, ¬f.IsRoot t := by
        intro t ht htRoot
        exact hconsecutive t
          ⟨hay.trans_le ht.1, ht.2.trans_lt hz.2⟩ (hfRootToP htRoot)
      have hsame := eval_mul_pos_of_no_root_between hf0 hyz hfNoRoot
      nlinarith [hpos f hf]
    · have hzy : z ≤ y := le_of_not_ge hyz
      have hfNoRoot : ∀ t ∈ Icc z y, ¬f.IsRoot t := by
        intro t ht htRoot
        exact hconsecutive t
          ⟨hz.1.trans_le ht.1, ht.2.trans_lt hyb⟩ (hfRootToP htRoot)
      have hsame := eval_mul_pos_of_no_root_between hf0 hzy hfNoRoot
      nlinarith [hpos f hf]

end OptimalConvergenceRates.KrivineStengle

end
