import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Tactic
/-!
# The actual parity boundary of an indexed hypergraph

The boundary is the finite sum of edge vertex sets in the Boolean ring
`AsBoolRing (Finset V)`. Addition in this ring is symmetric difference.
Consequently a vertex toggles its membership once per incident edge.
This realizes the boundary map required by `BoundaryWitness.lean`.
-/

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Foundation

open scoped BigOperators symmDiff

section BooleanRingSum

variable {E R : Type*} [DecidableEq E] [BooleanRing R]

/-- A finite sum in a Boolean ring respects symmetric differences of its
index sets: the terms in their intersection occur twice and cancel. -/
theorem booleanRing_sum_symmDiff (f : E → R) (S T : Finset E) :
    (∑ e ∈ S ∆ T, f e) = (∑ e ∈ S, f e) + ∑ e ∈ T, f e := by
  have hS : (∑ e ∈ S \ T, f e) + (∑ e ∈ S ∩ T, f e) =
      ∑ e ∈ S, f e := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S T), Finset.sdiff_union_inter]
  have hT : (∑ e ∈ T \ S, f e) + (∑ e ∈ S ∩ T, f e) =
      ∑ e ∈ T, f e := by
    rw [Finset.inter_comm S T]
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter T S), Finset.sdiff_union_inter]
  have hdis : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro e heS heT
    exact (Finset.mem_sdiff.mp heS).2 (Finset.mem_sdiff.mp heT).1
  have hsets : S ∆ T = (S \ T) ∪ (T \ S) := by
    ext e
    simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
  have hsum : (∑ e ∈ S ∆ T, f e) =
      (∑ e ∈ S \ T, f e) + ∑ e ∈ T \ S, f e := by
    rw [hsets, Finset.sum_union hdis]
  symm
  calc
    (∑ e ∈ S, f e) + (∑ e ∈ T, f e) =
        ((∑ e ∈ S \ T, f e) + (∑ e ∈ T \ S, f e)) +
          ((∑ e ∈ S ∩ T, f e) + ∑ e ∈ S ∩ T, f e) := by
      rw [← hS, ← hT]
      abel
    _ = (∑ e ∈ S \ T, f e) + ∑ e ∈ T \ S, f e := by
      rw [BooleanRing.add_self, add_zero]
    _ = ∑ e ∈ S ∆ T, f e := hsum.symm

end BooleanRingSum

section HypergraphBoundary

variable {E V : Type*} [DecidableEq E] [DecidableEq V]

/-- The parity boundary of an edge subset, with edges allowed to repeat
as vertex sets because their indices are distinct. -/
def parityBoundary (edge : E → Finset V) (A : Finset E) : Finset V :=
  ofBoolRing (∑ e ∈ A, (toBoolRing (edge e) : AsBoolRing (Finset V)))

omit [DecidableEq E] in
@[simp] theorem parityBoundary_empty (edge : E → Finset V) :
    parityBoundary edge ∅ = ∅ := by
  simp only [parityBoundary, Finset.sum_empty]
  rfl

omit [DecidableEq E] in
@[simp] theorem parityBoundary_singleton (edge : E → Finset V) (e : E) :
    parityBoundary edge {e} = edge e := by
  simp [parityBoundary]

variable [Fintype V]

/-- This is the symmetric-difference law in the abstract witness interface. -/
theorem parityBoundary_symmDiff (edge : E → Finset V) (A B : Finset E) :
    parityBoundary edge (A ∆ B) =
      parityBoundary edge A ∆ parityBoundary edge B := by
  unfold parityBoundary
  rw [booleanRing_sum_symmDiff, ofBoolRing_add]

/-- Adding a new indexed edge toggles precisely that edge's vertex set. -/
theorem parityBoundary_insert (edge : E → Finset V) (e : E) (A : Finset E)
    (he : e ∉ A) :
    parityBoundary edge (insert e A) = edge e ∆ parityBoundary edge A := by
  simp [parityBoundary, Finset.sum_insert he, ofBoolRing_add]

theorem parityBoundary_disjoint_union (edge : E → Finset V) (A B : Finset E)
    (h : Disjoint A B) :
    parityBoundary edge (A ∪ B) =
      parityBoundary edge A ∆ parityBoundary edge B := by
  unfold parityBoundary
  rw [Finset.sum_union h, ofBoolRing_add]

/-- Membership in the boundary toggles exactly when a newly added edge
contains the vertex. This recurrence is the finite parity interpretation. -/
theorem mem_parityBoundary_insert (edge : E → Finset V) (e : E) (A : Finset E)
    (he : e ∉ A) (v : V) :
    v ∈ parityBoundary edge (insert e A) ↔
      (v ∈ edge e ∧ v ∉ parityBoundary edge A) ∨
        (v ∈ parityBoundary edge A ∧ v ∉ edge e) := by
  rw [parityBoundary_insert edge e A he]
  exact Finset.mem_symmDiff

/-- No vertex outside the union of the selected edges can lie in the boundary. -/
theorem parityBoundary_subset_biUnion (edge : E → Finset V) (A : Finset E) :
    parityBoundary edge A ⊆ A.biUnion edge := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert e A he ih =>
      rw [parityBoundary_insert edge e A he, Finset.biUnion_insert]
      intro v hv
      rcases Finset.mem_symmDiff.mp hv with h | h
      · exact Finset.mem_union.mpr (Or.inl h.1)
      · exact Finset.mem_union.mpr (Or.inr (ih h.1))

end HypergraphBoundary

end Foundation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
