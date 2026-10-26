import Mathlib.Tactic
/-!
# Short boundary witnesses and their equivalence relation

The boundary map and its expansion property are explicit hypotheses of
the deterministic lemmas here. `ParityBoundary` constructs the parity
boundary of a triple system, and `ExpandingHypergraph` supplies the
required expansion property.
-/

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

open scoped symmDiff

section Cardinality

variable {α : Type*} [DecidableEq α]

/-- A symmetric difference contains no more elements than the two sets together. -/
theorem symmDiff_card_le (S T : Finset α) :
    (S ∆ T).card ≤ S.card + T.card := by
  have hsub : S ∆ T ⊆ S ∪ T := by
    intro i hi
    rcases Finset.mem_symmDiff.mp hi with h | h
    · exact Finset.mem_union.mpr (Or.inl h.1)
    · exact Finset.mem_union.mpr (Or.inr h.1)
  calc
    (S ∆ T).card ≤ (S ∪ T).card := Finset.card_le_card hsub
    _ ≤ S.card + T.card := Finset.card_union_le S T

end Cardinality

section Witnesses

variable {E V : Type*} [DecidableEq E] [DecidableEq V]

/-- Expansion through `8*K` edges, including the empty edge set.
The usual nonempty expansion inequality implies this version immediately. -/
def BoundaryExpansion (bd : Finset E → Finset V) (K : ℕ) : Prop :=
  ∀ A, A.card ≤ 8 * K → A.card ≤ 2 * (bd A).card

/-- A short edge set representing a specified parity boundary. -/
def IsBoundaryWitness (bd : Finset E → Finset V) (K : ℕ)
    (D : Finset V) (A : Finset E) : Prop :=
  A.card ≤ 4 * K ∧ bd A = D

/-- Vertex sets are related if their symmetric difference has a short witness. -/
def BoundaryRelated (bd : Finset E → Finset V) (K : ℕ)
    (S T : Finset V) : Prop :=
  ∃ A, IsBoundaryWitness bd K (S ∆ T) A

/-- Two short witnesses for one boundary must coincide. The symmetric
difference lies in the expansion range and has empty boundary. -/
theorem boundary_witness_unique (bd : Finset E → Finset V) (K : ℕ)
    (bd_symmDiff : ∀ A B, bd (A ∆ B) = bd A ∆ bd B)
    (expand : BoundaryExpansion bd K)
    {D : Finset V} {A B : Finset E}
    (hA : IsBoundaryWitness bd K D A)
    (hB : IsBoundaryWitness bd K D B) : A = B := by
  have hAcard : A.card ≤ 4 * K := hA.1
  have hBcard : B.card ≤ 4 * K := hB.1
  have hsmall : (A ∆ B).card ≤ 8 * K := by
    have h := symmDiff_card_le A B
    omega
  have hzero : bd (A ∆ B) = ∅ := by
    rw [bd_symmDiff, hA.2, hB.2]
    simp
  have hcard := expand (A ∆ B) hsmall
  have hempty : A ∆ B = ∅ := by
    apply Finset.card_eq_zero.mp
    rw [hzero, Finset.card_empty] at hcard
    omega
  exact Finset.symmDiff_eq_empty.mp hempty

omit [DecidableEq E] in
/-- The empty edge set witnesses each reflexive pair. -/
theorem boundary_related_refl (bd : Finset E → Finset V) (K : ℕ)
    (bd_empty : bd ∅ = ∅) (S : Finset V) :
    BoundaryRelated bd K S S := by
  refine ⟨∅, ?_, ?_⟩
  · simp
  · simpa using bd_empty

omit [DecidableEq E] in
/-- The witness for a pair also witnesses its reversal. -/
theorem boundary_related_symm (bd : Finset E → Finset V) (K : ℕ)
    {S T : Finset V} (h : BoundaryRelated bd K S T) :
    BoundaryRelated bd K T S := by
  rcases h with ⟨A, hAcard, hAbd⟩
  exact ⟨A, hAcard, hAbd.trans (symmDiff_comm S T)⟩

/-- Two composable witnesses initially have size at most `8*K`. Their
boundary has size at most `2*K`, so expansion shrinks their symmetric
difference to size at most `4*K`, making it an admissible witness.
Only the endpoint cardinalities are needed for this argument. -/
theorem boundary_related_trans (bd : Finset E → Finset V) (K : ℕ)
    (bd_symmDiff : ∀ A B, bd (A ∆ B) = bd A ∆ bd B)
    (expand : BoundaryExpansion bd K)
    {S T U : Finset V} (hS : S.card ≤ K) (hU : U.card ≤ K)
    (hST : BoundaryRelated bd K S T)
    (hTU : BoundaryRelated bd K T U) :
    BoundaryRelated bd K S U := by
  rcases hST with ⟨A, hAcard, hAbd⟩
  rcases hTU with ⟨B, hBcard, hBbd⟩
  have hsmall : (A ∆ B).card ≤ 8 * K := by
    have h := symmDiff_card_le A B
    omega
  have hboundary : bd (A ∆ B) = S ∆ U := by
    rw [bd_symmDiff, hAbd, hBbd]
    rw [symmDiff_assoc, symmDiff_symmDiff_cancel_left]
  have hboundary_card : (bd (A ∆ B)).card ≤ 2 * K := by
    rw [hboundary]
    have h := symmDiff_card_le S U
    omega
  have hshrink := expand (A ∆ B) hsmall
  refine ⟨A ∆ B, ?_, hboundary⟩
  omega

/-- The actual equivalence relation is restricted to vertex subsets of size
at most `K`. No finiteness assumption on the ambient vertex type is needed. -/
def boundaryWitnessSetoid (bd : Finset E → Finset V) (K : ℕ)
    (bd_empty : bd ∅ = ∅)
    (bd_symmDiff : ∀ A B, bd (A ∆ B) = bd A ∆ bd B)
    (expand : BoundaryExpansion bd K) :
    Setoid { S : Finset V // S.card ≤ K } where
  r S T := BoundaryRelated bd K S.val T.val
  iseqv :=
    { refl := fun S => boundary_related_refl bd K bd_empty S.val
      symm := fun h => boundary_related_symm bd K h
      trans := fun {S _T U} hST hTU =>
        boundary_related_trans bd K bd_symmDiff expand S.property U.property hST hTU }

end Witnesses

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
