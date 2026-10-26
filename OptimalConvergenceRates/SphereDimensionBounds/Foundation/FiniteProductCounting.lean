import Mathlib.Tactic
/-! Exact finite-product counts and a counting form of the union bound. -/

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

open scoped BigOperators

section

variable {E T : Type*} [Fintype E] [Fintype T] [DecidableEq E] [DecidableEq T]

def constrainedFunctions (A : Finset E) (W : Finset T) : Finset (E → T) :=
  Fintype.piFinset (fun e => if e ∈ A then W else Finset.univ)

omit [DecidableEq T] in
theorem mem_constrainedFunctions (A : Finset E) (W : Finset T) (f : E → T) :
    f ∈ constrainedFunctions A W ↔ ∀ e ∈ A, f e ∈ W := by
  simp only [constrainedFunctions, Fintype.mem_piFinset]
  constructor
  · intro h e he
    simpa [he] using h e
  · intro h e
    by_cases he : e ∈ A
    · simpa [he] using h e he
    · simp [he]

omit [DecidableEq T] in
theorem card_constrainedFunctions (A : Finset E) (W : Finset T) :
    (constrainedFunctions A W).card =
      W.card ^ A.card * Fintype.card T ^ (Fintype.card E - A.card) := by
  classical
  simp only [constrainedFunctions, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, Finset.card_univ]
  rw [Finset.prod_ite]
  simp [Finset.filter_not, Finset.filter_mem_eq_inter,
    Finset.card_sdiff]

variable {Z : Type*} [Fintype Z]

/-- If the sum of all cylinder-event cardinalities is smaller than the full
sample space, some sample avoids every event. Every count is an exact natural
number; no probabilistic oracle or external computation is used. -/
theorem exists_avoiding_cylinders (A : Z → Finset E) (W : Z → Finset T)
    (budget : (∑ z : Z,
      (W z).card ^ (A z).card * Fintype.card T ^ (Fintype.card E - (A z).card)) <
        Fintype.card T ^ Fintype.card E) :
    ∃ f : E → T, ∀ z : Z, ¬(∀ e ∈ A z, f e ∈ W z) := by
  classical
  by_contra hno
  push_neg at hno
  let bad : Finset (E → T) := Finset.univ.biUnion (fun z => constrainedFunctions (A z) (W z))
  have hcover : (Finset.univ : Finset (E → T)) ⊆ bad := by
    intro f hf
    obtain ⟨z, hz⟩ := hno f
    exact Finset.mem_biUnion.mpr ⟨z, Finset.mem_univ z,
      (mem_constrainedFunctions (A z) (W z) f).mpr hz⟩
  have hupper : bad.card ≤ ∑ z : Z,
      (W z).card ^ (A z).card * Fintype.card T ^ (Fintype.card E - (A z).card) := by
    exact (Finset.card_biUnion_le).trans_eq (by simp only [card_constrainedFunctions])
  have hlower : Fintype.card T ^ Fintype.card E ≤ bad.card := by
    simpa [Fintype.card_fun] using Finset.card_le_card hcover
  exact (not_le_of_gt budget) (hlower.trans hupper)

end

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
