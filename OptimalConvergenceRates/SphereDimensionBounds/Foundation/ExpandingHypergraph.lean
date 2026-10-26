import OptimalConvergenceRates.SphereDimensionBounds.Foundation.FiniteProductCounting
import OptimalConvergenceRates.SphereDimensionBounds.Foundation.HypergraphIncidence

/-!
# Finite counting construction of expanding indexed triple systems

The combinatorial theorem is conditional on an explicit natural-number
counting inequality. That budget is a numerical obligation, not the
existence of an expanding graph or a pseudoexpectation.
-/

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

open scoped BigOperators

abbrev Triple (N : ℕ) := { S : Finset (Fin N) // S.card = 3 }

@[simp] theorem card_triple (N : ℕ) : Fintype.card (Triple N) = N.choose 3 := by
  simp [Triple, Fintype.card_finset_len]

/-- The allowed alphabet for an obstruction supported on a vertex set. -/
def containedTriples {N : ℕ} (W : Finset (Fin N)) : Finset (Triple N) :=
  Finset.univ.filter (fun T => T.val ⊆ W)

@[simp] theorem mem_containedTriples {N : ℕ} (W : Finset (Fin N)) (T : Triple N) :
    T ∈ containedTriples W ↔ T.val ⊆ W := by
  simp [containedTriples]

@[simp] theorem card_containedTriples {N : ℕ} (W : Finset (Fin N)) :
    (containedTriples W).card = W.card.choose 3 := by
  have hcard : (containedTriples W).card = (W.powersetCard 3).card := by
    apply Finset.card_bij (fun T _ => T.val)
    · intro T hT
      exact Finset.mem_powersetCard.mpr ⟨(mem_containedTriples W T).mp hT, T.property⟩
    · intro S hS T hT hST
      exact Subtype.ext hST
    · intro S hS
      refine ⟨⟨S, (Finset.mem_powersetCard.mp hS).2⟩, ?_, rfl⟩
      exact (mem_containedTriples _ _).mpr (Finset.mem_powersetCard.mp hS).1
  rw [hcard, Finset.card_powersetCard]

abbrev TripleObstruction (N s : ℕ) :=
  Σ a : Fin s,
    { A : Finset (Fin (8 * N)) // A.card = a.val + 1 } ×
      { W : Finset (Fin N) // W.card = 7 * (a.val + 1) / 4 }

def obstructionEdges {N s : ℕ} (z : TripleObstruction N s) : Finset (Fin (8 * N)) :=
  z.2.1.val

def obstructionVertices {N s : ℕ} (z : TripleObstruction N s) : Finset (Fin N) :=
  z.2.2.val

def tripleSystemCountingBudget (N s : ℕ) : ℕ :=
  ∑ a : Fin s,
    (8 * N).choose (a.val + 1) * N.choose (7 * (a.val + 1) / 4) *
      ((7 * (a.val + 1) / 4).choose 3 ^ (a.val + 1) *
        N.choose 3 ^ (8 * N - (a.val + 1)))

/-- Exact reindexing of all obstruction cylinders by their edge-set size. -/
theorem tripleObstruction_count (N s : ℕ) :
    (∑ z : TripleObstruction N s,
      (containedTriples (obstructionVertices z)).card ^ (obstructionEdges z).card *
        Fintype.card (Triple N) ^ (8 * N - (obstructionEdges z).card)) =
      tripleSystemCountingBudget N s := by
  classical
  rw [Fintype.sum_sigma]
  unfold tripleSystemCountingBudget
  apply Finset.sum_congr rfl
  intro a ha
  rw [Fintype.sum_prod_type]
  have hterm
      (A : { A : Finset (Fin (8 * N)) // A.card = a.val + 1 })
      (W : { W : Finset (Fin N) // W.card = 7 * (a.val + 1) / 4 }) :
      (containedTriples W.val).card ^ A.val.card *
        Fintype.card (Triple N) ^ (8 * N - A.val.card) =
      (7 * (a.val + 1) / 4).choose 3 ^ (a.val + 1) *
        N.choose 3 ^ (8 * N - (a.val + 1)) := by
    rw [card_containedTriples, A.property, W.property, card_triple]
  change (∑ A : { A : Finset (Fin (8 * N)) // A.card = a.val + 1 },
    ∑ W : { W : Finset (Fin N) // W.card = 7 * (a.val + 1) / 4 },
      (containedTriples W.val).card ^ A.val.card *
        Fintype.card (Triple N) ^ (8 * N - A.val.card)) = _
  simp_rw [hterm]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_finset_len, Fintype.card_fin, Nat.cast_id]
  ring

/-- An explicit count smaller than the sample space yields a triple system
with uniform small-edge-set support growth. All samples and events are finite. -/
theorem exists_tripleSystem_support_growth_of_budget (N s : ℕ)
    (hvertex : ∀ a : Fin s, 7 * (a.val + 1) / 4 ≤ N)
    (budget : tripleSystemCountingBudget N s < N.choose 3 ^ (8 * N)) :
    ∃ edge : Fin (8 * N) → Finset (Fin N),
      (∀ e, (edge e).card = 3) ∧
      ∀ A : Finset (Fin (8 * N)), A.Nonempty → A.card ≤ s →
        7 * A.card < 4 * (A.biUnion edge).card := by
  classical
  have hbudget :
      (∑ z : TripleObstruction N s,
        (containedTriples (obstructionVertices z)).card ^ (obstructionEdges z).card *
          Fintype.card (Triple N) ^
            (Fintype.card (Fin (8 * N)) - (obstructionEdges z).card)) <
        Fintype.card (Triple N) ^ Fintype.card (Fin (8 * N)) := by
    simp only [Fintype.card_fin]
    rw [tripleObstruction_count, card_triple]
    exact budget
  obtain ⟨f, hf⟩ := exists_avoiding_cylinders
    (fun z : TripleObstruction N s => obstructionEdges z)
    (fun z => containedTriples (obstructionVertices z)) hbudget
  let edge : Fin (8 * N) → Finset (Fin N) := fun e => (f e).val
  refine ⟨edge, fun e => (f e).property, ?_⟩
  intro A hA hAs
  by_contra hgrowth
  have hApos : 0 < A.card := Finset.card_pos.mpr hA
  let a : Fin s := ⟨A.card - 1, by omega⟩
  have ha : a.val + 1 = A.card := by dsimp [a]; omega
  have hsmall : (A.biUnion edge).card ≤ 7 * (a.val + 1) / 4 := by
    rw [ha]
    omega
  obtain ⟨W, hAW, _hWuniv, hWcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (A.biUnion edge)) hsmall
    (by simpa using hvertex a)
  let z : TripleObstruction N s := ⟨a, ⟨⟨A, ha.symm⟩, ⟨W, hWcard⟩⟩⟩
  apply hf z
  change ∀ e ∈ A, f e ∈ containedTriples W
  intro e he
  apply (mem_containedTriples W (f e)).mpr
  intro v hv
  exact hAW (Finset.mem_biUnion.mpr ⟨e, he, hv⟩)

theorem exists_tripleSystem_boundary_expansion_of_budget (N K : ℕ)
    (hvertex : ∀ a : Fin (8 * K), 7 * (a.val + 1) / 4 ≤ N)
    (budget : tripleSystemCountingBudget N (8 * K) < N.choose 3 ^ (8 * N)) :
    ∃ edge : Fin (8 * N) → Finset (Fin N),
      (∀ e, (edge e).card = 3) ∧ BoundaryExpansion (parityBoundary edge) K := by
  obtain ⟨edge, harity, hgrowth⟩ :=
    exists_tripleSystem_support_growth_of_budget N (8 * K) hvertex budget
  exact ⟨edge, harity, boundaryExpansion_of_support_growth edge harity K hgrowth⟩

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
