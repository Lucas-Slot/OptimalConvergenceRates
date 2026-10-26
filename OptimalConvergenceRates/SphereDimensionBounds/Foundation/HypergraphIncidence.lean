import OptimalConvergenceRates.SphereDimensionBounds.Foundation.ParityBoundary
import OptimalConvergenceRates.SphereDimensionBounds.Foundation.BoundaryWitness

/-! Incidence counting connects support growth to parity-boundary expansion. -/

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

open scoped BigOperators

variable {E V : Type*} [DecidableEq E] [DecidableEq V] [Fintype V]

def incidenceCount (edge : E → Finset V) (A : Finset E) (v : V) : ℕ :=
  (A.filter (fun e => v ∈ edge e)).card

omit [Fintype V] in
theorem incidenceCount_insert (edge : E → Finset V) (A : Finset E) (e : E)
    (he : e ∉ A) (v : V) :
    incidenceCount edge (insert e A) v =
      if v ∈ edge e then incidenceCount edge A v + 1 else incidenceCount edge A v := by
  by_cases hv : v ∈ edge e
  · simp [incidenceCount, Finset.filter_insert, hv, he, Nat.add_comm]
  · simp [incidenceCount, Finset.filter_insert, hv]

theorem mem_parityBoundary_iff_odd_incidence (edge : E → Finset V) (A : Finset E) (v : V) :
    v ∈ parityBoundary edge A ↔ Odd (incidenceCount edge A v) := by
  induction A using Finset.induction_on with
  | empty => simp [incidenceCount]
  | @insert e A he ih =>
      rw [parityBoundary_insert edge e A he, Finset.mem_symmDiff,
        incidenceCount_insert edge A e he v]
      by_cases hv : v ∈ edge e
      · simp [hv, ih, Nat.odd_add_one]
      · simp [hv, ih]

omit [DecidableEq E] [Fintype V] in
theorem incidenceCount_pos_of_mem_support (edge : E → Finset V) (A : Finset E) {v : V}
    (hv : v ∈ A.biUnion edge) : 0 < incidenceCount edge A v := by
  obtain ⟨e, he, hv⟩ := Finset.mem_biUnion.mp hv
  exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hv⟩⟩

omit [DecidableEq E] in
theorem sum_incidenceCount (edge : E → Finset V) (A : Finset E) :
    (∑ v : V, incidenceCount edge A v) = ∑ e ∈ A, (edge e).card := by
  calc
    (∑ v : V, incidenceCount edge A v) =
        ∑ v : V, ∑ e ∈ A, if v ∈ edge e then 1 else 0 := by
      simp [incidenceCount]
    _ = ∑ e ∈ A, ∑ v : V, if v ∈ edge e then 1 else 0 := Finset.sum_comm
    _ = ∑ e ∈ A, (edge e).card := by simp

theorem parityBoundary_incidence_lower (edge : E → Finset V) (A : Finset E) :
    2 * (A.biUnion edge).card ≤
      (∑ e ∈ A, (edge e).card) + (parityBoundary edge A).card := by
  have hpoint (v : V) :
      2 * (if v ∈ A.biUnion edge then 1 else 0) ≤
        incidenceCount edge A v + (if v ∈ parityBoundary edge A then 1 else 0) := by
    by_cases hv : v ∈ A.biUnion edge
    · have hdpos := incidenceCount_pos_of_mem_support edge A hv
      by_cases hd : incidenceCount edge A v = 1
      · have hb : v ∈ parityBoundary edge A :=
          (mem_parityBoundary_iff_odd_incidence edge A v).mpr (by simp [hd])
        simp [hv, hd, hb]
      · have hdlarge : 2 ≤ incidenceCount edge A v := by omega
        split_ifs <;> omega
    · simp [hv]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun v _ => hpoint v)
  have hleft : (∑ v : V, 2 * (if v ∈ A.biUnion edge then 1 else 0)) =
      2 * (A.biUnion edge).card := by
    rw [← Finset.mul_sum]
    simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Nat.cast_id]
  have hright :
      (∑ v : V, (incidenceCount edge A v + (if v ∈ parityBoundary edge A then 1 else 0))) =
        (∑ e ∈ A, (edge e).card) + (parityBoundary edge A).card := by
    rw [Finset.sum_add_distrib, sum_incidenceCount]
    simp
  simpa only [hleft, hright] using hsum

theorem triple_parityBoundary_lower (edge : E → Finset V)
    (htriple : ∀ e, (edge e).card = 3) (A : Finset E) :
    2 * (A.biUnion edge).card ≤ 3 * A.card + (parityBoundary edge A).card := by
  simpa [htriple, Nat.mul_comm] using parityBoundary_incidence_lower edge A

theorem boundaryExpansion_of_support_growth (edge : E → Finset V)
    (htriple : ∀ e, (edge e).card = 3) (K : ℕ)
    (hgrowth : ∀ A : Finset E, A.Nonempty → A.card ≤ 8 * K →
      7 * A.card < 4 * (A.biUnion edge).card) :
    BoundaryExpansion (parityBoundary edge) K := by
  intro A hA
  by_cases he : A = ∅
  · simp [he]
  · have hg := hgrowth A (Finset.nonempty_iff_ne_empty.mpr he) hA
    have hb := triple_parityBoundary_lower edge htriple A
    omega

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
