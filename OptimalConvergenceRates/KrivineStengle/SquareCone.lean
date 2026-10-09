/-
  OptimalConvergenceRates/KrivineStengle/SquareCone.lean

  Possibly improper square-closed subsemirings.
-/
import Mathlib.Order.Zorn
import Mathlib.Tactic.Ring

noncomputable section

namespace OptimalConvergenceRates.KrivineStengle

variable {R : Type*} [CommRing R]

/-- A possibly improper cone: a subsemiring containing every square. -/
structure IsSquareCone (P : Set R) : Prop where
  zero_mem : 0 ∈ P
  one_mem : 1 ∈ P
  add_mem : ∀ {x y}, x ∈ P → y ∈ P → x + y ∈ P
  mul_mem : ∀ {x y}, x ∈ P → y ∈ P → x * y ∈ P
  sq_mem : ∀ x, x ^ 2 ∈ P

/-- Properness is deliberately separate: intermediate certificate cones may be improper. -/
def IsProperSquareCone (P : Set R) : Prop :=
  IsSquareCone P ∧ -1 ∉ P

namespace IsSquareCone

theorem subset_adjoinSign {P : Set R} (hP : IsSquareCone P) (a : R) :
    P ⊆ {x | ∃ u ∈ P, ∃ v ∈ P, x = u + a * v} := by
  intro x hx
  exact ⟨x, hx, 0, hP.zero_mem, by ring⟩

/-- The cone obtained by adjoining one chosen sign. -/
def adjoinSign (P : Set R) (a : R) : Set R :=
  {x | ∃ u ∈ P, ∃ v ∈ P, x = u + a * v}

theorem mem_adjoinSign (hP : IsSquareCone P) (a : R) : a ∈ adjoinSign P a := by
  exact ⟨0, hP.zero_mem, 1, hP.one_mem, by ring⟩

theorem isSquareCone_adjoinSign (hP : IsSquareCone P) (a : R) :
    IsSquareCone (adjoinSign P a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨0, hP.zero_mem, 0, hP.zero_mem, by ring⟩
  · exact ⟨1, hP.one_mem, 0, hP.zero_mem, by ring⟩
  · rintro x y ⟨u, hu, v, hv, rfl⟩ ⟨w, hw, z, hz, rfl⟩
    exact ⟨u + w, hP.add_mem hu hw, v + z, hP.add_mem hv hz, by ring⟩
  · rintro x y ⟨u, hu, v, hv, rfl⟩ ⟨w, hw, z, hz, rfl⟩
    refine ⟨u * w + a ^ 2 * (v * z), hP.add_mem (hP.mul_mem hu hw) ?_,
      u * z + v * w, hP.add_mem (hP.mul_mem hu hz) (hP.mul_mem hv hw), ?_⟩
    · exact hP.mul_mem (hP.sq_mem a) (hP.mul_mem hv hz)
    · ring
  · intro x
    exact ⟨x ^ 2, hP.sq_mem x, 0, hP.zero_mem, by ring⟩

end IsSquareCone

/-- The union of a nonempty chain of proper square cones is again a proper square cone. -/
theorem isProperSquareCone_sUnion {c : Set (Set R)}
    (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty)
    (hproper : ∀ P ∈ c, IsProperSquareCone P) :
    IsProperSquareCone (Set.sUnion c) := by
  obtain ⟨P₀, hP₀⟩ := hne
  have hcone₀ := (hproper P₀ hP₀).1
  refine ⟨?_, ?_⟩
  · refine ⟨Set.mem_sUnion_of_mem hcone₀.zero_mem hP₀,
      Set.mem_sUnion_of_mem hcone₀.one_mem hP₀, ?_, ?_, ?_⟩
    · intro x y hx hy
      obtain ⟨P, hPc, hxP⟩ := Set.mem_sUnion.mp hx
      obtain ⟨Q, hQc, hyQ⟩ := Set.mem_sUnion.mp hy
      by_cases hPQeq : P = Q
      · subst Q
        exact Set.mem_sUnion_of_mem ((hproper P hPc).1.add_mem hxP hyQ) hPc
      rcases hc hPc hQc hPQeq with hPQ | hQP
      · exact Set.mem_sUnion_of_mem ((hproper Q hQc).1.add_mem (hPQ hxP) hyQ) hQc
      · exact Set.mem_sUnion_of_mem ((hproper P hPc).1.add_mem hxP (hQP hyQ)) hPc
    · intro x y hx hy
      obtain ⟨P, hPc, hxP⟩ := Set.mem_sUnion.mp hx
      obtain ⟨Q, hQc, hyQ⟩ := Set.mem_sUnion.mp hy
      by_cases hPQeq : P = Q
      · subst Q
        exact Set.mem_sUnion_of_mem ((hproper P hPc).1.mul_mem hxP hyQ) hPc
      rcases hc hPc hQc hPQeq with hPQ | hQP
      · exact Set.mem_sUnion_of_mem ((hproper Q hQc).1.mul_mem (hPQ hxP) hyQ) hQc
      · exact Set.mem_sUnion_of_mem ((hproper P hPc).1.mul_mem hxP (hQP hyQ)) hPc
    · intro x
      exact Set.mem_sUnion_of_mem ((hproper P₀ hP₀).1.sq_mem x) hP₀
  · intro hneg
    obtain ⟨P, hPc, hnegP⟩ := Set.mem_sUnion.mp hneg
    exact (hproper P hPc).2 hnegP

/-- Every proper square cone is contained in a maximal proper square cone. -/
theorem exists_maximal_isProperSquareCone {C : Set R} (hC : IsProperSquareCone C) :
    ∃ P, C ⊆ P ∧ Maximal (fun Q : Set R ↦ IsProperSquareCone Q ∧ C ⊆ Q) P := by
  let S : Set (Set R) := {P | IsProperSquareCone P ∧ C ⊆ P}
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ S, ∀ P ∈ c, P ⊆ ub := by
    intro c hcS hc hne
    refine ⟨Set.sUnion c, ?_, ?_⟩
    · refine ⟨isProperSquareCone_sUnion hc hne (fun P hP ↦ (hcS hP).1), ?_⟩
      obtain ⟨P, hP⟩ := hne
      exact (hcS hP).2.trans (Set.subset_sUnion_of_mem hP)
    · intro P hP
      exact Set.subset_sUnion_of_mem hP
  obtain ⟨P, hCP, hmax⟩ := zorn_subset_nonempty S hchain C ⟨hC, Set.Subset.rfl⟩
  exact ⟨P, hCP, hmax⟩

end OptimalConvergenceRates.KrivineStengle

end
