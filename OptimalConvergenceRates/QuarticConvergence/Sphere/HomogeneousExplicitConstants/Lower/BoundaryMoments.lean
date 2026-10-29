import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.Pseudoexpectation
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.ParityBoundary

/-! Signed Gram moments obtained from short parity-boundary witnesses. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Foundation

open scoped BigOperators symmDiff

variable {E V : Type*} [DecidableEq E] [DecidableEq V] [Fintype V]

/-- A witness moment is its edge-label product; boundaries with no short
witness have zero moment. The expansion lemmas establish witness uniqueness. -/
def boundaryMoment (bd : Finset E → Finset V) (K : ℕ) (sign : E → ℝ)
    (D : Finset V) : ℝ := by
  classical
  exact if h : ∃ A, IsBoundaryWitness bd K D A then
    booleanCharacter sign (Classical.choose h)
  else 0

omit [Fintype V] in
theorem boundaryMoment_eq_of_witness
    (bd : Finset E → Finset V) (K : ℕ) (sign : E → ℝ)
    (bd_symmDiff : ∀ A B, bd (A ∆ B) = bd A ∆ bd B)
    (expand : BoundaryExpansion bd K)
    {D : Finset V} {A : Finset E} (hA : IsBoundaryWitness bd K D A) :
    boundaryMoment bd K sign D = booleanCharacter sign A := by
  classical
  have hex : ∃ B, IsBoundaryWitness bd K D B := ⟨A, hA⟩
  unfold boundaryMoment
  rw [dite_eq_left hex]
  have hchosen : Classical.choose hex = A :=
    boundary_witness_unique bd K bd_symmDiff expand (Classical.choose_spec hex) hA
  rw [hchosen]

omit [Fintype V] in
theorem boundaryMoment_empty
    (bd : Finset E → Finset V) (K : ℕ) (sign : E → ℝ)
    (bd_empty : bd ∅ = ∅)
    (bd_symmDiff : ∀ A B, bd (A ∆ B) = bd A ∆ bd B)
    (expand : BoundaryExpansion bd K) : boundaryMoment bd K sign ∅ = 1 := by
  rw [boundaryMoment_eq_of_witness bd K sign bd_symmDiff expand
    (A := ∅) ⟨by simp, bd_empty⟩]
  exact booleanCharacter_empty sign

/-- The concrete low-degree moment matrix consists of signed rank-one
blocks. Representatives are ordinary quotient choices; no sign consistency
or positive-functional premise is assumed. -/
theorem boundaryMoment_signedBlocks
    (bd : Finset E → Finset V) (K : ℕ) (sign : E → ℝ)
    (hsign : ∀ e, sign e ^ 2 = 1)
    (bd_empty : bd ∅ = ∅)
    (bd_symmDiff : ∀ A B, bd (A ∆ B) = bd A ∆ bd B)
    (expand : BoundaryExpansion bd K) :
    ∃ (classOf : BooleanIndex V K → BooleanIndex V K)
      (weight : BooleanIndex V K → ℝ),
      ∀ S T, boundaryMoment bd K sign (S.val ∆ T.val) =
        signedBlockKernel classOf weight S T := by
  classical
  let rel := boundaryWitnessSetoid bd K bd_empty bd_symmDiff expand
  let q : BooleanIndex V K → Quotient rel := fun S ↦ Quotient.mk rel S
  let rep : BooleanIndex V K → BooleanIndex V K := fun S ↦ (q S).out
  have hrep (S : BooleanIndex V K) :
      BoundaryRelated bd K S.val (rep S).val := by
    exact Quotient.exact (Quotient.out_eq (q S)).symm
  have hclasses {S T : BooleanIndex V K} :
      rep S = rep T ↔ BoundaryRelated bd K S.val T.val := by
    constructor
    · intro h
      have hq : q S = q T := Quotient.out_inj.mp h
      exact Quotient.exact hq
    · intro h
      have hq : q S = q T := Quotient.sound h
      exact congrArg Quotient.out hq
  let A : BooleanIndex V K → Finset E := fun S ↦ Classical.choose (hrep S)
  have hw (S : BooleanIndex V K) :
      IsBoundaryWitness bd K (S.val ∆ (rep S).val) (A S) :=
    Classical.choose_spec (hrep S)
  let weight : BooleanIndex V K → ℝ := fun S ↦ booleanCharacter sign (A S)
  refine ⟨rep, weight, ?_⟩
  intro S T
  by_cases hclass : rep S = rep T
  · rw [signedBlockKernel, ite_eq_left hclass]
    have hsmall : (A S ∆ A T).card ≤ 8 * K := by
      have h := symmDiff_card_le (A S) (A T)
      have hS := (hw S).1
      have hT := (hw T).1
      omega
    have hboundary : bd (A S ∆ A T) = S.val ∆ T.val := by
      rw [bd_symmDiff, (hw S).2, (hw T).2, hclass]
      rw [symmDiff_symmDiff_symmDiff_comm]
      simp
    have hboundary_card : (bd (A S ∆ A T)).card ≤ 2 * K := by
      rw [hboundary]
      have h := symmDiff_card_le S.val T.val
      have hS := S.property
      have hT := T.property
      omega
    have hshrink := expand (A S ∆ A T) hsmall
    have hfour : (A S ∆ A T).card ≤ 4 * K := by omega
    rw [boundaryMoment_eq_of_witness bd K sign bd_symmDiff expand
      ⟨hfour, hboundary⟩]
    exact (booleanCharacter_mul sign hsign (A S) (A T)).symm
  · rw [signedBlockKernel, ite_eq_right hclass]
    unfold boundaryMoment
    apply dite_eq_right
    intro hex
    exact hclass (hclasses.mpr hex)

theorem boundaryMoment_gram
    (bd : Finset E → Finset V) (K : ℕ) (sign : E → ℝ)
    (hsign : ∀ e, sign e ^ 2 = 1)
    (bd_empty : bd ∅ = ∅)
    (bd_symmDiff : ∀ A B, bd (A ∆ B) = bd A ∆ bd B)
    (expand : BoundaryExpansion bd K) :
    ∃ u : BooleanIndex V K → BooleanIndex V K → ℝ,
      ∀ S T, boundaryMoment bd K sign (S.val ∆ T.val) = finiteGramKernel u S T := by
  classical
  obtain ⟨classOf, weight, hblocks⟩ :=
    boundaryMoment_signedBlocks bd K sign hsign bd_empty bd_symmDiff expand
  refine ⟨signedBlockFeature classOf weight, ?_⟩
  intro S T
  rw [hblocks, signedBlockKernel_eq_gram]

/-- The deterministic assembly of an actual degree-`2*K` positive functional.
It is conditional only on explicit finite boundary expansion and sign data. -/
def boundaryPseudoexpectation
    (bd : Finset E → Finset V) (K : ℕ) (sign : E → ℝ)
    (hsign : ∀ e, sign e ^ 2 = 1)
    (bd_empty : bd ∅ = ∅)
    (bd_symmDiff : ∀ A B, bd (A ∆ B) = bd A ∆ bd B)
    (expand : BoundaryExpansion bd K) : TruncatedBooleanPseudoexpectation V K where
  functional := (booleanMomentFunctional (boundaryMoment bd K sign)).comp
    (booleanDegreeSpace (2 * K)).subtype
  normalized := by
    change booleanMomentFunctional (boundaryMoment bd K sign) (fun _ ↦ 1) = 1
    rw [booleanMomentFunctional_one,
      boundaryMoment_empty bd K sign bd_empty bd_symmDiff expand]
  square_nonneg f hf := by
    obtain ⟨u, hgram⟩ := boundaryMoment_gram bd K sign hsign bd_empty bd_symmDiff expand
    exact booleanMomentFunctional_square_nonneg_of_gram _ K u hgram f hf

theorem boundaryPseudoexpectation_character
    (bd : Finset E → Finset V) (K : ℕ) (sign : E → ℝ)
    (hsign : ∀ e, sign e ^ 2 = 1)
    (bd_empty : bd ∅ = ∅)
    (bd_symmDiff : ∀ A B, bd (A ∆ B) = bd A ∆ bd B)
    (expand : BoundaryExpansion bd K) (D : Finset V) (hD : D.card ≤ 2 * K) :
    (boundaryPseudoexpectation bd K sign hsign bd_empty bd_symmDiff expand).functional
      ⟨cubeCharacter D, hasBooleanDegree_character (2 * K) D hD⟩ =
        boundaryMoment bd K sign D := by
  exact booleanMomentFunctional_character _ D

theorem boundaryPseudoexpectation_abs_le
    (bd : Finset E → Finset V) (K : ℕ) (sign : E → ℝ)
    (hsign : ∀ e, sign e ^ 2 = 1)
    (bd_empty : bd ∅ = ∅)
    (bd_symmDiff : ∀ A B, bd (A ∆ B) = bd A ∆ bd B)
    (expand : BoundaryExpansion bd K)
    (f : booleanDegreeSpace (I := V) (2 * K)) (B : ℝ)
    (hB : ∀ x, |f.val x| ≤ B) :
    |(boundaryPseudoexpectation bd K sign hsign bd_empty bd_symmDiff expand).functional f| ≤
      cubeSize V * B := by
  obtain ⟨u, hgram⟩ := boundaryMoment_gram bd K sign hsign bd_empty bd_symmDiff expand
  exact booleanMomentFunctional_abs_le_of_gram _ K
    (boundaryMoment_empty bd K sign bd_empty bd_symmDiff expand)
    u hgram f.val f.property B hB

/-- A singleton edge witnesses its own prescribed parity moment. -/
theorem parityBoundaryMoment_clause (edge : E → Finset V) (K : ℕ)
    (hK : 0 < K) (sign : E → ℝ)
    (expand : BoundaryExpansion (parityBoundary edge) K) (e : E) :
    boundaryMoment (parityBoundary edge) K sign (edge e) = sign e := by
  rw [boundaryMoment_eq_of_witness (parityBoundary edge) K sign
    (parityBoundary_symmDiff edge) expand (A := {e})]
  · exact booleanCharacter_singleton sign e
  · constructor
    · simp only [Finset.card_singleton]
      omega
    · exact parityBoundary_singleton edge e

def hypergraphPseudoexpectation (edge : E → Finset V) (K : ℕ) (sign : E → ℝ)
    (hsign : ∀ e, sign e ^ 2 = 1)
    (expand : BoundaryExpansion (parityBoundary edge) K) :
    TruncatedBooleanPseudoexpectation V K :=
  boundaryPseudoexpectation (parityBoundary edge) K sign hsign
    (parityBoundary_empty edge) (parityBoundary_symmDiff edge) expand

theorem hypergraphPseudoexpectation_clause (edge : E → Finset V) (K : ℕ)
    (hK : 0 < K) (sign : E → ℝ) (hsign : ∀ e, sign e ^ 2 = 1)
    (expand : BoundaryExpansion (parityBoundary edge) K)
    (e : E) (hdegree : (edge e).card ≤ 2 * K) :
    (hypergraphPseudoexpectation edge K sign hsign expand).functional
      ⟨cubeCharacter (edge e), hasBooleanDegree_character (2 * K) _ hdegree⟩ = sign e := by
  change booleanMomentFunctional (boundaryMoment (parityBoundary edge) K sign)
    (cubeCharacter (edge e)) = sign e
  rw [booleanMomentFunctional_character, parityBoundaryMoment_clause edge K hK sign expand e]

/-- The exact deterministic Boolean input, conditional on the expanding
triple system. The missing random existence theorem is not assumed away. -/
theorem exists_hypergraphPseudoexpectation (edge : E → Finset V) (K : ℕ)
    (hK : 0 < K) (sign : E → ℝ) (hsign : ∀ e, sign e ^ 2 = 1)
    (expand : BoundaryExpansion (parityBoundary edge) K)
    (hdegree : ∀ e, (edge e).card ≤ 2 * K) :
    ∃ P : TruncatedBooleanPseudoexpectation V K,
      (∀ e, P.functional
        ⟨cubeCharacter (edge e), hasBooleanDegree_character (2 * K) _ (hdegree e)⟩ = sign e) ∧
      ∀ (f : booleanDegreeSpace (I := V) (2 * K)) (B : ℝ),
        (∀ x, |f.val x| ≤ B) → |P.functional f| ≤ cubeSize V * B := by
  refine ⟨hypergraphPseudoexpectation edge K sign hsign expand, ?_, ?_⟩
  · intro e
    exact hypergraphPseudoexpectation_clause edge K hK sign hsign expand e (hdegree e)
  · intro f B hB
    exact boundaryPseudoexpectation_abs_le (parityBoundary edge) K sign hsign
      (parityBoundary_empty edge) (parityBoundary_symmDiff edge) expand f B hB

end Foundation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
