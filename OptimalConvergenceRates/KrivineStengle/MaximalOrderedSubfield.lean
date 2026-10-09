/-
  OptimalConvergenceRates/KrivineStengle/MaximalOrderedSubfield.lean

  Maximal orderable intermediate fields inside a fixed algebraic closure.
-/
import OptimalConvergenceRates.KrivineStengle.OrderExtension
import OptimalConvergenceRates.KrivineStengle.WeightedSquares
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Order.Zorn

noncomputable section

namespace OptimalConvergenceRates.KrivineStengle

universe u v w

variable (F : Type u) [Field F] [LinearOrder F] [IsStrictOrderedRing F]

namespace WeightedSquareRep

/-- Finite weighted sums of squares are preserved by base-algebra homomorphisms. -/
theorem map {L : Type v} {K : Type w} [Field L] [Field K] [Algebra F L] [Algebra F K]
    {z : L} (hz : WeightedSquareRep F L z) (i : L →ₐ[F] K) :
    WeightedSquareRep F K (i z) := by
  induction hz with
  | zero => simpa using zero (F := F) (L := K)
  | add hx hy ihx ihy => simpa only [map_add] using add ihx ihy
  | term c hc z =>
      simpa only [map_mul, map_pow, i.commutes] using term (F := F) (L := K) c hc (i z)

end WeightedSquareRep

variable {A : Type v} [Field A] [Algebra F A]

private theorem weightedSquareRep_iSup_chain
    (c : Set (IntermediateField F A)) (hc : IsChain (· ≤ ·) c) (hcne : c.Nonempty)
    {z : ↥(⨆ E : c, (E : IntermediateField F A))}
    (hz : WeightedSquareRep F ↥(⨆ E : c, (E : IntermediateField F A)) z) :
    ∃ E : c, ∃ x : (E : IntermediateField F A),
      WeightedSquareRep F (E : IntermediateField F A) x ∧
        IntermediateField.inclusion
          (le_iSup (fun E : c ↦ (E : IntermediateField F A)) E) x = z := by
  let t : c → IntermediateField F A := fun E ↦ E
  letI : Nonempty c := hcne.to_subtype
  have hdir : Directed (· ≤ ·) t := hc.directed
  induction hz with
  | zero =>
      let E : c := ⟨hcne.choose, hcne.choose_spec⟩
      exact ⟨E, 0, .zero, by simp⟩
  | @add x y hx hy ihx ihy =>
      obtain ⟨E, a, ha, hax⟩ := ihx
      obtain ⟨D, b, hb, hby⟩ := ihy
      rcases hc.total E.property D.property with hED | hDE
      · let iED := IntermediateField.inclusion hED
        let hDU : (D : IntermediateField F A) ≤ ⨆ E : c, (E : IntermediateField F A) :=
          le_iSup (fun E : c ↦ (E : IntermediateField F A)) D
        refine ⟨D, iED a + b, .add (ha.map F iED) hb, ?_⟩
        rw [map_add, IntermediateField.inclusion_inclusion, hax, hby]
      · let iDE := IntermediateField.inclusion hDE
        let hEU : (E : IntermediateField F A) ≤ ⨆ E : c, (E : IntermediateField F A) :=
          le_iSup (fun E : c ↦ (E : IntermediateField F A)) E
        refine ⟨E, a + iDE b, .add ha (hb.map F iDE), ?_⟩
        rw [map_add, IntermediateField.inclusion_inclusion, hax, hby]
  | term a ha0 w =>
      have hcoe := IntermediateField.coe_iSup_of_directed hdir
      have hw : (w : A) ∈ ⋃ E : c, (E : Set A) := by
        rw [← hcoe]
        exact w.property
      obtain ⟨E, hwE⟩ := Set.mem_iUnion.mp hw
      let wE : (E : IntermediateField F A) := ⟨w, hwE⟩
      let x : (E : IntermediateField F A) := algebraMap F _ a * wE ^ 2
      refine ⟨E, x, .term a ha0 wE, ?_⟩
      apply Subtype.ext
      simp [x, wE]

/-- Inside any ambient field, the intermediate fields admitting an order extending the base
order have a maximal member. -/
theorem exists_maximal_orderableIntermediateField :
    ∃ M : IntermediateField F A,
      Nonempty (OrderedExtensionData F M) ∧
        Maximal (fun E : IntermediateField F A ↦
          Nonempty (OrderedExtensionData F E)) M := by
  let S : Set (IntermediateField F A) :=
    {E | Nonempty (OrderedExtensionData F E)}
  let baseOrder : OrderedExtensionData F F :=
    ⟨inferInstance, inferInstance, fun h ↦ h⟩
  have hbot : (⊥ : IntermediateField F A) ∈ S := by
    exact ⟨baseOrder.transport F (IntermediateField.botEquiv F A).symm⟩
  have hchains : ∀ c ⊆ S, IsChain (· ≤ ·) c →
      ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcS hc
    rcases c.eq_empty_or_nonempty with rfl | hcne
    · exact ⟨⊥, hbot, by simp⟩
    · let U : IntermediateField F A := ⨆ E : c, (E : IntermediateField F A)
      have hproper : -1 ∉ weightedSquareCone F U := by
        intro hneg
        have hrep : WeightedSquareRep F U (-1) :=
          (mem_weightedSquareCone_iff F U).mp hneg
        obtain ⟨E, x, hx, hxneg⟩ := weightedSquareRep_iSup_chain F c hc hcne hrep
        have hxneg' : x = -1 :=
          (IntermediateField.inclusion
            (le_iSup (fun E : c ↦ (E : IntermediateField F A)) E)).injective (by
              simpa using hxneg)
        obtain ⟨orderE⟩ := hcS E.property
        exact (weightedSquareCone_isProper_of_orderedExtension F E orderE).2
          ((mem_weightedSquareCone_iff F E).mpr (hxneg' ▸ hx))
      have hU : U ∈ S := (nonempty_orderedExtensionData_iff F U).2 hproper
      refine ⟨U, hU, ?_⟩
      intro E hEc
      exact le_iSup (fun E : c ↦ (E : IntermediateField F A)) ⟨E, hEc⟩
  obtain ⟨M, hM⟩ := zorn_le₀ S hchains
  exact ⟨M, hM.prop, hM⟩

end OptimalConvergenceRates.KrivineStengle

end
