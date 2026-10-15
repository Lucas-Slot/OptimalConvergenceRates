/-
  OptimalConvergenceRates/KrivineStengle/PGroupIndex.lean

  A proper subgroup of a finite p-group is contained in a subgroup of
  index p.  This is the group-theoretic step used to extract a quadratic
  intermediate field from a nontrivial finite two-extension.
-/
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Order.Atoms.Finite

noncomputable section

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {G : Type u} [Group G] [Finite G]
  {p : ℕ} [Fact p.Prime]

/-- Every proper subgroup of a finite p-group is contained in a subgroup
of index p. -/
theorem IsPGroup.exists_le_index_eq_prime
    (hG : IsPGroup p G) {H : Subgroup G} (hH : H ≠ ⊤) :
    ∃ K : Subgroup G, H ≤ K ∧ K.index = p := by
  obtain ⟨K, hK, hHK⟩ := (eq_top_or_exists_le_coatom H).resolve_left hH
  letI : Group.IsNilpotent G := IsPGroup.isNilpotent hG
  letI : K.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom K
      (Group.normalizerCondition_of_isNilpotent (G := G)) hK
  let Q := G ⧸ K
  have hQ : IsPGroup p Q := hG.to_quotient K
  letI : Nontrivial Q := QuotientGroup.nontrivial_iff.mpr hK.ne_top
  letI : IsSimpleGroup Q :=
    { toNontrivial := inferInstance
      eq_bot_or_eq_top_of_normal := fun L _ => by
        have hle : K ≤ L.comap (QuotientGroup.mk' K) :=
          QuotientGroup.le_comap_mk' K L
        rcases hK.le_iff.mp hle with htop | hbot
        · right
          apply Subgroup.comap_injective (QuotientGroup.mk'_surjective K)
          simp [htop]
        · left
          apply Subgroup.comap_injective (QuotientGroup.mk'_surjective K)
          rw [hbot]
          simp }
  have hcenter : Subgroup.center Q = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center Q) with hbot | htop
    · exact (hQ.bot_lt_center.ne hbot.symm).elim
    · exact htop
  letI : CommGroup Q := Group.commGroupOfCenterEqTop hcenter
  have hprime : (Nat.card Q).Prime := IsSimpleGroup.prime_card
  have hdvd : p ∣ Nat.card Q :=
    (hG.to_quotient K).card_eq_or_dvd.resolve_left hprime.ne_one
  have hp : p = Nat.card Q :=
    (Nat.prime_dvd_prime_iff_eq Fact.out hprime).mp hdvd
  refine ⟨K, hHK, ?_⟩
  exact K.index_eq_card.trans hp.symm

end OptimalConvergenceRates.KrivineStengle

end
