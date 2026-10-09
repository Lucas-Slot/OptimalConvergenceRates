/-
  OptimalConvergenceRates/KrivineStengle/Inertia.lean

  Basis-independent positive and negative inertia indices of finite quadratic forms.
-/
import OptimalConvergenceRates.KrivineStengle.SignatureDiagonalization
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section

open QuadraticMap

namespace OptimalConvergenceRates.KrivineStengle

universe u v w

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {W : Type w} [AddCommGroup W] [Module F W] [FiniteDimensional F W]


/-- A quadratic form is positive definite when restricted to a given subspace. -/
def IsPositiveOn (Q : QuadraticForm F V) (S : Submodule F V) : Prop :=
  ∀ x : S, x ≠ 0 → 0 < Q x

/-- The finite set of dimensions of positive-definite subspaces of a quadratic form. -/
def positiveRanks (Q : QuadraticForm F V) : Finset ℕ := by
  classical
  exact (Finset.range (Module.finrank F V + 1)).filter fun k ↦
    ∃ S : Submodule F V, IsPositiveOn Q S ∧ Module.finrank F S = k

private theorem positiveRanks_nonempty (Q : QuadraticForm F V) :
    (positiveRanks Q).Nonempty := by
  classical
  refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _), ?_⟩⟩
  refine ⟨⊥, ?_, by simp⟩
  intro x hx
  exact False.elim (hx (Subsingleton.elim x 0))

/-- The largest dimension of a subspace on which a quadratic form is positive definite. -/
def positiveIndex (Q : QuadraticForm F V) : ℕ :=
  (positiveRanks Q).max' (positiveRanks_nonempty Q)

/-- A positive-definite subspace attaining the positive index exists. -/
theorem exists_positiveSubspace_finrank_eq_positiveIndex
    (Q : QuadraticForm F V) :
    ∃ S : Submodule F V,
      IsPositiveOn Q S ∧ Module.finrank F S = positiveIndex Q := by
  classical
  have hmem : positiveIndex Q ∈ positiveRanks Q :=
    Finset.max'_mem (positiveRanks Q) (positiveRanks_nonempty Q)
  exact (Finset.mem_filter.mp hmem).2

/-- Every positive-definite subspace has dimension at most the positive index. -/
theorem finrank_le_positiveIndex (Q : QuadraticForm F V)
    (S : Submodule F V) (hS : IsPositiveOn Q S) :
    Module.finrank F S ≤ positiveIndex Q := by
  classical
  have hrank : Module.finrank F S < Module.finrank F V + 1 :=
    Nat.lt_succ_of_le (Submodule.finrank_le S)
  have hmem : Module.finrank F S ∈ positiveRanks Q := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hrank, ⟨S, hS, rfl⟩⟩
  exact Finset.le_max' (positiveRanks Q) _ hmem

/-- A linear equivalence carries a positive-definite subspace to a positive-definite
subspace when it preserves the quadratic form. -/
theorem IsPositiveOn.map {QV : QuadraticForm F V} {QW : QuadraticForm F W}
    (e : V ≃ₗ[F] W) (hQ : ∀ x, QW (e x) = QV x)
    {S : Submodule F V} (hS : IsPositiveOn QV S) :
    IsPositiveOn QW (S.map e.toLinearMap) := by
  intro y hy
  obtain ⟨y, hyS⟩ := y
  obtain ⟨x, hxS, rfl⟩ := Submodule.mem_map.mp hyS
  change 0 < QW (e x)
  rw [hQ]
  apply hS ⟨x, hxS⟩
  intro hx
  apply hy
  apply Subtype.ext
  have : x = 0 := congrArg Subtype.val hx
  simp [this]

/-- The positive index is invariant under a quadratic isometry. -/
theorem positiveIndex_congr {QV : QuadraticForm F V} {QW : QuadraticForm F W}
    (e : V ≃ₗ[F] W) (hQ : ∀ x, QW (e x) = QV x) :
    positiveIndex QV = positiveIndex QW := by
  apply le_antisymm
  · obtain ⟨S, hS, hdim⟩ :=
      exists_positiveSubspace_finrank_eq_positiveIndex QV
    have hmap := IsPositiveOn.map e hQ hS
    have hle := finrank_le_positiveIndex QW (S.map e.toLinearMap) hmap
    rw [LinearEquiv.finrank_map_eq, hdim] at hle
    exact hle
  · obtain ⟨S, hS, hdim⟩ :=
      exists_positiveSubspace_finrank_eq_positiveIndex QW
    have hQsymm : ∀ y, QV (e.symm y) = QW y := by
      intro y
      rw [← hQ (e.symm y), e.apply_symm_apply]
    have hmap := IsPositiveOn.map e.symm hQsymm hS
    have hle := finrank_le_positiveIndex QV (S.map e.symm.toLinearMap) hmap
    rw [LinearEquiv.finrank_map_eq, hdim] at hle
    exact hle

/-- The largest dimension of a subspace on which a quadratic form is negative definite. -/
def negativeIndex (Q : QuadraticForm F V) : ℕ :=
  positiveIndex (-Q)

/-- The signature defined intrinsically as positive inertia minus negative inertia. -/
def signature (Q : QuadraticForm F V) : ℤ :=
  (positiveIndex Q : ℤ) - (negativeIndex Q : ℤ)

/-- The negative index is invariant under a quadratic isometry. -/
theorem negativeIndex_congr {QV : QuadraticForm F V} {QW : QuadraticForm F W}
    (e : V ≃ₗ[F] W) (hQ : ∀ x, QW (e x) = QV x) :
    negativeIndex QV = negativeIndex QW := by
  apply positiveIndex_congr e
  intro x
  simp only [neg_apply, hQ]

/-- The intrinsic signature is invariant under a quadratic isometry. -/
theorem signature_congr {QV : QuadraticForm F V} {QW : QuadraticForm F W}
    (e : V ≃ₗ[F] W) (hQ : ∀ x, QW (e x) = QV x) :
    signature QV = signature QW := by
  simp [signature, positiveIndex_congr e hQ, negativeIndex_congr e hQ]

end OptimalConvergenceRates.KrivineStengle

end
