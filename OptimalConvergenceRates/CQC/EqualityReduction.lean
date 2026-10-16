import OptimalConvergenceRates.CQC.Defs

/-!
# Reducing inequality presentations with encoded equalities

Exact signed generator classes are reduced to one canonical representative.
Ordinary inequalities, including same-sign duplicates without an opposite,
remain distinct.
-/

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

/-- Two indices belong to the same signed polynomial class. -/
def SameSignedConstraint (g : Fin m → MvPolynomial (Fin n) ℝ)
    (i j : Fin m) : Prop :=
  g j = g i ∨ g j = -g i

theorem sameSignedConstraint_refl
    (g : Fin m → MvPolynomial (Fin n) ℝ) (i : Fin m) :
    SameSignedConstraint g i i :=
  Or.inl rfl

theorem sameSignedConstraint_symm
    {g : Fin m → MvPolynomial (Fin n) ℝ} {i j : Fin m}
    (h : SameSignedConstraint g i j) :
    SameSignedConstraint g j i := by
  rcases h with h | h
  · exact Or.inl h.symm
  · right
    rw [h]
    simp

theorem sameSignedConstraint_trans
    {g : Fin m → MvPolynomial (Fin n) ℝ} {i j k : Fin m}
    (hij : SameSignedConstraint g i j)
    (hjk : SameSignedConstraint g j k) :
    SameSignedConstraint g i k := by
  rcases hij with hij | hij <;> rcases hjk with hjk | hjk
  · exact Or.inl (hjk.trans hij)
  · exact Or.inr (hjk.trans (congrArg Neg.neg hij))
  · exact Or.inr (hjk.trans hij)
  · left
    rw [hjk, hij]
    simp

/-- The finite signed class of one generator. -/
def signedConstraintClass (g : Fin m → MvPolynomial (Fin n) ℝ)
    (i : Fin m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (SameSignedConstraint g i)

theorem mem_signedConstraintClass
    {g : Fin m → MvPolynomial (Fin n) ℝ} {i j : Fin m} :
    j ∈ signedConstraintClass g i ↔ SameSignedConstraint g i j := by
  classical
  simp [signedConstraintClass]

theorem self_mem_signedConstraintClass
    (g : Fin m → MvPolynomial (Fin n) ℝ) (i : Fin m) :
    i ∈ signedConstraintClass g i := by
  simp [mem_signedConstraintClass, sameSignedConstraint_refl]

/-- Least raw index in a signed generator class. -/
def signedConstraintRepresentative
    (g : Fin m → MvPolynomial (Fin n) ℝ) (i : Fin m) : Fin m :=
  (signedConstraintClass g i).min' ⟨i, self_mem_signedConstraintClass g i⟩

theorem signedConstraintRepresentative_mem
    (g : Fin m → MvPolynomial (Fin n) ℝ) (i : Fin m) :
    signedConstraintRepresentative g i ∈ signedConstraintClass g i :=
  Finset.min'_mem _ _

theorem signedConstraintRepresentative_sameSigned
    (g : Fin m → MvPolynomial (Fin n) ℝ) (i : Fin m) :
    SameSignedConstraint g i (signedConstraintRepresentative g i) :=
  mem_signedConstraintClass.mp (signedConstraintRepresentative_mem g i)

theorem signedConstraintRepresentative_le
    (g : Fin m → MvPolynomial (Fin n) ℝ) {i j : Fin m}
    (hj : SameSignedConstraint g i j) :
    signedConstraintRepresentative g i ≤ j :=
  Finset.min'_le _ _ (mem_signedConstraintClass.mpr hj)

theorem hasOppositeConstraint_representative
    {g : Fin m → MvPolynomial (Fin n) ℝ} {i : Fin m}
    (hi : HasOppositeConstraint g i) :
    HasOppositeConstraint g (signedConstraintRepresentative g i) := by
  let r := signedConstraintRepresentative g i
  change HasOppositeConstraint g r
  obtain ⟨j, hji, hj⟩ := hi
  have hr₀ : SameSignedConstraint g i r := by
    exact signedConstraintRepresentative_sameSigned g i
  rcases hr₀ with hr | hr
  · by_cases hjr : j = r
    · refine ⟨i, ?_, ?_⟩
      · intro hir
        apply hji
        rw [hir, hjr]
      · have hj' : g r = -g i := by simpa [hjr] using hj
        simpa [hr] using hj'
    · refine ⟨j, hjr, ?_⟩
      simpa [hr] using hj
  · by_cases hir : i = r
    · refine ⟨j, ?_, ?_⟩
      · simpa [hir] using hji
      · simpa [hir] using hj
    · refine ⟨i, hir, ?_⟩
      rw [hr]
      simp

theorem isEqualityRepresentative_signedConstraintRepresentative
    {g : Fin m → MvPolynomial (Fin n) ℝ} {i : Fin m}
    (hi : HasOppositeConstraint g i) :
    IsEqualityRepresentative g (signedConstraintRepresentative g i) := by
  refine ⟨hasOppositeConstraint_representative hi, ?_⟩
  intro j hj
  exact signedConstraintRepresentative_le g
    (sameSignedConstraint_trans
      (signedConstraintRepresentative_sameSigned g i) hj)

theorem exists_equalityRepresentative_sameSigned
    {g : Fin m → MvPolynomial (Fin n) ℝ} {i : Fin m}
    (hi : HasOppositeConstraint g i) :
    ∃ j, IsEqualityRepresentative g j ∧ SameSignedConstraint g i j :=
  ⟨signedConstraintRepresentative g i,
    isEqualityRepresentative_signedConstraintRepresentative hi,
    signedConstraintRepresentative_sameSigned g i⟩

/-- Raw constraints retained by the equality-aware reduction. -/
def IsSelectedConstraint (g : Fin m → MvPolynomial (Fin n) ℝ)
    (i : Fin m) : Prop :=
  ¬HasOppositeConstraint g i ∨ IsEqualityRepresentative g i

/-- The finite type of retained raw constraints. -/
abbrev SelectedConstraintIndex
    (g : Fin m → MvPolynomial (Fin n) ℝ) :=
  {i : Fin m // IsSelectedConstraint g i}

/-- Number of retained constraints. -/
def selectedConstraintCount
    (g : Fin m → MvPolynomial (Fin n) ℝ) : ℕ := by
  classical
  exact Fintype.card (SelectedConstraintIndex g)

/-- Canonical enumeration of retained constraints. -/
def selectedConstraintEquiv
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    Fin (selectedConstraintCount g) ≃ SelectedConstraintIndex g := by
  classical
  exact (Fintype.equivFin (SelectedConstraintIndex g)).symm

/-- Raw index represented by a reduced constraint index. -/
def selectedRawIndex
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (i : Fin (selectedConstraintCount g)) : Fin m :=
  selectedConstraintEquiv g i

theorem selectedRawIndex_injective
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    Function.Injective (selectedRawIndex g) := by
  intro i j hij
  apply (selectedConstraintEquiv g).injective
  exact Subtype.ext hij

/-- Generator family obtained by retaining all ordinary inequalities and one
representative of every equality class. -/
def selectedGenerator
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    Fin (selectedConstraintCount g) → MvPolynomial (Fin n) ℝ :=
  fun i ↦ g (selectedRawIndex g i)

/-- Reduced index corresponding to a retained raw index. -/
def selectedIndexOf
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (i : SelectedConstraintIndex g) : Fin (selectedConstraintCount g) :=
  (selectedConstraintEquiv g).symm i

@[simp]
theorem selectedConstraintEquiv_selectedIndexOf
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (i : SelectedConstraintIndex g) :
    selectedConstraintEquiv g (selectedIndexOf g i) = i :=
  (selectedConstraintEquiv g).apply_symm_apply i

@[simp]
theorem selectedRawIndex_selectedIndexOf
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (i : SelectedConstraintIndex g) :
    selectedRawIndex g (selectedIndexOf g i) = i :=
  congrArg Subtype.val (selectedConstraintEquiv_selectedIndexOf g i)

theorem selectedRawIndex_isSelected
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (i : Fin (selectedConstraintCount g)) :
    IsSelectedConstraint g (selectedRawIndex g i) :=
  (selectedConstraintEquiv g i).2

theorem selectedConstraintCount_le
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    selectedConstraintCount g ≤ m := by
  classical
  rw [selectedConstraintCount]
  simpa using
    (Fintype.card_le_of_injective
      (fun i : SelectedConstraintIndex g ↦ i.1) Subtype.val_injective)


theorem selectedConstraintCount_pos
    {g : Fin m → MvPolynomial (Fin n) ℝ} (hm : 0 < m) :
    0 < selectedConstraintCount g := by
  classical
  let i : Fin m := ⟨0, hm⟩
  have hselected : Nonempty (SelectedConstraintIndex g) := by
    by_cases hi : HasOppositeConstraint g i
    · obtain ⟨j, hj, _⟩ := exists_equalityRepresentative_sameSigned hi
      exact ⟨⟨j, Or.inr hj⟩⟩
    · exact ⟨⟨i, Or.inl hi⟩⟩
  rw [selectedConstraintCount]
  exact Fintype.card_pos_iff.mpr hselected

end CQCInternal
end OptimalConvergenceRates

end
