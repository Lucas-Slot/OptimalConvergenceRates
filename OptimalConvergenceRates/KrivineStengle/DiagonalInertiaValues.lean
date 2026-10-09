/-
  OptimalConvergenceRates/KrivineStengle/DiagonalInertiaValues.lean

  Computation of inertia indices for diagonal quadratic forms.
-/
import OptimalConvergenceRates.KrivineStengle.DiagonalInertia

noncomputable section

open QuadraticMap

namespace OptimalConvergenceRates.KrivineStengle

universe u v

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- Coordinates carrying a strictly positive diagonal coefficient. -/
def positiveCoordinates (diagonal : I → F) : Finset I :=
  Finset.univ.filter fun i ↦ 0 < diagonal i

/-- Coordinates carrying a nonpositive diagonal coefficient. -/
def nonpositiveCoordinates (diagonal : I → F) : Finset I :=
  Finset.univ.filter fun i ↦ ¬0 < diagonal i

/-- The diagonal form is positive definite on the subspace supported on its positive
coordinates. -/
theorem weightedSumSquares_isPositiveOn_positiveCoordinates (diagonal : I → F) :
    IsPositiveOn (weightedSumSquares F diagonal)
      (coordinateSubspace (F := F) (positiveCoordinates diagonal)) := by
  classical
  intro x hx
  rw [weightedSumSquares_apply]
  apply Finset.sum_pos'
  · intro i hi
    by_cases hpos : 0 < diagonal i
    · exact mul_nonneg hpos.le (mul_self_nonneg ((x : I → F) i))
    · have hzero : (x : I → F) i = 0 :=
        (mem_coordinateSubspace_iff
          (F := F) (positiveCoordinates diagonal) x).mp x.property i (by
            simp [positiveCoordinates, hpos])
      simp [hzero]
  · have hex : ∃ i, (x : I → F) i ≠ 0 := by
      by_contra h
      apply hx
      apply Subtype.ext
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    have hpos : 0 < diagonal i := by
      by_contra hnot
      have hzero : (x : I → F) i = 0 :=
        (mem_coordinateSubspace_iff
          (F := F) (positiveCoordinates diagonal) x).mp x.property i (by
            simp [positiveCoordinates, hnot])
      exact hi hzero
    exact ⟨i, Finset.mem_univ i, mul_pos hpos (mul_self_pos.mpr hi)⟩

/-- The diagonal form is nonpositive on the subspace supported on its nonpositive
coordinates. -/
theorem weightedSumSquares_nonpos_on_nonpositiveCoordinates
    (diagonal : I → F) {x : I → F}
    (hx : x ∈ coordinateSubspace (F := F) (nonpositiveCoordinates diagonal)) :
    weightedSumSquares F diagonal x ≤ 0 := by
  classical
  rw [weightedSumSquares_apply]
  apply Finset.sum_nonpos
  intro i hi
  by_cases hpos : 0 < diagonal i
  · have hzero : (x : I → F) i = 0 :=
      (mem_coordinateSubspace_iff
        (F := F) (nonpositiveCoordinates diagonal) x).mp hx i (by
          simp [nonpositiveCoordinates, hpos])
    simp [hzero]
  · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hpos)
      (mul_self_nonneg ((x : I → F) i))

/-- A positive-definite subspace is disjoint from the nonpositive coordinate subspace. -/
theorem disjoint_nonpositiveCoordinates_of_isPositiveOn
    (diagonal : I → F) (S : Submodule F (I → F))
    (hS : IsPositiveOn (weightedSumSquares F diagonal) S) :
    Disjoint S (coordinateSubspace (F := F) (nonpositiveCoordinates diagonal)) := by
  rw [Submodule.disjoint_def]
  intro x hxS hxNonpos
  by_contra hx
  have hpos := hS ⟨x, hxS⟩ (by
    intro h
    apply hx
    exact congrArg Subtype.val h)
  have hnonpos := weightedSumSquares_nonpos_on_nonpositiveCoordinates diagonal hxNonpos
  exact (not_lt_of_ge hnonpos) hpos

/-- The positive inertia index of a diagonal form is the number of positive diagonal
coefficients. -/
theorem positiveIndex_weightedSumSquares (diagonal : I → F) :
    positiveIndex (weightedSumSquares F diagonal) =
      (positiveCoordinates diagonal).card := by
  classical
  apply le_antisymm
  · obtain ⟨S, hS, hdim⟩ :=
      exists_positiveSubspace_finrank_eq_positiveIndex
        (weightedSumSquares F diagonal)
    have hdisjoint :=
      disjoint_nonpositiveCoordinates_of_isPositiveOn diagonal S hS
    have hdimBound := Submodule.finrank_add_finrank_le_of_disjoint hdisjoint
    rw [finrank_coordinateSubspace,
      Module.finrank_fintype_fun_eq_card F, hdim] at hdimBound
    have hpartition :
        (positiveCoordinates diagonal).card +
          (nonpositiveCoordinates diagonal).card = Fintype.card I := by
      simpa [positiveCoordinates, nonpositiveCoordinates] using
        (Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset I)) (p := fun i ↦ 0 < diagonal i))
    omega
  · rw [← finrank_coordinateSubspace (F := F)
        (positiveCoordinates diagonal)]
    exact finrank_le_positiveIndex (weightedSumSquares F diagonal)
      (coordinateSubspace (F := F) (positiveCoordinates diagonal))
      (weightedSumSquares_isPositiveOn_positiveCoordinates diagonal)

/-- Coordinates carrying a strictly negative diagonal coefficient. -/
def negativeCoordinates (diagonal : I → F) : Finset I :=
  Finset.univ.filter fun i ↦ diagonal i < 0

/-- The negative inertia index of a diagonal form is the number of negative diagonal
coefficients. -/
theorem negativeIndex_weightedSumSquares (diagonal : I → F) :
    negativeIndex (weightedSumSquares F diagonal) =
      (negativeCoordinates diagonal).card := by
  have hneg :
      -(weightedSumSquares F diagonal) =
        weightedSumSquares F (fun i ↦ -diagonal i) := by
    ext x
    simp [weightedSumSquares_apply]
  rw [negativeIndex, hneg, positiveIndex_weightedSumSquares]
  congr 1
  ext i
  simp [positiveCoordinates, negativeCoordinates]

end OptimalConvergenceRates.KrivineStengle

end
