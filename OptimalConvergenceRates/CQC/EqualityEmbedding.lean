import OptimalConvergenceRates.CQC.EqualityBoxLift
import OptimalConvergenceRates.CQC.ModulePullback

/-!
# Embedding the selected slack-value variables into the original family
-/

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

/-- Coordinate embedding that retains every base variable and sends a selected
slack-value variable to the corresponding raw generator slot. -/
def selectedValueEmbedding
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    Fin (n + selectedConstraintCount g) → Fin (n + m) :=
  Fin.addCases (Fin.castAdd m)
    (fun i ↦ Fin.natAdd n (selectedRawIndex g i))

theorem selectedValueEmbedding_injective
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    Function.Injective (selectedValueEmbedding g) := by
  intro i j hij
  have hcases : ∀ k : Fin (n + selectedConstraintCount g),
      (∃ a : Fin n, k = Fin.castAdd (selectedConstraintCount g) a) ∨
        ∃ b : Fin (selectedConstraintCount g), k = Fin.natAdd n b := by
    intro k
    exact Fin.addCases
      (fun a ↦ Or.inl ⟨a, rfl⟩)
      (fun b ↦ Or.inr ⟨b, rfl⟩) k
  rcases hcases i with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases hcases j with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · apply Fin.ext
    have h := congrArg Fin.val hij
    simpa [selectedValueEmbedding] using h
  · exfalso
    have h := congrArg Fin.val hij
    simp [selectedValueEmbedding] at h
    omega
  · exfalso
    have h := congrArg Fin.val hij
    simp [selectedValueEmbedding] at h
    omega
  · have hraw : selectedRawIndex g a = selectedRawIndex g b := by
      apply Fin.ext
      have h := congrArg Fin.val hij
      simpa [selectedValueEmbedding] using h
    have hab : a = b := selectedRawIndex_injective g hraw
    subst b
    rfl

/-- Rename a polynomial in selected slack values into the full raw slack-value
space. Unselected variables do not occur in the result. -/
def embedSelectedPolynomial
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (P : MvPolynomial (Fin (n + selectedConstraintCount g)) ℝ) :
    MvPolynomial (Fin (n + m)) ℝ :=
  MvPolynomial.rename (selectedValueEmbedding g) P

/-- Restrict a full raw slack-value point to the selected coordinates. -/
def selectedValuePoint
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin (n + m) → ℝ) :
    Fin (n + selectedConstraintCount g) → ℝ :=
  combinePoint (basePoint z)
    (fun i ↦ slackPoint z (selectedRawIndex g i))

@[simp]
theorem basePoint_selectedValuePoint
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin (n + m) → ℝ) :
    basePoint (selectedValuePoint g z) = basePoint z := by
  simp [selectedValuePoint]

@[simp]
theorem slackPoint_selectedValuePoint
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin (n + m) → ℝ)
    (i : Fin (selectedConstraintCount g)) :
    slackPoint (selectedValuePoint g z) i =
      slackPoint z (selectedRawIndex g i) := by
  simp [selectedValuePoint]

@[simp]
theorem eval_embedSelectedPolynomial
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin (n + m) → ℝ)
    (P : MvPolynomial (Fin (n + selectedConstraintCount g)) ℝ) :
    MvPolynomial.eval z (embedSelectedPolynomial g P) =
      MvPolynomial.eval (selectedValuePoint g z) P := by
  rw [embedSelectedPolynomial, MvPolynomial.eval_rename]
  have hpoint : z ∘ selectedValueEmbedding g = selectedValuePoint g z := by
    apply _root_.funext
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [selectedValueEmbedding, selectedValuePoint, combinePoint, basePoint]
    · intro k
      simp [selectedValueEmbedding, selectedValuePoint, combinePoint, slackPoint]
  rw [hpoint]

theorem selectedValuePoint_mem_slackValueBox
    {R : ℝ} (g : Fin m → MvPolynomial (Fin n) ℝ)
    {z : Fin (n + m) → ℝ} (hz : z ∈ slackValueBox R) :
    selectedValuePoint g z ∈ slackValueBox R := by
  constructor
  · intro j
    simpa using hz.1 j
  · intro i
    simpa using hz.2 (selectedRawIndex g i)

theorem embedSelectedPolynomial_nonneg_on_slackValueBox
    {R : ℝ} (g : Fin m → MvPolynomial (Fin n) ℝ)
    (P : MvPolynomial (Fin (n + selectedConstraintCount g)) ℝ)
    (hP : ∀ z ∈ slackValueBox R, 0 ≤ MvPolynomial.eval z P) :
    ∀ z ∈ slackValueBox R,
      0 ≤ MvPolynomial.eval z (embedSelectedPolynomial g P) := by
  intro z hz
  rw [eval_embedSelectedPolynomial]
  exact hP (selectedValuePoint g z)
    (selectedValuePoint_mem_slackValueBox g hz)

theorem totalDegree_embedSelectedPolynomial_le
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (P : MvPolynomial (Fin (n + selectedConstraintCount g)) ℝ) :
    (embedSelectedPolynomial g P).totalDegree ≤ P.totalDegree :=
  MvPolynomial.totalDegree_rename_le _ _

theorem generatorSlackSubstitution_embedSelectedPolynomial
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (P : MvPolynomial (Fin (n + selectedConstraintCount g)) ℝ) :
    generatorSlackSubstitution g (embedSelectedPolynomial g P) =
      generatorSlackSubstitution (selectedGenerator g) P := by
  unfold generatorSlackSubstitution embedSelectedPolynomial
  rw [MvPolynomial.aeval_rename]
  congr 1
  ext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [selectedValueEmbedding]
  · intro k
    simp [selectedValueEmbedding, selectedGenerator]

/-- Sum of the canonical equality representatives in the original variable
space. -/
def equalityRepresentativeSum
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ e : Fin (selectedEqualityCount g),
    selectedGenerator g (selectedEqualityIndex g e)

theorem generatorSlackSubstitution_equalitySlackValueSum
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    generatorSlackSubstitution (selectedGenerator g)
        (equalitySlackValueSum g) =
      equalityRepresentativeSum g := by
  simp [equalitySlackValueSum, equalityRepresentativeSum]

theorem generatorSlackSubstitution_descendedEqualitySlackObjective
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (M : ℝ) :
    generatorSlackSubstitution (selectedGenerator g)
        (descendedEqualitySlackObjective g p M) =
      determinantMultiplier (selectedGenerator g) ^ 2 * p +
        C M * equalityRepresentativeSum g := by
  simp [descendedEqualitySlackObjective,
    generatorSlackSubstitution_descendedSlackObjective,
    generatorSlackSubstitution_equalitySlackValueSum]

theorem generatorSlackSubstitution_embedded_descendedEqualitySlackObjective
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (M : ℝ) :
    generatorSlackSubstitution g
        (embedSelectedPolynomial g
          (descendedEqualitySlackObjective g p M)) =
      determinantMultiplier (selectedGenerator g) ^ 2 * p +
        C M * equalityRepresentativeSum g := by
  rw [generatorSlackSubstitution_embedSelectedPolynomial,
    generatorSlackSubstitution_descendedEqualitySlackObjective]

end CQCInternal
end OptimalConvergenceRates

end
