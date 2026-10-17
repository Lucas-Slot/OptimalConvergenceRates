import OptimalConvergenceRates.CQC.EqualityReduction
import OptimalConvergenceRates.CQC.SlackGeometry
import OptimalConvergenceRates.CQC.RegularPenaltyNearest

/-!
# Squared slacks with encoded equalities

The selected generator family has one member for every ordinary inequality and
one member for every equality class. Equality representatives still receive a
squared slack so that the existing algebraic descent applies, and an additional
linear equation forces precisely those slacks to zero.
-/

noncomputable section

open MvPolynomial Finset Set

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

/-- A selected constraint that represents an encoded equality. -/
def SelectedEncodesEquality
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (i : Fin (selectedConstraintCount g)) : Prop :=
  HasOppositeConstraint g (selectedRawIndex g i)

noncomputable instance selectedEncodesEqualityDecidable
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (i : Fin (selectedConstraintCount g)) :
    Decidable (SelectedEncodesEquality g i) :=
  Classical.propDecidable _

/-- Selected equality representatives as a finite subtype. -/
abbrev SelectedEqualityIndex
    (g : Fin m → MvPolynomial (Fin n) ℝ) :=
  {i : Fin (selectedConstraintCount g) // SelectedEncodesEquality g i}

/-- Number of selected equality representatives. -/
def selectedEqualityCount
    (g : Fin m → MvPolynomial (Fin n) ℝ) : ℕ := by
  classical
  exact Fintype.card (SelectedEqualityIndex g)

/-- Canonical enumeration of selected equality representatives. -/
def selectedEqualityEquiv
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    Fin (selectedEqualityCount g) ≃ SelectedEqualityIndex g := by
  classical
  exact (Fintype.equivFin (SelectedEqualityIndex g)).symm

/-- Selected-generator index of an enumerated equality representative. -/
def selectedEqualityIndex
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (i : Fin (selectedEqualityCount g)) :
    Fin (selectedConstraintCount g) :=
  selectedEqualityEquiv g i

theorem selectedEqualityIndex_injective
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    Function.Injective (selectedEqualityIndex g) := by
  intro i j hij
  apply (selectedEqualityEquiv g).injective
  exact Subtype.ext hij

theorem selectedEqualityIndex_encodes
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (i : Fin (selectedEqualityCount g)) :
    SelectedEncodesEquality g (selectedEqualityIndex g i) :=
  (selectedEqualityEquiv g i).2

/-- The complete regular equation family. Its first block consists of the
usual squared-slack equations for selected generators; its second block sets
the equality slacks to zero linearly. -/
def equalitySlackPolynomial
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    Fin (selectedConstraintCount g + selectedEqualityCount g) →
      MvPolynomial (Fin (n + selectedConstraintCount g)) ℝ :=
  Fin.addCases (slackPolynomial (selectedGenerator g))
    (fun i ↦ X (Fin.natAdd n (selectedEqualityIndex g i)))

/-- Common zero set of the equality-aware slack equations. -/
def equalitySlackZeroSet
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    Set (Fin (n + selectedConstraintCount g) → ℝ) :=
  polynomialZeroSet (equalitySlackPolynomial g)

theorem mem_selected_slackZeroSet_of_mem_equalitySlackZeroSet
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {z : Fin (n + selectedConstraintCount g) → ℝ}
    (hz : z ∈ equalitySlackZeroSet g) :
    z ∈ slackZeroSet (selectedGenerator g) := by
  intro i
  simpa [equalitySlackPolynomial] using hz (Fin.castAdd (selectedEqualityCount g) i)

theorem equality_slack_eq_zero_of_mem_equalitySlackZeroSet
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {z : Fin (n + selectedConstraintCount g) → ℝ}
    (hz : z ∈ equalitySlackZeroSet g)
    (i : Fin (selectedEqualityCount g)) :
    slackPoint z (selectedEqualityIndex g i) = 0 := by
  have hi := hz (Fin.natAdd (selectedConstraintCount g) i)
  simpa [equalitySlackPolynomial, slackPoint] using hi

/-- Projection of an equality-aware slack zero satisfies every original raw
inequality, including the discarded opposite copies. -/
theorem basePoint_mem_basicClosedSet_of_mem_equalitySlackZeroSet
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {z : Fin (n + selectedConstraintCount g) → ℝ}
    (hz : z ∈ equalitySlackZeroSet g) :
    basePoint z ∈ KrivineStengle.basicClosedSet g := by
  classical
  let hcore := mem_selected_slackZeroSet_of_mem_equalitySlackZeroSet hz
  intro i
  by_cases hi : HasOppositeConstraint g i
  · obtain ⟨j, hjrep, hij⟩ := exists_equalityRepresentative_sameSigned hi
    let js : SelectedConstraintIndex g := ⟨j, Or.inr hjrep⟩
    let k := selectedIndexOf g js
    have hkraw : selectedRawIndex g k = j := by
      simpa [k, js] using selectedRawIndex_selectedIndexOf g js
    have hkenc : SelectedEncodesEquality g k := by
      simpa [SelectedEncodesEquality, hkraw] using hjrep.1
    let ke : SelectedEqualityIndex g := ⟨k, hkenc⟩
    let e := (selectedEqualityEquiv g).symm ke
    have heindex : selectedEqualityIndex g e = k := by
      exact congrArg Subtype.val ((selectedEqualityEquiv g).apply_symm_apply ke)
    have hy : slackPoint z k = 0 := by
      rw [← heindex]
      exact equality_slack_eq_zero_of_mem_equalitySlackZeroSet hz e
    have hk := hcore k
    simp [eval_slackPolynomial, hy] at hk
    have hgj : MvPolynomial.eval (basePoint z) (g j) = 0 := by
      simpa [selectedGenerator, hkraw] using hk
    have hgi : MvPolynomial.eval (basePoint z) (g i) = 0 := by
      rcases hij with hij | hij
      · simpa [hij] using hgj
      · rw [hij, map_neg] at hgj
        linarith
    exact hgi.ge
  · let is : SelectedConstraintIndex g := ⟨i, Or.inl hi⟩
    let k := selectedIndexOf g is
    have hkraw : selectedRawIndex g k = i := by
      simpa [k, is] using selectedRawIndex_selectedIndexOf g is
    have hk := hcore k
    rw [eval_slackPolynomial] at hk
    have hge :
        MvPolynomial.eval (basePoint z) (g i) =
          (slackPoint z k) ^ 2 := by
      simpa [selectedGenerator, hkraw] using sub_eq_zero.mp hk
    rw [hge]
    exact sq_nonneg _

/-- Equality-aware lift of a feasible point, using zero for equality slacks
and the nonnegative square root for ordinary inequalities. -/
def equalitySlackLift
    (g : Fin m → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    Fin (n + selectedConstraintCount g) → ℝ := by
  classical
  exact combinePoint x fun i ↦
    if SelectedEncodesEquality g i then 0
    else Real.sqrt (MvPolynomial.eval x (selectedGenerator g i))

@[simp]
theorem basePoint_equalitySlackLift
    (g : Fin m → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    basePoint (equalitySlackLift g x) = x := by
  simp [equalitySlackLift]

@[simp]
theorem slackPoint_equalitySlackLift
    (g : Fin m → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ)
    (i : Fin (selectedConstraintCount g)) :
    slackPoint (equalitySlackLift g x) i =
      if SelectedEncodesEquality g i then 0
      else Real.sqrt (MvPolynomial.eval x (selectedGenerator g i)) := by
  classical
  simp [equalitySlackLift]

theorem equalitySlackLift_mem_equalitySlackZeroSet
    {g : Fin m → MvPolynomial (Fin n) ℝ} {x : Fin n → ℝ}
    (hx : x ∈ KrivineStengle.basicClosedSet g) :
    equalitySlackLift g x ∈ equalitySlackZeroSet g := by
  classical
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro k
    rw [show equalitySlackPolynomial g (Fin.castAdd (selectedEqualityCount g) k) =
        slackPolynomial (selectedGenerator g) k by
      simp [equalitySlackPolynomial]]
    rw [eval_slackPolynomial, basePoint_equalitySlackLift,
      slackPoint_equalitySlackLift]
    by_cases hk : SelectedEncodesEquality g k
    · simpa [hk, selectedGenerator] using
        (eval_eq_zero_of_hasOppositeConstraint hx hk)
    · simp only [hk, ↓reduceIte]
      have hnonneg : 0 ≤ MvPolynomial.eval x (selectedGenerator g k) := by
        simpa [selectedGenerator] using hx (selectedRawIndex g k)
      rw [Real.sq_sqrt hnonneg]
      ring
  · intro e
    simp [equalitySlackPolynomial, equalitySlackLift, combinePoint,
      selectedEqualityIndex_encodes]

/-- Signed equality-aware lift used to express the zero set as a finite union
of images of the original feasible set. -/
def signedEqualitySlackLift
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (s : Fin (selectedConstraintCount g) → Bool)
    (x : Fin n → ℝ) : Fin (n + selectedConstraintCount g) → ℝ := by
  classical
  exact combinePoint x fun i ↦
    if SelectedEncodesEquality g i then 0
    else if s i then -Real.sqrt (MvPolynomial.eval x (selectedGenerator g i))
    else Real.sqrt (MvPolynomial.eval x (selectedGenerator g i))

@[simp]
theorem basePoint_signedEqualitySlackLift
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (s : Fin (selectedConstraintCount g) → Bool) (x : Fin n → ℝ) :
    basePoint (signedEqualitySlackLift g s x) = x := by
  simp [signedEqualitySlackLift]

@[simp]
theorem slackPoint_signedEqualitySlackLift
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (s : Fin (selectedConstraintCount g) → Bool)
    (x : Fin n → ℝ) (i : Fin (selectedConstraintCount g)) :
    slackPoint (signedEqualitySlackLift g s x) i =
      if SelectedEncodesEquality g i then 0
      else if s i then -Real.sqrt (MvPolynomial.eval x (selectedGenerator g i))
      else Real.sqrt (MvPolynomial.eval x (selectedGenerator g i)) := by
  classical
  simp [signedEqualitySlackLift]

theorem signedEqualitySlackLift_mem_equalitySlackZeroSet
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {x : Fin n → ℝ} (hx : x ∈ KrivineStengle.basicClosedSet g)
    (s : Fin (selectedConstraintCount g) → Bool) :
    signedEqualitySlackLift g s x ∈ equalitySlackZeroSet g := by
  classical
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro k
    rw [show equalitySlackPolynomial g (Fin.castAdd (selectedEqualityCount g) k) =
        slackPolynomial (selectedGenerator g) k by
      simp [equalitySlackPolynomial]]
    rw [eval_slackPolynomial, basePoint_signedEqualitySlackLift,
      slackPoint_signedEqualitySlackLift]
    by_cases hk : SelectedEncodesEquality g k
    · simpa [hk, selectedGenerator] using
        (eval_eq_zero_of_hasOppositeConstraint hx hk)
    · simp only [hk, ↓reduceIte]
      have hnonneg : 0 ≤ MvPolynomial.eval x (selectedGenerator g k) := by
        simpa [selectedGenerator] using hx (selectedRawIndex g k)
      split_ifs
      · rw [neg_sq, Real.sq_sqrt hnonneg]
        ring
      · rw [Real.sq_sqrt hnonneg]
        ring
  · intro e
    simp [equalitySlackPolynomial, signedEqualitySlackLift, combinePoint,
      selectedEqualityIndex_encodes]

theorem continuous_signedEqualitySlackLift
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (s : Fin (selectedConstraintCount g) → Bool) :
    Continuous (signedEqualitySlackLift g s) := by
  classical
  apply continuous_pi
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simpa [signedEqualitySlackLift, combinePoint] using
      (continuous_apply i : Continuous (fun x : Fin n → ℝ ↦ x i))
  · intro i
    by_cases hi : SelectedEncodesEquality g i
    · simpa [signedEqualitySlackLift, combinePoint, hi] using
        (continuous_const : Continuous (fun _ : (Fin n → ℝ) ↦ (0 : ℝ)))
    · by_cases hs : s i = true
      · simp only [signedEqualitySlackLift, combinePoint, Fin.addCases_right,
          hi, ↓reduceIte, hs]
        exact (Real.continuous_sqrt.comp
          (continuous_eval (selectedGenerator g i))).neg
      · have hs' : s i = false := Bool.eq_false_of_not_eq_true hs
        simp only [signedEqualitySlackLift, combinePoint, Fin.addCases_right,
          hi, ↓reduceIte, hs', Bool.false_eq_true]
        exact Real.continuous_sqrt.comp (continuous_eval (selectedGenerator g i))

theorem equalitySlackZeroSet_eq_iUnion_signedLift
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    equalitySlackZeroSet g =
      ⋃ s : Fin (selectedConstraintCount g) → Bool,
        signedEqualitySlackLift g s '' KrivineStengle.basicClosedSet g := by
  classical
  ext z
  constructor
  · intro hz
    let s : Fin (selectedConstraintCount g) → Bool :=
      fun i ↦ decide (slackPoint z i < 0)
    refine Set.mem_iUnion.2 ⟨s, ?_⟩
    refine ⟨basePoint z, basePoint_mem_basicClosedSet_of_mem_equalitySlackZeroSet hz, ?_⟩
    apply _root_.funext
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simp [signedEqualitySlackLift, combinePoint, basePoint]
    · intro i
      by_cases hi : SelectedEncodesEquality g i
      · let ie : SelectedEqualityIndex g := ⟨i, hi⟩
        let e := (selectedEqualityEquiv g).symm ie
        have heindex : selectedEqualityIndex g e = i := by
          exact congrArg Subtype.val ((selectedEqualityEquiv g).apply_symm_apply ie)
        have hy : slackPoint z i = 0 := by
          rw [← heindex]
          exact equality_slack_eq_zero_of_mem_equalitySlackZeroSet hz e
        simp [signedEqualitySlackLift, combinePoint, hi, slackPoint] at hy ⊢
        exact hy.symm
      · have hcore := mem_selected_slackZeroSet_of_mem_equalitySlackZeroSet hz i
        rw [eval_slackPolynomial] at hcore
        have hsquare :
            MvPolynomial.eval (basePoint z) (selectedGenerator g i) =
              (slackPoint z i) ^ 2 := by linarith
        simp only [signedEqualitySlackLift, combinePoint, Fin.addCases_right, hi,
          ↓reduceIte]
        by_cases hy : slackPoint z i < 0
        · have hy' : z (Fin.natAdd n i) < 0 := by simpa [slackPoint] using hy
          simp [s, hy, hy', hsquare, Real.sqrt_sq_eq_abs, slackPoint, abs_of_neg hy']
        · have hy0 : 0 ≤ slackPoint z i := le_of_not_gt hy
          have hy0' : 0 ≤ z (Fin.natAdd n i) := by simpa [slackPoint] using hy0
          have hnot : ¬z (Fin.natAdd n i) < 0 := not_lt.mpr hy0'
          simp [s, hy, hy0', hnot, hsquare, Real.sqrt_sq_eq_abs, slackPoint]
  · intro hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨s, x, hx, rfl⟩ := hz
    exact signedEqualitySlackLift_mem_equalitySlackZeroSet hx s

theorem equalitySlackZeroSet_isCompact
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (harch : GeneralArchimedean.IsArchimedean g) :
    IsCompact (equalitySlackZeroSet g) := by
  rw [equalitySlackZeroSet_eq_iUnion_signedLift]
  exact isCompact_iUnion fun s ↦
    harch.isCompact_basicClosedSet.image
      (continuous_signedEqualitySlackLift g s)

end CQCInternal
end OptimalConvergenceRates

end
