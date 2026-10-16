import OptimalConvergenceRates.CQC.EqualitySlackRank
import OptimalConvergenceRates.CQC.BoxLiftPenalty
import OptimalConvergenceRates.CQC.SlackValueGeometry

/-!
# Penalized lift and slack-value descent with encoded equalities
-/

noncomputable section

open MvPolynomial Finset Set

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

/-- Sum of squares of the linear equations forcing equality slacks to zero. -/
def equalitySlackSquareSum
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin (n + selectedConstraintCount g)) ℝ :=
  ∑ e : Fin (selectedEqualityCount g),
    X (Fin.natAdd n (selectedEqualityIndex g e)) ^ 2

/-- The corrected selected-family objective with both the usual slack-equation
penalty and the extra equality-slack penalty. -/
def penalizedEqualitySlackObjective
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (M : ℝ) :
    MvPolynomial (Fin (n + selectedConstraintCount g)) ℝ :=
  penalizedSlackObjective (selectedGenerator g) p M +
    C M * equalitySlackSquareSum g

/-- Extra equality penalty after replacing every squared slack by an
independent nonnegative slack-value variable. -/
def equalitySlackValueSum
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin (n + selectedConstraintCount g)) ℝ :=
  ∑ e : Fin (selectedEqualityCount g),
    X (Fin.natAdd n (selectedEqualityIndex g e))

/-- Descended equality-aware objective in independent slack-value variables. -/
def descendedEqualitySlackObjective
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (M : ℝ) :
    MvPolynomial (Fin (n + selectedConstraintCount g)) ℝ :=
  descendedSlackObjective (selectedGenerator g) p M +
    C M * equalitySlackValueSum g

theorem equationSquareSum_equalitySlackPolynomial
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    equationSquareSum (equalitySlackPolynomial g) =
      equationSquareSum (slackPolynomial (selectedGenerator g)) +
        equalitySlackSquareSum g := by
  classical
  simp [equationSquareSum, equalitySlackSquareSum, equalitySlackPolynomial,
    Fin.sum_univ_add]

theorem squareSlackSubstitution_equalitySlackValueSum
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    squareSlackSubstitution (equalitySlackValueSum g) =
      equalitySlackSquareSum g := by
  classical
  simp [equalitySlackValueSum, equalitySlackSquareSum]

theorem squareSlackSubstitution_descendedEqualitySlackObjective
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (M : ℝ) :
    squareSlackSubstitution (descendedEqualitySlackObjective g p M) =
      penalizedEqualitySlackObjective g p M := by
  simp [descendedEqualitySlackObjective, penalizedEqualitySlackObjective,
    squareSlackSubstitution_descendedSlackObjective,
    squareSlackSubstitution_equalitySlackValueSum]

theorem equalitySlackGradientAt_eq_polynomialGradientAt
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin (n + selectedConstraintCount g) → ℝ)
    (i : Fin (selectedConstraintCount g + selectedEqualityCount g)) :
    equalitySlackGradientAt g z i =
      polynomialGradientAt (equalitySlackPolynomial g i) z :=
  rfl

theorem correctedSlackObjective_equality_normal_derivative
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    {z : Fin (n + selectedConstraintCount g) → ℝ}
    (hz : z ∈ equalitySlackZeroSet g)
    (e : Fin (selectedEqualityCount g)) :
    QuarticConvergence.mvPolynomialEvalFDeriv
        (correctedSlackObjective (selectedGenerator g) p) z
        (polynomialGradientAt
          (X (Fin.natAdd n (selectedEqualityIndex g e))) z) = 0 := by
  let q := descendedSlackObjective (selectedGenerator g) p 0
  have hdesc :
      squareSlackSubstitution q =
        correctedSlackObjective (selectedGenerator g) p := by
    simpa [q, penalizedSlackObjective] using
      squareSlackSubstitution_descendedSlackObjective
        (selectedGenerator g) p 0
  rw [← hdesc, mvPolynomialEvalFDeriv_apply]
  have hzero :
      slackPoint z (selectedEqualityIndex g e) = 0 :=
    equality_slack_eq_zero_of_mem_equalitySlackZeroSet hz e
  rw [show polynomialGradientAt
      (X (Fin.natAdd n (selectedEqualityIndex g e))) z =
        fun j ↦ if j = Fin.natAdd n (selectedEqualityIndex g e) then 1 else 0 by
    apply _root_.funext
    intro j
    simpa [equalitySlackGradientAt, equalitySlackPolynomial] using
      equalitySlackGradientAt_equality g z e j]
  rw [Finset.sum_eq_single (Fin.natAdd n (selectedEqualityIndex g e))]
  · simp only [↓reduceIte, mul_one]
    change MvPolynomial.eval z
      (MvPolynomial.pderiv (Fin.natAdd n (selectedEqualityIndex g e))
        (squareSlackSubstitution q)) = 0
    rw [pderiv_slack_squareSlackSubstitution]
    simp [slackPoint] at hzero
    simp [hzero]
  · intro j _ hj
    simp [hj]
  · simp

theorem correctedSlackObjective_equalitySystem_normal_derivative
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    {z : Fin (n + selectedConstraintCount g) → ℝ}
    (hz : z ∈ equalitySlackZeroSet g)
    (i : Fin (selectedConstraintCount g + selectedEqualityCount g)) :
    QuarticConvergence.mvPolynomialEvalFDeriv
        (correctedSlackObjective (selectedGenerator g) p) z
        (polynomialGradientAt (equalitySlackPolynomial g i) z) = 0 := by
  refine Fin.addCases ?_ ?_ i
  · intro k
    have hcore := mem_selected_slackZeroSet_of_mem_equalitySlackZeroSet hz
    simpa [equalitySlackPolynomial] using
      correctedSlackObjective_normal_derivative
        (selectedGenerator g) p hcore k
  · intro e
    simpa [equalitySlackPolynomial] using
      correctedSlackObjective_equality_normal_derivative g p hz e

theorem correctedSlackObjective_nonneg_on_equalitySlackZeroSet
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g))
    {z : Fin (n + selectedConstraintCount g) → ℝ}
    (hz : z ∈ equalitySlackZeroSet g) :
    0 ≤ MvPolynomial.eval z
      (correctedSlackObjective (selectedGenerator g) p) := by
  have hcore := mem_selected_slackZeroSet_of_mem_equalitySlackZeroSet hz
  rw [eval_correctedSlackObjective_on_zeroSet
    (selectedGenerator g) p hcore]
  exact mul_nonneg (sq_nonneg _)
    (hp (basePoint z)
      (basePoint_mem_basicClosedSet_of_mem_equalitySlackZeroSet hz))

theorem equalitySlackZeroSet_nonempty
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty) :
    (equalitySlackZeroSet g).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  exact ⟨equalitySlackLift g x, equalitySlackLift_mem_equalitySlackZeroSet hx⟩

theorem exists_scaledHypercube_containing_equalitySlackZeroSet
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (harch : GeneralArchimedean.IsArchimedean g) :
    ∃ R : ℝ, 0 < R ∧
      equalitySlackZeroSet g ⊆
        ScaledHypercube R (n + selectedConstraintCount g) ∧
      ∀ z ∈ equalitySlackZeroSet g, ∀ j, |z j| < R := by
  obtain ⟨B, hB⟩ :
      ∃ B : ℝ, ∀ z ∈ equalitySlackZeroSet g, ‖z‖ ≤ B :=
    IsCompact.exists_bound_of_continuousOn
      (equalitySlackZeroSet_isCompact harch) continuous_id.continuousOn
  let R := max B 0 + 1
  have hR : 0 < R := by
    dsimp [R]
    linarith [le_max_right B 0]
  have hstrict : ∀ z ∈ equalitySlackZeroSet g, ∀ j, |z j| < R := by
    intro z hz j
    calc
      |z j| = ‖z j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖z‖ := norm_le_pi_norm z j
      _ ≤ B := hB z hz
      _ < R := by
        dsimp [R]
        linarith [le_max_left B 0]
  refine ⟨R, hR, ?_, hstrict⟩
  intro z hz
  rw [ScaledHypercube_mem_abs R hR.le z]
  exact fun j ↦ (hstrict z hz j).le

/-- One fixed quadratic penalty makes the equality-aware corrected lift
nonnegative on a symmetric box. -/
theorem exists_penalizedEqualitySlackObjective_nonneg_on_scaledHypercube
    (hn : 0 < n)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : GeneralArchimedean.IsArchimedean g)
    (hcqc : CQCWithEqualities g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ R M : ℝ, 0 < R ∧ 0 ≤ M ∧
      equalitySlackZeroSet g ⊆
        ScaledHypercube R (n + selectedConstraintCount g) ∧
      (∀ z ∈ equalitySlackZeroSet g, ∀ j, |z j| < R) ∧
      ∀ z ∈ ScaledHypercube R (n + selectedConstraintCount g),
        0 ≤ MvPolynomial.eval z (penalizedEqualitySlackObjective g p M) := by
  obtain ⟨R, hR, hVsub, hVstrict⟩ :=
    exists_scaledHypercube_containing_equalitySlackZeroSet g harch
  have hN : 0 < n + selectedConstraintCount g := by omega
  have hregular : ∀ z ∈ polynomialZeroSet (equalitySlackPolynomial g),
      LinearIndependent ℝ
        (fun i ↦ polynomialGradientAt (equalitySlackPolynomial g i) z) := by
    intro z hz
    change LinearIndependent ℝ (equalitySlackGradientAt g z)
    exact equalitySlackGradients_linearIndependent hcqc hz
  obtain ⟨M, hM, hpenalty⟩ := exists_regularPolynomialPenalty hN
    (equalitySlackPolynomial g)
    (correctedSlackObjective (selectedGenerator g) p)
    (ScaledHypercube R (n + selectedConstraintCount g))
    (ScaledHypercube_compact R) (scaledHypercube_convex R)
    hVsub (equalitySlackZeroSet_nonempty hne)
    (equalitySlackZeroSet_isCompact harch) hregular
    (fun z hz ↦ correctedSlackObjective_nonneg_on_equalitySlackZeroSet hp hz)
    (fun z hz i ↦
      correctedSlackObjective_equalitySystem_normal_derivative g p hz i)
  refine ⟨R, M, hR, hM, hVsub, hVstrict, ?_⟩
  intro z hz
  have hz' := hpenalty z hz
  simpa [penalizedEqualitySlackObjective, penalizedSlackObjective,
    equationSquareSum_equalitySlackPolynomial, add_assoc,
    mul_add, C_mul] using hz'

theorem descendedEqualitySlackObjective_nonneg_on_slackValueBox
    {R M : ℝ} (hR : 0 < R)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (hpenalty : ∀ y ∈ ScaledHypercube R (n + selectedConstraintCount g),
      0 ≤ MvPolynomial.eval y (penalizedEqualitySlackObjective g p M)) :
    ∀ z ∈ slackValueBox R,
      0 ≤ MvPolynomial.eval z (descendedEqualitySlackObjective g p M) := by
  intro z hz
  have hroot := slackRootPoint_mem_scaledHypercube hR.le hz
  have hnonneg := hpenalty (slackRootPoint z) hroot
  rw [← squareSlackSubstitution_descendedEqualitySlackObjective,
    eval_squareSlackSubstitution] at hnonneg
  have heq : squaredSlackPoint (slackRootPoint z) = z :=
    squaredSlackPoint_slackRootPoint fun i ↦ (hz.2 i).1
  rw [heq] at hnonneg
  exact hnonneg

end CQCInternal
end OptimalConvergenceRates

end
