import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import OptimalConvergenceRates.GeneralArchimedean.ArchimedeanGeometry

/-!
# Squared slacks and CQC regularity

The original variables occupy the first `n` coordinates of `Fin (n + m)` and
the slack variables occupy the final `m` coordinates.
-/

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

/-- Restriction of a combined point to the original variables. -/
def basePoint (z : Fin (n + m) → ℝ) : Fin n → ℝ :=
  fun i ↦ z (Fin.castAdd m i)

/-- Restriction of a combined point to the slack variables. -/
def slackPoint (z : Fin (n + m) → ℝ) : Fin m → ℝ :=
  fun i ↦ z (Fin.natAdd n i)

/-- Combine original and slack coordinates. -/
def combinePoint (x : Fin n → ℝ) (y : Fin m → ℝ) : Fin (n + m) → ℝ :=
  Fin.addCases x y

@[simp]
theorem basePoint_combinePoint (x : Fin n → ℝ) (y : Fin m → ℝ) :
    basePoint (combinePoint x y) = x := by
  funext i
  simp [basePoint, combinePoint]

@[simp]
theorem slackPoint_combinePoint (x : Fin n → ℝ) (y : Fin m → ℝ) :
    slackPoint (combinePoint x y) = y := by
  funext i
  simp [slackPoint, combinePoint]

/-- Embed a polynomial in the original variables into the combined variable
space. -/
def liftBasePolynomial (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin (n + m)) ℝ :=
  MvPolynomial.rename (Fin.castAdd m) p

@[simp]
theorem eval_liftBasePolynomial (z : Fin (n + m) → ℝ)
    (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.eval z (liftBasePolynomial p) =
      MvPolynomial.eval (basePoint z) p := by
  rw [liftBasePolynomial, MvPolynomial.eval_rename]
  rfl

/-- The squared-slack equation `g_i(x) - y_i^2`. -/
def slackPolynomial (g : Fin m → MvPolynomial (Fin n) ℝ) (i : Fin m) :
    MvPolynomial (Fin (n + m)) ℝ :=
  liftBasePolynomial (g i) - X (Fin.natAdd n i) ^ 2

@[simp]
theorem eval_slackPolynomial
    (g : Fin m → MvPolynomial (Fin n) ℝ) (i : Fin m)
    (z : Fin (n + m) → ℝ) :
    MvPolynomial.eval z (slackPolynomial g i) =
      MvPolynomial.eval (basePoint z) (g i) - (slackPoint z i) ^ 2 := by
  simp [slackPolynomial, slackPoint]

/-- Common zero set of all squared-slack equations. -/
def slackZeroSet (g : Fin m → MvPolynomial (Fin n) ℝ) :
    Set (Fin (n + m) → ℝ) :=
  {z | ∀ i, MvPolynomial.eval z (slackPolynomial g i) = 0}

/-- The active-gradient condition used internally. `MainResults.lean` exposes
the same formula under the public name `CQC`. -/
def ActiveGradientIndependent
    (g : Fin m → MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ x ∈ KrivineStengle.basicClosedSet g,
    LinearIndependent ℝ
      (fun i : {i : Fin m // MvPolynomial.eval x (g i) = 0} ↦
        fun j : Fin n ↦ MvPolynomial.eval x (MvPolynomial.pderiv j (g i)))

/-- Projection of a slack zero is feasible for the original inequalities. -/
theorem basePoint_mem_basicClosedSet_of_mem_slackZeroSet
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {z : Fin (n + m) → ℝ} (hz : z ∈ slackZeroSet g) :
    basePoint z ∈ KrivineStengle.basicClosedSet g := by
  intro i
  have hi := hz i
  rw [eval_slackPolynomial] at hi
  nlinarith [sq_nonneg (slackPoint z i)]

/-- Canonical set-theoretic lift of a feasible point using nonnegative square
roots. It is used only for geometry, never in a certificate substitution. -/
def slackLift (g : Fin m → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    Fin (n + m) → ℝ :=
  combinePoint x fun i ↦ Real.sqrt (MvPolynomial.eval x (g i))

@[simp]
theorem basePoint_slackLift
    (g : Fin m → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    basePoint (slackLift g x) = x := by
  simp [slackLift]

@[simp]
theorem slackPoint_slackLift
    (g : Fin m → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (i : Fin m) :
    slackPoint (slackLift g x) i = Real.sqrt (MvPolynomial.eval x (g i)) := by
  simp [slackLift]

/-- Every feasible point has a squared-slack lift. -/
theorem slackLift_mem_slackZeroSet
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {x : Fin n → ℝ} (hx : x ∈ KrivineStengle.basicClosedSet g) :
    slackLift g x ∈ slackZeroSet g := by
  intro i
  rw [eval_slackPolynomial, basePoint_slackLift, slackPoint_slackLift]
  rw [Real.sq_sqrt (hx i)]
  ring

/-- The slack zero set is nonempty whenever the original feasible set is. -/
theorem slackZeroSet_nonempty
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty) :
    (slackZeroSet g).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  exact ⟨slackLift g x, slackLift_mem_slackZeroSet hx⟩

/-- The squared-slack zero set is closed. -/
theorem slackZeroSet_isClosed
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    IsClosed (slackZeroSet g) := by
  rw [show slackZeroSet g =
      ⋂ i, {z | MvPolynomial.eval z (slackPolynomial g i) = 0} by
    ext z
    simp [slackZeroSet]]
  exact isClosed_iInter fun i ↦
    isClosed_eq (continuous_eval (slackPolynomial g i)) continuous_const

end CQCInternal
end OptimalConvergenceRates

end
