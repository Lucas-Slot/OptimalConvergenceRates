import Mathlib.Algebra.MvPolynomial.PDeriv
import OptimalConvergenceRates.CQC.SlackRegularity

/-! Public definition of the constraint qualification used by the CQC results. -/

noncomputable section

namespace OptimalConvergenceRates

variable {n m : ℕ}

/-- An inequality generator has an explicit opposite when a distinct member of
the same family is exactly its negation. -/
def HasOppositeConstraint (g : Fin m → MvPolynomial (Fin n) ℝ) (i : Fin m) : Prop :=
  ∃ j, j ≠ i ∧ g j = -g i

/-- The canonical representative of an equality encoded by a signed generator
pair is the least index in its entire class up to sign. -/
def IsEqualityRepresentative (g : Fin m → MvPolynomial (Fin n) ℝ) (i : Fin m) : Prop :=
  HasOppositeConstraint g i ∧
    ∀ j, (g j = g i ∨ g j = -g i) → i ≤ j

/-- Indices whose gradients participate in `CQCWithEqualities`: every active
ordinary inequality and one canonical representative of every encoded
equality. -/
def IsActiveWithEqualities (g : Fin m → MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) (i : Fin m) : Prop :=
  MvPolynomial.eval x (g i) = 0 ∧
    (¬HasOppositeConstraint g i ∨ IsEqualityRepresentative g i)

/-- Opposite inequalities force their common polynomial to vanish at every
feasible point. -/
theorem eval_eq_zero_of_hasOppositeConstraint
    {g : Fin m → MvPolynomial (Fin n) ℝ} {x : Fin n → ℝ}
    (hx : x ∈ KrivineStengle.basicClosedSet g) {i : Fin m}
    (hi : HasOppositeConstraint g i) :
    MvPolynomial.eval x (g i) = 0 := by
  obtain ⟨j, -, hj⟩ := hi
  have hgi := hx i
  have hgj := hx j
  rw [hj, map_neg] at hgj
  linarith

/-- The constraint qualification used by the transfer theorem: at every
feasible point, the gradients of the active members of the specified
generator family are linearly independent. -/
def CQC (g : Fin m → MvPolynomial (Fin n) ℝ) : Prop :=
  letI : NormedSpace ℝ ℝ := NormedField.toNormedSpace
  ∀ x ∈ KrivineStengle.basicClosedSet g,
    LinearIndependent ℝ
      (fun i : {i : Fin m // MvPolynomial.eval x (g i) = 0} ↦
        fun j : Fin n ↦ MvPolynomial.eval x (MvPolynomial.pderiv j (g i)))

/-- Constraint qualification for inequality-only presentations that encode an
equality `q = 0` by including both `q` and `-q` as generators. This module does
not allow equality constraints explicitly, so every exact signed class is
treated as one equality constraint when testing linear independence of the
active gradients. -/
def CQCWithEqualities (g : Fin m → MvPolynomial (Fin n) ℝ) : Prop :=
  letI : NormedSpace ℝ ℝ := NormedField.toNormedSpace
  ∀ x ∈ KrivineStengle.basicClosedSet g,
    LinearIndependent ℝ
      (fun i : {i : Fin m // IsActiveWithEqualities g x i} ↦
        fun j : Fin n ↦ MvPolynomial.eval x (MvPolynomial.pderiv j (g i)))

/-- Ordinary CQC implies the equality-aware version by restriction to the
selected active indices. -/
theorem cqcWithEqualities_of_cqc {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hcqc : CQC g) : CQCWithEqualities g := by
  intro x hx
  let inclusion : {i : Fin m // IsActiveWithEqualities g x i} →
      {i : Fin m // MvPolynomial.eval x (g i) = 0} :=
    fun i ↦ ⟨i, i.2.1⟩
  have hinjective : Function.Injective inclusion := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun k : {i : Fin m // MvPolynomial.eval x (g i) = 0} ↦ k.1) hij
  exact (hcqc x hx).comp inclusion hinjective

end OptimalConvergenceRates

end
