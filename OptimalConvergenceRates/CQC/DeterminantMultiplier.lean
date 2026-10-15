import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.ContinuousFunctionalCalculus
import OptimalConvergenceRates.CQC.SlackRank

/-!
# The CQC determinant multiplier

The squared-slack Jacobian has independent rows on its zero set. Consequently
its row Gram determinant is positive. Substituting `y_i^2 = g_i(x)` produces
the fixed polynomial multiplier used by the transfer argument.
-/

noncomputable section

open MvPolynomial Finset Matrix

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

/-- The evaluated squared-slack Jacobian, with constraints indexing rows. -/
def slackJacobianAt (g : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin (n + m) → ℝ) : Matrix (Fin m) (Fin (n + m)) ℝ :=
  fun i j ↦ slackGradientAt g z i j

/-- The row Gram matrix of the squared-slack Jacobian. -/
def slackGramAt (g : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin (n + m) → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  slackJacobianAt g z * (slackJacobianAt g z)ᵀ

/-- Linear independence of the slack gradients is exactly the injectivity
needed by the row-Gram positive-definiteness theorem. -/
theorem slackJacobianAt_vecMul_injective
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {z : Fin (n + m) → ℝ}
    (hli : LinearIndependent ℝ (slackGradientAt g z)) :
    Function.Injective (slackJacobianAt g z).vecMul := by
  intro c d hcd
  have hsum : ∑ i, (c i - d i) • slackGradientAt g z i = 0 := by
    apply funext
    intro j
    have hj := congrFun hcd j
    simp only [Matrix.vecMul, dotProduct, slackJacobianAt] at hj
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hj
  have hzero := (Fintype.linearIndependent_iff.mp hli) (fun i ↦ c i - d i) hsum
  funext i
  exact sub_eq_zero.mp (hzero i)

/-- The squared-slack Gram matrix is positive definite on the slack variety. -/
theorem slackGramAt_posDef
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hcqc : ActiveGradientIndependent g)
    {z : Fin (n + m) → ℝ} (hz : z ∈ slackZeroSet g) :
    (slackGramAt g z).PosDef := by
  have hinj := slackJacobianAt_vecMul_injective
    (slackGradients_linearIndependent hcqc hz)
  simpa [slackGramAt] using
    Matrix.PosDef.mul_conjTranspose_self (slackJacobianAt g z) hinj

/-- The polynomial Gram matrix obtained after replacing the square of each
slack variable by the corresponding generator. -/
def cqcGramPolynomial (g : Fin m → MvPolynomial (Fin n) ℝ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ) :=
  fun i k ↦
    (∑ j : Fin n, MvPolynomial.pderiv j (g i) *
      MvPolynomial.pderiv j (g k)) +
      if i = k then MvPolynomial.C 4 * g i else 0

/-- Evaluation of the polynomial Gram matrix. -/
def cqcGramAt (g : Fin m → MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i k ↦
    (∑ j : Fin n,
      MvPolynomial.eval x (MvPolynomial.pderiv j (g i)) *
      MvPolynomial.eval x (MvPolynomial.pderiv j (g k))) +
      if i = k then 4 * MvPolynomial.eval x (g i) else 0

@[simp]
theorem eval_cqcGramPolynomial
    (g : Fin m → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ)
    (i k : Fin m) :
    MvPolynomial.eval x (cqcGramPolynomial g i k) = cqcGramAt g x i k := by
  by_cases hik : i = k <;> simp [cqcGramPolynomial, cqcGramAt, hik]

/-- On the slack variety, the evaluated polynomial Gram matrix is the row
Gram matrix of the squared-slack Jacobian. -/
theorem cqcGramAt_eq_slackGramAt
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {z : Fin (n + m) → ℝ} (hz : z ∈ slackZeroSet g) :
    cqcGramAt g (basePoint z) = slackGramAt g z := by
  ext i k
  rw [slackGramAt, Matrix.mul_apply, Fin.sum_univ_add]
  simp only [Matrix.transpose_apply, slackJacobianAt, slackGradientAt_base,
    slackGradientAt_slack]
  have hdiag :
      (∑ j : Fin m,
        (if j = i then -2 * slackPoint z i else 0) *
          (if j = k then -2 * slackPoint z k else 0)) =
        if i = k then 4 * MvPolynomial.eval (basePoint z) (g i) else 0 := by
    by_cases hik : i = k
    · subst k
      rw [Finset.sum_eq_single i]
      · have hi := hz i
        rw [eval_slackPolynomial] at hi
        simp only [↓reduceIte]
        nlinarith
      · intro j _ hji
        simp [hji]
      · simp
    · simp only [ite_eq_right hik]
      apply Fintype.sum_eq_zero
      intro j
      by_cases hji : j = i
      · subst j
        simp [hik]
      · simp [hji]
  rw [hdiag]
  rfl

/-- The determinant multiplier `a(x)`. -/
def determinantMultiplier (g : Fin m → MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  Matrix.det (cqcGramPolynomial g)

@[simp]
theorem eval_determinantMultiplier
    (g : Fin m → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval x (determinantMultiplier g) =
      Matrix.det (cqcGramAt g x) := by
  let ev : MvPolynomial (Fin n) ℝ →+* ℝ :=
    MvPolynomial.eval₂Hom (RingHom.id ℝ) x
  calc
    MvPolynomial.eval x (determinantMultiplier g) =
        ev (Matrix.det (cqcGramPolynomial g)) := by
          simp [determinantMultiplier, ev, MvPolynomial.eval₂_id]
    _ = Matrix.det (ev.mapMatrix (cqcGramPolynomial g)) :=
      RingHom.map_det ev (cqcGramPolynomial g)
    _ = Matrix.det (cqcGramAt g x) := by
      congr 1
      ext i k
      simp [ev, MvPolynomial.eval₂_id]

/-- CQC makes the determinant multiplier strictly positive everywhere on the
original feasible set. -/
theorem determinantMultiplier_posOn
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hcqc : ActiveGradientIndependent g) :
    ∀ x ∈ KrivineStengle.basicClosedSet g,
      0 < MvPolynomial.eval x (determinantMultiplier g) := by
  intro x hx
  have hz : slackLift g x ∈ slackZeroSet g :=
    slackLift_mem_slackZeroSet hx
  rw [eval_determinantMultiplier]
  have heq : cqcGramAt g x = slackGramAt g (slackLift g x) := by
    simpa using cqcGramAt_eq_slackGramAt hz
  rw [heq]
  exact (slackGramAt_posDef hcqc hz).det_pos

end CQCInternal
end OptimalConvergenceRates

end
