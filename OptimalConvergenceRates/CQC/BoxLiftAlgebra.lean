import OptimalConvergenceRates.CQC.DeterminantMultiplier
import OptimalConvergenceRates.CQC.RegularPenaltyGlobal

/-!
# Algebra of the corrected squared-slack lift
-/

noncomputable section

open MvPolynomial Finset Set Matrix

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

/-- Polynomial Jacobian of the squared-slack equations. -/
def slackJacobianPolynomial (g : Fin m → MvPolynomial (Fin n) ℝ) :
    Matrix (Fin m) (Fin (n + m)) (MvPolynomial (Fin (n + m)) ℝ) :=
  fun i j ↦ MvPolynomial.pderiv j (slackPolynomial g i)

/-- Polynomial row Gram matrix of the squared-slack Jacobian. -/
def slackGramPolynomial (g : Fin m → MvPolynomial (Fin n) ℝ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin (n + m)) ℝ) :=
  slackJacobianPolynomial g * (slackJacobianPolynomial g)ᵀ

/-- Determinant of the squared-slack row Gram matrix. -/
def slackDeterminant (g : Fin m → MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin (n + m)) ℝ :=
  Matrix.det (slackGramPolynomial g)

/-- The vector `2 p grad Delta + Delta grad p` in the combined variables. -/
def slackW (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) :
    Fin (n + m) → MvPolynomial (Fin (n + m)) ℝ :=
  fun j ↦ MvPolynomial.C 2 * liftBasePolynomial p *
      MvPolynomial.pderiv j (slackDeterminant g) +
    slackDeterminant g * MvPolynomial.pderiv j (liftBasePolynomial p)

/-- Adjugate correction coefficients. -/
def slackCorrection (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) :
    Fin m → MvPolynomial (Fin (n + m)) ℝ :=
  (slackGramPolynomial g).adjugate *ᵥ
    ((slackJacobianPolynomial g) *ᵥ slackW g p)

/-- Corrected extension whose normal first derivatives vanish on the slack
zero set. -/
def correctedSlackObjective (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin (n + m)) ℝ :=
  (slackDeterminant g) ^ 2 * liftBasePolynomial p -
    ∑ i, slackPolynomial g i * slackCorrection g p i

/-- Corrected extension plus a scalar multiple of the squared equations. -/
def penalizedSlackObjective (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (M : ℝ) :
    MvPolynomial (Fin (n + m)) ℝ :=
  correctedSlackObjective g p + MvPolynomial.C M *
    equationSquareSum (slackPolynomial g)

theorem pderiv_rename_eq_zero_of_not_mem_range
    {σ τ : Type*} (f : σ → τ) (y : τ) (P : MvPolynomial σ ℝ)
    (hy : y ∉ Set.range f) :
    MvPolynomial.pderiv y (MvPolynomial.rename f P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      have hne : f i ≠ y := fun hiy ↦ hy ⟨i, hiy⟩
      simp [hP, hne]

theorem polynomialGradientAt_slackPolynomial
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin (n + m) → ℝ) (i : Fin m) :
    polynomialGradientAt (slackPolynomial g i) z = slackGradientAt g z i := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro k
    have hdis : Fin.castAdd m k ≠ Fin.natAdd n i := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    change MvPolynomial.eval z
      (MvPolynomial.pderiv (Fin.castAdd m k) (slackPolynomial g i)) = _
    rw [show MvPolynomial.pderiv (Fin.castAdd m k) (slackPolynomial g i) =
        liftBasePolynomial (MvPolynomial.pderiv k (g i)) by
      simp [slackPolynomial, liftBasePolynomial,
        MvPolynomial.pderiv_rename (Fin.castAdd_injective n m), hdis]]
    simp [slackGradientAt]
  · intro k
    have hout : Fin.natAdd n k ∉ Set.range (Fin.castAdd m) := by
      rintro ⟨l, hl⟩
      have hval := congrArg Fin.val hl
      simp at hval
      omega
    change MvPolynomial.eval z
      (MvPolynomial.pderiv (Fin.natAdd n k) (slackPolynomial g i)) = _
    rw [show MvPolynomial.pderiv (Fin.natAdd n k) (slackPolynomial g i) =
        if k = i then -(2 • X (Fin.natAdd n i)) else 0 by
      simp [slackPolynomial, liftBasePolynomial,
        pderiv_rename_eq_zero_of_not_mem_range _ _ _ hout]
      by_cases hki : k = i
      · subst k
        simp
      · have hne : Fin.natAdd n k ≠ Fin.natAdd n i := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
          exact hki (Fin.ext hv)
        simp [hki, hne]]
    by_cases hki : k = i
    · subst k
      simp [slackGradientAt, slackPoint]
    · simp [slackGradientAt, slackPoint, hki]

@[simp]
theorem eval_slackJacobianPolynomial
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin (n + m) → ℝ) (i : Fin m) (j : Fin (n + m)) :
    MvPolynomial.eval z (slackJacobianPolynomial g i j) =
      slackJacobianAt g z i j := by
  change polynomialGradientAt (slackPolynomial g i) z j = _
  rw [polynomialGradientAt_slackPolynomial]
  rfl

@[simp]
theorem eval_slackGramPolynomial
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin (n + m) → ℝ) (i k : Fin m) :
    MvPolynomial.eval z (slackGramPolynomial g i k) =
      slackGramAt g z i k := by
  simp [slackGramPolynomial, slackGramAt, Matrix.mul_apply,
    slackJacobianAt]

@[simp]
theorem eval_slackDeterminant
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin (n + m) → ℝ) :
    MvPolynomial.eval z (slackDeterminant g) =
      Matrix.det (slackGramAt g z) := by
  let ev : MvPolynomial (Fin (n + m)) ℝ →+* ℝ :=
    MvPolynomial.eval₂Hom (RingHom.id ℝ) z
  calc
    MvPolynomial.eval z (slackDeterminant g) =
        ev (Matrix.det (slackGramPolynomial g)) := by
          simp [slackDeterminant, ev, MvPolynomial.eval₂_id]
    _ = Matrix.det (ev.mapMatrix (slackGramPolynomial g)) :=
      RingHom.map_det ev (slackGramPolynomial g)
    _ = Matrix.det (slackGramAt g z) := by
      congr 1
      ext i k
      simp [ev, MvPolynomial.eval₂_id]

theorem eval_slackDeterminant_pos
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hcqc : ActiveGradientIndependent g)
    {z : Fin (n + m) → ℝ} (hz : z ∈ slackZeroSet g) :
    0 < MvPolynomial.eval z (slackDeterminant g) := by
  rw [eval_slackDeterminant]
  exact (slackGramAt_posDef hcqc hz).det_pos

end CQCInternal
end OptimalConvergenceRates

end
