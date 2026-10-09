import OptimalConvergenceRates.CQC.SlackValuePullback

/-!
# Geometry of nonnegative slack-value boxes
-/

noncomputable section

open MvPolynomial Set

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

/-- Replace each slack coordinate by its square. -/
def squaredSlackPoint (z : Fin (n + m) → ℝ) : Fin (n + m) → ℝ :=
  combinePoint (basePoint z) fun i ↦ (slackPoint z i) ^ 2

/-- Replace each nonnegative slack-value coordinate by its nonnegative square
root. -/
def slackRootPoint (z : Fin (n + m) → ℝ) : Fin (n + m) → ℝ :=
  combinePoint (basePoint z) fun i ↦ Real.sqrt (slackPoint z i)

/-- Product box `[-R,R]^n × [0,R²]^m`. -/
def slackValueBox (R : ℝ) : Set (Fin (n + m) → ℝ) :=
  {z | (∀ j, |basePoint z j| ≤ R) ∧
    ∀ i, 0 ≤ slackPoint z i ∧ slackPoint z i ≤ R ^ 2}

@[simp]
theorem basePoint_squaredSlackPoint (z : Fin (n + m) → ℝ) :
    basePoint (squaredSlackPoint z) = basePoint z := by
  simp [squaredSlackPoint]

@[simp]
theorem slackPoint_squaredSlackPoint
    (z : Fin (n + m) → ℝ) (i : Fin m) :
    slackPoint (squaredSlackPoint z) i = (slackPoint z i) ^ 2 := by
  simp [squaredSlackPoint]

@[simp]
theorem eval_squareSlackSubstitution
    (z : Fin (n + m) → ℝ)
    (P : MvPolynomial (Fin (n + m)) ℝ) :
    MvPolynomial.eval z (squareSlackSubstitution P) =
      MvPolynomial.eval (squaredSlackPoint z) P := by
  unfold squareSlackSubstitution
  change MvPolynomial.eval₂Hom (RingHom.id ℝ) z
      (MvPolynomial.bind₁ _ P) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  have hcoords :
      (fun i ↦ MvPolynomial.eval₂Hom (RingHom.id ℝ) z
        (Fin.addCases (fun k ↦ X (Fin.castAdd m k))
          (fun i ↦ X (Fin.natAdd n i) ^ 2) i)) = squaredSlackPoint z := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro k
      simp only [Fin.addCases_left, MvPolynomial.eval₂Hom_X']
      change basePoint z k = basePoint (squaredSlackPoint z) k
      simp [squaredSlackPoint]
    · intro i
      simp only [Fin.addCases_right, map_pow, MvPolynomial.eval₂Hom_X']
      change (slackPoint z i) ^ 2 = slackPoint (squaredSlackPoint z) i
      simp [squaredSlackPoint]
  rw [hcoords]
  rfl

theorem squaredSlackPoint_slackRootPoint
    {z : Fin (n + m) → ℝ}
    (hz : ∀ i, 0 ≤ slackPoint z i) :
    squaredSlackPoint (slackRootPoint z) = z := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro k
    change basePoint (squaredSlackPoint (slackRootPoint z)) k = basePoint z k
    simp [squaredSlackPoint, slackRootPoint]
  · intro i
    change slackPoint (squaredSlackPoint (slackRootPoint z)) i = slackPoint z i
    simp [squaredSlackPoint, slackRootPoint, Real.sq_sqrt (hz i)]

theorem slackRootPoint_mem_scaledHypercube
    {R : ℝ} (hR : 0 ≤ R) {z : Fin (n + m) → ℝ}
    (hz : z ∈ slackValueBox R) :
    slackRootPoint z ∈ ScaledHypercube R (n + m) := by
  rw [ScaledHypercube_mem_abs R hR]
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro k
    change |basePoint (slackRootPoint z) k| ≤ R
    rw [show basePoint (slackRootPoint z) = basePoint z by
      simp [slackRootPoint]]
    exact hz.1 k
  · intro i
    change |slackPoint (slackRootPoint z) i| ≤ R
    rw [show slackPoint (slackRootPoint z) i =
        Real.sqrt (slackPoint z i) by simp [slackRootPoint]]
    have hui := hz.2 i
    have hsqrt : 0 ≤ Real.sqrt (slackPoint z i) := Real.sqrt_nonneg _
    have hsq : (Real.sqrt (slackPoint z i)) ^ 2 = slackPoint z i :=
      Real.sq_sqrt hui.1
    rw [abs_of_nonneg hsqrt]
    nlinarith

/-- Nonnegativity of the even squared-slack lift descends to the product box
in the independent slack values. -/
theorem descendedSlackObjective_nonneg_on_slackValueBox
    {R M : ℝ} (hR : 0 < R)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (hpenalty : ∀ y ∈ ScaledHypercube R (n + m),
      0 ≤ MvPolynomial.eval y (penalizedSlackObjective g p M)) :
    ∀ z ∈ slackValueBox R,
      0 ≤ MvPolynomial.eval z (descendedSlackObjective g p M) := by
  intro z hz
  have hroot := slackRootPoint_mem_scaledHypercube hR.le hz
  have hnonneg := hpenalty (slackRootPoint z) hroot
  rw [← squareSlackSubstitution_descendedSlackObjective,
    eval_squareSlackSubstitution] at hnonneg
  have heq : squaredSlackPoint (slackRootPoint z) = z :=
    squaredSlackPoint_slackRootPoint fun i ↦ (hz.2 i).1
  rw [heq] at hnonneg
  exact hnonneg

end CQCInternal
end OptimalConvergenceRates

end
