import OptimalConvergenceRates.CQC.SlackRegularity

/-!
# Geometry of the squared-slack variety

This file proves compactness of the squared-slack variety by exhibiting it as
a finite union of continuous images of the original feasible set. The finite
index records the choices of signs of the slack coordinates.
-/

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

/-- A lift of a feasible point with a prescribed sign for every square root. -/
def signedSlackLift (g : Fin m → MvPolynomial (Fin n) ℝ)
    (s : Fin m → Bool) (x : Fin n → ℝ) : Fin (n + m) → ℝ :=
  combinePoint x fun i ↦
    if s i then -Real.sqrt (MvPolynomial.eval x (g i))
    else Real.sqrt (MvPolynomial.eval x (g i))

@[simp]
theorem basePoint_signedSlackLift
    (g : Fin m → MvPolynomial (Fin n) ℝ) (s : Fin m → Bool)
    (x : Fin n → ℝ) :
    basePoint (signedSlackLift g s x) = x := by
  simp [signedSlackLift]

@[simp]
theorem slackPoint_signedSlackLift
    (g : Fin m → MvPolynomial (Fin n) ℝ) (s : Fin m → Bool)
    (x : Fin n → ℝ) (i : Fin m) :
    slackPoint (signedSlackLift g s x) i =
      if s i then -Real.sqrt (MvPolynomial.eval x (g i))
      else Real.sqrt (MvPolynomial.eval x (g i)) := by
  simp [signedSlackLift]

/-- Every signed square-root lift of a feasible point lies on the slack
variety. -/
theorem signedSlackLift_mem_slackZeroSet
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {x : Fin n → ℝ} (hx : x ∈ KrivineStengle.basicClosedSet g)
    (s : Fin m → Bool) :
    signedSlackLift g s x ∈ slackZeroSet g := by
  intro i
  rw [eval_slackPolynomial, basePoint_signedSlackLift,
    slackPoint_signedSlackLift]
  split_ifs
  · rw [neg_sq, Real.sq_sqrt (hx i)]
    ring
  · rw [Real.sq_sqrt (hx i)]
    ring

/-- For fixed signs, the signed square-root lift is continuous. -/
theorem continuous_signedSlackLift
    (g : Fin m → MvPolynomial (Fin n) ℝ) (s : Fin m → Bool) :
    Continuous (signedSlackLift g s) := by
  apply continuous_pi
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simpa [signedSlackLift, combinePoint] using
      (continuous_apply i : Continuous (fun x : Fin n → ℝ ↦ x i))
  · intro i
    by_cases hs : s i = true
    · simp only [signedSlackLift, combinePoint, Fin.addCases_right, hs,
        ↓reduceIte]
      exact (Real.continuous_sqrt.comp (continuous_eval (g i))).neg
    · have hs' : s i = false := Bool.eq_false_of_not_eq_true hs
      simp only [signedSlackLift, combinePoint, Fin.addCases_right, hs',
        Bool.false_eq_true, ↓reduceIte]
      exact Real.continuous_sqrt.comp (continuous_eval (g i))

/-- Every point on the slack variety is one of the finitely many signed
square-root lifts. -/
theorem slackZeroSet_eq_iUnion_signedSlackLift
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    slackZeroSet g =
      ⋃ s : Fin m → Bool,
        signedSlackLift g s '' KrivineStengle.basicClosedSet g := by
  ext z
  constructor
  · intro hz
    let s : Fin m → Bool := fun i ↦ decide (slackPoint z i < 0)
    refine Set.mem_iUnion.2 ⟨s, ?_⟩
    refine ⟨basePoint z, basePoint_mem_basicClosedSet_of_mem_slackZeroSet hz, ?_⟩
    apply funext
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simp [signedSlackLift, combinePoint, basePoint]
    · intro i
      have hi := hz i
      rw [eval_slackPolynomial] at hi
      have hsquare : MvPolynomial.eval (basePoint z) (g i) =
          (slackPoint z i) ^ 2 := by linarith
      simp only [signedSlackLift, combinePoint, Fin.addCases_right]
      by_cases hy : slackPoint z i < 0
      · have hy' : z (Fin.natAdd n i) < 0 := by
          simpa [slackPoint] using hy
        simp [s, hy, hy', hsquare, Real.sqrt_sq_eq_abs, slackPoint]
        simpa [abs_of_neg hy']
      · have hy0 : 0 ≤ slackPoint z i := le_of_not_gt hy
        have hy0' : 0 ≤ z (Fin.natAdd n i) := by
          simpa [slackPoint] using hy0
        have hnot : ¬ z (Fin.natAdd n i) < 0 := not_lt.mpr hy0'
        simp [s, hy, hy0', hnot, hsquare, Real.sqrt_sq_eq_abs, slackPoint]
  · intro hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨s, x, hx, rfl⟩ := hz
    exact signedSlackLift_mem_slackZeroSet hx s

/-- The squared-slack variety is compact under the Archimedean hypothesis. -/
theorem slackZeroSet_isCompact
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (harch : GeneralArchimedean.IsArchimedean g) :
    IsCompact (slackZeroSet g) := by
  rw [slackZeroSet_eq_iUnion_signedSlackLift]
  exact isCompact_iUnion fun s ↦
    harch.isCompact_basicClosedSet.image (continuous_signedSlackLift g s)

end CQCInternal
end OptimalConvergenceRates

end
