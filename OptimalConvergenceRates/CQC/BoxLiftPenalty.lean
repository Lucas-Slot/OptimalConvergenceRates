import OptimalConvergenceRates.CQC.BoxLiftCancellation

/-!
# A fixed nonnegative penalized squared-slack lift
-/

noncomputable section

open MvPolynomial Finset Set

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

theorem scaledHypercube_convex (R : ℝ) :
    Convex ℝ (ScaledHypercube R n) := by
  exact convex_pi fun _ _ ↦ convex_Icc _ _

/-- Compactness of the squared-slack variety supplies a fixed symmetric box
strictly containing it coordinatewise. -/
theorem exists_scaledHypercube_containing_slackZeroSet
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (harch : GeneralArchimedean.IsArchimedean g) :
    ∃ R : ℝ, 0 < R ∧
      slackZeroSet g ⊆ ScaledHypercube R (n + m) ∧
      ∀ z ∈ slackZeroSet g, ∀ j, |z j| < R := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ z ∈ slackZeroSet g, ‖z‖ ≤ B :=
    IsCompact.exists_bound_of_continuousOn
      (slackZeroSet_isCompact harch) continuous_id.continuousOn
  let R := max B 0 + 1
  have hR : 0 < R := by
    dsimp [R]
    linarith [le_max_right B 0]
  have hstrict : ∀ z ∈ slackZeroSet g, ∀ j, |z j| < R := by
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

/-- Under CQC, one fixed quadratic equation penalty makes the corrected lift
nonnegative on one fixed symmetric box. The slack variety lies strictly in
the interior of that box. -/
theorem exists_penalizedSlackObjective_nonneg_on_scaledHypercube
    (hn : 0 < n)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : GeneralArchimedean.IsArchimedean g)
    (hcqc : ActiveGradientIndependent g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ R M : ℝ, 0 < R ∧ 0 ≤ M ∧
      slackZeroSet g ⊆ ScaledHypercube R (n + m) ∧
      (∀ z ∈ slackZeroSet g, ∀ j, |z j| < R) ∧
      ∀ z ∈ ScaledHypercube R (n + m),
        0 ≤ MvPolynomial.eval z (penalizedSlackObjective g p M) := by
  obtain ⟨R, hR, hVsub, hVstrict⟩ :=
    exists_scaledHypercube_containing_slackZeroSet g harch
  have hN : 0 < n + m := by omega
  have hregular : ∀ z ∈ polynomialZeroSet (slackPolynomial g),
      LinearIndependent ℝ
        (fun i ↦ polynomialGradientAt (slackPolynomial g i) z) := by
    intro z hz
    rw [show polynomialZeroSet (slackPolynomial g) = slackZeroSet g from rfl] at hz
    simpa only [polynomialGradientAt_slackPolynomial] using
      slackGradients_linearIndependent hcqc hz
  obtain ⟨M, hM, hpenalty⟩ := exists_regularPolynomialPenalty hN
    (slackPolynomial g) (correctedSlackObjective g p)
    (ScaledHypercube R (n + m))
    (ScaledHypercube_compact R) (scaledHypercube_convex R)
    hVsub (slackZeroSet_nonempty hne) (slackZeroSet_isCompact harch)
    hregular
    (fun z hz ↦ eval_correctedSlackObjective_nonneg_on_zeroSet hp hz)
    (fun z hz i ↦ correctedSlackObjective_normal_derivative g p hz i)
  exact ⟨R, M, hR, hM, hVsub, hVstrict, hpenalty⟩

end CQCInternal
end OptimalConvergenceRates

end
