import OptimalConvergenceRates.CQC.BoxLiftPenalty
import OptimalConvergenceRates.CQC.SlackValueGeometry

/-!
# The fixed descended box lift
-/

noncomputable section

open MvPolynomial Set

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

/-- The analytic squared-slack construction, packaged in the descended slack
variables. The same radius strictly bounds both the original coordinates and
the square roots of the generator values on the feasible set. -/
theorem exists_descendedSlackObjective
    (hn : 0 < n)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : GeneralArchimedean.IsArchimedean g)
    (hcqc : ActiveGradientIndependent g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ R M : ℝ, 0 < R ∧ 0 ≤ M ∧
      (∀ z ∈ slackValueBox R,
        0 ≤ MvPolynomial.eval z (descendedSlackObjective g p M)) ∧
      (∀ x ∈ KrivineStengle.basicClosedSet g, ∀ j, |x j| < R) ∧
      (∀ x ∈ KrivineStengle.basicClosedSet g, ∀ i,
        MvPolynomial.eval x (g i) < R ^ 2) ∧
      generatorSlackSubstitution g (descendedSlackObjective g p M) =
        determinantMultiplier g ^ 2 * p ∧
      (∀ x ∈ KrivineStengle.basicClosedSet g,
        0 < MvPolynomial.eval x (determinantMultiplier g)) := by
  obtain ⟨R, M, hR, hM, -, hstrict, hpenalty⟩ :=
    exists_penalizedSlackObjective_nonneg_on_scaledHypercube hn
      hne harch hcqc hp
  have hdesc := descendedSlackObjective_nonneg_on_slackValueBox
    hR g p hpenalty
  have hbase : ∀ x ∈ KrivineStengle.basicClosedSet g, ∀ j, |x j| < R := by
    intro x hx j
    have hz := hstrict (slackLift g x) (slackLift_mem_slackZeroSet hx)
      (Fin.castAdd m j)
    change |basePoint (slackLift g x) j| < R at hz
    simpa only [basePoint_slackLift] using hz
  have hslack : ∀ x ∈ KrivineStengle.basicClosedSet g, ∀ i,
      MvPolynomial.eval x (g i) < R ^ 2 := by
    intro x hx i
    have hz := hstrict (slackLift g x) (slackLift_mem_slackZeroSet hx)
      (Fin.natAdd n i)
    change |slackPoint (slackLift g x) i| < R at hz
    rw [slackPoint_slackLift] at hz
    have hsq : (Real.sqrt (MvPolynomial.eval x (g i))) ^ 2 =
        MvPolynomial.eval x (g i) := Real.sq_sqrt (hx i)
    have hsqrt0 := Real.sqrt_nonneg (MvPolynomial.eval x (g i))
    rw [abs_of_nonneg hsqrt0] at hz
    nlinarith
  exact ⟨R, M, hR, hM, hdesc, hbase, hslack,
    generatorSlackSubstitution_descendedSlackObjective g p M,
    determinantMultiplier_posOn hcqc⟩

end CQCInternal
end OptimalConvergenceRates

end
