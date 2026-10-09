/-
  OptimalConvergenceRates/GeneralArchimedean/Stengle.lean

  The qualitative Krivine--Stengle input used by the general Archimedean
  rate argument.
-/
import OptimalConvergenceRates.KrivineStengle.MainResults

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

variable {n m : ℕ}

/-- On a nonempty feasible set, a positive perturbation generator cannot
vanish identically when the original polynomial is nonnegative. -/
theorem perturbationGenerator_ne_zero
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    KrivineStengle.perturbationGenerator p epsilon ≠ 0 := by
  obtain ⟨x, hx⟩ := hne
  intro hzero
  have heval := congrArg (MvPolynomial.eval x) hzero
  have hp0 := hp x hx
  simp only [KrivineStengle.perturbationGenerator, eval_sub, eval_neg,
    eval_C, map_zero] at heval
  linarith
/-- The exact nonnegative Krivine--Stengle witness needed in the Putinar-rate proof. -/
theorem nonnegative_krivine_stengle_witness
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    Nonempty (KrivineStengle.KSWitness g p) :=
  KrivineStengle.nonnegative_krivine_stengle g p hp

/-- The Krivine--Stengle witness gives a preordering refutation of
`-p-ε ≥ 0`, at one truncation order independent of positive `ε`. -/
theorem exists_uniform_perturbation_refutation
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ r, ∀ {ε : ℝ}, 0 < ε →
      (-1 : MvPolynomial (Fin n) ℝ) ∈
        GenPreordering
          (KrivineStengle.appendGenerator g
            (KrivineStengle.perturbationGenerator p ε)) r := by
  obtain ⟨w⟩ := nonnegative_krivine_stengle_witness g p hp
  exact w.exists_perturbation_refutation_order

end OptimalConvergenceRates.GeneralArchimedean

end
