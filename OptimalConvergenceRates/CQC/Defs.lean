import Mathlib.Algebra.MvPolynomial.PDeriv
import OptimalConvergenceRates.CQC.SlackRegularity

/-! Public definition of the constraint qualification used by the CQC results. -/

noncomputable section

namespace OptimalConvergenceRates

/-- The constraint qualification used by the transfer theorem: at every
feasible point, the gradients of the active members of the specified
generator family are linearly independent. -/
def CQC {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ) : Prop :=
  letI : NormedSpace ℝ ℝ := NormedField.toNormedSpace
  ∀ x ∈ KrivineStengle.basicClosedSet g,
    LinearIndependent ℝ
      (fun i : {i : Fin m // MvPolynomial.eval x (g i) = 0} ↦
        fun j : Fin n ↦ MvPolynomial.eval x (MvPolynomial.pderiv j (g i)))

end OptimalConvergenceRates

end
