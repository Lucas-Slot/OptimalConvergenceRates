import OptimalConvergenceRates.KrivineStengle.Nonnegative

namespace OptimalConvergenceRates.KrivineStengle

/-- Nonnegative Krivine--Stengle, stated explicitly: if `p` is nonnegative whenever all
generators are nonnegative, then there are preordering elements `S` and `T` and an integer
`k ≥ 1` such that `p * S = p ^ (2 * k) + T`. -/
def MainTheoremStatement : Prop :=
  ∀ {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ),
    (∀ x, (∀ i, 0 ≤ MvPolynomial.eval x (g i)) → 0 ≤ MvPolynomial.eval x p) →
      ∃ k : ℕ, 1 ≤ k ∧
        ∃ S T : MvPolynomial (Fin n) ℝ,
          PreorderingMem g S ∧ PreorderingMem g T ∧
            p * S = p ^ (2 * k) + T

/-- The equivalence form of the explicit nonnegative Krivine--Stengle theorem. -/
def MainTheoremIffStatement : Prop :=
  ∀ {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ),
    (∀ x, (∀ i, 0 ≤ MvPolynomial.eval x (g i)) → 0 ≤ MvPolynomial.eval x p) ↔
      ∃ k : ℕ, 1 ≤ k ∧
        ∃ S T : MvPolynomial (Fin n) ℝ,
          PreorderingMem g S ∧ PreorderingMem g T ∧
            p * S = p ^ (2 * k) + T

end OptimalConvergenceRates.KrivineStengle
