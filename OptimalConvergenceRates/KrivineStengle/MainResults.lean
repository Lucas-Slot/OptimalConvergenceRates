import OptimalConvergenceRates.KrivineStengle.MainResultsProofs

/-!
# Nonnegative Krivine--Stengle

This file is the readable public statement layer. All proof construction is
kept in `MainResultsProofs`.
-/

namespace OptimalConvergenceRates.KrivineStengle

/-- If `p` is nonnegative whenever all generators are nonnegative, then there
are preordering elements `S` and `T` and an integer `k ≥ 1` such that
`p * S = p ^ (2 * k) + T`. -/
theorem mainTheorem :
    ∀ {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
      (p : MvPolynomial (Fin n) ℝ),
      (∀ x, (∀ i, 0 ≤ MvPolynomial.eval x (g i)) → 0 ≤ MvPolynomial.eval x p) →
        ∃ k : ℕ, 1 ≤ k ∧
          ∃ S T : MvPolynomial (Fin n) ℝ,
            PreorderingMem g S ∧ PreorderingMem g T ∧
              p * S = p ^ (2 * k) + T :=
  mainTheorem_proof

/-- A polynomial is nonnegative whenever all generators are nonnegative if
and only if it admits the displayed Krivine--Stengle certificate. -/
theorem mainTheoremIff :
    ∀ {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
      (p : MvPolynomial (Fin n) ℝ),
      (∀ x, (∀ i, 0 ≤ MvPolynomial.eval x (g i)) → 0 ≤ MvPolynomial.eval x p) ↔
        ∃ k : ℕ, 1 ≤ k ∧
          ∃ S T : MvPolynomial (Fin n) ℝ,
            PreorderingMem g S ∧ PreorderingMem g T ∧
              p * S = p ^ (2 * k) + T :=
  mainTheoremIff_proof

end OptimalConvergenceRates.KrivineStengle
