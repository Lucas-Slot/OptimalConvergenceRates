/-
  Iteration of the quantitative implicit-graph recurrence through order five.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.ImplicitGraphBootstrap

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- Ambient derivatives through order six and strict normal curvature give one common bound for
all positive-order derivatives through order five of the minimizing graph.  The constant is
dimension-independent. -/
theorem exists_uniform_minimizingGraph_five_deriv_bound (M : ℝ) (hM : 1 ≤ M) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {n : ℕ} {input : NormalizedLocalSplitInput n}
        (graph : MinimizingGraphData input) (y : Fin n → ℝ),
        (∀ k, k ≤ 6 →
          ‖iteratedFDeriv ℝ k input.function (implicitGraphLift graph y)‖ ≤ M) →
        ∀ q, 1 ≤ q → q ≤ 5 →
          ‖iteratedFDeriv ℝ q graph.graph y‖ ≤ B := by
  obtain ⟨A1, hA1, hnext1⟩ :=
    exists_uniform_minimizingGraph_next_deriv_bound 0 M 1
      (by norm_num) hM (by norm_num)
  obtain ⟨A2, hA2, hnext2⟩ :=
    exists_uniform_minimizingGraph_next_deriv_bound 1 M A1
      (by norm_num) hM hA1
  let B2 := max A1 A2
  have hB2 : 1 ≤ B2 := hA1.trans (le_max_left _ _)
  obtain ⟨A3, hA3, hnext3⟩ :=
    exists_uniform_minimizingGraph_next_deriv_bound 2 M B2
      (by norm_num) hM hB2
  let B3 := max B2 A3
  have hB3 : 1 ≤ B3 := hB2.trans (le_max_left _ _)
  obtain ⟨A4, hA4, hnext4⟩ :=
    exists_uniform_minimizingGraph_next_deriv_bound 3 M B3
      (by norm_num) hM hB3
  let B4 := max B3 A4
  have hB4 : 1 ≤ B4 := hB3.trans (le_max_left _ _)
  obtain ⟨A5, hA5, hnext5⟩ :=
    exists_uniform_minimizingGraph_next_deriv_bound 4 M B4
      (by norm_num) hM hB4
  let B5 := max B4 A5
  have hB5 : 1 ≤ B5 := hB4.trans (le_max_left _ _)
  refine ⟨B5, hB5, ?_⟩
  intro n input graph y hambient
  have h1 : ‖iteratedFDeriv ℝ 1 graph.graph y‖ ≤ A1 := by
    simpa using hnext1 graph y hambient (by
      intro k hkOne hkZero
      omega)
  have h2 : ‖iteratedFDeriv ℝ 2 graph.graph y‖ ≤ A2 := by
    simpa using hnext2 graph y hambient (by
      intro k hkOne hk
      have hkEq : k = 1 := by omega
      subst k
      exact h1)
  have h12 : ∀ k, 1 ≤ k → k ≤ 2 →
      ‖iteratedFDeriv ℝ k graph.graph y‖ ≤ B2 := by
    intro k hkOne hk
    interval_cases k
    · exact h1.trans (le_max_left _ _)
    · exact h2.trans (le_max_right _ _)
  have h3 : ‖iteratedFDeriv ℝ 3 graph.graph y‖ ≤ A3 := by
    simpa using hnext3 graph y hambient h12
  have h123 : ∀ k, 1 ≤ k → k ≤ 3 →
      ‖iteratedFDeriv ℝ k graph.graph y‖ ≤ B3 := by
    intro k hkOne hk
    by_cases hk3 : k = 3
    · subst k
      exact h3.trans (le_max_right _ _)
    · exact (h12 k hkOne (by omega)).trans (le_max_left _ _)
  have h4 : ‖iteratedFDeriv ℝ 4 graph.graph y‖ ≤ A4 := by
    simpa using hnext4 graph y hambient h123
  have h1234 : ∀ k, 1 ≤ k → k ≤ 4 →
      ‖iteratedFDeriv ℝ k graph.graph y‖ ≤ B4 := by
    intro k hkOne hk
    by_cases hk4 : k = 4
    · subst k
      exact h4.trans (le_max_right _ _)
    · exact (h123 k hkOne (by omega)).trans (le_max_left _ _)
  have h5 : ‖iteratedFDeriv ℝ 5 graph.graph y‖ ≤ A5 := by
    simpa using hnext5 graph y hambient h1234
  intro q hqOne hqFive
  by_cases hq5 : q = 5
  · subst q
    exact h5.trans (le_max_right _ _)
  exact (h1234 q hqOne (by omega)).trans (le_max_left _ _)

end QuarticConvergence
end OptimalConvergenceRates

end
