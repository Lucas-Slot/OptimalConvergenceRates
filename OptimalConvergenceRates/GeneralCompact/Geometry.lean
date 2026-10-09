/-
  Compactness and minimum-attainment facts used by the Schmüdgen hierarchy.
-/
import OptimalConvergenceRates.GeneralCompact.Defs
import OptimalConvergenceRates.GeneralArchimedean.ArchimedeanGeometry

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralCompact

variable {n m : ℕ}

/-- A compact set of real points is contained in a strict Euclidean ball. -/
theorem compact_exists_sum_sq_lt
    {K : Set (Fin n → ℝ)} (hne : K.Nonempty) (hK : IsCompact K) :
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ K, ∑ i, (x i) ^ 2 < R := by
  let q : MvPolynomial (Fin n) ℝ := ∑ i, X i ^ 2
  have hbdd : BddAbove ((fun x ↦ eval x q) '' K) :=
    hK.bddAbove_image (continuous_eval q).continuousOn
  obtain ⟨M, hM⟩ := bddAbove_def.mp hbdd
  obtain ⟨x₀, hx₀⟩ := hne
  have hM0 : 0 ≤ M := by
    have hx := hM (eval x₀ q) ⟨x₀, hx₀, rfl⟩
    have hq0 : 0 ≤ eval x₀ q := by
      simp only [q, eval_sum, eval_pow, eval_X]
      exact Finset.sum_nonneg fun i _ ↦ sq_nonneg (x₀ i)
    exact hq0.trans hx
  refine ⟨M + 1, by linarith, ?_⟩
  intro x hx
  have hxM := hM (eval x q) ⟨x, hx, rfl⟩
  have : ∑ i, (x i) ^ 2 ≤ M := by simpa [q] using hxM
  linarith

/-- A polynomial attains its minimum on a nonempty compact feasible set. -/
theorem polynomialMinimum_mem_of_compact
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (hcompact : IsCompact (KrivineStengle.basicClosedSet g))
    (f : MvPolynomial (Fin n) ℝ) :
    ∃ x ∈ KrivineStengle.basicClosedSet g,
      eval x f = GeneralArchimedean.polynomialMinimum g f := by
  have hc := hcompact.image (continuous_eval f)
  have himage :
      ((fun x ↦ eval x f) '' KrivineStengle.basicClosedSet g).Nonempty :=
    hne.image _
  obtain ⟨x, hx, hfx⟩ := hc.sInf_mem himage
  exact ⟨x, hx, hfx⟩

/-- The compact minimum is a pointwise lower bound on the feasible set. -/
theorem polynomialMinimum_le_eval_of_compact
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hcompact : IsCompact (KrivineStengle.basicClosedSet g))
    (f : MvPolynomial (Fin n) ℝ) {x : Fin n → ℝ}
    (hx : x ∈ KrivineStengle.basicClosedSet g) :
    GeneralArchimedean.polynomialMinimum g f ≤ eval x f := by
  unfold GeneralArchimedean.polynomialMinimum
  exact csInf_le (hcompact.image (continuous_eval f)).bddBelow ⟨x, hx, rfl⟩

/-- Centering at the compact minimum produces a nonnegative polynomial. -/
theorem centered_nonnegOn_of_compact
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hcompact : IsCompact (KrivineStengle.basicClosedSet g))
    (f : MvPolynomial (Fin n) ℝ) :
    IsNonnegOn
      (f - C (GeneralArchimedean.polynomialMinimum g f))
      (KrivineStengle.basicClosedSet g) := by
  intro x hx
  simp only [eval_sub, eval_C]
  exact sub_nonneg.mpr (polynomialMinimum_le_eval_of_compact hcompact f hx)

end OptimalConvergenceRates.GeneralCompact

end
