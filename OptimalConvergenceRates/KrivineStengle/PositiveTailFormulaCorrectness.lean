/-
  OptimalConvergenceRates/KrivineStengle/PositiveTailFormulaCorrectness.lean

  Semantic interpretation of the positive-leading formula as existence of
  a common positive tail.
-/
import OptimalConvergenceRates.KrivineStengle.TailSignFormula
import OptimalConvergenceRates.KrivineStengle.CommonPolynomialTail

noncomputable section

open MvPolynomial Polynomial

namespace OptimalConvergenceRates.KrivineStengle

theorem realizes_allPositiveLeadingFormula_iff_exists_tail
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] [IsRealClosed F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (fs : List ((MvPolynomial (Fin n) ℝ)[X])) :
    (allPositiveLeadingFormula fs).Realizes coeff x ↔
      ∃ B : F, ∀ y, B < y → ∀ f ∈ fs,
        0 < (specializePolynomial coeff x f).eval y := by
  rw [realizes_allPositiveLeadingFormula_iff]
  let specialized : List F[X] := fs.map (specializePolynomial coeff x)
  have htail := exists_common_positive_tail_iff specialized
  constructor
  · intro h
    have hspecialized : ∀ p ∈ specialized,
        p ≠ 0 ∧ 0 < p.leadingCoeff := by
      intro p hp
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hp
      exact h f hf
    obtain ⟨B, hB⟩ := htail.2 hspecialized
    refine ⟨B, ?_⟩
    intro y hy f hf
    exact hB y hy _ (List.mem_map.mpr ⟨f, hf, rfl⟩)
  · intro h f hf
    have hspecialized : ∃ B : F, ∀ y, B < y → ∀ p ∈ specialized,
        0 < p.eval y := by
      obtain ⟨B, hB⟩ := h
      refine ⟨B, ?_⟩
      intro y hy p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hB y hy q hq
    exact (htail.1 hspecialized) _ (List.mem_map.mpr ⟨f, hf, rfl⟩)

end OptimalConvergenceRates.KrivineStengle

end
