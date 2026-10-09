/-
  OptimalConvergenceRates/KrivineStengle/TailSignFormula.lean

  Finite degree-branch formulas for the signs of polynomial tails.
-/
import OptimalConvergenceRates.KrivineStengle.DegreeBranchPartition

import OptimalConvergenceRates.KrivineStengle.TotalSignatureFormula
noncomputable section

open MvPolynomial Polynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- The specialization is nonzero and has positive leading coefficient;
equivalently, it is eventually positive at positive infinity. -/
def positiveLeadingFormula {n : ℕ}
    (f : (MvPolynomial (Fin n) ℝ)[X]) : SignFormula n :=
  SignFormula.any ((List.range (f.natDegree + 1)).map fun d ↦
    .conj (degreeBranch f d) (.positive (f.coeff d)))

theorem realizes_positiveLeadingFormula_iff
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (f : (MvPolynomial (Fin n) ℝ)[X]) :
    (positiveLeadingFormula f).Realizes coeff x ↔
      specializePolynomial coeff x f ≠ 0 ∧
        0 < (specializePolynomial coeff x f).leadingCoeff := by
  let p := specializePolynomial coeff x f
  rw [positiveLeadingFormula, SignFormula.realizes_any]
  constructor
  · rintro ⟨formula, hformula, hrealizes⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hformula
    rw [SignFormula.realizes_conj, SignFormula.realizes_positive] at hrealizes
    have hdegree := (realizes_degreeBranch_iff coeff x f d).1 hrealizes.1
    have hpDegree : p.degree = d :=
      (actualDegreeCondition_iff_degree_eq coeff x f d).1 hdegree
    have hp0 : p ≠ 0 := by
      intro hp
      rw [hp] at hpDegree
      simp at hpDegree
    have hnat : p.natDegree = d := natDegree_eq_of_degree_eq_some hpDegree
    refine ⟨hp0, ?_⟩
    change 0 < p.leadingCoeff
    rw [leadingCoeff, hnat]
    dsimp only [p, specializePolynomial]
    rw [Polynomial.coeff_map]
    exact hrealizes.2
  · rintro ⟨hp0, hlead⟩
    let d := p.natDegree
    have hdle : d ≤ f.natDegree := by
      dsimp only [d, p, specializePolynomial]
      exact natDegree_map_le
    have hdegree : ActualDegreeCondition coeff x f d := by
      rw [actualDegreeCondition_iff_degree_eq]
      exact degree_eq_natDegree hp0
    refine ⟨_, List.mem_map.mpr
      ⟨d, List.mem_range.mpr (Nat.lt_succ_of_le hdle), rfl⟩, ?_⟩
    rw [SignFormula.realizes_conj, SignFormula.realizes_positive]
    refine ⟨(realizes_degreeBranch_iff coeff x f d).2 hdegree, ?_⟩
    change 0 < p.leadingCoeff at hlead
    rw [leadingCoeff] at hlead
    rw [← Polynomial.coeff_map]
    change 0 < p.coeff d
    simpa only [d] using hlead

/-- Every member of a finite list has positive leading coefficient after
specialization. -/
def allPositiveLeadingFormula {n : ℕ}
    (fs : List ((MvPolynomial (Fin n) ℝ)[X])) : SignFormula n :=
  SignFormula.all (fs.map positiveLeadingFormula)

theorem realizes_allPositiveLeadingFormula_iff
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (fs : List ((MvPolynomial (Fin n) ℝ)[X])) :
    (allPositiveLeadingFormula fs).Realizes coeff x ↔
      ∀ f ∈ fs, specializePolynomial coeff x f ≠ 0 ∧
        0 < (specializePolynomial coeff x f).leadingCoeff := by
  rw [allPositiveLeadingFormula, SignFormula.realizes_all]
  constructor
  · intro h f hf
    apply (realizes_positiveLeadingFormula_iff coeff x f).1
    exact h _ (List.mem_map.mpr ⟨f, hf, rfl⟩)
  · intro h formula hformula
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hformula
    exact (realizes_positiveLeadingFormula_iff coeff x f).2 (h f hf)

end OptimalConvergenceRates.KrivineStengle

end
