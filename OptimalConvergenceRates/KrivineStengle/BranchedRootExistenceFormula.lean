/-
  OptimalConvergenceRates/KrivineStengle/BranchedRootExistenceFormula.lean

  Elimination of a nonzero univariate equation, including all possible
  degree drops under specialization.
-/
import OptimalConvergenceRates.KrivineStengle.StrictRootExistenceFormula
import OptimalConvergenceRates.KrivineStengle.DegreeBranchPartition

noncomputable section

open MvPolynomial Polynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- Disjoin the strict-root formula over every possible actual degree of
`f`. The zero-polynomial specialization contributes no roots to Lean's
`Polynomial.roots`, and hence needs no branch for this precise API. -/
def branchedRootExistenceFormula {n s : ℕ}
    (f : (MvPolynomial (Fin n) ℝ)[X])
    (g : Fin s → (MvPolynomial (Fin n) ℝ)[X]) : SignFormula n :=
  SignFormula.any ((List.range (f.natDegree + 1)).map fun d ↦
    .conj (degreeBranch f d) (strictRootExistenceFormula f g d))

/-- Correctness after finite branching on the actual specialized degree.
This is the positive-degree-equation core of one-variable elimination. -/
theorem realizes_branchedRootExistenceFormula_iff
    {n s : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] [IsRealClosed F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (f : (MvPolynomial (Fin n) ℝ)[X])
    (g : Fin s → (MvPolynomial (Fin n) ℝ)[X]) :
    (branchedRootExistenceFormula f g).Realizes coeff x ↔
      ∃ r ∈ (specializePolynomial coeff x f).roots.toFinset,
        ∀ i, 0 < (specializePolynomial coeff x (g i)).eval r := by
  rw [branchedRootExistenceFormula, SignFormula.realizes_any]
  constructor
  · rintro ⟨formula, hformula, hrealizes⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hformula
    rw [SignFormula.realizes_conj] at hrealizes
    have hdegree := (realizes_degreeBranch_iff coeff x f d).1 hrealizes.1
    exact (realizes_strictRootExistenceFormula_iff
      coeff x f g d hdegree).1 hrealizes.2
  · intro hroot
    obtain ⟨r, hr, hpos⟩ := hroot
    let p := specializePolynomial coeff x f
    have hp0 : p ≠ 0 := by
      intro hp
      simp [p, hp] at hr
    let d := p.natDegree
    have hdle : d ≤ f.natDegree := by
      dsimp only [d, p, specializePolynomial]
      exact natDegree_map_le
    have hdegree : ActualDegreeCondition coeff x f d := by
      rw [actualDegreeCondition_iff_degree_eq]
      exact degree_eq_natDegree hp0
    refine ⟨_, List.mem_map.mpr
      ⟨d, List.mem_range.mpr (Nat.lt_succ_of_le hdle), rfl⟩, ?_⟩
    rw [SignFormula.realizes_conj]
    exact ⟨(realizes_degreeBranch_iff coeff x f d).2 hdegree,
      (realizes_strictRootExistenceFormula_iff
        coeff x f g d hdegree).2 ⟨r, hr, hpos⟩⟩

end OptimalConvergenceRates.KrivineStengle

end
