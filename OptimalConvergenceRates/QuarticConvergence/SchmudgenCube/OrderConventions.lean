/-
  Thin adapters for the repository's canonical box-cone order and hierarchy APIs.
-/
import OptimalConvergenceRates.BasicNotions.Lasserre

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

variable {n r s : ℕ} {p q : MvPolynomial (Fin n) ℝ}

/-- Zero belongs to every level of the canonical box preordering. -/
theorem zero_mem_BoxPreordering (n r : ℕ) :
    (0 : MvPolynomial (Fin n) ℝ) ∈ BoxPreordering n r := by
  refine ⟨0, ?_, ?_, ?_⟩
  · intro J
    exact IsSOS_zero
  · intro J
    simp
  · simp

/-- Every nonnegative constant belongs to every level of the canonical box preordering. -/
theorem nonneg_const_mem_BoxPreordering {c : ℝ} (hc : 0 ≤ c) (n r : ℕ) :
    MvPolynomial.C c ∈ BoxPreordering n r := by
  by_cases hzero : c = 0
  · subst c
    simpa using zero_mem_BoxPreordering n r
  · exact positive_const_in_box_preordering (lt_of_le_of_ne hc (Ne.symm hzero)) n r

/-- Preordering certificates at different orders can be added at their maximum order. -/
theorem BoxPreordering_add_max {p : MvPolynomial (Fin n) ℝ} {q : MvPolynomial (Fin n) ℝ}
    {r s : ℕ} (hp : p ∈ BoxPreordering n r) (hq : q ∈ BoxPreordering n s) :
    p + q ∈ BoxPreordering n (max r s) := by
  exact BoxPreordering_add
    (box_preordering_mono (le_max_left r s) hp)
    (box_preordering_mono (le_max_right r s) hq)

/-- Insert one explicitly degree-bounded SOS multiplier into the canonical preordering. -/
theorem sos_mul_generatorProd_mem_BoxPreordering (J : Finset (Fin n))
    (σ : MvPolynomial (Fin n) ℝ) (hσ : IsSOS σ)
    (hdeg : (σ * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r) :
    σ * BoxSemialgebraicGeneratorProd J ∈ BoxPreordering n r := by
  have hJ : J ∈ (Finset.univ : Finset (Fin n)).powerset :=
    Finset.mem_powerset.mpr (Finset.subset_univ J)
  refine ⟨Function.update 0 J σ, ?_, ?_, ?_⟩
  · intro K
    by_cases hK : K = J
    · subst K
      simpa using hσ
    · rw [Function.update_of_ne hK, Pi.zero_apply]
      exact IsSOS_zero
  · intro K
    by_cases hK : K = J
    · subst K
      simpa using hdeg
    · simp [Function.update_of_ne hK]
  · rw [Finset.sum_eq_single J
      (fun K _ hK ↦ by simp [Function.update_of_ne hK])
      (fun h ↦ absurd hJ h)]
    simp

/-- Zero belongs to every level of the canonical box quadratic module. -/
theorem zero_mem_BoxQuadraticModule (n r : ℕ) :
    (0 : MvPolynomial (Fin n) ℝ) ∈ BoxQuadraticModule n r := by
  refine ⟨0, 0, IsSOS_zero, ?_, ?_, ?_, ?_⟩
  · intro i
    exact IsSOS_zero
  · simp
  · intro i
    simp
  · simp

/-- Every nonnegative constant belongs to every level of the canonical box quadratic module. -/
theorem nonneg_const_mem_BoxQuadraticModule {c : ℝ} (hc : 0 ≤ c) (n r : ℕ) :
    MvPolynomial.C c ∈ BoxQuadraticModule n r := by
  by_cases hzero : c = 0
  · subst c
    simpa using zero_mem_BoxQuadraticModule n r
  · exact positive_const_in_BoxQuadraticModule (lt_of_le_of_ne hc (Ne.symm hzero)) n r

/-- Quadratic-module certificates at different orders can be added at their maximum order. -/
theorem BoxQuadraticModule_add_max {p : MvPolynomial (Fin n) ℝ}
    {q : MvPolynomial (Fin n) ℝ} {r s : ℕ}
    (hp : p ∈ BoxQuadraticModule n r) (hq : q ∈ BoxQuadraticModule n s) :
    p + q ∈ BoxQuadraticModule n (max r s) := by
  exact BoxQuadraticModule_add
    (BoxQuadraticModule_mono (le_max_left r s) hp)
    (BoxQuadraticModule_mono (le_max_right r s) hq)

/-- A concrete feasible preordering value makes its `WithBot` hierarchy value real. -/
theorem exists_real_lasserre_bound_box_preo_of_feasible
    (f : MvPolynomial (Fin n) ℝ) (r : ℕ) {l : ℝ}
    (hl : f - MvPolynomial.C l ∈ BoxPreordering n r) :
    ∃ b : ℝ, lasserre_bound_box_preo f r = (b : WithBot ℝ) := by
  have hle := lasserre_bound_box_preo_ge_feasible f r hl
  have hne : lasserre_bound_box_preo f r ≠ ⊥ := by
    intro hbot
    rw [hbot] at hle
    exact (not_le_of_gt (WithBot.bot_lt_coe l)) hle
  obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.mp hne
  exact ⟨b, hb.symm⟩

/-- A concrete feasible quadratic-module value makes its `WithBot` hierarchy value real. -/
theorem exists_real_lasserre_bound_box_qm_of_feasible
    (f : MvPolynomial (Fin n) ℝ) (r : ℕ) {l : ℝ}
    (hl : f - MvPolynomial.C l ∈ BoxQuadraticModule n r) :
    ∃ b : ℝ, lasserre_bound_box_qm f r = (b : WithBot ℝ) := by
  have hle := lasserre_bound_box_qm_ge_feasible f r hl
  have hne : lasserre_bound_box_qm f r ≠ ⊥ := by
    intro hbot
    rw [hbot] at hle
    exact (not_le_of_gt (WithBot.bot_lt_coe l)) hle
  obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.mp hne
  exact ⟨b, hb.symm⟩

end QuarticConvergence
end OptimalConvergenceRates

end
