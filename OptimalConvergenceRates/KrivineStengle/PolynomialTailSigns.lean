/-
  OptimalConvergenceRates/KrivineStengle/PolynomialTailSigns.lean

  Algebraic tail-sign lemmas over arbitrary real-closed ordered fields.
-/
import OptimalConvergenceRates.KrivineStengle.RealFactorization
import Mathlib.Algebra.Polynomial.FieldDivision

noncomputable section

open Polynomial
open UniqueFactorizationMonoid

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

private theorem monic_irreducible_eventually_pos {q : R[X]}
    (hqMonic : q.Monic) (hqIrr : Irreducible q) :
    ∃ B : R, ∀ x, B < x → 0 < q.eval x := by
  rcases irreducible_natDegree_eq_one_or_two hqIrr with hdegree | hdegree
  · refine ⟨-q.coeff 0, ?_⟩
    intro x hx
    rw [hqMonic.eq_X_add_C hdegree]
    simp only [eval_add, eval_X, eval_C]
    linarith
  · exact ⟨0, fun x _ ↦
      monic_irreducible_quadratic_eval_pos hqMonic hqIrr hdegree x⟩

private theorem multiset_prod_eventually_pos
    (factors : Multiset R[X])
    (hfactor : ∀ q ∈ factors, q.Monic ∧ Irreducible q) :
    ∃ B : R, ∀ x, B < x → 0 < factors.prod.eval x := by
  induction factors using Multiset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @cons q factors ih =>
      have hq := hfactor q (by simp)
      have hrest : ∀ r ∈ factors, r.Monic ∧ Irreducible r := by
        intro r hr
        exact hfactor r (by simp [hr])
      obtain ⟨Bq, hBq⟩ := monic_irreducible_eventually_pos hq.1 hq.2
      obtain ⟨Br, hBr⟩ := ih hrest
      refine ⟨max Bq Br, ?_⟩
      intro x hx
      simp only [Multiset.prod_cons, eval_mul]
      exact mul_pos (hBq x (lt_of_le_of_lt (le_max_left _ _) hx))
        (hBr x (lt_of_le_of_lt (le_max_right _ _) hx))

/-- A polynomial with positive leading coefficient is eventually strictly
positive, over any real-closed ordered field. This is algebraic and does
not use an Archimedean or topological assumption. -/
theorem exists_forall_gt_eval_pos_of_leadingCoeff_pos {p : R[X]}
    (hlead : 0 < p.leadingCoeff) :
    ∃ B : R, ∀ x, B < x → 0 < p.eval x := by
  have hp0 : p ≠ 0 := leadingCoeff_ne_zero.mp (ne_of_gt hlead)
  have hfactor : ∀ q ∈ normalizedFactors p, q.Monic ∧ Irreducible q := by
    intro q hq
    rw [Polynomial.mem_normalizedFactors_iff hp0] at hq
    exact ⟨hq.2.1, hq.1⟩
  obtain ⟨B, hB⟩ := multiset_prod_eventually_pos (normalizedFactors p) hfactor
  refine ⟨B, ?_⟩
  intro x hx
  have heval := congrArg (Polynomial.eval x)
    (leadingCoeff_mul_prod_normalizedFactors p)
  rw [eval_mul, eval_C] at heval
  rw [← heval]
  exact mul_pos hlead (hB x hx)

end OptimalConvergenceRates.KrivineStengle

end
