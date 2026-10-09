import OptimalConvergenceRates.KrivineStengle.RealFactorization
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset

noncomputable section

open Polynomial Set
open UniqueFactorizationMonoid

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

private theorem normalizedFactor_eval_mul_pos_of_no_root_between
    {p q : R[X]} {a b : R} (hp : p ≠ 0) (hab : a ≤ b)
    (hNoRoot : ∀ x ∈ Icc a b, ¬p.IsRoot x)
    (hq : q ∈ normalizedFactors p) :
    0 < q.eval a * q.eval b := by
  rw [Polynomial.mem_normalizedFactors_iff hp] at hq
  obtain ⟨hqIrr, hqMonic, hqDvd⟩ := hq
  rcases irreducible_natDegree_eq_one_or_two hqIrr with hdegree | hdegree
  · have hqEq : q = X + C (q.coeff 0) := hqMonic.eq_X_add_C hdegree
    let r : R := -q.coeff 0
    have hqRoot : q.IsRoot r := by
      rw [hqEq, IsRoot]
      simp [r]
    have hpRoot : p.IsRoot r := hqRoot.dvd hqDvd
    have hrOutside : r < a ∨ b < r := by
      by_contra h
      push_neg at h
      exact hNoRoot r ⟨h.1, h.2⟩ hpRoot
    rw [hqEq]
    simp only [eval_add, eval_X, eval_C]
    rcases hrOutside with hra | hrb
    · have : 0 < a + q.coeff 0 := by dsimp [r] at hra; linarith
      have : 0 < b + q.coeff 0 := by dsimp [r] at hra; linarith
      positivity
    · have hqa : a + q.coeff 0 < 0 := by dsimp [r] at hrb; linarith
      have hqb : b + q.coeff 0 < 0 := by dsimp [r] at hrb; linarith
      exact mul_pos_of_neg_of_neg hqa hqb
  · exact mul_pos (monic_irreducible_quadratic_eval_pos hqMonic hqIrr hdegree a)
      (monic_irreducible_quadratic_eval_pos hqMonic hqIrr hdegree b)

/-- If a polynomial has no root in `[a,b]`, its endpoint values have positive product. -/
theorem eval_mul_pos_of_no_root_between {p : R[X]} {a b : R}
    (hp : p ≠ 0) (hab : a ≤ b) (hNoRoot : ∀ x ∈ Icc a b, ¬p.IsRoot x) :
    0 < p.eval a * p.eval b := by
  classical
  have hfactor :
      ∀ q ∈ normalizedFactors p, 0 < q.eval a * q.eval b := by
    intro q hq
    exact normalizedFactor_eval_mul_pos_of_no_root_between hp hab hNoRoot hq
  have hprod :
      0 < ((normalizedFactors p).map fun q => q.eval a * q.eval b).prod := by
    apply Multiset.prod_pos
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hy
    exact hfactor q hq
  have hprod' :
      0 < (normalizedFactors p).prod.eval a *
        (normalizedFactors p).prod.eval b := by
    simpa only [eval_multiset_prod, Multiset.prod_map_mul] using hprod
  have ha := congrArg (Polynomial.eval a)
    (leadingCoeff_mul_prod_normalizedFactors p)
  have hb := congrArg (Polynomial.eval b)
    (leadingCoeff_mul_prod_normalizedFactors p)
  simp only [eval_mul, eval_C] at ha hb
  rw [← ha, ← hb]
  calc
    0 < p.leadingCoeff ^ 2 *
        ((normalizedFactors p).prod.eval a *
          (normalizedFactors p).prod.eval b) :=
      mul_pos (sq_pos_of_ne_zero (leadingCoeff_ne_zero.mpr hp)) hprod'
    _ = (p.leadingCoeff * (normalizedFactors p).prod.eval a) *
        (p.leadingCoeff * (normalizedFactors p).prod.eval b) := by ring

/-- Polynomial intermediate value over a real-closed ordered field, in sign-change form. -/
theorem exists_isRoot_mem_Icc_of_eval_mul_nonpos {p : R[X]} {a b : R}
    (hab : a ≤ b) (hsign : p.eval a * p.eval b ≤ 0) :
    ∃ x ∈ Icc a b, p.IsRoot x := by
  by_cases hp : p = 0
  · subst p
    exact ⟨a, left_mem_Icc.mpr hab, by simp⟩
  by_contra hroot
  push_neg at hroot
  exact (not_lt_of_ge hsign) (eval_mul_pos_of_no_root_between hp hab hroot)

/-- Endpoint sign change gives a root between the endpoints. -/
theorem exists_isRoot_mem_Icc_of_eval_nonpos_of_nonneg {p : R[X]} {a b : R}
    (hab : a ≤ b) (ha : p.eval a ≤ 0) (hb : 0 ≤ p.eval b) :
    ∃ x ∈ Icc a b, p.IsRoot x :=
  exists_isRoot_mem_Icc_of_eval_mul_nonpos hab (mul_nonpos_of_nonpos_of_nonneg ha hb)

end OptimalConvergenceRates.KrivineStengle

end
