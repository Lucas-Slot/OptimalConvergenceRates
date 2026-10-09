/-
  OptimalConvergenceRates/KrivineStengle/AlgebraicRolle.lean

  Rolle's theorem for consecutive roots over a real-closed ordered field.
-/
import OptimalConvergenceRates.KrivineStengle.PolynomialIntermediateValue
import Mathlib.Algebra.Polynomial.FieldDivision

noncomputable section

open Polynomial Set

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-- Between two distinct roots of a nonzero polynomial, with no root strictly
between them, the derivative has a root strictly between them. This is the
algebraic consecutive-root form of Rolle's theorem. -/
theorem exists_derivative_isRoot_mem_Ioo_of_consecutive_roots
    {p : R[X]} {a b : R} (hp : p ≠ 0) (hab : a < b)
    (ha : p.IsRoot a) (hb : p.IsRoot b)
    (hconsecutive : ∀ x ∈ Ioo a b, ¬p.IsRoot x) :
    ∃ x ∈ Ioo a b, p.derivative.IsRoot x := by
  classical
  let A : R[X] := X - C a
  let B : R[X] := X - C b
  let m := p.rootMultiplicity a
  let q := p /ₘ A ^ m
  let n := q.rootMultiplicity b
  let r := q /ₘ B ^ n
  have hm : 0 < m := by
    exact (rootMultiplicity_pos hp).2 ha
  have hpq : A ^ m * q = p := by
    simpa [A, m, q] using p.pow_mul_divByMonic_rootMultiplicity_eq a
  have hq0 : q ≠ 0 := by
    intro hq
    apply hp
    rw [← hpq, hq, mul_zero]
  have hqEvalB : q.eval b = 0 := by
    have h := congrArg (Polynomial.eval b) hpq
    simp only [eval_mul, eval_pow, A, eval_sub, eval_X, eval_C] at h
    rw [hb.eq_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr hab.ne'))
  have hbq : q.IsRoot b := by
    rwa [IsRoot]
  have hn : 0 < n := by
    exact (rootMultiplicity_pos hq0).2 hbq
  have hqr : B ^ n * r = q := by
    simpa [B, n, r] using q.pow_mul_divByMonic_rootMultiplicity_eq b
  have hfactor : A ^ m * (B ^ n * r) = p := by
    rw [hqr, hpq]
  have hqEvalA : q.eval a ≠ 0 := by
    simpa [A, m, q] using eval_divByMonic_pow_rootMultiplicity_ne_zero a hp
  have hrEvalB : r.eval b ≠ 0 := by
    simpa [B, n, r] using eval_divByMonic_pow_rootMultiplicity_ne_zero b hq0
  have hrEvalA : r.eval a ≠ 0 := by
    have h := congrArg (Polynomial.eval a) hqr
    simp only [eval_mul, eval_pow, B, eval_sub, eval_X, eval_C] at h
    exact fun hra ↦ hqEvalA (by rw [← h, hra, mul_zero])
  have hr0 : r ≠ 0 := by
    intro hr
    exact hrEvalA (by simp [hr])
  have hrNoRoot : ∀ x ∈ Icc a b, ¬r.IsRoot x := by
    intro x hx hrx
    rcases hx with ⟨hax, hxb⟩
    rcases hax.eq_or_lt with rfl | hax
    · exact hrEvalA hrx.eq_zero
    rcases hxb.eq_or_lt with rfl | hxb
    · exact hrEvalB hrx.eq_zero
    · apply hconsecutive x ⟨hax, hxb⟩
      rw [IsRoot, ← hfactor, eval_mul, eval_pow, eval_mul, eval_pow, hrx.eq_zero,
        mul_zero, mul_zero]
  have hrSign : 0 < r.eval a * r.eval b :=
    eval_mul_pos_of_no_root_between hr0 hab.le hrNoRoot
  obtain ⟨m0, hmEq⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  obtain ⟨n0, hnEq⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let h : R[X] :=
    C (m0 + 1 : R) * B * r + C (n0 + 1 : R) * A * r + A * B * r.derivative
  have hderiv : p.derivative = A ^ m0 * B ^ n0 * h := by
    rw [← hfactor, hmEq, hnEq]
    dsimp [h, A, B]
    simp only [derivative_mul, derivative_pow_succ, derivative_sub, derivative_X,
      derivative_C, sub_zero, mul_one]
    ring
  have hEvalA : h.eval a = (m0 + 1 : R) * (a - b) * r.eval a := by
    simp [h, A, B]
  have hEvalB : h.eval b = (n0 + 1 : R) * (b - a) * r.eval b := by
    simp [h, A, B]
  have hmCast : 0 < (m0 + 1 : R) := by positivity
  have hnCast : 0 < (n0 + 1 : R) := by positivity
  have hEvalMul : h.eval a * h.eval b < 0 := by
    rw [hEvalA, hEvalB]
    calc
      ((m0 + 1 : R) * (a - b) * r.eval a) *
          ((n0 + 1 : R) * (b - a) * r.eval b) =
          -(((m0 + 1 : R) * (n0 + 1 : R)) * (b - a) ^ 2 *
            (r.eval a * r.eval b)) := by ring
      _ < 0 := neg_neg_of_pos (mul_pos
        (mul_pos (mul_pos hmCast hnCast) (sq_pos_of_pos (sub_pos.mpr hab))) hrSign)
  obtain ⟨x, hx, hxRoot⟩ :=
    exists_isRoot_mem_Icc_of_eval_mul_nonpos hab.le hEvalMul.le
  have hEvalANe : h.eval a ≠ 0 := by
    rw [hEvalA]
    exact mul_ne_zero (mul_ne_zero hmCast.ne' (sub_ne_zero.mpr hab.ne)) hrEvalA
  have hEvalBNe : h.eval b ≠ 0 := by
    rw [hEvalB]
    exact mul_ne_zero (mul_ne_zero hnCast.ne' (sub_ne_zero.mpr hab.ne')) hrEvalB
  refine ⟨x, ⟨?_, ?_⟩, ?_⟩
  · exact hx.1.lt_of_ne fun hxa ↦ hEvalANe (hxa ▸ hxRoot.eq_zero)
  · exact hx.2.lt_of_ne fun hxb ↦ hEvalBNe (hxb ▸ hxRoot.eq_zero)
  · rw [IsRoot, hderiv, eval_mul, eval_mul, hxRoot.eq_zero, mul_zero]

end OptimalConvergenceRates.KrivineStengle

end
