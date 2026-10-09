/-
  OptimalConvergenceRates/KrivineStengle/OddDegreeExtension.lean

  Degree control for weighted sums of polynomial squares.  This is the
  cancellation-free polynomial infrastructure used by the odd-degree
  order-extension argument.
-/
import OptimalConvergenceRates.KrivineStengle.WeightedSquares
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Tactic

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Finite sums of terms consisting of a nonnegative scalar times a
polynomial square. -/
inductive PolynomialWeightedSquareRep : F[X] → Prop
  | zero : PolynomialWeightedSquareRep 0
  | add {p q : F[X]} : PolynomialWeightedSquareRep p →
      PolynomialWeightedSquareRep q → PolynomialWeightedSquareRep (p + q)
  | term (c : F) (hc : 0 ≤ c) (q : F[X]) :
      PolynomialWeightedSquareRep (C c * q ^ 2)

namespace PolynomialWeightedSquareRep

/-- A nonzero weighted sum of polynomial squares has even degree and
positive leading coefficient. -/
theorem eq_zero_or_even_natDegree_and_pos_leadingCoeff {p : F[X]}
    (hp : PolynomialWeightedSquareRep p) :
    p = 0 ∨ (Even p.natDegree ∧ 0 < p.leadingCoeff) := by
  induction hp with
  | zero => exact Or.inl rfl
  | term c hc q =>
      by_cases hc0 : c = 0
      · left
        simp [hc0]
      by_cases hq0 : q = 0
      · left
        simp [hq0]
      right
      have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      have hC0 : C c ≠ (0 : F[X]) := C_ne_zero.mpr hc0
      have hq20 : q ^ 2 ≠ (0 : F[X]) := pow_ne_zero _ hq0
      constructor
      · rw [natDegree_mul hC0 hq20, natDegree_C, zero_add, natDegree_pow]
        exact even_two_mul q.natDegree
      · rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_pow]
        exact mul_pos hcpos (sq_pos_of_ne_zero (leadingCoeff_ne_zero.mpr hq0))
  | @add p q hp hq ihp ihq =>
      rcases ihp with rfl | ⟨hpEven, hpLead⟩
      · simpa using ihq
      rcases ihq with rfl | ⟨hqEven, hqLead⟩
      · simpa using Or.inr ⟨hpEven, hpLead⟩
      have hp0 : p ≠ 0 := leadingCoeff_ne_zero.mp hpLead.ne'
      have hq0 : q ≠ 0 := leadingCoeff_ne_zero.mp hqLead.ne'
      rcases lt_trichotomy p.natDegree q.natDegree with hpq | hpq | hpq
      · right
        have hdeg : (p + q).natDegree = q.natDegree :=
          natDegree_add_eq_right_of_natDegree_lt hpq
        have hlc : (p + q).leadingCoeff = q.leadingCoeff :=
          leadingCoeff_add_of_degree_lt (degree_lt_degree hpq)
        exact ⟨hdeg.symm ▸ hqEven, hlc.symm ▸ hqLead⟩
      · right
        have hdegree : p.degree = q.degree := by
          rw [degree_eq_natDegree hp0, degree_eq_natDegree hq0, hpq]
        have hlead : 0 < p.leadingCoeff + q.leadingCoeff :=
          add_pos hpLead hqLead
        have hdeg : (p + q).natDegree = p.natDegree := by
          apply natDegree_eq_of_degree_eq
          rw [degree_add_eq_of_leadingCoeff_add_ne_zero hlead.ne', hdegree, max_self]
        have hlc : (p + q).leadingCoeff = p.leadingCoeff + q.leadingCoeff :=
          leadingCoeff_add_of_degree_eq hdegree hlead.ne'
        exact ⟨hdeg.symm ▸ hpEven, hlc.symm ▸ hlead⟩
      · right
        have hdeg : (p + q).natDegree = p.natDegree :=
          natDegree_add_eq_left_of_natDegree_lt hpq
        have hlc : (p + q).leadingCoeff = p.leadingCoeff :=
          leadingCoeff_add_of_degree_lt' (degree_lt_degree hpq)
        exact ⟨hdeg.symm ▸ hpEven, hlc.symm ▸ hpLead⟩

end PolynomialWeightedSquareRep

/-- A weighted polynomial-square representation in which every squared
polynomial has degree strictly below the bound. -/
inductive BoundedPolynomialWeightedSquareRep (d : ℕ) : F[X] → Prop
  | zero : BoundedPolynomialWeightedSquareRep d 0
  | add {p q : F[X]} : BoundedPolynomialWeightedSquareRep d p →
      BoundedPolynomialWeightedSquareRep d q →
      BoundedPolynomialWeightedSquareRep d (p + q)
  | term (c : F) (hc : 0 ≤ c) (q : F[X]) (hq : q.natDegree < d) :
      BoundedPolynomialWeightedSquareRep d (C c * q ^ 2)

namespace BoundedPolynomialWeightedSquareRep

/-- Forget the degree bound. -/
theorem toPolynomialWeightedSquareRep {d : ℕ} {p : F[X]}
    (hp : BoundedPolynomialWeightedSquareRep d p) :
    PolynomialWeightedSquareRep p := by
  induction hp with
  | zero => exact .zero
  | add _ _ ihp ihq => exact .add ihp ihq
  | term c hc q _ => exact .term c hc q

/-- Every represented polynomial has natural degree strictly below twice
its term bound, provided the bound is positive. -/
theorem natDegree_lt_two_mul {d : ℕ} {p : F[X]}
    (hp : BoundedPolynomialWeightedSquareRep d p) (hd : 0 < d) :
    p.natDegree < 2 * d := by
  induction hp with
  | zero => simp; omega
  | @add p q hp hq ihp ihq =>
      exact (natDegree_add_le p q).trans_lt (by omega)
  | term c hc q hq =>
      calc
        (C c * q ^ 2).natDegree ≤ (C c).natDegree + (q ^ 2).natDegree :=
          natDegree_mul_le
        _ ≤ 0 + 2 * q.natDegree := by
          gcongr
          · simp
          · exact natDegree_pow_le
        _ < 2 * d := by omega

end BoundedPolynomialWeightedSquareRep

end OptimalConvergenceRates.KrivineStengle

end
