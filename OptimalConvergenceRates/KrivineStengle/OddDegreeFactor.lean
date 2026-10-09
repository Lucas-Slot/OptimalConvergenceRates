/-
  OptimalConvergenceRates/KrivineStengle/OddDegreeFactor.lean

  Parity and factor extraction for the odd-degree order-extension induction.
-/
import OptimalConvergenceRates.KrivineStengle.OddDegreeObstruction
import Mathlib.RingTheory.Polynomial.UniqueFactorization

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Dividing an even-degree obstruction by its odd-degree defining polynomial leaves a
nonconstant odd-degree quotient of strictly smaller degree. -/
theorem OddDegreePolynomialObstruction.exists_odd_degree_quotient {m : F[X]}
    (ob : OddDegreePolynomialObstruction m) (hm : Irreducible m)
    (hmOdd : Odd m.natDegree) :
    ∃ h : F[X],
      ob.polynomial = m * h ∧ h ≠ 0 ∧ Odd h.natDegree ∧
        0 < h.natDegree ∧ h.natDegree < m.natDegree := by
  obtain ⟨h, hmul⟩ := ob.definingPolynomial_dvd
  have hh0 : h ≠ 0 := by
    intro hh
    apply ob.ne_zero
    rw [hmul, hh, mul_zero]
  have hdeg : ob.polynomial.natDegree = m.natDegree + h.natDegree := by
    rw [hmul, Polynomial.natDegree_mul hm.ne_zero hh0]
  have hsumEven : Even (m.natDegree + h.natDegree) := by
    rw [← hdeg]
    exact ob.even_natDegree
  have hhOdd : Odd h.natDegree := (Nat.even_add'.mp hsumEven).mp hmOdd
  have hhPos : 0 < h.natDegree := hhOdd.pos
  have hhLt : h.natDegree < m.natDegree := by
    have hbound := ob.natDegree_lt_two_mul
    rw [hdeg] at hbound
    omega
  exact ⟨h, hmul, hh0, hhOdd, hhPos, hhLt⟩

/-- Every polynomial of odd natural degree over a field has an irreducible factor of odd
natural degree. -/
theorem exists_irreducible_factor_of_odd_natDegree {p : F[X]}
    (hpOdd : Odd p.natDegree) :
    ∃ r : F[X], Irreducible r ∧ Odd r.natDegree ∧ r ∣ p := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
      have hpPos : 0 < p.natDegree := hpOdd.pos
      obtain ⟨r, hr, hrp⟩ := Polynomial.exists_irreducible_of_natDegree_pos hpPos
      rcases Nat.even_or_odd r.natDegree with hrEven | hrOdd
      · obtain ⟨q, hpq⟩ := hrp
        have hp0 : p ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hpPos
        have hq0 : q ≠ 0 := by
          intro hq
          apply hp0
          rw [hpq, hq, mul_zero]
        have hdeg : p.natDegree = r.natDegree + q.natDegree := by
          rw [hpq, Polynomial.natDegree_mul hr.ne_zero hq0]
        have hsumOdd : Odd (r.natDegree + q.natDegree) := by
          rw [← hdeg]
          exact hpOdd
        have hqOdd : Odd q.natDegree := (Nat.odd_add'.mp hsumOdd).mpr hrEven
        have hrPos : 0 < r.natDegree := hr.natDegree_pos
        have hqLt : q.natDegree < n := by omega
        obtain ⟨s, hs, hsOdd, hsq⟩ := ih q.natDegree hqLt (p := q) hqOdd rfl
        have hqp : q ∣ p := ⟨r, by rw [hpq, mul_comm]⟩
        exact ⟨s, hs, hsOdd, hsq.trans hqp⟩
      · exact ⟨r, hr, hrOdd, hrp⟩

end OptimalConvergenceRates.KrivineStengle

end
