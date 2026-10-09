/-
  OptimalConvergenceRates/KrivineStengle/OddDegreeObstruction.lean

  Polynomial obstruction extracted from a failure to order an odd-degree simple extension.
-/
import OptimalConvergenceRates.KrivineStengle.OddDegreeExtension
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.AdjoinRoot

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

open PolynomialWeightedSquareRep

namespace PolynomialWeightedSquareRep

/-- A weighted sum of polynomial squares evaluates nonnegatively in its ordered base field. -/
theorem eval_nonneg {p : F[X]} (hp : PolynomialWeightedSquareRep p) (x : F) :
    0 ≤ p.eval x := by
  induction hp with
  | zero => simp
  | add hp hq ihp ihq => simpa using add_nonneg ihp ihq
  | term c hc q =>
      simp only [eval_mul, eval_C, eval_pow]
      exact mul_nonneg hc (sq_nonneg _)

/-- Weighted polynomial squares remain nonnegative after evaluation in any ordered extension. -/
theorem aeval_nonneg {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    [Algebra F L] {p : F[X]} (hp : PolynomialWeightedSquareRep p)
    (hbase : ∀ c : F, 0 ≤ c → 0 ≤ algebraMap F L c) (x : L) :
    0 ≤ aeval x p := by
  induction hp with
  | zero => simp
  | add hp hq ihp ihq => simpa using add_nonneg ihp ihq
  | term c hc q =>
      simp only [map_mul, map_pow, Polynomial.aeval_C]
      exact mul_nonneg (hbase c hc) (sq_nonneg _)

end PolynomialWeightedSquareRep

/-- Every class in an irreducible adjoined-root extension has a representative of degree
strictly below the degree of the defining polynomial. -/
private theorem adjoinRoot_exists_reducedRepresentative (m : F[X]) (hm : Irreducible m)
    (z : AdjoinRoot m) :
    ∃ q : F[X], q.natDegree < m.natDegree ∧ z = AdjoinRoot.mk m q := by
  letI : Fact (Irreducible m) := ⟨hm⟩
  let pb := AdjoinRoot.powerBasis hm.ne_zero
  obtain ⟨q, hq, hz⟩ := pb.exists_eq_aeval z
  refine ⟨q, by simpa [pb] using hq, ?_⟩
  rw [hz]
  simp [pb]

/-- A finite weighted sum of squares in an adjoined-root field can be represented by a
degree-bounded weighted sum of polynomial squares. -/
private theorem weightedSquareRep_adjoinRoot_exists_bounded (m : F[X])
    [Fact (Irreducible m)] (hm : Irreducible m) {z : AdjoinRoot m}
    (hz : WeightedSquareRep F (AdjoinRoot m) z) :
    ∃ p : F[X],
      BoundedPolynomialWeightedSquareRep m.natDegree p ∧
        z = AdjoinRoot.mk m p := by
  induction hz with
  | zero => exact ⟨0, .zero, by simp⟩
  | @add x y hx hy ihx ihy =>
      obtain ⟨p, hp, hxp⟩ := ihx
      obtain ⟨q, hq, hyq⟩ := ihy
      refine ⟨p + q, .add hp hq, ?_⟩
      rw [hxp, hyq, map_add]
  | term c hc w =>
      obtain ⟨q, hq, hwq⟩ := adjoinRoot_exists_reducedRepresentative m hm w
      refine ⟨C c * q ^ 2, .term c hc q hq, ?_⟩
      rw [hwq]
      simp

/-- The cancellation-free polynomial obstruction obtained from `-1` in the weighted-square
cone of an irreducible simple extension. -/
structure OddDegreePolynomialObstruction (m : F[X]) where
  polynomial : F[X]
  remainder : F[X]
  remainder_representation :
    BoundedPolynomialWeightedSquareRep m.natDegree remainder
  polynomial_eq_one_add_remainder : polynomial = 1 + remainder
  representation :
    BoundedPolynomialWeightedSquareRep m.natDegree polynomial
  definingPolynomial_dvd : m ∣ polynomial
  ne_zero : polynomial ≠ 0
  even_natDegree : Even polynomial.natDegree
  leadingCoeff_pos : 0 < polynomial.leadingCoeff
  natDegree_lt_two_mul : polynomial.natDegree < 2 * m.natDegree

/-- Improperness of the weighted-square cone in an irreducible simple extension yields the
nonzero even-degree multiple used by the odd-degree induction. -/
theorem exists_oddDegreePolynomialObstruction (m : F[X]) (hm : Irreducible m) :
    letI : Fact (Irreducible m) := ⟨hm⟩
    (-1 ∈ weightedSquareCone F (AdjoinRoot m) →
      Nonempty (OddDegreePolynomialObstruction m)) := by
  letI : Fact (Irreducible m) := ⟨hm⟩
  intro hneg
  have hd : 0 < m.natDegree := hm.natDegree_pos
  have hrep : WeightedSquareRep F (AdjoinRoot m) (-1) :=
    (mem_weightedSquareCone_iff F _).mp hneg
  obtain ⟨p, hp, hpRoot⟩ := weightedSquareRep_adjoinRoot_exists_bounded m hm hrep
  let P : F[X] := 1 + p
  have hOne :
      BoundedPolynomialWeightedSquareRep m.natDegree
        (1 : F[X]) := by
    simpa using
      (BoundedPolynomialWeightedSquareRep.term
        (d := m.natDegree) (1 : F) zero_le_one (1 : F[X]) (by simpa using hd))
  have hP :
      BoundedPolynomialWeightedSquareRep m.natDegree P := by
    exact BoundedPolynomialWeightedSquareRep.add hOne hp
  have hPRoot : AdjoinRoot.mk m P = 0 := by
    rw [show P = 1 + p by rfl, map_add, map_one, ← hpRoot]
    norm_num
  have hPdvd : m ∣ P := AdjoinRoot.mk_eq_zero.mp hPRoot
  have hP0 : P ≠ 0 := by
    intro hzero
    have hpEval : 0 ≤ p.eval 0 :=
      PolynomialWeightedSquareRep.eval_nonneg
        (BoundedPolynomialWeightedSquareRep.toPolynomialWeightedSquareRep
          hp) 0
    have heval := congrArg (Polynomial.eval 0) hzero
    simp only [P, eval_add, eval_one, eval_zero] at heval
    linarith
  have hPShape :=
    PolynomialWeightedSquareRep.eq_zero_or_even_natDegree_and_pos_leadingCoeff
      (BoundedPolynomialWeightedSquareRep.toPolynomialWeightedSquareRep
        hP)
  rcases hPShape with hzero | ⟨hEven, hLead⟩
  · exact (hP0 hzero).elim
  · exact ⟨⟨P, p, hp, rfl, hP, hPdvd, hP0, hEven, hLead,
      BoundedPolynomialWeightedSquareRep.natDegree_lt_two_mul hP hd⟩⟩

end OptimalConvergenceRates.KrivineStengle

end
