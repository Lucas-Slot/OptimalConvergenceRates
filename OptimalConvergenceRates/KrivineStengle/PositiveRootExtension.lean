/-
  OptimalConvergenceRates/KrivineStengle/PositiveRootExtension.lean

  Adjoining a square root of a positive element preserves orderability.
-/
import OptimalConvergenceRates.KrivineStengle.WeightedSquares
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- The polynomial used to adjoin a square root. -/
def sqrtPolynomial (a : F) : F[X] := X ^ 2 - C a

private theorem sqrtPolynomial_ne_zero (a : F) : sqrtPolynomial a ≠ 0 :=
  X_pow_sub_C_ne_zero (by omega) a

@[simp] theorem sqrtPolynomial_natDegree (a : F) : (sqrtPolynomial a).natDegree = 2 :=
  natDegree_X_pow_sub_C

theorem sqrtPolynomial_monic (a : F) : (sqrtPolynomial a).Monic :=
  monic_X_pow_sub_C a (by omega)

theorem sqrtPolynomial_irreducible {a : F} (ha : ¬IsSquare a) :
    Irreducible (sqrtPolynomial a) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · simp
  · intro x hx
    apply ha
    rw [isSquare_iff_exists_sq]
    refine ⟨x, ?_⟩
    have hzero : x ^ 2 - a = 0 := by
      simpa [Polynomial.IsRoot.def, sqrtPolynomial] using hx
    exact (sub_eq_zero.mp hzero).symm

@[simp] theorem sqrtAdjoinRoot_sq (a : F) :
    (AdjoinRoot.root (sqrtPolynomial a)) ^ 2 =
      algebraMap F (AdjoinRoot (sqrtPolynomial a)) a := by
  have h := AdjoinRoot.eval₂_root (sqrtPolynomial a)
  simpa [sqrtPolynomial, sub_eq_zero] using h

/-- Every element of the quadratic adjoined-root field has the expected two-coordinate normal
form. -/
private theorem sqrtAdjoinRoot_exists_normal {a : F}
    [Fact (Irreducible (sqrtPolynomial a))] (z : AdjoinRoot (sqrtPolynomial a)) :
    ∃ u v : F, z = algebraMap F (AdjoinRoot (sqrtPolynomial a)) u +
      algebraMap F (AdjoinRoot (sqrtPolynomial a)) v *
        AdjoinRoot.root (sqrtPolynomial a) := by
  let pb := AdjoinRoot.powerBasis (sqrtPolynomial_ne_zero a)
  obtain ⟨q, hq, hz⟩ := pb.exists_eq_aeval z
  have hq2 : q.natDegree < 2 := by simpa [pb] using hq
  have hqform : q = C (q.coeff 0) + C (q.coeff 1) * X := by
    ext n
    by_cases hn : n < 2
    · interval_cases n <;> simp
    · have h2n : 2 ≤ n := Nat.le_of_not_gt hn
      rw [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hq2 h2n)]
      rw [coeff_add, coeff_C_ne_zero (by omega), coeff_C_mul_X, if_neg (by omega)]
      simp
  refine ⟨q.coeff 0, q.coeff 1, ?_⟩
  rw [hz, hqform]
  simp [pb]

private theorem linearPolynomial_natDegree_lt_two (u v : F) :
    (C u + C v * X : F[X]).natDegree < 2 := by
  calc
    (C u + C v * X : F[X]).natDegree ≤
        max (C u).natDegree (C v * X).natDegree := natDegree_add_le _ _
    _ ≤ 1 := by
      apply max_le
      · simp
      · calc
          (C v * X : F[X]).natDegree ≤ (C v).natDegree + X.natDegree := natDegree_mul_le
          _ ≤ 1 := by simp
    _ < 2 := by omega

/-- Uniqueness of the two quadratic coordinates, in the zero case. -/
private theorem sqrtAdjoinRoot_normal_eq_zero {a u v : F}
    (h : algebraMap F (AdjoinRoot (sqrtPolynomial a)) u +
      algebraMap F (AdjoinRoot (sqrtPolynomial a)) v *
        AdjoinRoot.root (sqrtPolynomial a) = 0) :
    u = 0 ∧ v = 0 := by
  let q : F[X] := C u + C v * X
  have hmk : AdjoinRoot.mk (sqrtPolynomial a) q = 0 := by
    simpa [q] using h
  have hq : q = 0 := by
    by_contra hn
    exact AdjoinRoot.mk_ne_zero_of_natDegree_lt (sqrtPolynomial_monic a) hn
      (by simpa [q] using linearPolynomial_natDegree_lt_two u v) hmk
  constructor
  · have hc := congrArg (fun r : F[X] ↦ r.coeff 0) hq
    simpa [q] using hc
  · have hc := congrArg (fun r : F[X] ↦ r.coeff 1) hq
    simpa [q] using hc

/-- In a positive quadratic extension, every finite weighted sum of squares has a
nonnegative constant coordinate. -/
private theorem weightedSquareRep_sqrtAdjoinRoot_normal_nonneg {a : F}
    [Fact (Irreducible (sqrtPolynomial a))] (ha : 0 < a)
    {z : AdjoinRoot (sqrtPolynomial a)}
    (hz : WeightedSquareRep F (AdjoinRoot (sqrtPolynomial a)) z) :
    ∃ u v : F, 0 ≤ u ∧
      z = algebraMap F (AdjoinRoot (sqrtPolynomial a)) u +
        algebraMap F (AdjoinRoot (sqrtPolynomial a)) v *
          AdjoinRoot.root (sqrtPolynomial a) := by
  induction hz with
  | zero => exact ⟨0, 0, le_rfl, by simp⟩
  | add hx hy ihx ihy =>
      obtain ⟨u, v, hu, huv⟩ := ihx
      obtain ⟨s, t, hs, hst⟩ := ihy
      refine ⟨u + s, v + t, add_nonneg hu hs, ?_⟩
      rw [huv, hst]
      push_cast
      ring
  | term c hc w =>
      obtain ⟨x, y, hxy⟩ := sqrtAdjoinRoot_exists_normal w
      refine ⟨c * (x ^ 2 + a * y ^ 2), c * (2 * x * y), ?_, ?_⟩
      · exact mul_nonneg hc
          (add_nonneg (sq_nonneg x) (mul_nonneg ha.le (sq_nonneg y)))
      · rw [hxy]
        simp only [map_mul, map_add, map_pow, map_ofNat]
        ring_nf
        rw [sqrtAdjoinRoot_sq]

private theorem sqrtAdjoinRoot_weightedSquareCone_isProper {a : F}
    (ha : 0 < a) (hns : ¬IsSquare a) :
    letI : Fact (Irreducible (sqrtPolynomial a)) :=
      ⟨sqrtPolynomial_irreducible hns⟩
    IsProperSquareCone
      (weightedSquareCone F (AdjoinRoot (sqrtPolynomial a))) := by
  letI : Fact (Irreducible (sqrtPolynomial a)) :=
    ⟨sqrtPolynomial_irreducible hns⟩
  refine ⟨weightedSquareCone_isSquareCone F _, ?_⟩
  intro hneg
  have hrep : WeightedSquareRep F (AdjoinRoot (sqrtPolynomial a)) (-1) :=
    (mem_weightedSquareCone_iff F _).mp hneg
  obtain ⟨u, v, hu, huv⟩ :=
    weightedSquareRep_sqrtAdjoinRoot_normal_nonneg ha hrep
  have hzero : algebraMap F (AdjoinRoot (sqrtPolynomial a)) (u + 1) +
      algebraMap F (AdjoinRoot (sqrtPolynomial a)) v *
        AdjoinRoot.root (sqrtPolynomial a) = 0 := by
    rw [map_add, map_one]
    calc
      algebraMap F (AdjoinRoot (sqrtPolynomial a)) u + 1 +
          algebraMap F (AdjoinRoot (sqrtPolynomial a)) v *
            AdjoinRoot.root (sqrtPolynomial a) =
        (algebraMap F (AdjoinRoot (sqrtPolynomial a)) u +
          algebraMap F (AdjoinRoot (sqrtPolynomial a)) v *
            AdjoinRoot.root (sqrtPolynomial a)) + 1 := by ring
      _ = -1 + 1 := by rw [← huv]
      _ = 0 := by ring
  have huv0 := sqrtAdjoinRoot_normal_eq_zero hzero
  have : u = -1 := by linarith [huv0.1]
  linarith

/-- Every positive element acquires a square root in some ordered field extension. -/
theorem exists_orderedExtension_with_sq_eq {a : F} (ha : 0 < a) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra F L),
      Nonempty (OrderedExtensionData F L) ∧
        ∃ r : L, r ^ 2 = algebraMap F L a := by
  by_cases hsq : IsSquare a
  · obtain ⟨r, hr⟩ := (isSquare_iff_exists_sq a).mp hsq
    refine ⟨F, inferInstance, inferInstance, ?_, r, ?_⟩
    · exact ⟨⟨inferInstance, inferInstance, fun h ↦ by simpa using h⟩⟩
    · simpa using hr.symm
  · letI : Fact (Irreducible (sqrtPolynomial a)) :=
      ⟨sqrtPolynomial_irreducible hsq⟩
    let L := AdjoinRoot (sqrtPolynomial a)
    have hproper : -1 ∉ weightedSquareCone F L :=
      (sqrtAdjoinRoot_weightedSquareCone_isProper ha hsq).2
    refine ⟨L, inferInstance, inferInstance,
      (nonempty_orderedExtensionData_iff F L).2 hproper,
      AdjoinRoot.root (sqrtPolynomial a), ?_⟩
    exact sqrtAdjoinRoot_sq a

/-- The positive-root extension can be chosen algebraic over the base field. -/
theorem exists_algebraic_orderedExtension_with_sq_eq {a : F} (ha : 0 < a) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra F L),
      Algebra.IsAlgebraic F L ∧ Nonempty (OrderedExtensionData F L) ∧
        ∃ r : L, r ^ 2 = algebraMap F L a := by
  by_cases hsq : IsSquare a
  · obtain ⟨r, hr⟩ := (isSquare_iff_exists_sq a).mp hsq
    refine ⟨F, inferInstance, inferInstance, inferInstance, ?_, r, ?_⟩
    · exact ⟨⟨inferInstance, inferInstance, fun h ↦ by simpa using h⟩⟩
    · simpa using hr.symm
  · letI : Fact (Irreducible (sqrtPolynomial a)) :=
      ⟨sqrtPolynomial_irreducible hsq⟩
    let L := AdjoinRoot (sqrtPolynomial a)
    letI : Module.Finite F L := (sqrtPolynomial_monic a).finite_adjoinRoot
    have hproper : -1 ∉ weightedSquareCone F L :=
      (sqrtAdjoinRoot_weightedSquareCone_isProper ha hsq).2
    refine ⟨L, inferInstance, inferInstance, inferInstance,
      (nonempty_orderedExtensionData_iff F L).2 hproper,
      AdjoinRoot.root (sqrtPolynomial a), ?_⟩
    exact sqrtAdjoinRoot_sq a

end OptimalConvergenceRates.KrivineStengle

end
