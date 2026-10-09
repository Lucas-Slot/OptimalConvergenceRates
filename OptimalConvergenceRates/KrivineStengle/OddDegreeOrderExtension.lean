/-
  OptimalConvergenceRates/KrivineStengle/OddDegreeOrderExtension.lean

  Extension of an ordered-field order across an irreducible odd-degree simple extension.
-/
import OptimalConvergenceRates.KrivineStengle.OddDegreeFactor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

open PolynomialWeightedSquareRep

/-- The order on an ordered field extends across every irreducible odd-degree adjoined-root
extension. This is the inductive order-extension lemma used in the real-closure construction. -/
theorem nonempty_orderedExtensionData_adjoinRoot_of_irreducible_of_odd_natDegree
    (m : F[X]) (hm : Irreducible m) (hmOdd : Odd m.natDegree) :
    letI : Fact (Irreducible m) := ⟨hm⟩
    Nonempty (OrderedExtensionData F (AdjoinRoot m)) := by
  induction hd : m.natDegree using Nat.strong_induction_on generalizing m with
  | h d ih =>
      letI : Fact (Irreducible m) := ⟨hm⟩
      rw [nonempty_orderedExtensionData_iff]
      intro hneg
      obtain ⟨ob⟩ := exists_oddDegreePolynomialObstruction m hm hneg
      obtain ⟨q, hmul, hq0, hqOdd, hqPos, hqLt⟩ :=
        ob.exists_odd_degree_quotient hm hmOdd
      obtain ⟨r, hr, hrOdd, hrq⟩ :=
        exists_irreducible_factor_of_odd_natDegree hqOdd
      have hrLe : r.natDegree ≤ q.natDegree :=
        Polynomial.natDegree_le_of_dvd hrq hq0
      have hrLt : r.natDegree < d := by omega
      letI : Fact (Irreducible r) := ⟨hr⟩
      have hrOrder : Nonempty (OrderedExtensionData F (AdjoinRoot r)) := by
        exact ih r.natDegree hrLt r hr hrOdd rfl
      obtain ⟨E⟩ := hrOrder
      letI : LinearOrder (AdjoinRoot r) := E.order
      letI : IsStrictOrderedRing (AdjoinRoot r) := E.strictOrderedRing
      have hbase (c : F) (hc : 0 ≤ c) :
          0 ≤ algebraMap F (AdjoinRoot r) c := by
        simpa only [map_zero] using E.algebraMap_monotone hc
      have hremNonneg :
          0 ≤ aeval (AdjoinRoot.root r) ob.remainder := by
        exact PolynomialWeightedSquareRep.aeval_nonneg
          (BoundedPolynomialWeightedSquareRep.toPolynomialWeightedSquareRep
            ob.remainder_representation)
          hbase (AdjoinRoot.root r)
      have hrPolynomial : r ∣ ob.polynomial := by
        obtain ⟨s, hs⟩ := hrq
        refine ⟨m * s, ?_⟩
        rw [hmul, hs]
        ring
      have hzero : AdjoinRoot.mk r ob.polynomial = 0 :=
        AdjoinRoot.mk_eq_zero.mpr hrPolynomial
      have heq : (0 : AdjoinRoot r) =
          1 + aeval (AdjoinRoot.root r) ob.remainder := by
        calc
          0 = AdjoinRoot.mk r ob.polynomial := hzero.symm
          _ = AdjoinRoot.mk r (1 + ob.remainder) :=
            congrArg (AdjoinRoot.mk r) ob.polynomial_eq_one_add_remainder
          _ = 1 + AdjoinRoot.mk r ob.remainder := by rw [map_add, map_one]
          _ = 1 + aeval (AdjoinRoot.root r) ob.remainder := by
            rw [AdjoinRoot.aeval_eq]
      linarith

end OptimalConvergenceRates.KrivineStengle

end
