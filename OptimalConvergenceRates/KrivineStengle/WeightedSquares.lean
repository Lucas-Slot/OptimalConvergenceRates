/-
  OptimalConvergenceRates/KrivineStengle/WeightedSquares.lean

  Finite weighted-sum representation of the cone used in order extension.
-/
import OptimalConvergenceRates.KrivineStengle.OrderExtension
import Mathlib.Tactic.Ring

noncomputable section

namespace OptimalConvergenceRates.KrivineStengle

universe u v

variable (F : Type u) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable (L : Type v) [Field L] [Algebra F L]

/-- Explicit finite sums of terms `c * z²` with nonnegative base-field coefficients. -/
inductive WeightedSquareRep : L → Prop
  | zero : WeightedSquareRep 0
  | add {x y : L} : WeightedSquareRep x → WeightedSquareRep y →
      WeightedSquareRep (x + y)
  | term (c : F) (hc : 0 ≤ c) (z : L) :
      WeightedSquareRep (algebraMap F L c * z ^ 2)

namespace WeightedSquareRep

theorem one : WeightedSquareRep F L 1 := by
  simpa using term (F := F) (L := L) 1 zero_le_one 1

theorem sq (z : L) : WeightedSquareRep F L (z ^ 2) := by
  simpa using term (F := F) (L := L) 1 zero_le_one z

theorem mul {x y : L} (hx : WeightedSquareRep F L x) (hy : WeightedSquareRep F L y) :
    WeightedSquareRep F L (x * y) := by
  induction hx with
  | zero => simpa using (zero (F := F) (L := L))
  | add hx₁ hx₂ ih₁ ih₂ =>
      rw [add_mul]
      exact add ih₁ ih₂
  | term c hc z =>
      induction hy with
      | zero => simpa using (zero (F := F) (L := L))
      | add hy₁ hy₂ ih₁ ih₂ =>
          rw [mul_add]
          exact add ih₁ ih₂
      | term d hd w =>
          have hcd : 0 ≤ c * d := mul_nonneg hc hd
          have hterm := term (F := F) (L := L) (c * d) hcd (z * w)
          convert hterm using 1
          all_goals simp only [map_mul, pow_two]
          all_goals ring

theorem isSquareCone : IsSquareCone {x : L | WeightedSquareRep F L x} where
  zero_mem := zero (F := F) (L := L)
  one_mem := one F L
  add_mem := fun hx hy ↦ add hx hy
  mul_mem := fun hx hy ↦ mul F L hx hy
  sq_mem := sq F L

theorem algebraMap (c : F) (hc : 0 ≤ c) :
    WeightedSquareRep F L (algebraMap F L c) := by
  simpa using term (F := F) (L := L) c hc 1

end WeightedSquareRep

/-- The impredicative least-cone definition agrees with literal finite weighted sums of
squares. This is the induction principle used by the algebraic-extension arguments. -/
theorem mem_weightedSquareCone_iff {x : L} :
    x ∈ weightedSquareCone F L ↔ WeightedSquareRep F L x := by
  constructor
  · intro hx
    exact hx {y : L | WeightedSquareRep F L y}
      (WeightedSquareRep.isSquareCone F L) (WeightedSquareRep.algebraMap F L)
  · intro hx P hP hbase
    induction hx with
    | zero => exact hP.zero_mem
    | add hx hy ihx ihy => exact hP.add_mem ihx ihy
    | term c hc z => exact hP.mul_mem (hbase c hc) (hP.sq_mem z)

end OptimalConvergenceRates.KrivineStengle

end
