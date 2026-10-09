/-
  OptimalConvergenceRates/KrivineStengle/PolynomialSigns.lean

  Polynomial sign lemmas over the reals and ordered fields.
-/
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

open Filter Set

namespace OptimalConvergenceRates.KrivineStengle

open Polynomial

private theorem realPolynomial_exists_isRoot_of_odd_of_leadingCoeff_pos
    {f : ℝ[X]} (hodd : Odd f.natDegree) (hlc : 0 < f.leadingCoeff) :
    ∃ x, f.IsRoot x := by
  have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hodd.pos
  have htop : Tendsto f.eval atTop atTop :=
    f.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlc.le
  have hcompdeg : 0 < (f.comp (-X)).degree := by
    simp [hdeg]
  have hcomplc : (f.comp (-X)).leadingCoeff ≤ 0 := by
    rw [comp_neg_X_leadingCoeff_eq, hodd.neg_one_pow]
    simp [hlc.le]
  have hcompbot : Tendsto (f.comp (-X)).eval atTop atBot :=
    (f.comp (-X)).tendsto_atBot_of_leadingCoeff_nonpos hcompdeg hcomplc
  have hpos : ∀ᶠ x in atTop, 0 ≤ f.eval x :=
    htop.eventually (eventually_ge_atTop 0)
  have hneg : ∀ᶠ x in atTop, (f.comp (-X)).eval x ≤ 0 :=
    hcompbot.eventually (eventually_le_atBot 0)
  have hnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ x := eventually_ge_atTop 0
  obtain ⟨c, hcpos, hcneg, hc⟩ := (hpos.and (hneg.and hnonneg)).exists
  have hleft : f.eval (-c) ≤ 0 := by
    simpa using hcneg
  have hzero : (0 : ℝ) ∈ Icc (f.eval (-c)) (f.eval c) := ⟨hleft, hcpos⟩
  obtain ⟨x, -, hx⟩ :=
    (intermediate_value_Icc (neg_le_self hc) f.continuous.continuousOn) hzero
  exact ⟨x, hx⟩

/-- Every real polynomial of odd degree has a real root. -/
theorem realPolynomial_exists_isRoot_of_odd_natDegree {f : ℝ[X]}
    (hodd : Odd f.natDegree) : ∃ x, f.IsRoot x := by
  have hf : f ≠ 0 := by
    intro hf
    subst f
    simp at hodd
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hf) with hlc | hlc
  · obtain ⟨x, hx⟩ :=
      realPolynomial_exists_isRoot_of_odd_of_leadingCoeff_pos
        (f := -f) (by rwa [natDegree_neg]) (by simpa using hlc)
    exact ⟨x, by simpa using hx⟩
  · exact realPolynomial_exists_isRoot_of_odd_of_leadingCoeff_pos hodd hlc

/-- The standard real numbers satisfy Mathlib's algebraic `IsRealClosed` interface. -/
instance realIsRealClosed : IsRealClosed ℝ :=
  IsRealClosed.of_linearOrderedField
    (fun {x} hx ↦ ⟨Real.sqrt x, by simpa [pow_two] using (Real.sq_sqrt hx).symm⟩)
    realPolynomial_exists_isRoot_of_odd_natDegree

end OptimalConvergenceRates.KrivineStengle

end
