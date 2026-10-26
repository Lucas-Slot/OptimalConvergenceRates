import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
/-!
# Finite Boolean characters and signed Gram matrices

The signed-block result supplies the algebraic positivity step in the
sparse XOR construction. `BoundaryWitness` and `ParityBoundary` treat the
boundary map, while `ExpandingHypergraph` proves the expansion existence
used by the lower bound.
-/

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

open scoped BigOperators symmDiff

section Characters

variable {V : Type*}

/-- The Boolean character indexed by a finite subset of coordinates. -/
def booleanCharacter (z : V → ℝ) (S : Finset V) : ℝ :=
  ∏ i ∈ S, z i

@[simp] theorem booleanCharacter_empty (z : V → ℝ) :
    booleanCharacter z ∅ = 1 := by
  simp [booleanCharacter]

@[simp] theorem booleanCharacter_singleton (z : V → ℝ) (i : V) :
    booleanCharacter z {i} = z i := by
  simp [booleanCharacter]

/-- On a sign assignment every character has square one. -/
theorem booleanCharacter_sq (z : V → ℝ)
    (hz : ∀ i, (z i) ^ 2 = 1) (S : Finset V) :
    (booleanCharacter z S) ^ 2 = 1 := by
  classical
  unfold booleanCharacter
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i hi
  exact hz i

theorem booleanCharacter_mul_self (z : V → ℝ)
    (hz : ∀ i, (z i) ^ 2 = 1) (S : Finset V) :
    booleanCharacter z S * booleanCharacter z S = 1 := by
  simpa only [pow_two] using booleanCharacter_sq z hz S

/-- Disjoint unions multiply characters, even away from the Boolean cube. -/
theorem booleanCharacter_union [DecidableEq V] (z : V → ℝ)
    (S T : Finset V) (h : Disjoint S T) :
    booleanCharacter z (S ∪ T) =
      booleanCharacter z S * booleanCharacter z T := by
  exact Finset.prod_union h

/-- This is the multiplication rule used by the truncated Boolean moment
matrix. Repeated coordinates cancel because each coordinate squares to one. -/
theorem booleanCharacter_mul [DecidableEq V] (z : V → ℝ)
    (hz : ∀ i, (z i) ^ 2 = 1) (S T : Finset V) :
    booleanCharacter z S * booleanCharacter z T =
      booleanCharacter z (S ∆ T) := by
  have hS : booleanCharacter z S =
      booleanCharacter z (S \ T) * booleanCharacter z (S ∩ T) := by
    calc
      booleanCharacter z S =
          booleanCharacter z ((S \ T) ∪ (S ∩ T)) := by
        rw [Finset.sdiff_union_inter]
      _ = _ := booleanCharacter_union z _ _ (Finset.disjoint_sdiff_inter S T)
  have hT : booleanCharacter z T =
      booleanCharacter z (T \ S) * booleanCharacter z (S ∩ T) := by
    calc
      booleanCharacter z T =
          booleanCharacter z ((T \ S) ∪ (T ∩ S)) := by
        rw [Finset.sdiff_union_inter]
      _ = booleanCharacter z (T \ S) * booleanCharacter z (T ∩ S) :=
        booleanCharacter_union z _ _ (Finset.disjoint_sdiff_inter T S)
      _ = _ := by rw [Finset.inter_comm]
  have hdis : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hiS hiT
    exact (Finset.mem_sdiff.mp hiS).2 (Finset.mem_sdiff.mp hiT).1
  have hsets : S ∆ T = (S \ T) ∪ (T \ S) := by
    ext i
    simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
  calc
    booleanCharacter z S * booleanCharacter z T =
        (booleanCharacter z (S \ T) * booleanCharacter z (T \ S)) *
          (booleanCharacter z (S ∩ T) * booleanCharacter z (S ∩ T)) := by
      rw [hS, hT]
      ring
    _ = booleanCharacter z (S \ T) * booleanCharacter z (T \ S) := by
      rw [booleanCharacter_mul_self z hz, mul_one]
    _ = booleanCharacter z (S ∆ T) := by
      rw [hsets, booleanCharacter_union z _ _ hdis]

end Characters

section FiniteGram

variable {I C : Type*} [Fintype I] [Fintype C]

/-- The ordinary real Gram kernel for a finite family of finite vectors. -/
def finiteGramKernel (u : I → C → ℝ) (i j : I) : ℝ :=
  ∑ a, u i a * u j a

/-- Expanding a Gram quadratic form gives a sum of ordinary squares. -/
theorem finiteGram_quadratic_eq (u : I → C → ℝ) (c : I → ℝ) :
    (∑ i, ∑ j, c i * c j * finiteGramKernel u i j) =
      ∑ a, (∑ i, c i * u i a) ^ 2 := by
  classical
  unfold finiteGramKernel
  calc
    (∑ i, ∑ j, c i * c j * ∑ a, u i a * u j a) =
        ∑ i, ∑ j, ∑ a, (c i * u i a) * (c j * u j a) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = ∑ i, ∑ a, ∑ j, (c i * u i a) * (c j * u j a) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, (c i * u i a) * (c j * u j a) := by
      exact Finset.sum_comm
    _ = ∑ a, (∑ i, c i * u i a) ^ 2 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [pow_two, Finset.sum_mul_sum]

theorem finiteGram_quadratic_nonneg (u : I → C → ℝ) (c : I → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * finiteGramKernel u i j := by
  rw [finiteGram_quadratic_eq]
  exact Finset.sum_nonneg fun a ha => sq_nonneg _

end FiniteGram

section SignedBlocks

variable {I C : Type*} [Fintype I] [Fintype C] [DecidableEq C]

/-- The kernel consisting of one rank-one block for each class. -/
def signedBlockKernel (classOf : I → C) (sign : I → ℝ) (i j : I) : ℝ :=
  if classOf i = classOf j then sign i * sign j else 0

/-- Embed a signed index as a multiple of its class's standard basis vector. -/
def signedBlockFeature (classOf : I → C) (sign : I → ℝ) (i : I) (a : C) : ℝ :=
  if a = classOf i then sign i else 0

omit [Fintype I] in
/-- Every signed block kernel has an explicit finite Gram representation. -/
theorem signedBlockKernel_eq_gram (classOf : I → C) (sign : I → ℝ) (i j : I) :
    signedBlockKernel classOf sign i j =
      finiteGramKernel (signedBlockFeature classOf sign) i j := by
  classical
  unfold finiteGramKernel
  by_cases h : classOf i = classOf j
  · rw [signedBlockKernel, ite_eq_left h]
    symm
    calc
      (∑ a, signedBlockFeature classOf sign i a *
          signedBlockFeature classOf sign j a) =
          signedBlockFeature classOf sign i (classOf i) *
            signedBlockFeature classOf sign j (classOf i) := by
        apply Finset.sum_eq_single (classOf i)
        · intro a ha hai
          simp [signedBlockFeature, hai]
        · intro hnot
          exact (hnot (Finset.mem_univ _)).elim
      _ = sign i * sign j := by
        simp [signedBlockFeature, h]
  · rw [signedBlockKernel, ite_eq_right h]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    by_cases hi : a = classOf i
    · have hj : a ≠ classOf j := by
        intro hj
        exact h (hi.symm.trans hj)
      simp [signedBlockFeature, hi, hj, h]
    · simp [signedBlockFeature, hi]

/-- In particular the signed equivalence-class moment matrix is positive.
The signs can be arbitrary real scalars; positivity does not need their
square-one property. -/
theorem signedBlock_quadratic_nonneg (classOf : I → C) (sign c : I → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * signedBlockKernel classOf sign i j := by
  simp_rw [signedBlockKernel_eq_gram]
  exact finiteGram_quadratic_nonneg (signedBlockFeature classOf sign) c

omit [Fintype I] [Fintype C] in
/-- Square-one signs give the normalization required of Boolean moments. -/
theorem signedBlock_diagonal_eq_one (classOf : I → C) (sign : I → ℝ)
    (hsign : ∀ i, (sign i) ^ 2 = 1) (i : I) :
    signedBlockKernel classOf sign i i = 1 := by
  simpa [signedBlockKernel, pow_two] using hsign i

end SignedBlocks

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
