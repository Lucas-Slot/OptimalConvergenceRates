import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic
/-!
# Sound labels for an arbitrary Boolean prediction map

The main coding statement applies to every map from `N` Boolean variables
to `8*N` Boolean predictions. Consequently it applies to any fixed triple
system, with no expansion or independence assumptions on that system.
The proof uses an exact finite weighted enumeration and a finite sum bound.
-/

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Foundation

open scoped BigOperators

section WeightedEnumeration

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- A Hamming weight is a product of one factor per coordinate. -/
theorem hamming_weight_eq_prod (q : ℚ) (b x : I → Bool) :
    q ^ hammingDist b x = ∏ i, if b i ≠ x i then q else 1 := by
  symm
  simp [Finset.prod_ite, hammingDist]

/-- Exact enumeration of the weighted Boolean cube around any center. -/
theorem sum_hamming_weight (q : ℚ) (x : I → Bool) :
    (∑ b : I → Bool, q ^ hammingDist b x) =
      (1 + q) ^ Fintype.card I := by
  classical
  have hbit (i : I) :
      (∑ b : Bool, if b ≠ x i then q else 1) = 1 + q := by
    cases hx : x i <;> simp [Fintype.sum_bool, hx, add_comm]
  calc
    (∑ b : I → Bool, q ^ hammingDist b x) =
        ∑ b : I → Bool, ∏ i, if b i ≠ x i then q else 1 := by
      apply Finset.sum_congr rfl
      intro b hb
      exact hamming_weight_eq_prod q b x
    _ = ∏ i, ∑ b : Bool, if b ≠ x i then q else 1 := by
      exact (Fintype.prod_sum fun i (b : Bool) ↦ if b ≠ x i then q else 1).symm
    _ = (1 + q) ^ Fintype.card I := by
      simp_rw [hbit]
      simp

end WeightedEnumeration

section WeightedAvoidance

variable {I Z : Type*} [Fintype I] [DecidableEq I] [Fintype Z]

/-- A strict total weight budget leaves a label vector outside every
Hamming ball of radius `t` centered at one of the predictions.
This is a finite weighted counting argument, rather than a probabilistic
or independence hypothesis. -/
theorem exists_label_far_of_weight_budget (prediction : Z → I → Bool)
    (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (t : ℕ)
    (budget : (Fintype.card Z : ℚ) * (1 + q) ^ Fintype.card I <
      (Fintype.card (I → Bool) : ℚ) * q ^ t) :
    ∃ b : I → Bool, ∀ z : Z, t < hammingDist b (prediction z) := by
  classical
  by_contra havoid
  push_neg at havoid
  have hlower : (Fintype.card (I → Bool) : ℚ) * q ^ t ≤
      ∑ b : I → Bool, ∑ z : Z, q ^ hammingDist b (prediction z) := by
    calc
      (Fintype.card (I → Bool) : ℚ) * q ^ t =
          ∑ _b : I → Bool, q ^ t := by
        simp
      _ ≤ ∑ b : I → Bool, ∑ z : Z, q ^ hammingDist b (prediction z) := by
        apply Finset.sum_le_sum
        intro b hb
        obtain ⟨z, hz⟩ := havoid b
        calc
          q ^ t ≤ q ^ hammingDist b (prediction z) :=
            pow_le_pow_of_le_one hq0 hq1 hz
          _ ≤ ∑ z : Z, q ^ hammingDist b (prediction z) := by
            exact Finset.single_le_sum
              (fun z hz ↦ pow_nonneg hq0 _) (Finset.mem_univ z)
  have htotal :
      (∑ b : I → Bool, ∑ z : Z, q ^ hammingDist b (prediction z)) =
        (Fintype.card Z : ℚ) * (1 + q) ^ Fintype.card I := by
    calc
      (∑ b : I → Bool, ∑ z : Z, q ^ hammingDist b (prediction z)) =
          ∑ z : Z, ∑ b : I → Bool, q ^ hammingDist b (prediction z) :=
        Finset.sum_comm
      _ = ∑ _z : Z, (1 + q) ^ Fintype.card I := by
        simp_rw [sum_hamming_weight]
      _ = (Fintype.card Z : ℚ) * (1 + q) ^ Fintype.card I := by
        simp
  rw [htotal] at hlower
  exact (not_le_of_gt budget) hlower

end WeightedAvoidance

/-- There are labels violating more than one quarter of `8*N` arbitrary
Boolean predictions, simultaneously for all `2^N` assignments. -/
theorem exists_sound_labels_strict (N : ℕ) (hN : 0 < N)
    (prediction : (Fin N → Bool) → Fin (8 * N) → Bool) :
    ∃ b : Fin (8 * N) → Bool,
      ∀ z : Fin N → Bool, 2 * N < hammingDist b (prediction z) := by
  have hbase : (2 : ℚ) * (3 / 2 : ℚ) ^ 8 <
      (2 : ℚ) ^ 8 * (1 / 2 : ℚ) ^ 2 := by
    norm_num
  have hp := pow_lt_pow_left₀ hbase (by norm_num) (Nat.ne_of_gt hN)
  have hbudget : (2 : ℚ) ^ N * (1 + (1 / 2 : ℚ)) ^ (8 * N) <
      (2 : ℚ) ^ (8 * N) * (1 / 2 : ℚ) ^ (2 * N) := by
    convert hp using 1 <;> norm_num [mul_pow, pow_mul] <;>
      rw [← mul_pow] <;> norm_num
  apply exists_label_far_of_weight_budget prediction (1 / 2 : ℚ)
    (by norm_num) (by norm_num) (2 * N)
  simpa [Fintype.card_fun] using hbudget

/-- The weak soundness convention used in the quartic construction. -/
theorem exists_sound_labels (N : ℕ) (hN : 0 < N)
    (prediction : (Fin N → Bool) → Fin (8 * N) → Bool) :
    ∃ b : Fin (8 * N) → Bool,
      ∀ z : Fin N → Bool, 2 * N ≤ hammingDist b (prediction z) := by
  obtain ⟨b, hb⟩ := exists_sound_labels_strict N hN prediction
  exact ⟨b, fun z ↦ (hb z).le⟩

end Foundation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
