/-
  Walsh-sign orthogonality for the parity components on a product of circles.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.ParityReduction

open Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

variable {n : ℕ}

/-- The two signs attached to the two Boolean values. -/
def boolSign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem boolSign_false : boolSign false = 1 := rfl

@[simp] theorem boolSign_true : boolSign true = -1 := rfl

@[simp] theorem boolSign_sq (b : Bool) : boolSign b ^ 2 = 1 := by
  cases b <;> norm_num

/-- The Walsh character corresponding to a set of second coordinates. -/
def cubeSignCharacter (eps : Fin n → Bool) (J : Finset (Fin n)) : ℝ :=
  ∏ i : Fin n, if i ∈ J then boolSign (eps i) else 1

@[simp] theorem cubeSignCharacter_empty (eps : Fin n → Bool) :
    cubeSignCharacter eps ∅ = 1 := by
  simp [cubeSignCharacter]

/-- Multiplying two Walsh characters corresponds to symmetric difference.
The pointwise formulation is the one used in the orthogonality proof. -/
theorem cubeSignCharacter_mul (eps : Fin n → Bool)
    (J K : Finset (Fin n)) :
    cubeSignCharacter eps J * cubeSignCharacter eps K =
      ∏ i : Fin n,
        ((if i ∈ J then boolSign (eps i) else 1) *
          (if i ∈ K then boolSign (eps i) else 1)) := by
  simp only [cubeSignCharacter, Finset.prod_mul_distrib]

/-- Distinct Walsh characters are orthogonal under the uniform sum over signs. -/
theorem sum_cubeSignCharacter_mul (J K : Finset (Fin n)) :
    ∑ eps : Fin n → Bool, cubeSignCharacter eps J * cubeSignCharacter eps K =
      if J = K then (2 : ℝ) ^ n else 0 := by
  classical
  rw [show (∑ eps : Fin n → Bool,
      cubeSignCharacter eps J * cubeSignCharacter eps K) =
      ∏ i : Fin n, ∑ b : Bool,
        ((if i ∈ J then boolSign b else 1) *
          (if i ∈ K then boolSign b else 1)) by
    rw [Fintype.prod_sum]
    apply Fintype.sum_congr
    intro eps
    exact cubeSignCharacter_mul eps J K]
  by_cases hJK : J = K
  · subst K
    have hfactor (i : Fin n) :
        (∑ b : Bool,
          ((if i ∈ J then boolSign b else 1) *
            (if i ∈ J then boolSign b else 1))) = 2 := by
      by_cases hi : i ∈ J <;> simp [hi, boolSign]; norm_num
    rw [show (∏ i : Fin n, ∑ b : Bool,
        ((if i ∈ J then boolSign b else 1) *
          (if i ∈ J then boolSign b else 1))) =
        ∏ _i : Fin n, (2 : ℝ) by
      apply Finset.prod_congr rfl
      intro i _
      exact hfactor i]
    simp
  · rw [if_neg hJK]
    have hex : ∃ i : Fin n, (i ∈ J) ≠ (i ∈ K) := by
      by_contra h
      apply hJK
      ext i
      exact Iff.of_eq (not_ne_iff.mp (not_exists.mp h i))
    obtain ⟨i, hi⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rcases em (i ∈ J) with hiJ | hiJ <;>
      rcases em (i ∈ K) with hiK | hiK
    · exact (hi (propext ⟨fun _ ↦ hiK, fun _ ↦ hiJ⟩)).elim
    · simp [hiJ, hiK, boolSign]
    · simp [hiJ, hiK, boolSign]
    · exact (hi (propext ⟨fun h ↦ (hiJ h).elim, fun h ↦ (hiK h).elim⟩)).elim

/-- Parseval's identity for the finite Walsh transform, without normalization. -/
theorem sum_sq_walshTransform (a : Finset (Fin n) → ℝ) :
    ∑ eps : Fin n → Bool,
        (∑ J : Finset (Fin n), cubeSignCharacter eps J * a J) ^ 2 =
      (2 : ℝ) ^ n * ∑ J : Finset (Fin n), (a J) ^ 2 := by
  classical
  calc
    ∑ eps : Fin n → Bool,
        (∑ J : Finset (Fin n), cubeSignCharacter eps J * a J) ^ 2 =
        ∑ eps : Fin n → Bool,
          ∑ J : Finset (Fin n), ∑ K : Finset (Fin n),
            (cubeSignCharacter eps J * a J) *
              (cubeSignCharacter eps K * a K) := by
      apply Fintype.sum_congr
      intro eps
      rw [pow_two, Fintype.sum_mul_sum]
    _ = ∑ J : Finset (Fin n), ∑ K : Finset (Fin n),
          (∑ eps : Fin n → Bool,
            cubeSignCharacter eps J * cubeSignCharacter eps K) *
              (a J * a K) := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro J
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro K
      rw [Finset.sum_mul]
      apply Fintype.sum_congr
      intro eps
      ring
    _ = ∑ J : Finset (Fin n), ∑ K : Finset (Fin n),
          (if J = K then (2 : ℝ) ^ n else 0) * (a J * a K) := by
      simp_rw [sum_cubeSignCharacter_mul]
    _ = (2 : ℝ) ^ n * ∑ J : Finset (Fin n), (a J) ^ 2 := by
      simp [pow_two, Finset.mul_sum]

end QuarticConvergence
end OptimalConvergenceRates

end
