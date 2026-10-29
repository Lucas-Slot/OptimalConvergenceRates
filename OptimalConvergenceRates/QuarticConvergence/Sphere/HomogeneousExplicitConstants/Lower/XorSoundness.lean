import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.QuarticNormalization
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.SoundLabels
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.BooleanFourier

/-!
# From finite Boolean label counting to real sign soundness

The labels constructed here work for any three position maps. No expansion
assumption is needed for soundness or global quartic nonnegativity.
-/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Foundation

open scoped BigOperators

def xorClausePrediction {E V : Type*} (i j k : E → V) (z : V → Bool) (e : E) : Bool :=
  Bool.xor (Bool.xor (z (i e)) (z (j e))) (z (k e))

theorem boolean_clause_square (a b c label : Bool) :
    (booleanSign a * booleanSign b - booleanSign label * booleanSign c) ^ 2 =
      if label ≠ Bool.xor (Bool.xor a b) c then (4 : ℝ) else 0 := by
  cases a <;> cases b <;> cases c <;> cases label <;> norm_num [booleanSign]

theorem clauseSquareSum_eq_four_hamming {E V : Type*} [Fintype E]
    (i j k : E → V) (labels : E → Bool) (z : V → Bool) :
    clauseSquareSum i j k (fun e ↦ booleanSign (labels e))
        (fun v ↦ booleanSign (z v)) 1 =
      4 * (hammingDist labels (xorClausePrediction i j k z) : ℝ) := by
  classical
  unfold clauseSquareSum
  simp only [mul_one, boolean_clause_square]
  calc
    (∑ e : E, if labels e ≠ Bool.xor (Bool.xor (z (i e)) (z (j e))) (z (k e))
        then (4 : ℝ) else 0) =
        ∑ e : E, 4 * (if labels e ≠ xorClausePrediction i j k z e then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      simp [xorClausePrediction, mul_ite]
    _ = 4 * (hammingDist labels (xorClausePrediction i j k z) : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_boole (fun e ↦ labels e ≠ xorClausePrediction i j k z e) Finset.univ

/-- Every real square-one assignment is represented by Boolean signs. -/
theorem exists_boolean_assignment_of_sq_eq_one {V : Type*} (σ : V → ℝ)
    (hσ : ∀ v, σ v ^ 2 = 1) :
    ∃ z : V → Bool, ∀ v, booleanSign (z v) = σ v := by
  classical
  refine ⟨fun v ↦ if σ v = 1 then false else true, ?_⟩
  intro v
  rcases sq_eq_one_iff.mp (hσ v) with h | h <;> norm_num [h, booleanSign]

/-- Finite counting provides labels with the real sign-soundness hypothesis
used in the quartic construction, for every indexed triple system. -/
theorem exists_real_sound_xor_labels (N : ℕ) (hN : 0 < N)
    (i j k : Fin (8 * N) → Fin N) :
    ∃ b : Fin (8 * N) → ℝ, (∀ e, |b e| = 1) ∧
      ∀ σ : Fin N → ℝ, (∀ v, σ v ^ 2 = 1) →
        (Fintype.card (Fin (8 * N)) : ℝ) ≤ clauseSquareSum i j k b σ 1 := by
  obtain ⟨labels, hlabels⟩ := exists_sound_labels N hN (xorClausePrediction i j k)
  refine ⟨fun e ↦ booleanSign (labels e), fun e ↦ booleanSign_abs _, ?_⟩
  intro σ hσ
  obtain ⟨z, hz⟩ := exists_boolean_assignment_of_sq_eq_one σ hσ
  have hrepresentation : (fun v ↦ booleanSign (z v)) = σ := funext hz
  rw [← hrepresentation, clauseSquareSum_eq_four_hamming]
  have hfar : ((2 * N : ℕ) : ℝ) ≤
      (hammingDist labels (xorClausePrediction i j k z) : ℝ) := by
    exact_mod_cast hlabels z
  simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] at hfar ⊢
  linarith

/-- Consequently every indexed triple system admits a globally nonnegative
quartic of the prescribed shape. This removes sign soundness as an assumption. -/
theorem exists_nonnegative_xor_quartic (N : ℕ) (hN : 0 < N)
    (i j k : Fin (8 * N) → Fin N) :
    ∃ b : Fin (8 * N) → ℝ, (∀ e, |b e| = 1) ∧
      ∀ x : Fin N → ℝ, ∀ t : ℝ, 0 ≤ xorQuartic i j k b x t := by
  obtain ⟨b, hb, hsound⟩ := exists_real_sound_xor_labels N hN i j k
  exact ⟨b, hb, fun x t ↦ xorQuartic_nonneg i j k b hb hsound x t⟩

/-- The normalized polynomial realization is globally nonnegative and bounded
by one on the full unit ball, with labels supplied by the checked counting proof. -/
theorem exists_bounded_nonnegative_normalized_xor_quartic (N : ℕ) (hN : 0 < N)
    (i j k : Fin (8 * N) → Fin N) :
    ∃ b : Fin (8 * N) → ℝ, (∀ e, |b e| = 1) ∧
      (∀ σ : Fin N → ℝ, (∀ v, σ v ^ 2 = 1) →
        (Fintype.card (Fin (8 * N)) : ℝ) ≤ clauseSquareSum i j k b σ 1) ∧
      (∀ w : Option (Fin N) → ℝ,
        0 ≤ MvPolynomial.eval w (normalizedQuarticPolynomial i j k b)) ∧
      (∀ w : Option (Fin N) → ℝ,
        coordinateSquareSum (fun v ↦ w (some v)) + w none ^ 2 ≤ 1 →
          MvPolynomial.eval w (normalizedQuarticPolynomial i j k b) ≤ 1) := by
  obtain ⟨b, hb, hsound⟩ := exists_real_sound_xor_labels N hN i j k
  have hm : 8 ≤ Fintype.card (Fin (8 * N)) := by
    simp only [Fintype.card_fin]
    omega
  exact ⟨b, hb, hsound, normalizedQuarticPolynomial_nonneg i j k b hb hsound,
    fun w hw ↦ normalizedQuarticPolynomial_le_one i j k b hb hm w hw⟩

end Foundation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
