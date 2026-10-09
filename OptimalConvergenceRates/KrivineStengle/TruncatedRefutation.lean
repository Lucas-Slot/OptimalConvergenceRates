/-
  OptimalConvergenceRates/KrivineStengle/TruncatedRefutation.lean

  A fixed truncation order for the perturbation refutation attached to a
  Krivine--Stengle witness.
-/
import OptimalConvergenceRates.KrivineStengle.Refutation
import OptimalConvergenceRates.KrivineStengle.TruncatedPreordering

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.KrivineStengle

variable {n m : ℕ}

/-- Extend preordering coefficients along `Fin.castSucc`, assigning zero to
all genuinely new generator subsets. -/
def liftPreorderingCoefficient
    (σ : Finset (Fin m) → MvPolynomial (Fin n) ℝ)
    (J : Finset (Fin (m + 1))) : MvPolynomial (Fin n) ℝ :=
  ∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
    if I.map Fin.castSuccEmb = J then σ I else 0

theorem liftPreorderingCoefficient_isSOS
    (σ : Finset (Fin m) → MvPolynomial (Fin n) ℝ)
    (hσ : ∀ I, IsSOS (σ I)) (J : Finset (Fin (m + 1))) :
    IsSOS (liftPreorderingCoefficient σ J) := by
  classical
  apply IsSOS_sum_finset
  intro I _
  by_cases hI : I.map Fin.castSuccEmb = J
  · simp [hI, hσ I]
  · simp [hI, IsSOS_zero]

@[simp]
theorem generatorProduct_appendGenerator_map_castSucc
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (h : MvPolynomial (Fin n) ℝ) (I : Finset (Fin m)) :
    generatorProduct (appendGenerator g h) (I.map Fin.castSuccEmb) =
      generatorProduct g I := by
  classical
  simp [generatorProduct]

theorem liftPreorderingCoefficient_totalDegree_le
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (h : MvPolynomial (Fin n) ℝ)
    (σ : Finset (Fin m) → MvPolynomial (Fin n) ℝ) {r : ℕ}
    (hσdeg : ∀ I, (σ I * generatorProduct g I).totalDegree ≤ r)
    (J : Finset (Fin (m + 1))) :
    (liftPreorderingCoefficient σ J *
      generatorProduct (appendGenerator g h) J).totalDegree ≤ r := by
  classical
  rw [liftPreorderingCoefficient, Finset.sum_mul]
  apply totalDegree_sum_le_of_each
  intro I _
  by_cases hIJ : I.map Fin.castSuccEmb = J
  · subst J
    simpa using hσdeg I
  · simp [hIJ]

theorem liftPreorderingCoefficient_sum
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (h : MvPolynomial (Fin n) ℝ)
    (σ : Finset (Fin m) → MvPolynomial (Fin n) ℝ) :
    (∑ J ∈ (Finset.univ : Finset (Fin (m + 1))).powerset,
        liftPreorderingCoefficient σ J *
          generatorProduct (appendGenerator g h) J) =
      ∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
        σ I * generatorProduct g I := by
  classical
  simp_rw [liftPreorderingCoefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  rw [Finset.sum_eq_single (I.map Fin.castSuccEmb)]
  · simp
  · intro J _ hJI
    simp [hJI.symm]
  · simp

/-- A truncated certificate over `g` remains at the same order after one
generator is appended. -/
theorem genPreordering_lift_appendGenerator
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p h : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hp : p ∈ GenPreordering g r) :
    p ∈ GenPreordering (appendGenerator g h) r := by
  obtain ⟨σ, hσ, hσdeg, hp⟩ := hp
  refine ⟨liftPreorderingCoefficient σ,
    liftPreorderingCoefficient_isSOS σ hσ,
    liftPreorderingCoefficient_totalDegree_le g h σ hσdeg, ?_⟩
  rw [hp]
  simpa [generatorProduct] using (liftPreorderingCoefficient_sum g h σ).symm

end OptimalConvergenceRates.KrivineStengle

end
