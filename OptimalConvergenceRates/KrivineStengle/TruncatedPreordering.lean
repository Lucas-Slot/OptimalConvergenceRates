/-
  OptimalConvergenceRates/KrivineStengle/TruncatedPreordering.lean

  Degree-preserving operations for the repository's truncated preorderings.
-/
import OptimalConvergenceRates.KrivineStengle.Preordering

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.KrivineStengle

variable {n m : ℕ}

/-- A finite sum has bounded total degree when every summand does. -/
theorem totalDegree_sum_le_of_each {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin n) ℝ) (r : ℕ)
    (hf : ∀ i ∈ s, (f i).totalDegree ≤ r) :
    (∑ i ∈ s, f i).totalDegree ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (MvPolynomial.totalDegree_add _ _).trans
        (max_le (hf a (Finset.mem_insert_self a s))
          (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))

/-- Addition preserves an explicit preordering truncation bound. -/
theorem genPreordering_add
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r s : ℕ}
    (hp : p ∈ GenPreordering g r) (hq : q ∈ GenPreordering g s) :
    p + q ∈ GenPreordering g (max r s) := by
  obtain ⟨σ, hσ, hσdeg, hp⟩ := hp
  obtain ⟨τ, hτ, hτdeg, hq⟩ := hq
  refine ⟨fun I ↦ σ I + τ I, fun I ↦ IsSOS_add (hσ I) (hτ I), ?_, ?_⟩
  · intro I
    calc
      ((σ I + τ I) * generatorProduct g I).totalDegree =
          (σ I * generatorProduct g I +
            τ I * generatorProduct g I).totalDegree := by ring_nf
      _ ≤ max (σ I * generatorProduct g I).totalDegree
          (τ I * generatorProduct g I).totalDegree :=
        MvPolynomial.totalDegree_add _ _
      _ ≤ max r s := max_le_max (hσdeg I) (hτdeg I)
  · rw [hp, hq, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro I _
    ring

/-- The grouped coefficient in the product representation has the sum of
the two input degree bounds. -/
theorem productCoefficient_totalDegree_le
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (σ τ : Finset (Fin m) → MvPolynomial (Fin n) ℝ)
    {r s : ℕ}
    (hσdeg : ∀ I, (σ I * generatorProduct g I).totalDegree ≤ r)
    (hτdeg : ∀ I, (τ I * generatorProduct g I).totalDegree ≤ s)
    (K : Finset (Fin m)) :
    (productCoefficient g σ τ K * generatorProduct g K).totalDegree ≤ r + s := by
  classical
  rw [productCoefficient, Finset.sum_mul]
  apply totalDegree_sum_le_of_each
  intro IJ hIJ
  have hparity : subsetParity IJ.1 IJ.2 = K := (Finset.mem_filter.mp hIJ).2
  calc
    (((σ IJ.1 * τ IJ.2) *
          (∏ i ∈ IJ.1 ∩ IJ.2, g i) ^ 2) *
        generatorProduct g K).totalDegree =
        ((σ IJ.1 * generatorProduct g IJ.1) *
          (τ IJ.2 * generatorProduct g IJ.2)).totalDegree := by
      apply congrArg MvPolynomial.totalDegree
      rw [← hparity]
      calc
        (σ IJ.1 * τ IJ.2) *
              (∏ i ∈ IJ.1 ∩ IJ.2, g i) ^ 2 *
            generatorProduct g (subsetParity IJ.1 IJ.2) =
            (σ IJ.1 * τ IJ.2) *
              (generatorProduct g IJ.1 * generatorProduct g IJ.2) := by
          rw [generatorProduct_mul]; ring
        _ = (σ IJ.1 * generatorProduct g IJ.1) *
              (τ IJ.2 * generatorProduct g IJ.2) := by ring
    _ ≤ (σ IJ.1 * generatorProduct g IJ.1).totalDegree +
        (τ IJ.2 * generatorProduct g IJ.2).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ r + s := Nat.add_le_add (hσdeg IJ.1) (hτdeg IJ.2)

/-- Multiplication preserves an explicit preordering truncation bound. -/
theorem genPreordering_mul
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r s : ℕ}
    (hp : p ∈ GenPreordering g r) (hq : q ∈ GenPreordering g s) :
    p * q ∈ GenPreordering g (r + s) := by
  obtain ⟨σ, hσ, hσdeg, hp⟩ := hp
  obtain ⟨τ, hτ, hτdeg, hq⟩ := hq
  refine ⟨productCoefficient g σ τ,
    productCoefficient_isSOS g σ τ hσ hτ,
    productCoefficient_totalDegree_le σ τ hσdeg hτdeg, ?_⟩
  rw [hp, hq]
  simpa [generatorProduct] using productCoefficient_sum g σ τ

end OptimalConvergenceRates.KrivineStengle

end
