/-
  A finite normalized diagonal-dominance criterion for nonnegative
  quadratic forms.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section

open Finset

namespace OptimalConvergenceRates.GeneralArchimedean

set_option maxHeartbeats 400000 in
-- Normalizing the doubly indexed quadratic sum requires extra elaboration time.
/-- Quantitative lower bound for a normalized symmetric matrix in terms of
an off-diagonal row bound. -/
theorem quadraticForm_lower_of_normalized_diagonal_dominance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → ℝ)
    (hdiag : ∀ i, K i i = 1)
    (hsymm : ∀ i j, K i j = K j i)
    (θ : ℝ)
    (hrow : ∀ i, (∑ j : ι, if i = j then 0 else |K i j|) ≤ θ)
    (x : ι → ℝ) :
    (1 - θ) * (∑ i : ι, x i ^ 2) ≤ ∑ i : ι, ∑ j : ι, x i * K i j * x j := by
  let S : ℝ := ∑ i : ι, x i ^ 2
  let O : ℝ :=
    ∑ i : ι, ∑ j : ι, if i = j then 0 else x i * K i j * x j
  let A : ℝ :=
    ∑ i : ι, ∑ j : ι, if i = j then 0 else |K i j| * x i ^ 2
  let B : ℝ :=
    ∑ i : ι, ∑ j : ι, if i = j then 0 else |K i j| * x j ^ 2
  have hdecomp :
      (∑ i : ι, ∑ j : ι, x i * K i j * x j) = S + O := by
    calc
      (∑ i : ι, ∑ j : ι, x i * K i j * x j) =
          ∑ i : ι, ∑ j : ι,
            ((if i = j then x i ^ 2 else 0) +
              (if i = j then 0 else x i * K i j * x j)) := by
            apply Finset.sum_congr rfl
            intro i _hi
            apply Finset.sum_congr rfl
            intro j _hj
            by_cases hij : i = j
            · subst j
              simp [hdiag]
              ring
            · simp [hij]
      _ = S + O := by
        simp_rw [Finset.sum_add_distrib]
        simp [S, O]
  have hterm (i j : ι) :
      -(|K i j| * x i ^ 2 + |K i j| * x j ^ 2) / 2 ≤
        x i * K i j * x j := by
    have hxy : 2 * |x i * x j| ≤ x i ^ 2 + x j ^ 2 := by
      rw [abs_mul]
      have h := two_mul_le_add_sq |x i| |x j|
      rw [sq_abs, sq_abs] at h
      nlinarith
    have hscaled :
        2 * (|K i j| * |x i * x j|) ≤
          |K i j| * x i ^ 2 + |K i j| * x j ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hxy (abs_nonneg (K i j))
      nlinarith
    have habs :
        |x i * K i j * x j| = |K i j| * |x i * x j| := by
      rw [abs_mul, abs_mul]
      rw [abs_mul]
      ring
    have hneg := neg_abs_le (x i * K i j * x j)
    rw [habs] at hneg
    nlinarith
  have hoff : -(A + B) / 2 ≤ O := by
    dsimp [A, B, O]
    calc
      -((∑ i : ι, ∑ j : ι,
            if i = j then 0 else |K i j| * x i ^ 2) +
          (∑ i : ι, ∑ j : ι,
            if i = j then 0 else |K i j| * x j ^ 2)) / 2 =
          ∑ i : ι, ∑ j : ι,
            if i = j then 0
            else -(|K i j| * x i ^ 2 + |K i j| * x j ^ 2) / 2 := by
              let a : ι → ι → ℝ :=
                fun i j ↦ if i = j then 0 else |K i j| * x i ^ 2
              let b : ι → ι → ℝ :=
                fun i j ↦ if i = j then 0 else |K i j| * x j ^ 2
              calc
                -((∑ i : ι, ∑ j : ι, a i j) +
                    (∑ i : ι, ∑ j : ι, b i j)) / 2 =
                    ((∑ i : ι, ∑ j : ι, a i j) +
                      (∑ i : ι, ∑ j : ι, b i j)) * (-1 / 2) := by ring
                _ = (∑ i : ι, ∑ j : ι, a i j) * (-1 / 2) +
                    (∑ i : ι, ∑ j : ι, b i j) * (-1 / 2) := by ring
                _ = (∑ i : ι, ∑ j : ι, a i j * (-1 / 2)) +
                    (∑ i : ι, ∑ j : ι, b i j * (-1 / 2)) := by
                      simp_rw [Finset.sum_mul]
                _ = ∑ i : ι, ∑ j : ι,
                    (a i j * (-1 / 2) + b i j * (-1 / 2)) := by
                      simp_rw [Finset.sum_add_distrib]
                _ = ∑ i : ι, ∑ j : ι,
                    if i = j then 0
                    else -(|K i j| * x i ^ 2 + |K i j| * x j ^ 2) / 2 := by
                      apply Finset.sum_congr rfl
                      intro i _hi
                      apply Finset.sum_congr rfl
                      intro j _hj
                      by_cases hij : i = j <;> simp [a, b, hij] <;> ring
      _ ≤ ∑ i : ι, ∑ j : ι,
          if i = j then 0 else x i * K i j * x j := by
            apply Finset.sum_le_sum
            intro i _hi
            apply Finset.sum_le_sum
            intro j _hj
            by_cases hij : i = j
            · simp [hij]
            · simpa [hij] using hterm i j
  have hA : A ≤ θ * S := by
    dsimp [A, S]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _hi
    calc
      (∑ j : ι, if i = j then 0 else |K i j| * x i ^ 2) =
          x i ^ 2 * ∑ j : ι, if i = j then 0 else |K i j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            by_cases hij : i = j <;> simp [hij, mul_comm]
      _ ≤ x i ^ 2 * θ :=
        mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg (x i))
      _ = θ * x i ^ 2 := mul_comm _ _
  have hB : B ≤ θ * S := by
    dsimp [B, S]
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _hj
    calc
      (∑ i : ι, if i = j then 0 else |K i j| * x j ^ 2) =
          x j ^ 2 * ∑ i : ι, if j = i then 0 else |K j i| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            by_cases hij : i = j
            · subst j
              simp
            · have hji : j ≠ i := Ne.symm hij
              simp [hij, hji, hsymm, mul_comm]
      _ ≤ x j ^ 2 * θ :=
        mul_le_mul_of_nonneg_left (hrow j) (sq_nonneg (x j))
      _ = θ * x j ^ 2 := mul_comm _ _
  rw [hdecomp]
  have hAB : A + B ≤ 2 * θ * S := by linarith
  have hO : -θ * S ≤ O := by linarith

  change (1 - θ) * S ≤ S + O
  linarith
/-- A symmetric normalized matrix with absolute off-diagonal row sums at
most one has a nonnegative quadratic form. -/
theorem quadraticForm_nonneg_of_normalized_diagonal_dominance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → ℝ)
    (hdiag : ∀ i, K i i = 1)
    (hsymm : ∀ i j, K i j = K j i)
    (hrow : ∀ i, (∑ j : ι, if i = j then 0 else |K i j|) ≤ 1)
    (x : ι → ℝ) :
    0 ≤ ∑ i : ι, ∑ j : ι, x i * K i j * x j := by
  have h := quadraticForm_lower_of_normalized_diagonal_dominance
    K hdiag hsymm 1 hrow x
  simpa using h

/-- Matching quantitative upper estimate. -/
theorem quadraticForm_upper_of_normalized_diagonal_dominance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → ℝ)
    (hdiag : ∀ i, K i i = 1)
    (hsymm : ∀ i j, K i j = K j i)
    (θ : ℝ)
    (hrow : ∀ i, (∑ j : ι, if i = j then 0 else |K i j|) ≤ θ)
    (x : ι → ℝ) :
    (∑ i : ι, ∑ j : ι, x i * K i j * x j) ≤
      (1 + θ) * (∑ i : ι, x i ^ 2) := by
  let L : ι → ι → ℝ := fun i j ↦ if i = j then 1 else -K i j
  have hLdiag (i : ι) : L i i = 1 := by simp [L]
  have hLsymm (i j : ι) : L i j = L j i := by
    by_cases hij : i = j
    · subst j
      simp [L]
    · have hji : j ≠ i := Ne.symm hij
      simp [L, hij, hji, hsymm]
  have hLrow (i : ι) :
      (∑ j : ι, if i = j then 0 else |L i j|) ≤ θ := by
    calc
      _ = ∑ j : ι, if i = j then 0 else |K i j| := by
        apply Finset.sum_congr rfl
        intro j _hj
        by_cases hij : i = j
        · simp [hij]
        · simp [L, hij]
      _ ≤ θ := hrow i
  have hlower := quadraticForm_lower_of_normalized_diagonal_dominance
    L hLdiag hLsymm θ hLrow x
  have hadd :
      (∑ i : ι, ∑ j : ι, x i * K i j * x j) +
          (∑ i : ι, ∑ j : ι, x i * L i j * x j) =
        2 * ∑ i : ι, x i ^ 2 := by
    calc
      _ = ∑ i : ι, ∑ j : ι,
          (x i * K i j * x j + x i * L i j * x j) := by
            simp_rw [Finset.sum_add_distrib]
      _ = ∑ i : ι, ∑ j : ι, if i = j then 2 * x i ^ 2 else 0 := by
            apply Finset.sum_congr rfl
            intro i _hi
            apply Finset.sum_congr rfl
            intro j _hj
            by_cases hij : i = j
            · subst j
              simp [L, hdiag]
              ring
            · simp [L, hij]
      _ = 2 * ∑ i : ι, x i ^ 2 := by simp [Finset.mul_sum]
  linarith

end OptimalConvergenceRates.GeneralArchimedean

end
