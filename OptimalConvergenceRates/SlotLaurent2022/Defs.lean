/-
  OptimalConvergenceRates/SlotLaurent2022/Defs.lean

  Constants for the Slot-Laurent 2022 Schmuedgen convergence and membership bounds.
-/
import OptimalConvergenceRates.Chebyshev.Chebyshev
import Mathlib.Analysis.Real.Pi.Bounds

open MvPolynomial Finset Real

noncomputable section

namespace OptimalConvergenceRates

variable {n : ℕ}

/-! ## The constant C(n,d)

The constant C(n,d) from Theorem 2 of Slot-Laurent 2022:
  C(n,d) = |ℕ^n_d| · max_{κ ∈ ℕ^n_d} 2^{w(κ)/2} · 2nπ²d²
where ℕ^n_d is the set of multi-indices of degree ≤ d and w(κ) is the
Hamming weight (number of nonzero entries).

Upper bounds:
  C(n,d) ≤ 2π²d²n · 2^{n/2} · (d+1)^n   (fixed n)
  C(n,d) ≤ 2π²d²n · 2^{d/2} · (n+1)^d   (fixed d) -/

/-- C(n,d) := |ℕ^n_d| · max_{κ ∈ ℕ^n_d} 2^{w(κ)/2} · 2nπ²d² -/
noncomputable def constC (n d : ℕ) : ℝ :=
  (multiIndices n d).card *
  (Finset.sup' (multiIndices n d)
    ⟨0, multiIndices_mem_iff.mpr ⟨by simp [multiDegree], fun _ => Nat.zero_le _⟩⟩
    (fun κ => (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2))) *
  (2 * n * Real.pi ^ 2 * d ^ 2)

theorem constC_pos (n d : ℕ) (hn : 0 < n) (hd : 0 < d) : 0 < constC n d := by
  unfold constC
  have hne : (multiIndices n d).Nonempty :=
    ⟨0, multiIndices_mem_iff.mpr ⟨by simp [multiDegree], fun _ => Nat.zero_le _⟩⟩
  apply mul_pos (mul_pos _ _) _
  · exact Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
  · have h0 : (0 : Fin n → ℕ) ∈ multiIndices n d :=
      multiIndices_mem_iff.mpr ⟨by simp [multiDegree], fun _ => Nat.zero_le _⟩
    calc (0 : ℝ) < (2 : ℝ) ^ ((hammingWeight (0 : Fin n → ℕ) : ℝ) / 2) := by positivity
      _ ≤ Finset.sup' (multiIndices n d) hne
            (fun κ => (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2)) :=
          Finset.le_sup' (fun κ => (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2)) h0
  · positivity

/-! ## Bounds on C(n,d) -/

/-- C(n,d) ≤ 2π²d²n · 2^{n/2} · (d+1)^n -/
theorem constC_bound_fixed_n (n d : ℕ) :
    constC n d ≤ 2 * Real.pi ^ 2 * d ^ 2 * n *
      (2 : ℝ) ^ ((n : ℝ) / 2) * (d + 1) ^ n := by
  unfold constC
  have hne : (multiIndices n d).Nonempty :=
    ⟨0, multiIndices_mem_iff.mpr ⟨by simp [multiDegree], fun _ => Nat.zero_le _⟩⟩
  have hcard : ((multiIndices n d).card : ℝ) ≤ ((d + 1) ^ n : ℝ) := by
    exact_mod_cast multiIndices_card_le_pow n d
  have hsup : Finset.sup' (multiIndices n d) hne
      (fun κ => (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2)) ≤
      (2 : ℝ) ^ ((n : ℝ) / 2) := by
    apply Finset.sup'_le
    intro κ hκ
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) < 2).le
    exact_mod_cast hammingWeight_le_n κ
  have hthird_nonneg : 0 ≤ 2 * (n : ℝ) * Real.pi ^ 2 * (d : ℝ) ^ 2 := by positivity
  have hsup_nonneg : (0 : ℝ) ≤ Finset.sup' (multiIndices n d) hne
      (fun κ => (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2)) := by
    have h0 : (0 : Fin n → ℕ) ∈ multiIndices n d :=
      multiIndices_mem_iff.mpr ⟨by simp [multiDegree], fun _ => Nat.zero_le _⟩
    calc (0 : ℝ) ≤ (2 : ℝ) ^ ((hammingWeight (0 : Fin n → ℕ) : ℝ) / 2) := by positivity
      _ ≤ _ := Finset.le_sup' (fun κ => (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2)) h0
  calc (multiIndices n d).card *
      Finset.sup' (multiIndices n d) hne
        (fun κ => (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2)) *
      (2 * ↑n * Real.pi ^ 2 * ↑d ^ 2)
      ≤ ((d + 1) ^ n : ℝ) *
        ((2 : ℝ) ^ ((n : ℝ) / 2)) *
        (2 * ↑n * Real.pi ^ 2 * ↑d ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ hthird_nonneg
          exact mul_le_mul hcard hsup hsup_nonneg (by positivity)
    _ = 2 * Real.pi ^ 2 * ↑d ^ 2 * ↑n *
        (2 : ℝ) ^ ((↑n : ℝ) / 2) * (↑d + 1) ^ n := by
          ring

/-- C(n,d) ≤ 2π²d²n · 2^{d/2} · (n+1)^d -/
theorem constC_bound_fixed_d (n d : ℕ) :
    constC n d ≤ 2 * Real.pi ^ 2 * d ^ 2 * n *
      (2 : ℝ) ^ ((d : ℝ) / 2) * (n + 1) ^ d := by
  unfold constC
  have hne : (multiIndices n d).Nonempty :=
    ⟨0, multiIndices_mem_iff.mpr ⟨by simp [multiDegree], fun _ => Nat.zero_le _⟩⟩
  have hcard : ((multiIndices n d).card : ℝ) ≤ ((n + 1) ^ d : ℝ) := by
    exact_mod_cast multiIndices_card_le_pow' n d
  have hsup : Finset.sup' (multiIndices n d) hne
      (fun κ => (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2)) ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) := by
    apply Finset.sup'_le
    intro κ hκ
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) < 2).le
    have := hammingWeight_le_of_mem hκ
    exact_mod_cast le_trans this (min_le_right n d)
  have hthird_nonneg : 0 ≤ 2 * (n : ℝ) * Real.pi ^ 2 * (d : ℝ) ^ 2 := by positivity
  have hsup_nonneg : (0 : ℝ) ≤ Finset.sup' (multiIndices n d) hne
      (fun κ => (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2)) := by
    have h0 : (0 : Fin n → ℕ) ∈ multiIndices n d :=
      multiIndices_mem_iff.mpr ⟨by simp [multiDegree], fun _ => Nat.zero_le _⟩
    calc (0 : ℝ) ≤ (2 : ℝ) ^ ((hammingWeight (0 : Fin n → ℕ) : ℝ) / 2) := by positivity
      _ ≤ _ := Finset.le_sup' (fun κ => (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2)) h0
  calc (multiIndices n d).card *
      Finset.sup' (multiIndices n d) hne
        (fun κ => (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2)) *
      (2 * ↑n * Real.pi ^ 2 * ↑d ^ 2)
      ≤ ((n + 1) ^ d : ℝ) *
        ((2 : ℝ) ^ ((d : ℝ) / 2)) *
        (2 * ↑n * Real.pi ^ 2 * ↑d ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ hthird_nonneg
          exact mul_le_mul hcard hsup hsup_nonneg (by positivity)
    _ = 2 * Real.pi ^ 2 * ↑d ^ 2 * ↑n *
        (2 : ℝ) ^ ((↑d : ℝ) / 2) * (↑n + 1) ^ d := by
          ring

end OptimalConvergenceRates

end
