/-
  OptimalConvergenceRates/KrivineStengle/BoundedRefutation.lean

  Uniform truncation bounds for the perturbation refutation attached to a
  fixed Krivine--Stengle witness.
-/
import OptimalConvergenceRates.KrivineStengle.TruncatedRefutation

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.KrivineStengle

variable {n m : ℕ}

/-- A nonnegative constant has a degree-zero truncated certificate. -/
theorem genPreordering_C_nonneg
    (g : Fin m → MvPolynomial (Fin n) ℝ) {c : ℝ} (hc : 0 ≤ c) :
    C c ∈ GenPreordering g 0 := by
  classical
  refine ⟨Function.update 0 ∅ (C c), ?_, ?_, ?_⟩
  · intro I
    by_cases hI : I = ∅
    · subst I
      simpa using IsSOS_C_nonneg c hc
    · simp [Function.update_of_ne hI, IsSOS_zero]
  · intro I
    by_cases hI : I = ∅
    · subst I
      simp [MvPolynomial.totalDegree_C]
    · simp [Function.update_of_ne hI]
  · rw [Finset.sum_eq_single ∅]
    · simp
    · intro I _ hI
      simp [Function.update_of_ne hI]
    · simp

/-- Zero has a degree-zero truncated certificate. -/
theorem genPreordering_zero (g : Fin m → MvPolynomial (Fin n) ℝ) :
    0 ∈ GenPreordering g 0 := by
  simpa using genPreordering_C_nonneg g (c := 0) (le_refl 0)

/-- One has a degree-zero truncated certificate. -/
theorem genPreordering_one (g : Fin m → MvPolynomial (Fin n) ℝ) :
    1 ∈ GenPreordering g 0 := by
  simpa using genPreordering_C_nonneg g (c := 1) (by norm_num)

/-- A generator has a certificate at its own total degree. -/
theorem genPreordering_generator
    (g : Fin m → MvPolynomial (Fin n) ℝ) (i : Fin m) :
    g i ∈ GenPreordering g (g i).totalDegree := by
  classical
  refine ⟨Function.update 0 {i} 1, ?_, ?_, ?_⟩
  · intro I
    by_cases hI : I = {i}
    · subst I
      simpa using IsSOS_sq (1 : MvPolynomial (Fin n) ℝ)
    · simp [Function.update_of_ne hI, IsSOS_zero]
  · intro I
    by_cases hI : I = {i}
    · subst I
      simp
    · simp [Function.update_of_ne hI]
  · rw [Finset.sum_eq_single {i}]
    · simp
    · intro I _ hI
      simp [Function.update_of_ne hI]
    · simp

/-- Powers multiply an explicit truncation order by the exponent. -/
theorem genPreordering_pow
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hp : p ∈ GenPreordering g r) (N : ℕ) :
    p ^ N ∈ GenPreordering g (N * r) := by
  induction N with
  | zero => simpa using genPreordering_one g
  | succ N ih =>
      simpa [pow_succ, Nat.succ_mul] using genPreordering_mul ih hp

/-- A degree-controlled subtraction-free recurrence for a power difference.
The constant term is assigned order zero, so the bound is `N * d`. -/
theorem genPreordering_add_pow_sub_pow
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {c h : MvPolynomial (Fin n) ℝ} {d : ℕ}
    (hc : c ∈ GenPreordering g 0) (hh : h ∈ GenPreordering g d)
    (N : ℕ) :
    (c + h) ^ N - c ^ N ∈ GenPreordering g (N * d) := by
  induction N with
  | zero => simpa using genPreordering_zero g
  | succ N ih =>
      have hch : c + h ∈ GenPreordering g d := by
        simpa using genPreordering_add hc hh
      have hleft := genPreordering_mul hch ih
      have hcpow : c ^ N ∈ GenPreordering g 0 := by
        simpa using genPreordering_pow hc N
      have hright := genPreordering_mul hh hcpow
      have hsum := genPreordering_add hleft hright
      have hbound : max (d + N * d) (d + 0) ≤ (N + 1) * d := by
        apply max_le
        · simp [Nat.add_mul, Nat.add_comm]
        · simp [Nat.add_mul, Nat.add_comm]
      have hmem := GenPreordering_mono hbound hsum
      convert hmem using 1; ring

/-- The perturbation generator has degree at most the degree of the
polynomial being perturbed. -/
theorem perturbationGenerator_totalDegree_le
    (p : MvPolynomial (Fin n) ℝ) (c : ℝ) :
    (perturbationGenerator p c).totalDegree ≤ p.totalDegree := by
  simpa [perturbationGenerator] using
    (MvPolynomial.totalDegree_sub_C_le (-p) c)

end OptimalConvergenceRates.KrivineStengle

end
