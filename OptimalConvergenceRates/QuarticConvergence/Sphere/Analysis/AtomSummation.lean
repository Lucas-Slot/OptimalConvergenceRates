/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Analysis/AtomSummation.lean

  Finite overlap and dyadic-scale summation for the retained-root argument.
-/
import Mathlib.Algebra.Order.Field.GeomSum
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FiniteErrorAssembly

open Finset
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- If at most `B` entries of `a` are active and every active product is at
most `T`, then the whole cross-error sum is at most `B * T`. This is the
finite-overlap step in the cross-term estimate. -/
theorem sum_abs_mul_le_of_active_card {N : ℕ}
    (a e : Fin N → ℝ) (B : ℕ) (T : ℝ)
    (hT : 0 ≤ T)
    (hcard : (Finset.univ.filter fun i => a i ≠ 0).card ≤ B)
    (hterm : ∀ i, a i ≠ 0 → |a i * e i| ≤ T) :
    ∑ i, |a i * e i| ≤ (B : ℝ) * T := by
  classical
  let s : Finset (Fin N) := Finset.univ.filter fun i => a i ≠ 0
  have hsum :
      ∑ i, |a i * e i| = ∑ i ∈ s, |a i * e i| := by
    symm
    apply Finset.sum_subset (by
      intro i _
      exact Finset.mem_univ i)
    intro i _ hnot
    have hai : a i = 0 := by
      by_contra hne
      exact hnot (by
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hne)
    simp [hai]
  rw [hsum]
  calc
    ∑ i ∈ s, |a i * e i| ≤ ∑ _i ∈ s, T := by
      apply Finset.sum_le_sum
      intro i hi
      apply hterm i
      simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    _ = (s.card : ℝ) * T := by simp
    _ ≤ (B : ℝ) * T := by
      exact mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (by simpa [s] using hcard)) hT

/-- Summing squared errors over a finite dyadic scale partition costs only
the geometric factor `16 / 15`. The ratio `1 / 16` is the square of the
quartic scale gain `1 / 4` between consecutive dyadic radii. -/
theorem sum_sq_le_of_dyadic_fibers {N J : ℕ}
    (scale : Fin N → Fin J) (e : Fin N → ℝ) (A : ℝ)
    (hA : 0 ≤ A)
    (hscale : ∀ j : Fin J,
      ∑ i ∈ Finset.univ.filter (fun i => scale i = j), (e i) ^ 2 ≤
        A * (1 / 16 : ℝ) ^ (j : ℕ)) :
    ∑ i, (e i) ^ 2 ≤ (16 / 15 : ℝ) * A := by
  classical
  have hpartition :
      ∑ i, (e i) ^ 2 =
        ∑ j : Fin J,
          ∑ i ∈ Finset.univ.filter (fun i => scale i = j), (e i) ^ 2 := by
    symm
    exact Finset.sum_fiberwise Finset.univ scale (fun i => (e i) ^ 2)
  rw [hpartition]
  calc
    ∑ j : Fin J,
        ∑ i ∈ Finset.univ.filter (fun i => scale i = j), (e i) ^ 2
        ≤ ∑ j : Fin J, A * (1 / 16 : ℝ) ^ (j : ℕ) :=
      Finset.sum_le_sum fun j _ => hscale j
    _ = A * ∑ j : Fin J, (1 / 16 : ℝ) ^ (j : ℕ) := by
      rw [Finset.mul_sum]
    _ ≤ A * (16 / 15 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hA
      rw [Fin.sum_univ_eq_sum_range]
      have hgeom := geom_sum_Ico_le_of_lt_one
        (x := (1 / 16 : ℝ)) (m := 0) (n := J) (by norm_num) (by norm_num)
      norm_num at hgeom ⊢
      exact hgeom
    _ = (16 / 15 : ℝ) * A := by ring

/-- Finite annular shells with geometric ratio 1/2 sum with total loss at
most 2. This is the packing analogue of the 16/15 squared-error summation. -/
theorem sum_finset_le_two_mul_of_dyadic_fibers
    {ι : Type*} {J : ℕ}
    (s : Finset ι) (scale : ι → Fin J) (a : ι → ℝ) (A : ℝ)
    (hA : 0 ≤ A)
    (hscale : ∀ j : Fin J,
      ∑ i ∈ s.filter (fun i => scale i = j), a i ≤
        A * (1 / 2 : ℝ) ^ (j : ℕ)) :
    ∑ i ∈ s, a i ≤ 2 * A := by
  classical
  have hpartition :
      ∑ i ∈ s, a i =
        ∑ j : Fin J, ∑ i ∈ s.filter (fun i => scale i = j), a i := by
    symm
    exact Finset.sum_fiberwise s scale a
  rw [hpartition]
  calc
    ∑ j : Fin J, ∑ i ∈ s.filter (fun i => scale i = j), a i ≤
        ∑ j : Fin J, A * (1 / 2 : ℝ) ^ (j : ℕ) :=
      Finset.sum_le_sum fun j _ => hscale j
    _ = A * ∑ j : Fin J, (1 / 2 : ℝ) ^ (j : ℕ) := by
      rw [Finset.mul_sum]
    _ ≤ A * 2 := by
      apply mul_le_mul_of_nonneg_left _ hA
      rw [Fin.sum_univ_eq_sum_range]
      have hgeom := geom_sum_Ico_le_of_lt_one
        (x := (1 / 2 : ℝ)) (m := 0) (n := J) (by norm_num) (by norm_num)
      norm_num at hgeom ⊢
      exact hgeom
    _ = 2 * A := by ring

end QuarticConvergence
end OptimalConvergenceRates

end
