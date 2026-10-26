import Mathlib.Topology.Algebra.MvPolynomial
import OptimalConvergenceRates.SphereDimensionBounds.Foundation.Hierarchy

/-! Attainment of the sphere extrema used by the hierarchy. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

open scoped BigOperators

theorem unitSphere_nonempty {n : ℕ} (hn : 0 < n) : (unitSphere n).Nonempty := by
  let i₀ : Fin n := ⟨0, hn⟩
  refine ⟨fun i => if i = i₀ then 1 else 0, ?_⟩
  simp [unitSphere, ite_pow]

theorem unitSphere_isClosed (n : ℕ) : IsClosed (unitSphere n) := by
  have hc : Continuous (fun x : Fin n → ℝ => ∑ i : Fin n, x i ^ 2) := by
    exact continuous_finsetSum _ (fun i _ => (continuous_apply i).pow 2)
  exact isClosed_eq hc continuous_const

theorem unitSphere_subset_cube (n : ℕ) :
    unitSphere n ⊆ Set.Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1) := by
  intro x hx
  have hsum : ∑ j : Fin n, x j ^ 2 = 1 := hx
  have hbound (i : Fin n) : x i ^ 2 ≤ 1 := by
    calc
      x i ^ 2 ≤ ∑ j : Fin n, x j ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      _ = 1 := hsum
  constructor
  · intro i
    exact (abs_le.mp ((sq_le_one_iff_abs_le_one (x i)).mp (hbound i))).1
  · intro i
    exact (abs_le.mp ((sq_le_one_iff_abs_le_one (x i)).mp (hbound i))).2

theorem unitSphere_isCompact (n : ℕ) : IsCompact (unitSphere n) :=
  isCompact_Icc.of_isClosed_subset (unitSphere_isClosed n) (unitSphere_subset_cube n)

theorem sphereMinimum_exists {n : ℕ} (hn : 0 < n) (p : Polynomial n) :
    ∃ μ : ℝ, IsSphereMinimum p μ := by
  obtain ⟨x, hx, hmin⟩ := (unitSphere_isCompact n).exists_isMinOn
    (unitSphere_nonempty hn) (MvPolynomial.continuous_eval p).continuousOn
  exact ⟨MvPolynomial.eval x p, hmin, x, hx, rfl⟩

theorem sphereMinimum_attained {n : ℕ} (hn : 0 < n) (p : Polynomial n) :
    ∃ x ∈ unitSphere n, MvPolynomial.eval x p = sphereMinimum p := by
  obtain ⟨μ, hμ⟩ := sphereMinimum_exists hn p
  obtain ⟨x, hx, hvalue⟩ := hμ.2
  exact ⟨x, hx, hvalue.trans (sphereMinimum_eq hμ).symm⟩

theorem sphereNormValues_bddAbove {n : ℕ} (p : Polynomial n) :
    BddAbove {v : ℝ | ∃ x ∈ unitSphere n, |MvPolynomial.eval x p| = v} := by
  have hc := (unitSphere_isCompact n).image (MvPolynomial.continuous_eval p).abs
  have heq : (fun x => |MvPolynomial.eval x p|) '' unitSphere n =
      {v : ℝ | ∃ x ∈ unitSphere n, |MvPolynomial.eval x p| = v} := by
    ext v
    rfl
  rw [heq] at hc
  exact hc.bddAbove

theorem sphereSupNorm_attained {n : ℕ} (hn : 0 < n) (p : Polynomial n) :
    ∃ x ∈ unitSphere n, |MvPolynomial.eval x p| = sphereSupNorm p := by
  obtain ⟨x, hx, hmax⟩ := (unitSphere_isCompact n).exists_isMaxOn
    (unitSphere_nonempty hn) (MvPolynomial.continuous_eval p).abs.continuousOn
  refine ⟨x, hx, ?_⟩
  apply le_antisymm
  · exact le_csSup (sphereNormValues_bddAbove p) ⟨x, hx, rfl⟩
  · change sSup {v : ℝ | ∃ y ∈ unitSphere n, |MvPolynomial.eval y p| = v} ≤
      |MvPolynomial.eval x p|
    refine csSup_le (s := {v : ℝ | ∃ y ∈ unitSphere n,
      |MvPolynomial.eval y p| = v}) ?_ ?_
    · exact ⟨|MvPolynomial.eval x p|, x, hx, rfl⟩
    · rintro v ⟨y, hy, rfl⟩
      exact hmax hy

theorem sphereSupNorm_pos_of_nonzero_value {n : ℕ} {p : Polynomial n}
    {x : Fin n → ℝ} (hx : x ∈ unitSphere n) (hvalue : MvPolynomial.eval x p ≠ 0) :
    0 < sphereSupNorm p := by
  exact (abs_pos.mpr hvalue).trans_le
    (le_csSup (sphereNormValues_bddAbove p) ⟨x, hx, rfl⟩)

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
