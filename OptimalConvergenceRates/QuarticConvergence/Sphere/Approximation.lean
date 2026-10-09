/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Approximation.lean

  Analytic quartic approximation on the sphere by degree-bounded sums of squares.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FiniteAtomFilter

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

/-- The normalized analytic approximation statement obtained from the scale-resolved
decomposition and Boolean-filter construction. Normalization makes the analytic constants
independent of the size of the input polynomial. -/
def HasNormalizedQuarticSOSApproximation (n : ℕ) (C : ℝ) (b k₀ : ℕ) : Prop :=
  ∀ F : MvPolynomial (Fin n) ℝ,
    SphereNonnegative F → sphereC6Norm F ≤ 1 →
      HasQuarticSOSApproximation F 1 C b k₀

/-- The coarse finite filtered-root conclusion follows from the scale data, overlap bounds,
and dyadic summation lemmas. -/
theorem finiteFilteredRootApproximation {n : ℕ} (hn : 3 ≤ n) :
    ∃ (C : ℝ) (b k₀ : ℕ),
      0 < C ∧ 1 ≤ b ∧ HasFiniteFilteredRootApproximation n C b k₀ := by
  obtain ⟨C, k₀, hC, _hk₀, hscale⟩ := finiteFilteredRootScaleData hn
  exact ⟨C, 2 * (n + 3), k₀, hC, by omega,
    finiteFilteredRootApproximation_of_scaleData hscale⟩

/-- Normalized nonnegative sphere polynomials admit quartic-rate approximation by
ordinary SOS with root degree linear in the scale.

This follows from the explicit finite filtered-root estimate above by the finite
error-assembly lemma. -/
theorem normalizedQuarticSOSApproximation {n : ℕ} (hn : 3 ≤ n) :
    ∃ (C : ℝ) (b k₀ : ℕ),
      0 < C ∧ 1 ≤ b ∧ HasNormalizedQuarticSOSApproximation n C b k₀ := by
  obtain ⟨C, b, k₀, hC, hb, hfiltered⟩ :=
    finiteFilteredRootApproximation hn
  refine ⟨C, b, k₀, hC, hb, ?_⟩
  intro F hF hnorm k hk
  obtain ⟨N, a, p, hdegree, hcross, hsquare, hremainder⟩ :=
    hfiltered F hF hnorm k hk
  obtain ⟨Q, hQ, herror⟩ :=
    finite_filtered_square_approximation (by omega : 0 < n) F a p
      (C / (4 * (k : ℝ) ^ 4))
      (C / (4 * (k : ℝ) ^ 4))
      (C / (4 * (k : ℝ) ^ 4))
      hdegree hcross hsquare hremainder
  refine ⟨Q, hQ, herror.trans_eq ?_⟩
  ring

/-- Quartic approximation of every nonnegative sphere polynomial by an ordinary
bounded-degree SOS. This general form follows formally from the normalized analytic
input by homogeneity, including the zero-seminorm case. -/
theorem quarticSOSApproximation {n : ℕ} (hn : 3 ≤ n) :
    ∃ (C : ℝ) (b k₀ : ℕ),
      0 < C ∧ 1 ≤ b ∧
      ∀ F : MvPolynomial (Fin n) ℝ, SphereNonnegative F →
        HasQuarticSOSApproximation F (sphereC6Norm F) C b k₀ := by
  obtain ⟨C, b, k₀, hC, hb, hnormalized⟩ :=
    normalizedQuarticSOSApproximation hn
  refine ⟨C, b, k₀, hC, hb, ?_⟩
  intro F hF
  have hnpos : 0 < n := by omega
  let M := sphereC6Norm F
  have hMnonneg : 0 ≤ M := sphereC6Norm_nonneg hnpos F
  by_cases hMzero : M = 0
  · intro k hk
    refine ⟨0, ⟨DegreeBoundedSOS.zero n (b * k)⟩, ?_⟩
    change sphereSupNorm (F - 0) ≤ C * M / (k : ℝ) ^ 4
    have hsup : sphereSupNorm F = 0 := by
      apply le_antisymm
      · exact (sphereSupNorm_le_sphereRotNorm hnpos 6 F).trans_eq hMzero
      · exact sphereSupNorm_nonneg hnpos F
    simpa only [sub_zero, hMzero, mul_zero, zero_div] using hsup.le
  · have hMpos : 0 < M := lt_of_le_of_ne hMnonneg (Ne.symm hMzero)
    let Fn : MvPolynomial (Fin n) ℝ := M⁻¹ • F
    have hFnnonneg : SphereNonnegative Fn := by
      intro x hx
      dsimp [Fn]
      rw [MvPolynomial.smul_eq_C_mul, map_mul, eval_C]
      exact mul_nonneg (inv_nonneg.mpr hMnonneg) (hF x hx)
    have hFnnorm : sphereC6Norm Fn ≤ 1 := by
      dsimp [Fn]
      rw [sphereC6Norm_smul hnpos, abs_of_pos (inv_pos.mpr hMpos)]
      exact le_of_eq (inv_mul_cancel₀ hMzero)
    have happrox := hnormalized Fn hFnnonneg hFnnorm
    intro k hk
    obtain ⟨Q, ⟨hQ⟩, herr⟩ := happrox k hk
    refine ⟨MvPolynomial.C M * Q,
      ⟨DegreeBoundedSOS.nonnegScale hQ M hMnonneg⟩, ?_⟩
    change sphereSupNorm (F - MvPolynomial.C M * Q) ≤
      C * M / (k : ℝ) ^ 4
    have hpoly : F - MvPolynomial.C M * Q = M • (Fn - Q) := by
      dsimp [Fn]
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hMzero, one_smul,
        MvPolynomial.smul_eq_C_mul]
    rw [hpoly, sphereSupNorm_smul hnpos, abs_of_pos hMpos]
    calc
      M * sphereSupNorm (Fn - Q) ≤ M * (C * 1 / (k : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left herr hMnonneg
      _ = C * M / (k : ℝ) ^ 4 := by ring

end QuarticConvergence
end OptimalConvergenceRates

end
