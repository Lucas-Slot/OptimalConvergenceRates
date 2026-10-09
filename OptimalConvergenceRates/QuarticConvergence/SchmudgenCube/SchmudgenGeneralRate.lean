/-
  General fixed-degree quartic convergence for the canonical box preordering.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.SchmudgenDescent
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.LiftFixedDegree
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.CenteredBounds
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.OrderConventions

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- At twice the internal sphere order, every bounded-degree cube polynomial
has a Schmüdgen certificate after a quartically small upward perturbation from
its cube minimum. -/
theorem schmudgenFixedDegree_certificate_evenOrder {n d : ℕ} (hn : 0 < n) :
    ∃ (C : ℝ) (k₀ : ℕ),
      0 < C ∧ 0 < k₀ ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (k : ℕ),
        p.totalDegree ≤ d → k₀ ≤ k →
          p - MvPolynomial.C
              (polyMin p - C * (polyMax p - polyMin p) / (k : ℝ) ^ 4) ∈
            BoxPreordering n (2 * k) := by
  obtain ⟨C, k₀, hC, hk₀, hcert⟩ := quarticCubeLiftFixedDegree (n := n) (d := d) hn
  refine ⟨C, k₀, hC, hk₀, ?_⟩
  intro p k hpdeg hk
  have hsphere := hcert p k hpdeg hk
  have hlift :
      cubeSphereLift n
          (p - MvPolynomial.C
            (polyMin p - C * (polyMax p - polyMin p) / (k : ℝ) ^ 4)) =
        cubeSphereLift n (p - MvPolynomial.C (polyMin p)) +
          MvPolynomial.C (C * (polyMax p - polyMin p) / (k : ℝ) ^ 4) := by
    simp only [map_sub, cubeSphereLift_C]
    ring
  rw [← hlift] at hsphere
  exact sphereSOSMod_cubeSphereLift_to_boxPreordering hn hsphere

/-- For every sufficiently large canonical box order, every bounded-degree
cube polynomial has a Schmüdgen certificate with perturbation `O(r⁻⁴)`.

The factor `81 = 3⁴` absorbs the passage from an arbitrary order `r` to the
even order `2 * (r / 2)`. -/
theorem schmudgenFixedDegree_certificate {n d : ℕ} (hn : 0 < n) :
    ∃ (C : ℝ) (r₀ : ℕ),
      0 < C ∧ 0 < r₀ ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (r : ℕ),
        p.totalDegree ≤ d → r₀ ≤ r →
          p - MvPolynomial.C
              (polyMin p - C * (polyMax p - polyMin p) / (r : ℝ) ^ 4) ∈
            BoxPreordering n r := by
  obtain ⟨A, k₀, hA, hk₀, heven⟩ := schmudgenFixedDegree_certificate_evenOrder
    (n := n) (d := d) hn
  refine ⟨81 * A, 2 * k₀, by positivity, by omega, ?_⟩
  intro p r hpdeg hr
  let k := r / 2
  have hk : k₀ ≤ k := by
    dsimp [k]
    omega
  have hkpos : 0 < k := hk₀.trans_le hk
  have horder : 2 * k ≤ r := by
    dsimp [k]
    omega
  have hr_le : r ≤ 3 * k := by
    dsimp [k]
    omega
  let small : ℝ := A * (polyMax p - polyMin p) / (k : ℝ) ^ 4
  let large : ℝ :=
    (81 * A) * (polyMax p - polyMin p) / (r : ℝ) ^ 4
  have hAosc : 0 ≤ A * (polyMax p - polyMin p) :=
    mul_nonneg hA.le (polyMax_sub_polyMin_nonneg p)
  have hkreal : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hkpos
  have hrpos : 0 < r := by omega
  have hrreal : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hrpos
  have hcast : (r : ℝ) ≤ 3 * (k : ℝ) := by
    exact_mod_cast hr_le
  have hpow : (r : ℝ) ^ 4 ≤ 81 * (k : ℝ) ^ 4 := by
    calc
      (r : ℝ) ^ 4 ≤ (3 * (k : ℝ)) ^ 4 :=
        pow_le_pow_left₀ (Nat.cast_nonneg r) hcast 4
      _ = 81 * (k : ℝ) ^ 4 := by ring
  have hsmall_large : small ≤ large := by
    dsimp [small, large]
    rw [div_le_div_iff₀ (pow_pos hkreal 4) (pow_pos hrreal 4)]
    calc
      (A * (polyMax p - polyMin p)) * (r : ℝ) ^ 4 ≤
          (A * (polyMax p - polyMin p)) * (81 * (k : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hpow hAosc
      _ = ((81 * A) * (polyMax p - polyMin p)) * (k : ℝ) ^ 4 := by ring
  have hbase :
      p - MvPolynomial.C (polyMin p - small) ∈ BoxPreordering n r := by
    apply box_preordering_mono horder
    simpa only [small] using heven p k hpdeg hk
  have hconstant :
      MvPolynomial.C (large - small) ∈ BoxPreordering n r :=
    nonneg_const_mem_BoxPreordering (sub_nonneg.mpr hsmall_large) n r
  have hadd := BoxPreordering_add hbase hconstant
  have heq :
      (p - MvPolynomial.C (polyMin p - small)) +
          MvPolynomial.C (large - small) =
        p - MvPolynomial.C (polyMin p - large) := by
    simp only [map_sub]
    ring
  rw [heq] at hadd
  simpa only [large] using hadd

/-- The canonical Schmüdgen Lasserre hierarchy has a real value at every
sufficiently large order, and its gap from the true cube minimum is bounded
above by a fixed multiple of `r⁻⁴` for every polynomial of degree at most
`d`. -/
theorem schmudgenFixedDegree_lasserreRate {n d : ℕ} (hn : 0 < n) :
    ∃ (C : ℝ) (r₀ : ℕ),
      0 < C ∧ 0 < r₀ ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (r : ℕ),
        p.totalDegree ≤ d → r₀ ≤ r →
          ∃ b : ℝ,
            lasserre_bound_box_preo p r = (b : WithBot ℝ) ∧
            0 ≤ polyMin p - b ∧
            polyMin p - b ≤
              C * (polyMax p - polyMin p) / (r : ℝ) ^ 4 := by
  obtain ⟨C, r₀, hC, hr₀, hcert⟩ := schmudgenFixedDegree_certificate
    (n := n) (d := d) hn
  refine ⟨C, r₀, hC, hr₀, ?_⟩
  intro p r hpdeg hr
  let delta : ℝ := C * (polyMax p - polyMin p) / (r : ℝ) ^ 4
  have hfeasible :
      p - MvPolynomial.C (polyMin p - delta) ∈ BoxPreordering n r := by
    simpa only [delta] using hcert p r hpdeg hr
  obtain ⟨b, hb⟩ := exists_real_lasserre_bound_box_preo_of_feasible p r hfeasible
  have hlower := lasserre_bound_box_preo_ge_feasible p r hfeasible
  have hupper := lasserre_bound_box_preo_le_polyMin p r
  rw [hb, WithBot.coe_le_coe] at hlower hupper
  refine ⟨b, hb, by linarith, ?_⟩
  dsimp [delta]
  linarith

end QuarticConvergence
end OptimalConvergenceRates

end
