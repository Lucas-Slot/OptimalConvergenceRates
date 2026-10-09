/-
  Explicit degree-sensitive quartic convergence for the canonical cube
  Schmüdgen hierarchy.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.LiftRegularity
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.SchmudgenC6Order

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- Every cube polynomial of degree at most `d` has a canonical-order
Schmüdgen certificate after an explicit quartic perturbation from its cube
minimum.  Both constants depend only on the fixed cube dimension.

The degree factor is displayed as `(max d 1)^6`, and the order threshold is
linear in `max d 1`. -/
theorem schmudgenExplicitRate_certificate {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        p.totalDegree ≤ d → c * max d 1 ≤ r →
          p - MvPolynomial.C
              (polyMin p -
                A * ((max d 1 : ℕ) : ℝ) ^ 6 *
                    (polyMax p - polyMin p) / (r : ℝ) ^ 4) ∈
            BoxPreordering n r := by
  obtain ⟨A₀, c₀, hA₀, hc₀, hcertificate⟩ :=
    quarticSchmudgenCertificateOfNonneg_c6_atOrder hn
  let A : ℝ := (81 * A₀) * cubeSphereC6DimensionConstant n
  let c : ℕ := 2 * c₀ * (2 * n + 1)
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (by positivity) (cubeSphereC6DimensionConstant_pos n)
  have hc : 0 < c := by
    dsimp only [c]
    exact Nat.mul_pos (Nat.mul_pos (by omega) hc₀) (by omega)
  refine ⟨A, c, hA, hc, ?_⟩
  intro p d r hpdeg hr
  let e : ℕ := max d 1
  let q : MvPolynomial (Fin n) ℝ :=
    p - MvPolynomial.C (polyMin p)
  let small : ℝ :=
    (81 * A₀) * cubeSphereC6Norm n q / (r : ℝ) ^ 4
  let large : ℝ :=
    A * (e : ℝ) ^ 6 * (polyMax p - polyMin p) / (r : ℝ) ^ 4
  have he : 0 < e := by
    dsimp only [e]
    omega
  have hthresholdCore :
      max ((2 * n + 1) * d) 1 ≤ (2 * n + 1) * e := by
    apply max_le
    · exact Nat.mul_le_mul_left (2 * n + 1) (le_max_left d 1)
    · calc
        1 ≤ (2 * n + 1) * 1 := by omega
        _ ≤ (2 * n + 1) * e :=
          Nat.mul_le_mul_left (2 * n + 1) (by omega)
  have hthreshold :
      2 * (c₀ * max ((2 * n + 1) * d) 1) ≤ r := by
    calc
      2 * (c₀ * max ((2 * n + 1) * d) 1) ≤
          2 * (c₀ * ((2 * n + 1) * e)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left c₀ hthresholdCore)
      _ = c * e := by
        dsimp only [c]
        ac_rfl
      _ ≤ r := by
        simpa only [e] using hr
  have hrpos : 0 < r := (Nat.mul_pos hc he).trans_le (by
    simpa only [e] using hr)
  have hqdeg : q.totalDegree ≤ d := by
    simpa only [q] using centerAtPolyMin_totalDegree_le_of_le hpdeg
  have hqnonneg : IsNonnegOn q (Hypercube n) := by
    simpa only [q] using centerAtPolyMin_nonnegative p
  have hbase : q + MvPolynomial.C small ∈ BoxPreordering n r := by
    simpa only [small] using
      hcertificate q d r hqdeg hqnonneg hthreshold
  have hregularity :
      cubeSphereC6Norm n q ≤
        cubeSphereC6DimensionConstant n * (e : ℝ) ^ 6 *
          (polyMax p - polyMin p) := by
    simpa only [q, e] using cubeSphereC6Norm_centered_le hn p hpdeg
  have hcoefficient :
      (81 * A₀) * cubeSphereC6Norm n q ≤
        A * (e : ℝ) ^ 6 * (polyMax p - polyMin p) := by
    calc
      (81 * A₀) * cubeSphereC6Norm n q ≤
          (81 * A₀) *
            (cubeSphereC6DimensionConstant n * (e : ℝ) ^ 6 *
              (polyMax p - polyMin p)) :=
        mul_le_mul_of_nonneg_left hregularity (by positivity)
      _ = A * (e : ℝ) ^ 6 * (polyMax p - polyMin p) := by
        dsimp only [A]
        ring
  have hsmall_large : small ≤ large := by
    dsimp only [small, large]
    exact div_le_div_of_nonneg_right hcoefficient
      (pow_nonneg (Nat.cast_nonneg r) 4)
  have hconstant :
      MvPolynomial.C (large - small) ∈ BoxPreordering n r :=
    nonneg_const_mem_BoxPreordering (sub_nonneg.mpr hsmall_large) n r
  have hadd := BoxPreordering_add hbase hconstant
  have heq :
      (q + MvPolynomial.C small) + MvPolynomial.C (large - small) =
        p - MvPolynomial.C (polyMin p - large) := by
    dsimp only [q]
    simp only [map_sub]
    ring
  rw [heq] at hadd
  simpa only [large, e] using hadd

/-- The canonical Schmüdgen Lasserre bound is real at every order above a
dimension-only multiple of `max d 1`, and its gap from the cube minimum is
at most the explicit degree-six multiple of `r⁻⁴`.

The constants are chosen before `p`, `d`, and `r`, so they depend only on
the fixed dimension `n`. -/
theorem schmudgenExplicitRate_lasserreGap {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        p.totalDegree ≤ d → c * max d 1 ≤ r →
          ∃ b : ℝ,
            lasserre_bound_box_preo p r = (b : WithBot ℝ) ∧
            0 ≤ polyMin p - b ∧
            polyMin p - b ≤
              A * ((max d 1 : ℕ) : ℝ) ^ 6 *
                (polyMax p - polyMin p) / (r : ℝ) ^ 4 := by
  obtain ⟨A, c, hA, hc, hcertificate⟩ :=
    schmudgenExplicitRate_certificate hn
  refine ⟨A, c, hA, hc, ?_⟩
  intro p d r hpdeg hr
  let delta : ℝ :=
    A * ((max d 1 : ℕ) : ℝ) ^ 6 *
      (polyMax p - polyMin p) / (r : ℝ) ^ 4
  have hfeasible :
      p - MvPolynomial.C (polyMin p - delta) ∈ BoxPreordering n r := by
    simpa only [delta] using hcertificate p d r hpdeg hr
  obtain ⟨b, hb⟩ :=
    exists_real_lasserre_bound_box_preo_of_feasible p r hfeasible
  have hlower := lasserre_bound_box_preo_ge_feasible p r hfeasible
  have hupper := lasserre_bound_box_preo_le_polyMin p r
  rw [hb, WithBot.coe_le_coe] at hlower hupper
  refine ⟨b, hb, by linarith, ?_⟩
  dsimp only [delta]
  linarith

end QuarticConvergence
end OptimalConvergenceRates

end
