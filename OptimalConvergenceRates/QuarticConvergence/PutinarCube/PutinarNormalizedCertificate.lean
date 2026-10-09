/- Explicit certificate form from a normalized Putinar approximation family. -/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarNormalizedRate
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarApproximationCertificateOrder

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- Every nonnegative polynomial receives an explicit degree-six,
quartic-order Putinar certificate from a normalized approximation family. -/
theorem putinarExplicitRate_certificate_of_normalizedApproximation
    {n Aq B k₀ : ℕ} {L₀ : ℝ} (hn : 0 < n)
    (hAq : 1 ≤ Aq) (hrepair : HasPutinarDegreeLinearRepair (n := n) Aq)
    (hB : 1 ≤ B) (hk₀ : 1 ≤ k₀) (hL₀ : 0 < L₀)
    (hfamily : HasNormalizedQuarticBoxQMApproximation n B k₀ L₀) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (h : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        h.totalDegree ≤ d → IsNonnegOn h (Hypercube n) →
          c * max d 1 ≤ r →
          h + MvPolynomial.C
              (A * ((max d 1 : ℕ) : ℝ) ^ 6 * polySupNorm h /
                (r : ℝ) ^ 4) ∈
            BoxQuadraticModule n r := by
  let q : ℕ := Aq * B
  let A : ℝ :=
    2 * (2 * (q : ℝ)) ^ 4 * L₀ * cubeSphereC6DimensionConstant n
  let c : ℕ := 2 * q * k₀
  have hq : 1 ≤ q := Nat.mul_le_mul hAq hB
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (mul_pos (by positivity) hL₀)
      (cubeSphereC6DimensionConstant_pos n)
  have hc : 0 < c := by
    dsimp only [c]
    exact Nat.mul_pos (Nat.mul_pos (by omega) hq) (by omega)
  refine ⟨A, c, hA, hc, ?_⟩
  intro h d r hDegree hnonnegative hr
  let e : ℕ := max d 1
  let M : ℝ := cubeSphereC6Norm n h
  let L : ℝ := M * L₀
  let small : ℝ :=
    2 * (2 * (q : ℝ)) ^ 4 * L / (r : ℝ) ^ 4
  let large : ℝ := A * (e : ℝ) ^ 6 * polySupNorm h / (r : ℝ) ^ 4
  have hMnonneg : 0 ≤ M :=
    sphereC6Norm_nonneg (by omega : 0 < 2 * n + 1) (cubeSphereLift n h)
  have hL : 0 ≤ L := mul_nonneg hMnonneg hL₀.le
  have hthresholdCore : max d k₀ ≤ k₀ * e := by
    apply max_le
    · exact (le_max_left d 1).trans <| by
        simpa only [one_mul] using Nat.mul_le_mul_right e hk₀
    · calc
        k₀ = k₀ * 1 := by omega
        _ ≤ k₀ * e := Nat.mul_le_mul_left k₀ (le_max_right d 1)
  have hthreshold : 2 * (Aq * B) * max d k₀ ≤ r := by
    calc
      2 * (Aq * B) * max d k₀ ≤
          2 * (Aq * B) * (k₀ * e) :=
        Nat.mul_le_mul_left (2 * (Aq * B)) hthresholdCore
      _ = c * e := by
        dsimp only [c, q]
        ring
      _ ≤ r := by simpa only [e] using hr
  have happrox : ∀ m, k₀ ≤ m →
      HasQuarticBoxQMApproximationAt h B m L := by
    intro m hm
    simpa only [L, M] using
      hfamily.approximation hn h hnonnegative m hm
  have hbase : h + MvPolynomial.C small ∈ BoxQuadraticModule n r := by
    simpa only [small, q] using
      quarticBoxQMApproximation_certificate_arbitrary_order
        hAq hrepair hB hk₀ hL hDegree happrox hthreshold
  have hdegreeMax : max h.totalDegree 1 ≤ e :=
    max_le (hDegree.trans (le_max_left d 1)) (le_max_right d 1)
  have hdegreePow :
      (((max h.totalDegree 1 : ℕ) : ℝ) ^ 6) ≤ (e : ℝ) ^ 6 := by
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast hdegreeMax
  have hregularity :
      M ≤ cubeSphereC6DimensionConstant n * (e : ℝ) ^ 6 *
        polySupNorm h := by
    have hreg := cubeSphereC6Norm_le hn h
    rw [sphereSupNorm_cubeSphereLift hn h] at hreg
    apply hreg.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdegreePow
        (cubeSphereC6DimensionConstant_pos n).le)
      (polySupNorm_nonneg h)
  have hcoefficient :
      2 * (2 * (q : ℝ)) ^ 4 * L ≤
        A * (e : ℝ) ^ 6 * polySupNorm h := by
    calc
      2 * (2 * (q : ℝ)) ^ 4 * L =
          2 * (2 * (q : ℝ)) ^ 4 * (M * L₀) := by rfl
      _ ≤ 2 * (2 * (q : ℝ)) ^ 4 *
          ((cubeSphereC6DimensionConstant n * (e : ℝ) ^ 6 *
            polySupNorm h) * L₀) := by
        gcongr
      _ = A * (e : ℝ) ^ 6 * polySupNorm h := by
        dsimp only [A]
        ring
  have hsmallLarge : small ≤ large := by
    dsimp only [small, large]
    exact div_le_div_of_nonneg_right hcoefficient
      (pow_nonneg (Nat.cast_nonneg r) 4)
  have hconstant : MvPolynomial.C (large - small) ∈
      BoxQuadraticModule n r :=
    nonneg_const_mem_BoxQuadraticModule (sub_nonneg.mpr hsmallLarge) n r
  have hadd := BoxQuadraticModule_add hbase hconstant
  have hpoly :
      (h + MvPolynomial.C small) + MvPolynomial.C (large - small) =
        h + MvPolynomial.C large := by
    simp only [map_sub]
    ring
  rw [hpoly] at hadd
  simpa only [large, e] using hadd

end QuarticConvergence
end OptimalConvergenceRates

end
