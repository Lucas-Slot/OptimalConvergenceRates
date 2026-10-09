/-
  C6-controlled Schmüdgen certificates at every sufficiently large canonical order.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.SchmudgenC6
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.OrderConventions

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers


/-- The general C6-controlled certificate in the repository's canonical
total-certificate-degree convention, at every sufficiently large order.
The factor `81` absorbs replacing `r` by the internal root order `r / 2`. -/
theorem quarticSchmudgenCertificateOfNonneg_c6_atOrder {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        p.totalDegree ≤ d → IsNonnegOn p (Hypercube n) →
        2 * (c * max ((2 * n + 1) * d) 1) ≤ r →
          p + MvPolynomial.C
              ((81 * A) * cubeSphereC6Norm n p / (r : ℝ) ^ 4) ∈
            BoxPreordering n r := by
  obtain ⟨A, c, hA, hc, heven⟩ := quarticSchmudgenCertificateOfNonneg_c6 hn
  refine ⟨A, c, hA, hc, ?_⟩
  intro p d r hpdeg hpnonneg hr
  let k := r / 2
  have hk : c * max ((2 * n + 1) * d) 1 ≤ k := by
    dsimp [k]
    omega
  have hkpos : 0 < k := by
    have hthreshold : 0 < c * max ((2 * n + 1) * d) 1 :=
      Nat.mul_pos hc (by omega)
    exact hthreshold.trans_le hk
  have horder : 2 * k ≤ r := by
    dsimp [k]
    omega
  have hr_le : r ≤ 3 * k := by
    dsimp [k]
    omega
  let small : ℝ := A * cubeSphereC6Norm n p / (k : ℝ) ^ 4
  let large : ℝ := (81 * A) * cubeSphereC6Norm n p / (r : ℝ) ^ 4
  have hnorm : 0 ≤ cubeSphereC6Norm n p :=
    sphereC6Norm_nonneg (by omega : 0 < 2 * n + 1) (cubeSphereLift n p)
  have hAnorm : 0 ≤ A * cubeSphereC6Norm n p := mul_nonneg hA.le hnorm
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
      (A * cubeSphereC6Norm n p) * (r : ℝ) ^ 4 ≤
          (A * cubeSphereC6Norm n p) * (81 * (k : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hpow hAnorm
      _ = ((81 * A) * cubeSphereC6Norm n p) * (k : ℝ) ^ 4 := by ring
  have hbase : p + MvPolynomial.C small ∈ BoxPreordering n r := by
    apply box_preordering_mono horder
    simpa only [small] using heven p d k hpdeg hpnonneg hk
  have hconstant :
      MvPolynomial.C (large - small) ∈ BoxPreordering n r :=
    nonneg_const_mem_BoxPreordering (sub_nonneg.mpr hsmall_large) n r
  have hadd := BoxPreordering_add hbase hconstant
  have heq :
      (p + MvPolynomial.C small) + MvPolynomial.C (large - small) =
        p + MvPolynomial.C large := by
    simp only [map_sub]
    ring
  rw [heq] at hadd
  simpa only [large] using hadd

end QuarticConvergence
end OptimalConvergenceRates

end
