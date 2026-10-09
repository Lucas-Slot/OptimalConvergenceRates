/-
  General cube Schmüdgen certificates controlled by the lifted sphere C6 norm.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.SchmudgenDescent
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.LiftCertificate

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- Every nonnegative cube polynomial obtains a quartically small perturbation
in the canonical box preordering. The canonical order is twice the internal
sphere root order. -/
theorem quarticSchmudgenCertificateOfNonneg_c6 {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (d k : ℕ),
        p.totalDegree ≤ d → IsNonnegOn p (Hypercube n) →
        c * max ((2 * n + 1) * d) 1 ≤ k →
          p + MvPolynomial.C
              (A * cubeSphereC6Norm n p / (k : ℝ) ^ 4) ∈
            BoxPreordering n (2 * k) := by
  obtain ⟨A, c, hA, hc, hsphere⟩ := quarticCubeLiftCertificateOfNonneg hn
  refine ⟨A, c, hA, hc, ?_⟩
  intro p d k hpdeg hpnonneg hk
  have hcert := hsphere p d k hpdeg hpnonneg hk
  apply sphereSOSMod_cubeSphereLift_to_boxPreordering hn
  simpa only [map_add, cubeSphereLift_C] using hcert

/-- Centered all-polynomial form of the C6-controlled Schmüdgen certificate. -/
theorem quarticSchmudgenCertificate_c6 {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (d k : ℕ),
        p.totalDegree ≤ d →
        c * max ((2 * n + 1) * d) 1 ≤ k →
          (p - MvPolynomial.C (polyMin p)) +
              MvPolynomial.C
                (A * cubeSphereC6Norm n
                    (p - MvPolynomial.C (polyMin p)) / (k : ℝ) ^ 4) ∈
            BoxPreordering n (2 * k) := by
  obtain ⟨A, c, hA, hc, hsphere⟩ := quarticCubeLiftCertificate hn
  refine ⟨A, c, hA, hc, ?_⟩
  intro p d k hpdeg hk
  have hcert := hsphere p d k hpdeg hk
  apply sphereSOSMod_cubeSphereLift_to_boxPreordering hn
  simpa only [map_add, cubeSphereLift_C] using hcert

end QuarticConvergence
end OptimalConvergenceRates

end
