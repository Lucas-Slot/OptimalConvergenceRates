/-
  The existing quartic sphere certificate specialized to lifted cube
  polynomials.  Certificate descent to the box cones is kept as a separate
  algebraic layer.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.SphereLiftSection

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers


/-- The regularity size inherited from the already formalized sphere proof. -/
def cubeSphereC6Norm (n : ℕ) (p : MvPolynomial (Fin n) ℝ) : ℝ :=
  sphereC6Norm (cubeSphereLift n p)

theorem spherePolyMax_cubeSphereLift {n : ℕ} (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) :
    spherePolyMax (cubeSphereLift n p) = polyMax p := by
  apply le_antisymm
  · obtain ⟨z, hz, hmax⟩ :=
      spherePolyMax_mem (by omega : 0 < 2 * n + 1) (cubeSphereLift n p)
    rw [← hmax, eval_cubeSphereLift_eq_map]
    unfold polyMax
    exact le_csSup (Hypercube_image_compact p).bddAbove
      ⟨cubeSphereMap n z, cubeSphereMap_mem_hypercube hn z hz, rfl⟩
  · obtain ⟨x, hx, hmax⟩ := polyMax_mem p
    rw [← hmax]
    calc
      MvPolynomial.eval x p =
          MvPolynomial.eval (cubeSphereSection n x) (cubeSphereLift n p) := by
        rw [eval_cubeSphereLift_eq_map, cubeSphereMap_section hn x hx]
      _ ≤ spherePolyMax (cubeSphereLift n p) :=
        eval_le_spherePolyMax _ _ (cubeSphereSection_mem_sphere hn x hx)

theorem spherePolyOscillation_cubeSphereLift {n : ℕ} (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) :
    spherePolyOscillation (cubeSphereLift n p) = polyMax p - polyMin p := by
  simp [spherePolyOscillation, spherePolyMax_cubeSphereLift hn p,
    spherePolyMin_cubeSphereLift hn p]

/-- Direct specialization of the public nonnegative sphere theorem to the
polynomial lift of a cube polynomial. -/
theorem quarticCubeLiftCertificateOfNonneg {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        p.totalDegree ≤ d → IsNonnegOn p (Hypercube n) →
        c * max ((2 * n + 1) * d) 1 ≤ r →
          SphereSOSMod
            (cubeSphereLift n p +
              MvPolynomial.C (A * cubeSphereC6Norm n p / (r : ℝ) ^ 4)) r := by
  obtain ⟨A, c, hA, hc, hcert⟩ :=
    quarticSphereCertificateOfNonneg (by omega : 3 ≤ 2 * n + 1)
  refine ⟨A, c, hA, hc, ?_⟩
  intro p d r hpdeg hpnonneg hr
  apply hcert (cubeSphereLift n p) ((2 * n + 1) * d) r
  · exact (cubeSphereLift_totalDegree_le n p).trans
      (Nat.mul_le_mul_left (2 * n + 1) hpdeg)
  · exact cubeSphereLift_nonnegative hn hpnonneg
  · exact hr

/-- Centered form of the lifted certificate, using the actual cube minimum. -/
theorem quarticCubeLiftCertificate {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        p.totalDegree ≤ d → c * max ((2 * n + 1) * d) 1 ≤ r →
          SphereSOSMod
            (cubeSphereLift n (p - MvPolynomial.C (polyMin p)) +
              MvPolynomial.C
                (A * cubeSphereC6Norm n (p - MvPolynomial.C (polyMin p)) /
                  (r : ℝ) ^ 4)) r := by
  obtain ⟨A, c, hA, hc, hcert⟩ := quarticCubeLiftCertificateOfNonneg hn
  refine ⟨A, c, hA, hc, ?_⟩
  intro p d r hpdeg hr
  apply hcert (p - MvPolynomial.C (polyMin p)) d r
  · exact (MvPolynomial.totalDegree_sub _ _).trans (max_le hpdeg (by simp))
  · intro x hx
    simp only [map_sub, eval_C]
    exact sub_nonneg.mpr (polyMin_le_eval p x hx)
  · exact hr

end QuarticConvergence
end OptimalConvergenceRates

end
