import OptimalConvergenceRates.QuarticConvergence.Sphere.FixedDegree
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.SchmudgenExplicitRate
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarGeneralRate
import OptimalConvergenceRates.QuarticConvergence.InverseRate

open MvPolynomial Finset Set

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.MainResultsProofs

open SphereBallTransfers

theorem sphereQuarticRate_membership {n : ℕ} (hn : 3 ≤ n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (f : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        f.totalDegree ≤ d → c * max d 1 ≤ r →
          SphereSOSMod
            (f - MvPolynomial.C (spherePolyMin f) +
              MvPolynomial.C
                (A * sphereC6Norm
                  (f - MvPolynomial.C (spherePolyMin f)) / (r : ℝ) ^ 4))
            r := by
  simpa only [QuarticSphereCertificateStatement] using
    quarticSphereCertificate hn

theorem sphereQuarticRate_lasserreError {n : ℕ} (hn : 3 ≤ n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (f : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        f.totalDegree ≤ d → c * max d 1 ≤ r →
          ∃ b : ℝ,
            sphereSOSBound f r = (b : WithBot ℝ) ∧
            0 ≤ spherePolyMin f - b ∧
            spherePolyMin f - b ≤
              A * sphereC6Norm
                (f - MvPolynomial.C (spherePolyMin f)) / (r : ℝ) ^ 4 :=
  quarticSphereHierarchyError hn

theorem sphereFixedDegreeQuarticRate_membership {n d : ℕ} (hn : 3 ≤ n) :
    ∃ (C : ℝ) (r₀ : ℕ),
      0 < C ∧ 0 < r₀ ∧
      ∀ (f : MvPolynomial (Fin n) ℝ) (r : ℕ),
        f.totalDegree ≤ d → r₀ ≤ r →
          SphereSOSMod
            (f - MvPolynomial.C (spherePolyMin f) +
              MvPolynomial.C
                (C * (spherePolyMax f - spherePolyMin f) /
                  (r : ℝ) ^ 4))
            r :=
  quarticSphereFixedDegreeCertificate hn

theorem sphereFixedDegreeQuarticRate_lasserreError {n d : ℕ} (hn : 3 ≤ n) :
    ∃ (C : ℝ) (r₀ : ℕ),
      0 < C ∧ 0 < r₀ ∧
      ∀ (f : MvPolynomial (Fin n) ℝ) (r : ℕ),
        f.totalDegree ≤ d → r₀ ≤ r →
          ∃ b : ℝ,
            sphereSOSBound f r = (b : WithBot ℝ) ∧
            0 ≤ spherePolyMin f - b ∧
            spherePolyMin f - b ≤
              C * (spherePolyMax f - spherePolyMin f) /
                (r : ℝ) ^ 4 := by
  simpa only [spherePolyOscillation] using
    (quarticSphereFixedDegree (n := n) (d := d) hn)

theorem schmudgenCubeQuarticRate_membership {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        p.totalDegree ≤ d → c * max d 1 ≤ r →
          p - MvPolynomial.C
              (polyMin p -
                A * ((max d 1 : ℕ) : ℝ) ^ 6 *
                  (polyMax p - polyMin p) / (r : ℝ) ^ 4) ∈
            BoxPreordering n r :=
  schmudgenExplicitRate_certificate hn

theorem schmudgenCubeQuarticRate_lasserreError {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        p.totalDegree ≤ d → c * max d 1 ≤ r →
          ∃ b : ℝ,
            lasserre_bound_box_preo p r = (b : WithBot ℝ) ∧
            0 ≤ polyMin p - b ∧
            polyMin p - b ≤
              A * ((max d 1 : ℕ) : ℝ) ^ 6 *
                (polyMax p - polyMin p) / (r : ℝ) ^ 4 :=
  schmudgenExplicitRate_lasserreGap hn

theorem putinarCubeQuarticRate_membership {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (h : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        h.totalDegree ≤ d → IsNonnegOn h (Hypercube n) →
          c * max d 1 ≤ r →
          h + MvPolynomial.C
              (A * ((max d 1 : ℕ) : ℝ) ^ 6 * polySupNorm h /
                (r : ℝ) ^ 4) ∈
            BoxQuadraticModule n r :=
  putinarExplicitRate_certificate hn

theorem putinarCubeQuarticDegreeBound {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (h : MvPolynomial (Fin n) ℝ) (d : ℕ) (epsilon : ℝ),
        h.totalDegree ≤ d → IsNonnegOn h (Hypercube n) → 0 < epsilon →
          ∃ r : ℕ,
            (r : ℝ) < ((c * max d 1 : ℕ) : ℝ) +
                (A * ((max d 1 : ℕ) : ℝ) ^ 6 * polySupNorm h / epsilon) ^
                  ((1 : ℝ) / 4) + 1 ∧
              h + C epsilon ∈ BoxQuadraticModule n r := by
  obtain ⟨A, c, hA, hc, hcertificate⟩ := putinarExplicitRate_certificate hn
  refine ⟨A, c, hA, hc, ?_⟩
  intro h d epsilon hdegree hnonneg hepsilon
  let r₀ : ℕ := c * max d 1
  let N : ℝ := A * ((max d 1 : ℕ) : ℝ) ^ 6 * polySupNorm h
  let r : ℕ := quarticInverseOrder r₀ N epsilon
  have hr₀ : 0 < r₀ := by
    dsimp [r₀]
    exact Nat.mul_pos hc (by omega)
  have hN : 0 ≤ N := by
    dsimp [N]
    exact mul_nonneg
      (mul_nonneg hA.le (pow_nonneg (Nat.cast_nonneg _) 6))
      (polySupNorm_nonneg h)
  have hscale : N / (r : ℝ) ^ 4 ≤ epsilon := by
    dsimp [r]
    exact quarticScale_le_epsilon hr₀ hN hepsilon
  have hbase : h + C (N / (r : ℝ) ^ 4) ∈ BoxQuadraticModule n r := by
    dsimp [r]
    simpa only [N, r₀] using hcertificate h d (quarticInverseOrder r₀ N epsilon)
      hdegree hnonneg (quarticInverseOrder_ge r₀ N epsilon)
  have hconstant : C (epsilon - N / (r : ℝ) ^ 4) ∈ BoxQuadraticModule n r :=
    nonneg_const_mem_BoxQuadraticModule (sub_nonneg.mpr hscale) n r
  have hsum := BoxQuadraticModule_add hbase hconstant
  refine ⟨r, ?_, ?_⟩
  · simpa only [r₀, N] using quarticInverseOrder_lt r₀ hN hepsilon
  · have heq :
        h + C (N / (r : ℝ) ^ 4) + C (epsilon - N / (r : ℝ) ^ 4) =
          h + C epsilon := by
      rw [map_sub]
      ring
    rw [← heq]
    exact hsum

theorem schmudgenCubeQuarticDegreeBound {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (h : MvPolynomial (Fin n) ℝ) (d : ℕ) (epsilon : ℝ),
        h.totalDegree ≤ d → IsNonnegOn h (Hypercube n) → 0 < epsilon →
          ∃ r : ℕ,
            (r : ℝ) < ((c * max d 1 : ℕ) : ℝ) +
                (A * ((max d 1 : ℕ) : ℝ) ^ 6 * polySupNorm h / epsilon) ^
                  ((1 : ℝ) / 4) + 1 ∧
              h + C epsilon ∈ BoxPreordering n r := by
  obtain ⟨A, c, hA, hc, hcertificate⟩ := putinarCubeQuarticDegreeBound hn
  refine ⟨A, c, hA, hc, ?_⟩
  intro h d epsilon hdegree hnonneg hepsilon
  obtain ⟨r, hr, hmem⟩ := hcertificate h d epsilon hdegree hnonneg hepsilon
  exact ⟨r, hr, BoxQuadraticModule_subset_BoxPreordering hmem⟩

theorem putinarCubeQuarticRate_lasserreError {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        p.totalDegree ≤ d → c * max d 1 ≤ r →
          ∃ b : ℝ,
            lasserre_bound_box_qm p r = (b : WithBot ℝ) ∧
            0 ≤ polyMin p - b ∧
            polyMin p - b ≤
              A * ((max d 1 : ℕ) : ℝ) ^ 6 *
                (polyMax p - polyMin p) / (r : ℝ) ^ 4 :=
  putinarExplicitRate_lasserreGap hn

end OptimalConvergenceRates.QuarticConvergence.MainResultsProofs

end
