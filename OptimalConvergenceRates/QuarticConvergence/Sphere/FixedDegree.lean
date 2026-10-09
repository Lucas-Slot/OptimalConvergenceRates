/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/FixedDegree.lean

  Fixed-degree reduction of the quartic certificate theorem, including the
  finite-dimensional C6/oscillation comparison.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.QuarticRate

open MvPolynomial

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence
open SphereBallTransfers


/-- Uniform comparison of the explicit sphere `C6` norm with oscillation on ambient
polynomials of degree at most `d`. -/
def HasFixedDegreeC6Comparison (n d : ℕ) : Prop :=
  ∃ B : ℝ, 0 < B ∧
    ∀ f : MvPolynomial (Fin n) ℝ, f.totalDegree ≤ d →
      sphereC6Norm (f - MvPolynomial.C (spherePolyMin f)) ≤
        B * spherePolyOscillation f

/-- On each fixed ambient-degree space, the rotational `C6` norm is controlled by
oscillation. This proves the finite-dimensional norm-equivalence argument. -/
theorem fixedDegreeC6Comparison {n d : ℕ} (hn : 3 ≤ n) :
    HasFixedDegreeC6Comparison n d := by
  classical
  have hnpos : 0 < n := by omega
  let R := boundedSphereRestriction n d
  have hRrange : R.range = ⊤ :=
    LinearMap.range_eq_top.mpr (boundedSphereRestriction_surjective n d)
  obtain ⟨s, hs⟩ := R.exists_rightInverse_of_surjective hRrange
  let q : Seminorm ℝ (spherePolynomialSpace n d) :=
    (restrictedSphereC6Seminorm hnpos d).comp s
  obtain ⟨B, hB, hbound⟩ := seminorm_bound_of_finiteDimensional q
  refine ⟨B, hB, ?_⟩
  intro f hf
  let g : MvPolynomial.restrictTotalDegree (Fin n) ℝ d :=
    ⟨f - MvPolynomial.C (spherePolyMin f),
      (MvPolynomial.mem_restrictTotalDegree (Fin n) d _).mpr
        ((MvPolynomial.totalDegree_sub_C_le f _).trans hf)⟩
  let v : spherePolynomialSpace n d := R g
  have hsv : R (s v) = v := by
    have h := LinearMap.congr_fun hs v
    simpa using h
  have hrestr :
      sphereRestrictionLinear n (s v).1 = sphereRestrictionLinear n g.1 := by
    have h := congrArg Subtype.val hsv
    simpa only [R, v, boundedSphereRestriction_apply] using h
  have hzero : sphereRestrictionLinear n ((s v).1 - g.1) = 0 := by
    rw [map_sub, hrestr, sub_self]
  obtain ⟨a, ha⟩ :=
    sphereRestrictionKernelPrincipal_of_three_le hn ((s v).1 - g.1) hzero
  have hrep : (s v).1 = g.1 + sphereRelation n * a := by
    calc
      (s v).1 = ((s v).1 - g.1) + g.1 := by ring
      _ = sphereRelation n * a + g.1 := by rw [ha]
      _ = g.1 + sphereRelation n * a := add_comm _ _
  have hqeq : q v = sphereC6Norm g.1 := by
    change sphereC6Norm (s v).1 = sphereC6Norm g.1
    rw [hrep, sphereC6Norm_add_relation_mul]
  have hvnorm : ‖v‖ = sphereSupNorm g.1 := by
    change ‖sphereRestrictionLinear n g.1‖ = sphereSupNorm g.1
    exact norm_sphereRestrictionLinear_eq hnpos g.1
  calc
    sphereC6Norm (f - MvPolynomial.C (spherePolyMin f)) = q v := by
      exact hqeq.symm
    _ ≤ B * ‖v‖ := hbound v
    _ = B * spherePolyOscillation f := by
      rw [hvnorm]
      exact congrArg (B * ·) (sphereSupNorm_center_eq_oscillation hnpos f)

/-- Fixed-degree quartic sphere certificate controlled only by the sphere
maximum and minimum. -/
theorem quarticSphereFixedDegreeCertificate {n d : ℕ} (hn : 3 ≤ n) :
    ∃ (C : ℝ) (r₀ : ℕ),
      0 < C ∧ 0 < r₀ ∧
      ∀ (f : MvPolynomial (Fin n) ℝ) (r : ℕ),
        f.totalDegree ≤ d → r₀ ≤ r →
          SphereSOSMod
            (f - MvPolynomial.C (spherePolyMin f) +
              MvPolynomial.C
                (C * (spherePolyMax f - spherePolyMin f) /
                  (r : ℝ) ^ 4))
            r := by
  obtain ⟨A, c, hA, hc, hcert⟩ := quarticSphereCertificate hn
  obtain ⟨B, hB, hcompare⟩ := fixedDegreeC6Comparison hn
  refine ⟨A * B, c * max d 1, mul_pos hA hB, Nat.mul_pos hc (by omega), ?_⟩
  intro f r hdeg hr
  have hbase := hcert f d r hdeg hr
  have hrpos : 0 < r := lt_of_lt_of_le (Nat.mul_pos hc (by omega)) hr
  have hden : 0 < (r : ℝ) ^ 4 := pow_pos (Nat.cast_pos.mpr hrpos) _
  have hcompare' :
      sphereC6Norm (f - MvPolynomial.C (spherePolyMin f)) ≤
        B * (spherePolyMax f - spherePolyMin f) := by
    simpa only [spherePolyOscillation] using hcompare f hdeg
  have hnum :
      A * sphereC6Norm (f - MvPolynomial.C (spherePolyMin f)) ≤
        (A * B) * (spherePolyMax f - spherePolyMin f) := by
    calc
      A * sphereC6Norm (f - MvPolynomial.C (spherePolyMin f)) ≤
          A * (B * (spherePolyMax f - spherePolyMin f)) :=
        mul_le_mul_of_nonneg_left hcompare' hA.le
      _ = (A * B) * (spherePolyMax f - spherePolyMin f) := by ring
  have hquot :
      A * sphereC6Norm (f - MvPolynomial.C (spherePolyMin f)) /
          (r : ℝ) ^ 4 ≤
        (A * B) * (spherePolyMax f - spherePolyMin f) /
          (r : ℝ) ^ 4 :=
    (div_le_div_iff_of_pos_right hden).2 hnum
  have hconst :
      SphereSOSMod
        (MvPolynomial.C
          ((A * B) * (spherePolyMax f - spherePolyMin f) /
              (r : ℝ) ^ 4 -
            A * sphereC6Norm
              (f - MvPolynomial.C (spherePolyMin f)) / (r : ℝ) ^ 4) :
          MvPolynomial (Fin n) ℝ)
        r :=
    sphereSOSMod_const (sub_nonneg.mpr hquot)
  have hadd := hbase.add hconst
  convert hadd using 1
  simp only [map_sub]
  ring

/-- The fixed-degree hierarchy estimate follows from the main certificate statement and
the finite-dimensional norm comparison. -/
theorem quarticSphereFixedDegree_of_comparison {n d : ℕ} (hn : 3 ≤ n)
    (hmain : QuarticSphereCertificateStatement n)
    (hcompare : HasFixedDegreeC6Comparison n d) :
    ∃ (C : ℝ) (r₀ : ℕ),
      0 < C ∧ 0 < r₀ ∧
      ∀ (f : MvPolynomial (Fin n) ℝ) (r : ℕ),
        f.totalDegree ≤ d → r₀ ≤ r →
          ∃ b : ℝ,
            sphereSOSBound f r = (b : WithBot ℝ) ∧
            0 ≤ spherePolyMin f - b ∧
            spherePolyMin f - b ≤ C * spherePolyOscillation f / (r : ℝ) ^ 4 := by
  obtain ⟨A, c, hA, hc, hcert⟩ := hmain
  obtain ⟨B, hB, hcompare⟩ := hcompare
  refine ⟨A * B, c * max d 1, mul_pos hA hB, Nat.mul_pos hc (by omega), ?_⟩
  intro f r hdeg hr
  obtain ⟨b, hb, herr_nonneg, herr⟩ :=
    sphereSOSBound_error_of_certificate (sphereSet_nonempty (by omega)) f r _
      (hcert f d r hdeg hr)
  refine ⟨b, hb, herr_nonneg, herr.trans ?_⟩
  have hrpos : 0 < r := lt_of_lt_of_le (Nat.mul_pos hc (by omega)) hr
  have hden : 0 < (r : ℝ) ^ 4 := pow_pos (Nat.cast_pos.mpr hrpos) _
  have hnum :
      A * sphereC6Norm (f - MvPolynomial.C (spherePolyMin f)) ≤
        A * (B * spherePolyOscillation f) :=
    mul_le_mul_of_nonneg_left (hcompare f hdeg) hA.le
  calc
    A * sphereC6Norm (f - MvPolynomial.C (spherePolyMin f)) / (r : ℝ) ^ 4
        ≤ A * (B * spherePolyOscillation f) / (r : ℝ) ^ 4 :=
          (div_le_div_iff_of_pos_right hden).2 hnum
    _ = (A * B) * spherePolyOscillation f / (r : ℝ) ^ 4 := by ring

/-- Approximation, degree-linear repair, and the finite-degree norm comparison together
give the fixed-degree quartic hierarchy estimate. -/
theorem quarticSphereFixedDegree_of_approximation_repair_comparison
    {n d A b k₀ : ℕ} {C₀ : ℝ} (hn : 3 ≤ n)
    (hA : 1 ≤ A) (hb : 1 ≤ b) (hC₀ : 0 < C₀)
    (happrox : ∀ F : MvPolynomial (Fin n) ℝ, SphereNonnegative F →
      HasQuarticSOSApproximation F (sphereC6Norm F) C₀ b k₀)
    (hrepair : HasDegreeLinearRepair (n := n) A)
    (hcompare : HasFixedDegreeC6Comparison n d) :
    ∃ (C : ℝ) (r₀ : ℕ),
      0 < C ∧ 0 < r₀ ∧
      ∀ (f : MvPolynomial (Fin n) ℝ) (r : ℕ),
        f.totalDegree ≤ d → r₀ ≤ r →
          ∃ q : ℝ,
            sphereSOSBound f r = (q : WithBot ℝ) ∧
            0 ≤ spherePolyMin f - q ∧
            spherePolyMin f - q ≤
              C * spherePolyOscillation f / (r : ℝ) ^ 4 :=
  quarticSphereFixedDegree_of_comparison hn
    (quarticSphereCertificateStatement_of_approximation_repair
      hn hA hb hC₀ happrox hrepair)
    hcompare

/-- The unconditional fixed-degree quartic hierarchy estimate. -/
theorem quarticSphereFixedDegree {n d : ℕ} (hn : 3 ≤ n) :
    ∃ (C : ℝ) (r₀ : ℕ),
      0 < C ∧ 0 < r₀ ∧
      ∀ (f : MvPolynomial (Fin n) ℝ) (r : ℕ),
        f.totalDegree ≤ d → r₀ ≤ r →
          ∃ b : ℝ,
            sphereSOSBound f r = (b : WithBot ℝ) ∧
            0 ≤ spherePolyMin f - b ∧
            spherePolyMin f - b ≤
              C * spherePolyOscillation f / (r : ℝ) ^ 4 :=
  quarticSphereFixedDegree_of_comparison hn
    (quarticSphereCertificate hn) (fixedDegreeC6Comparison hn)

end QuarticConvergence
end OptimalConvergenceRates

end
