/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/QuarticRate.lean

  Quartic sphere certificates and their hierarchy consequences, including nonnegative,
  fixed-objective, and centered formulations.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Assembly
import OptimalConvergenceRates.QuarticConvergence.Sphere.Approximation
import OptimalConvergenceRates.QuarticConvergence.Sphere.Hierarchy
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Repair

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

/-- The uniform centered quartic certificate statement on the sphere. -/
def QuarticSphereCertificateStatement (n : ℕ) : Prop :=
  ∃ (A : ℝ) (c : ℕ),
    0 < A ∧ 0 < c ∧
    ∀ (f : MvPolynomial (Fin n) ℝ) (d r : ℕ),
      f.totalDegree ≤ d → c * max d 1 ≤ r →
        SphereSOSMod
          (f - MvPolynomial.C (spherePolyMin f) +
            MvPolynomial.C
              (A * sphereC6Norm (f - MvPolynomial.C (spherePolyMin f)) / (r : ℝ) ^ 4))
          r

/-- The direct nonnegative form of the sphere certificate statement. -/
def QuarticSphereCertificateOfNonnegStatement (n : ℕ) : Prop :=
  ∃ (A : ℝ) (c : ℕ),
    0 < A ∧ 0 < c ∧
    ∀ (F : MvPolynomial (Fin n) ℝ) (d r : ℕ),
      F.totalDegree ≤ d → SphereNonnegative F → c * max d 1 ≤ r →
        SphereSOSMod
          (F + MvPolynomial.C (A * sphereC6Norm F / (r : ℝ) ^ 4)) r

/-- The two substantive analytic interfaces imply the public nonnegative certificate
statement at every sufficiently large hierarchy order.  This is the exact algebraic
assembly point: later analytic files only need to provide the uniform approximation
constants and the degree-linear repair theorem. -/
theorem quarticSphereCertificateOfNonneg_of_approximation_repair
    {n A b k₀ : ℕ} {C : ℝ} (hn : 3 ≤ n)
    (hA : 1 ≤ A) (hb : 1 ≤ b) (hC : 0 < C)
    (happrox : ∀ F : MvPolynomial (Fin n) ℝ, SphereNonnegative F →
      HasQuarticSOSApproximation F (sphereC6Norm F) C b k₀)
    (hrepair : HasDegreeLinearRepair (n := n) A) :
    QuarticSphereCertificateOfNonnegStatement n := by
  let s : ℕ := 2 * A * b
  refine
    ⟨2 * C * (((2 * s : ℕ) : ℝ) ^ 4), s * max k₀ 1, ?_, ?_, ?_⟩
  · exact mul_pos (mul_pos (by norm_num) hC) (by positivity)
  · exact Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
      (by omega)
  · intro F d r hdeg hF hr
    let L : ℕ := max d 1
    have hL : 1 ≤ L := by
      exact le_max_right d 1
    have hk₀Bound : k₀ ≤ max k₀ 1 * L := by
      calc
        k₀ ≤ max k₀ 1 := le_max_left _ _
        _ ≤ max k₀ 1 * L := by
          simpa only [Nat.mul_one] using Nat.mul_le_mul_left (max k₀ 1) hL
    have hLBound : L ≤ max k₀ 1 * L := by
      simpa only [one_mul] using
        Nat.mul_le_mul_right L (le_max_right k₀ 1)
    have hinner : max k₀ L ≤ max k₀ 1 * L :=
      max_le hk₀Bound hLBound
    have hassembly : s * max k₀ (max d 1) ≤ r := by
      calc
        s * max k₀ (max d 1) = s * max k₀ L := by rfl
        _ ≤ s * (max k₀ 1 * L) := Nat.mul_le_mul_left s hinner
        _ = (s * max k₀ 1) * max d 1 := by
          simp only [L, Nat.mul_assoc]
        _ ≤ r := by simpa only [s] using hr
    have hcert :=
      assembleQuarticCertificateAtArbitraryOrder hA hb hC.le
        (sphereC6Norm_nonneg (by omega) F) hdeg hassembly
        (happrox F hF) hrepair
    convert hcert using 1
    dsimp only [s]
    ring_nf

/-- Public nonnegative certificate assembly from quartic approximation and concrete
positive near-identity operators on the finite-dimensional sphere polynomial spaces. -/
theorem quarticSphereCertificateOfNonneg_of_approximation_spherePolynomialKernels
    {n A b k₀ : ℕ} {C : ℝ} (hn : 3 ≤ n)
    (hA : 1 ≤ A) (hb : 1 ≤ b) (hC : 0 < C)
    (happrox : ∀ F : MvPolynomial (Fin n) ℝ, SphereNonnegative F →
      HasQuarticSOSApproximation F (sphereC6Norm F) C b k₀)
    (hkernel : SphereRestrictionKernelPrincipal n)
    (hK : HasSpherePolynomialKernelRepair (n := n) A) :
    QuarticSphereCertificateOfNonnegStatement n :=
  quarticSphereCertificateOfNonneg_of_approximation_repair
    hn hA hb hC happrox
      (hasDegreeLinearRepair_of_spherePolynomialKernels
        (by omega) hkernel hK)

/-- The unconditional nonnegative quartic sphere certificate, assembled from the analytic
approximation and polynomial-kernel repair results. -/
theorem quarticSphereCertificateOfNonneg {n : ℕ} (hn : 3 ≤ n) :
    QuarticSphereCertificateOfNonnegStatement n := by
  obtain ⟨C, b, k₀, hC, hb, happrox⟩ := quarticSOSApproximation hn
  obtain ⟨A, hA, hK⟩ := spherePolynomialKernelRepair hn
  exact quarticSphereCertificateOfNonneg_of_approximation_spherePolynomialKernels
    hn hA hb hC happrox (sphereRestrictionKernelPrincipal_of_three_le hn) hK


/-- The direct nonnegative certificate theorem implies the centered formulation used by
the hierarchy. -/
theorem quarticSphereCertificateStatement_of_nonnegative {n : ℕ}
    (hmain : QuarticSphereCertificateOfNonnegStatement n) :
    QuarticSphereCertificateStatement n := by
  obtain ⟨A, c, hA, hc, hcert⟩ := hmain
  refine ⟨A, c, hA, hc, ?_⟩
  intro f d r hdeg hr
  apply hcert (f - MvPolynomial.C (spherePolyMin f)) d r
  · exact (MvPolynomial.totalDegree_sub _ _).trans (max_le hdeg (by simp))
  · exact centerAtSphereMin_nonnegative f
  · exact hr

/-- The unconditional centered quartic sphere certificate. -/
theorem quarticSphereCertificate {n : ℕ} (hn : 3 ≤ n) :
    QuarticSphereCertificateStatement n :=
  quarticSphereCertificateStatement_of_nonnegative
    (quarticSphereCertificateOfNonneg hn)

/-- The approximation and repair interfaces imply the centered certificate statement. -/
theorem quarticSphereCertificateStatement_of_approximation_repair
    {n A b k₀ : ℕ} {C : ℝ} (hn : 3 ≤ n)
    (hA : 1 ≤ A) (hb : 1 ≤ b) (hC : 0 < C)
    (happrox : ∀ F : MvPolynomial (Fin n) ℝ, SphereNonnegative F →
      HasQuarticSOSApproximation F (sphereC6Norm F) C b k₀)
    (hrepair : HasDegreeLinearRepair (n := n) A) :
    QuarticSphereCertificateStatement n :=
  quarticSphereCertificateStatement_of_nonnegative
    (quarticSphereCertificateOfNonneg_of_approximation_repair
      hn hA hb hC happrox hrepair)

/-- The uniform nonnegative certificate target implies fixed-objective quartic convergence
with a strictly positive numerator constant. -/
theorem quarticSphereFixedObjective_of_nonnegativeStatement {n : ℕ} (hn : 3 ≤ n)
    (hmain : QuarticSphereCertificateOfNonnegStatement n)
    (F : MvPolynomial (Fin n) ℝ) (hF : SphereNonnegative F) :
    ∃ (C_F : ℝ) (r_F : ℕ),
      0 < C_F ∧ 0 < r_F ∧
      ∀ r : ℕ, max r_F 1 ≤ r →
        SphereSOSMod (F + MvPolynomial.C (C_F / (r : ℝ) ^ 4)) r := by
  obtain ⟨A, c, hA, hc, hcert⟩ := hmain
  refine ⟨A * (sphereC6Norm F + 1), c * max F.totalDegree 1, ?_, ?_, ?_⟩
  · exact mul_pos hA (by have hnorm := sphereC6Norm_nonneg (by omega) F; linarith)
  · exact Nat.mul_pos hc (by omega)
  · intro r hr
    have hrmain : c * max F.totalDegree 1 ≤ r :=
      (le_max_left _ _).trans hr
    have hrpos : 0 < r := lt_of_lt_of_le (Nat.mul_pos hc (by omega)) hrmain
    have hden : 0 < (r : ℝ) ^ 4 := pow_pos (Nat.cast_pos.mpr hrpos) _
    have hbase := hcert F F.totalDegree r le_rfl hF hrmain
    have hnum :
        A * sphereC6Norm F ≤ A * (sphereC6Norm F + 1) := by
      nlinarith
    have hquot :
        A * sphereC6Norm F / (r : ℝ) ^ 4 ≤
          A * (sphereC6Norm F + 1) / (r : ℝ) ^ 4 :=
      (div_le_div_iff_of_pos_right hden).2 hnum
    have hconst :
        SphereSOSMod
          (MvPolynomial.C
            (A * (sphereC6Norm F + 1) / (r : ℝ) ^ 4 -
              A * sphereC6Norm F / (r : ℝ) ^ 4) :
            MvPolynomial (Fin n) ℝ)
          r :=
      sphereSOSMod_const (sub_nonneg.mpr hquot)
    have hadd := hbase.add hconst
    convert hadd using 1
    simp only [map_sub]
    ring

/-- For each fixed nonnegative objective, the unrestricted sphere certificate rate is
quartic. -/
theorem quarticSphereFixedObjective {n : ℕ} (hn : 3 ≤ n)
    (F : MvPolynomial (Fin n) ℝ) (hF : SphereNonnegative F) :
    ∃ (C_F : ℝ) (r_F : ℕ),
      0 < C_F ∧ 0 < r_F ∧
      ∀ r : ℕ, max r_F 1 ≤ r →
        SphereSOSMod (F + MvPolynomial.C (C_F / (r : ℝ) ^ 4)) r :=
  quarticSphereFixedObjective_of_nonnegativeStatement hn
    (quarticSphereCertificateOfNonneg hn) F hF


/-- Once the exact certificate statement is proved, it immediately controls the actual
`WithBot` hierarchy bound. -/
theorem sphereHierarchyError_of_quarticCertificateStatement {n : ℕ} (hn : 3 ≤ n)
    (hmain : QuarticSphereCertificateStatement n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (f : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        f.totalDegree ≤ d → c * max d 1 ≤ r →
          ∃ b : ℝ,
            sphereSOSBound f r = (b : WithBot ℝ) ∧
            0 ≤ spherePolyMin f - b ∧
            spherePolyMin f - b ≤
              A * sphereC6Norm (f - MvPolynomial.C (spherePolyMin f)) / (r : ℝ) ^ 4 := by
  obtain ⟨A, c, hA, hc, hcert⟩ := hmain
  refine ⟨A, c, hA, hc, ?_⟩
  intro f d r hdeg hr
  exact sphereSOSBound_error_of_certificate (sphereSet_nonempty (by omega)) f r _
    (hcert f d r hdeg hr)

/-- The actual `WithBot`-valued sphere SOS hierarchy satisfies the quartic error estimate. -/
theorem quarticSphereHierarchyError {n : ℕ} (hn : 3 ≤ n) :
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
  sphereHierarchyError_of_quarticCertificateStatement hn
    (quarticSphereCertificate hn)

/-- The same two analytic interfaces imply the explicit error estimate for the actual
`WithBot`-valued sphere SOS hierarchy. -/
theorem quarticSphereHierarchyError_of_approximation_repair
    {n A b k₀ : ℕ} {C : ℝ} (hn : 3 ≤ n)
    (hA : 1 ≤ A) (hb : 1 ≤ b) (hC : 0 < C)
    (happrox : ∀ F : MvPolynomial (Fin n) ℝ, SphereNonnegative F →
      HasQuarticSOSApproximation F (sphereC6Norm F) C b k₀)
    (hrepair : HasDegreeLinearRepair (n := n) A) :
    ∃ (A' : ℝ) (c : ℕ),
      0 < A' ∧ 0 < c ∧
      ∀ (f : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        f.totalDegree ≤ d → c * max d 1 ≤ r →
          ∃ q : ℝ,
            sphereSOSBound f r = (q : WithBot ℝ) ∧
            0 ≤ spherePolyMin f - q ∧
            spherePolyMin f - q ≤
              A' * sphereC6Norm
                (f - MvPolynomial.C (spherePolyMin f)) / (r : ℝ) ^ 4 :=
  sphereHierarchyError_of_quarticCertificateStatement hn
    (quarticSphereCertificateStatement_of_approximation_repair
      hn hA hb hC happrox hrepair)

end QuarticConvergence
end OptimalConvergenceRates

end
