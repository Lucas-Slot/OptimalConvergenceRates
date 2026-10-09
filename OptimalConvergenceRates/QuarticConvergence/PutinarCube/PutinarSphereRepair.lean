/-
  Bounded-positivity adapter from degree-linear sphere repair to an SOS
  certificate for a polynomial bounded away from zero on the sphere.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Repair

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

variable {n A D : ℕ}

/-! ## The scalar interval estimate -/

/-- The scalar inequality behind the repair. On the interval from L/2 to
7L/2, subtracting 2L/3 from t - t^2/(4L) leaves an error of absolute value
at most L/3. -/
theorem abs_putinarSphereRepair_scalar_le
    {t L : ℝ} (hL : 0 < L) (hlo : L / 2 ≤ t) (hhi : t ≤ 7 * L / 2) :
    |t - t ^ 2 / (4 * L) - 2 * L / 3| ≤ L / 3 := by
  have hden : 0 < 4 * L := mul_pos (by norm_num) hL
  have hform :
      t - t ^ 2 / (4 * L) = (4 * L * t - t ^ 2) / (4 * L) := by
    field_simp
  have hprod : 0 ≤ (t - L / 2) * (7 * L / 2 - t) :=
    mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  have hlower : L / 3 ≤ t - t ^ 2 / (4 * L) := by
    rw [hform, le_div_iff₀ hden]
    nlinarith [sq_nonneg L]
  have hupper : t - t ^ 2 / (4 * L) ≤ L := by
    rw [hform, div_le_iff₀ hden]
    nlinarith [sq_nonneg (t - 2 * L)]
  rw [abs_le]
  constructor <;> nlinarith


/-! ## Polynomial repair pieces -/

/-- The concave quadratic transform R = P - P^2/(4L). -/
def putinarSphereRepairR
    (P : MvPolynomial (Fin n) ℝ) (L : ℝ) : MvPolynomial (Fin n) ℝ :=
  P - MvPolynomial.C (1 / (4 * L)) * P ^ 2

/-- The centered residual W = R - 2L/3. -/
def putinarSphereRepairW
    (P : MvPolynomial (Fin n) ℝ) (L : ℝ) : MvPolynomial (Fin n) ℝ :=
  putinarSphereRepairR P L - MvPolynomial.C (2 * L / 3)

/-- Evaluation of the quadratic transform. -/
theorem eval_putinarSphereRepairR
    (P : MvPolynomial (Fin n) ℝ) (L : ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval x (putinarSphereRepairR P L) =
      MvPolynomial.eval x P - MvPolynomial.eval x P ^ 2 / (4 * L) := by
  simp [putinarSphereRepairR, div_eq_mul_inv]
  ring

/-- Evaluation of the centered residual. -/
theorem eval_putinarSphereRepairW
    (P : MvPolynomial (Fin n) ℝ) (L : ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval x (putinarSphereRepairW P L) =
      MvPolynomial.eval x P - MvPolynomial.eval x P ^ 2 / (4 * L) -
        2 * L / 3 := by
  rw [putinarSphereRepairW, map_sub, eval_putinarSphereRepairR]
  simp

/-- The interval hypothesis bounds the centered residual in sphere sup norm. -/
theorem sphereSupNorm_putinarSphereRepairW_le
    (hn : 0 < n) {P : MvPolynomial (Fin n) ℝ} {L : ℝ} (hL : 0 < L)
    (hP : ∀ x ∈ sphereSet n,
      L / 2 ≤ MvPolynomial.eval x P ∧
        MvPolynomial.eval x P ≤ 7 * L / 2) :
    sphereSupNorm (putinarSphereRepairW P L) ≤ L / 3 := by
  apply sphereSupNorm_le_of_bound hn
  intro x hx
  rw [eval_putinarSphereRepairW]
  exact abs_putinarSphereRepair_scalar_le hL (hP x hx).1 (hP x hx).2

/-- The quadratic transform has total degree at most twice that of the input bound. -/
theorem putinarSphereRepairR_totalDegree_le
    {P : MvPolynomial (Fin n) ℝ} {L : ℝ} (hPdeg : P.totalDegree ≤ D) :
    (putinarSphereRepairR P L).totalDegree ≤ 2 * D := by
  unfold putinarSphereRepairR
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · omega
  · calc
      (MvPolynomial.C (1 / (4 * L)) * P ^ 2).totalDegree ≤
          (MvPolynomial.C (1 / (4 * L))).totalDegree +
            (P ^ 2).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + 2 * P.totalDegree := by
        exact Nat.add_le_add (by rw [MvPolynomial.totalDegree_C])
          (MvPolynomial.totalDegree_pow P 2)
      _ ≤ 2 * D := by omega

/-- Centering by a constant does not exceed the twice-input degree bound. -/
theorem putinarSphereRepairW_totalDegree_le
    {P : MvPolynomial (Fin n) ℝ} {L : ℝ} (hPdeg : P.totalDegree ≤ D) :
    (putinarSphereRepairW P L).totalDegree ≤ 2 * D := by
  unfold putinarSphereRepairW
  exact (MvPolynomial.totalDegree_sub _ _).trans
    (max_le (putinarSphereRepairR_totalDegree_le hPdeg) (by simp))


/-! ## Bounded positivity from a supplied repair -/

/-- A degree-linear repair converts a polynomial bounded between L/2 and
7L/2 on the sphere into a sphere SOS certificate. The order is a bound on
the square-root degrees, following the repository definition of SphereSOSMod. -/
theorem sphereSOSMod_of_bounded_positive_of_degreeLinearRepair
    (hn : 0 < n) (hA : 1 ≤ A) (hD : 1 ≤ D)
    {P : MvPolynomial (Fin n) ℝ} {L : ℝ}
    (hPdeg : P.totalDegree ≤ D) (hL : 0 < L)
    (hP : ∀ x ∈ sphereSet n,
      L / 2 ≤ MvPolynomial.eval x P ∧
        MvPolynomial.eval x P ≤ 7 * L / 2)
    (hrepair : HasDegreeLinearRepair (n := n) A) :
    SphereSOSMod P (2 * A * D) := by
  let R := putinarSphereRepairR P L
  let W := putinarSphereRepairW P L
  have hWdeg : W.totalDegree ≤ 2 * D := by
    simpa only [W] using putinarSphereRepairW_totalDegree_le hPdeg
  have hWnorm : sphereSupNorm W ≤ L / 3 := by
    simpa only [W] using sphereSupNorm_putinarSphereRepairW_le hn hL hP
  have hrepairW0 :
      SphereSOSMod (W + MvPolynomial.C (2 * sphereSupNorm W)) (A * (2 * D)) :=
    hrepair (2 * D) W (by omega) hWdeg
  have hrepairW :
      SphereSOSMod (W + MvPolynomial.C (2 * sphereSupNorm W)) (2 * A * D) := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hrepairW0
  have hextra : 0 ≤ 2 * L / 3 - 2 * sphereSupNorm W := by
    nlinarith
  have hextraCert :
      SphereSOSMod
        (MvPolynomial.C (2 * L / 3 - 2 * sphereSupNorm W) :
          MvPolynomial (Fin n) ℝ)
        (2 * A * D) :=
    sphereSOSMod_const hextra
  have hRcert : SphereSOSMod R (2 * A * D) := by
    have hsum := hrepairW.add hextraCert
    convert hsum using 1
    dsimp [W, R, putinarSphereRepairW]
    simp only [map_sub]
    ring
  have hcoefficient : 0 ≤ 1 / (4 * L) := by
    exact (one_div_pos.mpr (mul_pos (by norm_num) hL)).le
  have hsquare0 :
      SphereSOSMod
        (MvPolynomial.C (1 / (4 * L)) * P ^ 2 :
          MvPolynomial (Fin n) ℝ)
        P.totalDegree := by
    have hconstant :
        SphereSOSMod
          (MvPolynomial.C (1 / (4 * L)) : MvPolynomial (Fin n) ℝ)
          0 :=
      sphereSOSMod_const hcoefficient
    simpa using hconstant.mul_sq P
  have hfactor : 1 ≤ 2 * A := hA.trans (by omega)
  have hDorder : D ≤ 2 * A * D := by
    simpa only [one_mul, Nat.mul_assoc] using Nat.mul_le_mul_right D hfactor
  have hsquare :
      SphereSOSMod
        (MvPolynomial.C (1 / (4 * L)) * P ^ 2 :
          MvPolynomial (Fin n) ℝ)
        (2 * A * D) :=
    hsquare0.mono (hPdeg.trans hDorder)
  have hsum := hRcert.add hsquare
  convert hsum using 1
  dsimp [R, putinarSphereRepairR]
  ring


/-! ## Concrete dimension-only repair constant -/

/-- In every ambient dimension at least three, the concrete polynomial-kernel
repair supplies a dimension-only natural constant A for the bounded-positivity
certificate. -/
theorem exists_dimensionConstant_boundedPositiveSphereSOSMod
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ A : ℕ, 1 ≤ A ∧
      ∀ (D : ℕ) (P : MvPolynomial (Fin n) ℝ) (L : ℝ),
        1 ≤ D →
        P.totalDegree ≤ D →
        0 < L →
        (∀ x ∈ sphereSet n,
          L / 2 ≤ MvPolynomial.eval x P ∧
            MvPolynomial.eval x P ≤ 7 * L / 2) →
        SphereSOSMod P (2 * A * D) := by
  obtain ⟨A, hA, hK⟩ := spherePolynomialKernelRepair hn
  have hrepair : HasDegreeLinearRepair (n := n) A :=
    hasDegreeLinearRepair_of_spherePolynomialKernels (by omega)
      (sphereRestrictionKernelPrincipal_of_three_le hn) hK
  refine ⟨A, hA, ?_⟩
  intro D P L hD hPdeg hL hP
  exact sphereSOSMod_of_bounded_positive_of_degreeLinearRepair
    (by omega) hA hD hPdeg hL hP hrepair

end QuarticConvergence
end OptimalConvergenceRates

end
