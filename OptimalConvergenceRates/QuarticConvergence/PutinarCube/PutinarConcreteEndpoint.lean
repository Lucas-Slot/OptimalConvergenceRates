/-
  Concrete assembly of the general Putinar endpoint.

  All algebraic, approximation, normalization, repair, and canonical-order
  bookkeeping is unconditional.  The sole remaining input is the uniform
  weighted parity estimate for the controlled roots constructed in
  `ControlledRoots`.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarControlledAssembly
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarNormalizedCertificate
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarRepair

open MvPolynomial Finset Set

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- The remaining analytic statement, isolated at the exact interface used
by the concrete Putinar assembly.

For every dimension-only controlled-root package supplied by the existing
sphere construction, it asks for one nonnegative constant, uniform in the
normalized nonnegative polynomial, scale, and chosen controlled root data.
The constant may depend on the fixed dimension and on the root-construction
constant `C`, but never on the polynomial, scale, or number of retained
roots. -/
def HasUniformControlledWeightedParityBound (n : ℕ) : Prop :=
  ∀ (C : ℝ) (k₀ : ℕ), 0 < C → 1 ≤ k₀ →
    HasFiniteControlledRootData (2 * n + 1) C k₀ →
      ∃ H : ℝ, 0 ≤ H ∧
        ∀ (h : MvPolynomial (Fin n) ℝ),
          IsNonnegOn h (Hypercube n) → cubeSphereC6Norm n h ≤ 1 →
            ∀ k, k₀ ≤ k →
              ∀ data : FiniteControlledRootData
                (2 * n + 1) C k (cubeSphereLift n h),
                data.HasWeightedParityBound H

/-- A rootwise estimate proportional to the controlled-root error constant
is a convenient sufficient form of the remaining analytic statement.  This
is the form naturally produced by the overlap/jet budget in
`FiniteControlledRootData`. -/
theorem hasUniformControlledWeightedParityBound_of_mul_controlledConstant
    {n : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ {C : ℝ} {k : ℕ} {h : MvPolynomial (Fin n) ℝ},
      ∀ data : FiniteControlledRootData
        (2 * n + 1) C k (cubeSphereLift n h),
        data.HasWeightedParityBound (K * C)) :
    HasUniformControlledWeightedParityBound n := by
  intro C k₀ hC _hk₀ _hdata
  refine ⟨K * C, mul_nonneg hK hC.le, ?_⟩
  intro h _hnonnegative _hnorm k _hk data
  exact hbound data

/-- The controlled-root existence theorem and the weighted parity estimate
produce all parameters of the normalized quartic quadratic-module
approximation family. -/
theorem exists_normalizedQuarticBoxQMApproximation_of_controlledRoots
    {n : ℕ} (hn : 0 < n)
    (hweighted : HasUniformControlledWeightedParityBound n) :
    ∃ (B k₀ : ℕ) (L₀ : ℝ),
      1 ≤ B ∧ 1 ≤ k₀ ∧ 0 < L₀ ∧
        HasNormalizedQuarticBoxQMApproximation n B k₀ L₀ := by
  obtain ⟨C, k₀, hC, hk₀, hdata⟩ :=
    finiteControlledRootData (n := 2 * n + 1) (by omega)
  obtain ⟨H, hH, hparity⟩ := hweighted C k₀ hC hk₀ hdata
  let B : ℕ := controlledPutinarApproximationOrderCoefficient n
  let L₀ : ℝ := putinarWeightedApproximationConstant n
    (controlledCircleRootDegreeCoefficient n) C H
  have hB : 1 ≤ B := by
    exact controlledPutinarApproximationOrderCoefficient_one_le n
  have hL₀ : 0 < L₀ := by
    dsimp only [L₀, putinarWeightedApproximationConstant]
    have hcorrection : 0 ≤
        putinarCorrectionRateConstant n
          (controlledCircleRootDegreeCoefficient n : ℝ) * H :=
      mul_nonneg
        (putinarCorrectionRateConstant_nonneg n (Nat.cast_nonneg _)) hH
    linarith
  refine ⟨B, k₀, L₀, hB, hk₀, hL₀, ?_⟩
  dsimp only [B, L₀]
  exact hasNormalizedQuarticBoxQMApproximation_of_controlledRoots
    hn hk₀ hdata hparity

/-- Conditional only on the named weighted-parity analytic statement, every
nonnegative polynomial on the cube has a canonical Putinar certificate with
the explicit all-polynomial `O(r⁻⁴)` error and degree-six dependence. -/
theorem putinarExplicitRate_certificate_of_controlledRoots
    {n : ℕ} (hn : 0 < n)
    (hweighted : HasUniformControlledWeightedParityBound n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (h : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        h.totalDegree ≤ d → IsNonnegOn h (Hypercube n) →
          c * max d 1 ≤ r →
          h + MvPolynomial.C
              (A * ((max d 1 : ℕ) : ℝ) ^ 6 * polySupNorm h /
                (r : ℝ) ^ 4) ∈
            BoxQuadraticModule n r := by
  obtain ⟨B, k₀, L₀, hB, hk₀, hL₀, hfamily⟩ :=
    exists_normalizedQuarticBoxQMApproximation_of_controlledRoots hn hweighted
  obtain ⟨Aq, hAq, hrepair⟩ := exists_putinarDegreeLinearRepair hn
  exact putinarExplicitRate_certificate_of_normalizedApproximation
    hn hAq hrepair hB hk₀ hL₀ hfamily

/-- Conditional only on the named weighted-parity analytic statement, the
canonical Putinar/Lasserre lower bound has the general cube `O(r⁻⁴)` rate.
The quantified constants are fixed before the polynomial, its degree bound,
and the hierarchy order. -/
theorem putinarExplicitRate_lasserreGap_of_controlledRoots
    {n : ℕ} (hn : 0 < n)
    (hweighted : HasUniformControlledWeightedParityBound n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        p.totalDegree ≤ d → c * max d 1 ≤ r →
          ∃ ℓ : ℝ,
            lasserre_bound_box_qm p r = (ℓ : WithBot ℝ) ∧
              0 ≤ polyMin p - ℓ ∧
              polyMin p - ℓ ≤
                A * ((max d 1 : ℕ) : ℝ) ^ 6 *
                  (polyMax p - polyMin p) / (r : ℝ) ^ 4 := by
  obtain ⟨B, k₀, L₀, hB, hk₀, hL₀, hfamily⟩ :=
    exists_normalizedQuarticBoxQMApproximation_of_controlledRoots hn hweighted
  obtain ⟨Aq, hAq, hrepair⟩ := exists_putinarDegreeLinearRepair hn
  exact putinarExplicitRate_lasserreGap_of_normalizedApproximation
    hn hAq hrepair hB hk₀ hL₀ hfamily

end QuarticConvergence
end OptimalConvergenceRates

end
