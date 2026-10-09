/-
  Assembly of normalized Putinar approximations from controlled sphere roots.

  The single named hypothesis below is exactly the weighted parity estimate.
  This keeps the analytic gate explicit while all algebraic conversion,
  correction, and order bookkeeping remain unconditional.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.CircleRoots
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarApproximationFromWeighted
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarNormalizedRate

open MvPolynomial Finset Set
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- Common degree coefficient of the controlled roots after restriction to
the `n` circle blocks. -/
def controlledCircleRootDegreeCoefficient (n : ℕ) : ℕ :=
  2 * (2 * n + 1 + 3)

/-- Canonical quadratic-module order coefficient of the approximation built
from controlled roots and the explicit product-generator correction. -/
def controlledPutinarApproximationOrderCoefficient (n : ℕ) : ℕ :=
  2 * controlledCircleRootDegreeCoefficient n + 4 * n

theorem controlledCircleRootDegreeCoefficient_one_le (n : ℕ) :
    1 ≤ controlledCircleRootDegreeCoefficient n := by
  unfold controlledCircleRootDegreeCoefficient
  omega

theorem controlledPutinarApproximationOrderCoefficient_one_le (n : ℕ) :
    1 ≤ controlledPutinarApproximationOrderCoefficient n := by
  unfold controlledPutinarApproximationOrderCoefficient
  have := controlledCircleRootDegreeCoefficient_one_le n
  omega

/-- The precise remaining analytic estimate on one controlled root package.
It is pointwise, uses the original finite root family, and retains the full
weighted multiplier required by the explicit Putinar correction. -/
def FiniteControlledRootData.HasWeightedParityBound
    {n : ℕ} {C : ℝ} {k : ℕ} {h : MvPolynomial (Fin n) ℝ}
    (data : FiniteControlledRootData
      (2 * n + 1) C k (cubeSphereLift n h)) (H : ℝ) : Prop :=
  ∀ (x : Fin n → ℝ), x ∈ Hypercube n →
    ∀ I ∈ Finset.univ.powerset, ∀ J ∈ I.powerset,
      2 ≤ J.card →
      MvPolynomial.eval x
          (BoxSemialgebraicGeneratorProd (I \ J) *
            finiteCircleParityMultiplier
              data.productCirclePolynomial I) ≤
        H * ((controlledCircleRootDegreeCoefficient n : ℕ) : ℝ) ^
            (2 * J.card - 4) *
          (k : ℝ) ^ (2 * J.card - 4)

/-- Equivalent presentation of the weighted bound with the degree and scale
already combined, matching `hasQuarticBoxQMApproximationAt_of_weightedParity`. -/
theorem FiniteControlledRootData.hasWeightedParityBound_combined
    {n : ℕ} {C : ℝ} {k : ℕ} {h : MvPolynomial (Fin n) ℝ}
    (data : FiniteControlledRootData
      (2 * n + 1) C k (cubeSphereLift n h)) {H : ℝ}
    (hweighted : data.HasWeightedParityBound H)
    (x : Fin n → ℝ) (hx : x ∈ Hypercube n)
    (I : Finset (Fin n)) (hI : I ∈ Finset.univ.powerset)
    (J : Finset (Fin n)) (hJ : J ∈ I.powerset) (hJcard : 2 ≤ J.card) :
    MvPolynomial.eval x
        (BoxSemialgebraicGeneratorProd (I \ J) *
          finiteCircleParityMultiplier data.productCirclePolynomial I) ≤
      H * (((controlledCircleRootDegreeCoefficient n : ℕ) : ℝ) *
        (k : ℝ)) ^ (2 * J.card - 4) := by
  calc
    _ ≤ H * ((controlledCircleRootDegreeCoefficient n : ℕ) : ℝ) ^
          (2 * J.card - 4) * (k : ℝ) ^ (2 * J.card - 4) :=
      hweighted x hx I hI J hJ hJcard
    _ = _ := by rw [mul_pow]; ring

/-- The weighted estimate on a controlled root package gives the normalized
quartic quadratic-module approximation at that scale. -/
theorem FiniteControlledRootData.hasQuarticBoxQMApproximationAt
    {n : ℕ} (hn : 0 < n) {C H : ℝ} {k : ℕ}
    {h : MvPolynomial (Fin n) ℝ}
    (data : FiniteControlledRootData
      (2 * n + 1) C k (cubeSphereLift n h))
    (hk : 1 ≤ k) (hnonnegative : IsNonnegOn h (Hypercube n))
    (hweighted : data.HasWeightedParityBound H) :
    HasQuarticBoxQMApproximationAt h
      (controlledPutinarApproximationOrderCoefficient n) k
      (putinarWeightedApproximationConstant n
        (controlledCircleRootDegreeCoefficient n) C H) := by
  apply hasQuarticBoxQMApproximationAt_of_weightedParity h
    data.productCirclePolynomial hk hnonnegative
  · intro nu
    exact data.productCirclePolynomial_totalDegree_le nu
  · intro z hz
    exact data.productCircle_square_approximation hn hz
  · intro x hx I hI J hJ hJcard
    exact data.hasWeightedParityBound_combined hweighted
      x hx I hI J hJ hJcard

/-- A uniform weighted estimate for the controlled packages supplied by the
sphere construction is exactly the normalized approximation family required
by the final rate adapters. -/
theorem hasNormalizedQuarticBoxQMApproximation_of_controlledRoots
    {n : ℕ} (hn : 0 < n) {C H : ℝ} {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀)
    (hdata : HasFiniteControlledRootData (2 * n + 1) C k₀)
    (hweighted : ∀ (h : MvPolynomial (Fin n) ℝ),
      IsNonnegOn h (Hypercube n) → cubeSphereC6Norm n h ≤ 1 →
      ∀ k, k₀ ≤ k →
      ∀ data : FiniteControlledRootData
        (2 * n + 1) C k (cubeSphereLift n h),
        data.HasWeightedParityBound H) :
    HasNormalizedQuarticBoxQMApproximation n
      (controlledPutinarApproximationOrderCoefficient n) k₀
      (putinarWeightedApproximationConstant n
        (controlledCircleRootDegreeCoefficient n) C H) := by
  intro h hnonnegative hnorm k hk
  have hliftNonnegative : SphereNonnegative (cubeSphereLift n h) :=
    cubeSphereLift_nonnegative hn hnonnegative
  let data := Classical.choice
    (hdata (cubeSphereLift n h) hliftNonnegative hnorm k hk)
  exact data.hasQuarticBoxQMApproximationAt hn (hk₀.trans hk)
    hnonnegative (hweighted h hnonnegative hnorm k hk data)

end QuarticConvergence
end OptimalConvergenceRates

end
