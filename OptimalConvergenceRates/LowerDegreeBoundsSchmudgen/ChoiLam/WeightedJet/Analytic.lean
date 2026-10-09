/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/ChoiLam/WeightedJet/Analytic.lean

  Final analytic weighted-jet bound combining local, line, degree, and hole estimates.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.WeightedJet.SymmetricHole

open MvPolynomial Finset
open scoped Pointwise

noncomputable section

namespace OptimalConvergenceRates

/-- Higher-jet estimate wrapping the analytic core; certificate extraction and
degree-four comparison are derived from this statement. -/
theorem weightedJetLemma_higher_bounds_quarter
    {N k : ℕ} {epsilon A : ℝ}
    (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0)
    (hk : 1 ≤ k)
    (hA : 1 ≤ A)
    (hkSmall : (k : ℝ) ≤ weightedJetGamma0 * epsilon ^ (-(1 : ℝ) / 4))
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ k)
    (hlocal : ∀ x, boxSmall x →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i))
        ≤ A * (Real.sqrt epsilon + localSqNorm x))
    (hzeroLines : ∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i))
        ≤ A * Real.sqrt epsilon) :
    vecCoeffNorm4 (homogeneousPartVec4 2 Q) ≤ weightedJetQuarterConst * A ∧
    vecCoeffNorm4 (homogeneousPartVec4 3 Q) ≤ weightedJetQuarterConst * A * (k : ℝ) ∧
    vecCoeffNorm4 (homogeneousPartVec4 4 Q) ≤ weightedJetQuarterConst * A * (k : ℝ) ^ 2 := by
  exact symmetricHole_weightedJet_higher_coeff_bounds heps heps0 hk hA hkSmall Q hdeg
    hlocal hzeroLines

end OptimalConvergenceRates
