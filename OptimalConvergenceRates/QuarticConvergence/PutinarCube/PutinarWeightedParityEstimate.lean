/-
  From the two-rotation parity seed to the complete weighted multiplier bound.

  This file performs only finite enumeration, vector Bernstein iteration,
  shifted sine removal, and constant bookkeeping.  The analytic construction
  of the two-rotation seed is kept as an explicit input so that its separate
  filter-commutation proof can be reused unchanged.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.AngularShiftedBounds
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarControlledAssembly

open MvPolynomial Finset Set
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- Dimension-only loss from continuous sine removal and the scalar
product-circle Bernstein estimate. -/
def controlledWeightedParityDimensionConstant (n : ℕ) : ℝ :=
  144 * (Real.pi / 2) ^ (2 * n) * 10 ^ (2 * n)

theorem controlledWeightedParityDimensionConstant_nonneg (n : ℕ) :
    0 ≤ controlledWeightedParityDimensionConstant n := by
  unfold controlledWeightedParityDimensionConstant
  positivity

/-- A uniform two-rotation square estimate for every Walsh parity projection
implies the complete weighted estimate used by the Putinar conversion.

The finite family is never split into separate scalar suprema.  The remaining
rotations are propagated by the root-count-free vector Bernstein estimate,
and the selected sine factors are removed by the closed-boundary shifted FTC
estimate. -/
theorem FiniteControlledRootData.hasWeightedParityBound_of_paritySeed
    {n : ℕ} {C : ℝ} {k : ℕ} {h : MvPolynomial (Fin n) ℝ}
    (data : FiniteControlledRootData
      (2 * n + 1) C k (cubeSphereLift n h))
    (hseed : ∀ (I : Finset (Fin n)) (a b : Fin n),
      UniformAngularSqBound
        (parityTermAngularDerivativeVector
          data.productCirclePolynomial I) [b, a] (144 * C)) :
    data.HasWeightedParityBound
      (controlledWeightedParityDimensionConstant n * C) := by
  classical
  have hC : 0 ≤ C := by
    have hleft : 0 ≤ (data.atoms.overlapBound : ℝ) *
        data.regular.jetBound ^ 2 :=
      mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    nlinarith [data.overlap_jetBound_sq_le]
  intro x hx I _hI J hJI hJcard
  have hJsubset : J ⊆ I := by simpa using hJI
  have hJcardn : J.card ≤ n := by
    simpa using (Finset.card_le_univ J)
  generalize hlist : J.toList = selected
  cases selected with
  | nil =>
      have hzero : J.card = 0 := by
        rw [← Finset.length_toList J, hlist]
        rfl
      omega
  | cons a tail =>
      cases tail with
      | nil =>
          have hone : J.card = 1 := by
            rw [← Finset.length_toList J, hlist]
            rfl
          omega
      | cons b remaining =>
          have hselected : (a :: b :: remaining).toFinset = J := by
            rw [← hlist]
            exact Finset.toList_toFinset J
          have hnodup : (a :: b :: remaining).Nodup := by
            rw [← hlist]
            exact Finset.nodup_toList J
          have hcard : J.card = remaining.length + 2 := by
            rw [← Finset.length_toList J, hlist]
            simp
          have hexp : 2 * J.card - 4 = 2 * remaining.length := by omega
          let B : ℕ := controlledCircleRootDegreeCoefficient n
          let R : ℕ := B * k
          let D : ℝ := 10 * (R : ℝ)
          let Q : Fin data.atoms.N → MvPolynomial (CubeCircleVar n) ℝ :=
            fun nu ↦ pairedPolynomialParityTerm
              (data.productCirclePolynomial nu) I
          have hdegree (nu : Fin data.atoms.N) :
              (Q nu).totalDegree ≤ R := by
            exact (pairedPolynomialParityTerm_totalDegree_le
              (data.productCirclePolynomial nu) I).trans (by
                simpa [R, B, controlledCircleRootDegreeCoefficient] using
                  data.productCirclePolynomial_totalDegree_le nu)
          have hstep :
              ∀ (pref : List (Fin n)) (i : Fin n) {S : ℝ},
                0 ≤ S →
                  UniformAngularSqBound
                    (parityTermAngularDerivativeVector
                      data.productCirclePolynomial I) pref S →
                  UniformAngularSqBound
                    (parityTermAngularDerivativeVector
                      data.productCirclePolynomial I)
                    (i :: pref) (D ^ 2 * S) := by
            have hraw := circlePolynomialAngularDerivativeVector_step
              Q hdegree (productCircleFirstRotationBound R)
              (by positivity : (0 : ℝ) ≤ 10 * (R : ℝ))
            have hfamily :
                parityTermAngularDerivativeVector
                    data.productCirclePolynomial I =
                  (fun is theta ↦ finiteEuclideanVector
                    (fun nu phi ↦ MvPolynomial.eval
                      (cosineSineCirclePoint phi)
                      (iteratedCircleRotationDeriv is (Q nu))) theta) := by
              funext is theta
              rfl
            rw [hfamily]
            simpa [D] using hraw
          have hcore := eval_weightedParitySum_le_of_twoRotationSeed_hypercube
            data.productCirclePolynomial hJsubset a b remaining hselected
            hnodup (D := D) (H := 144 * C) (by positivity)
            (mul_nonneg (by norm_num) hC) (hseed I a b) hstep x hx
          have hpiOne : (1 : ℝ) ≤ Real.pi / 2 := by
            linarith [Real.two_le_pi]
          have hjexp : 2 * (remaining.length + 2) ≤ 2 * n := by
            omega
          have hexpn : 2 * remaining.length ≤ 2 * n := by omega
          have hpiPow :
              (Real.pi / 2) ^ (2 * (remaining.length + 2)) ≤
                (Real.pi / 2) ^ (2 * n) :=
            pow_le_pow_right₀ hpiOne hjexp
          have htenPow :
              (10 : ℝ) ^ (2 * remaining.length) ≤
                (10 : ℝ) ^ (2 * n) :=
            pow_le_pow_right₀ (by norm_num) hexpn
          have hcombined :
              (Real.pi / 2) ^ (2 * (remaining.length + 2)) *
                  (10 : ℝ) ^ (2 * remaining.length) ≤
                (Real.pi / 2) ^ (2 * n) * (10 : ℝ) ^ (2 * n) := by
            calc
              _ ≤ (Real.pi / 2) ^ (2 * n) *
                    (10 : ℝ) ^ (2 * remaining.length) :=
                mul_le_mul_of_nonneg_right hpiPow (by positivity)
              _ ≤ _ :=
                mul_le_mul_of_nonneg_left htenPow (by positivity)
          have hrest : 0 ≤
              ((B : ℝ) ^ (2 * remaining.length) *
                (k : ℝ) ^ (2 * remaining.length)) * (144 * C) := by
            positivity
          have hfinal :
              MvPolynomial.eval x
                  (BoxSemialgebraicGeneratorProd (I \ J) *
                    ∑ nu, (circleParityComponent
                      (data.productCirclePolynomial nu) I) ^ 2) ≤
                (controlledWeightedParityDimensionConstant n * C) *
                  (B : ℝ) ^ (2 * remaining.length) *
                    (k : ℝ) ^ (2 * remaining.length) := by
            calc
              _ ≤ (Real.pi / 2) ^ (2 * (remaining.length + 2)) *
                    (D ^ (2 * remaining.length) * (144 * C)) := hcore
              _ = ((Real.pi / 2) ^ (2 * (remaining.length + 2)) *
                    (10 : ℝ) ^ (2 * remaining.length)) *
                    (((B : ℝ) ^ (2 * remaining.length) *
                      (k : ℝ) ^ (2 * remaining.length)) * (144 * C)) := by
                simp only [D, R, Nat.cast_mul, mul_pow]
                ring
              _ ≤ ((Real.pi / 2) ^ (2 * n) * (10 : ℝ) ^ (2 * n)) *
                    (((B : ℝ) ^ (2 * remaining.length) *
                      (k : ℝ) ^ (2 * remaining.length)) * (144 * C)) :=
                mul_le_mul_of_nonneg_right hcombined hrest
              _ = (controlledWeightedParityDimensionConstant n * C) *
                    (B : ℝ) ^ (2 * remaining.length) *
                      (k : ℝ) ^ (2 * remaining.length) := by
                unfold controlledWeightedParityDimensionConstant
                ring
          simpa [finiteCircleParityMultiplier, B, hexp] using hfinal

end QuarticConvergence
end OptimalConvergenceRates

end
