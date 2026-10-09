/-
  Coefficient-bounded perturbation refutations using the sharp conversion.
-/
import OptimalConvergenceRates.GeneralArchimedean.BoundedPerturbation
import OptimalConvergenceRates.GeneralArchimedean.SharpBoundedBridge

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

variable {n m : ℕ}

/-- The power-bounded Krivine--Stengle perturbation refutation converts by
the fixed-theta sharp construction, with its coefficient budget retained. -/
theorem exists_sharp_bounded_quantitative_perturbation_module_refutation
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (harch : IsArchimedean g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ (k r d t : ℕ) (A R Hcoord G B : ℝ),
      1 ≤ k ∧ 0 ≤ A ∧ 1 ≤ R ∧ 0 ≤ Hcoord ∧ 1 ≤ G ∧
      d = r + perturbationGeneratorDegreeBound g p ∧
      G = perturbationGeneratorCommonCoeffBound g p ∧
      B = finiteFamilyEnvelopeBound (m + 1) n d R G ∧
      ∀ {epsilon : ℝ}, 0 < epsilon → epsilon ≤ 1 →
        let H : ℝ := (epsilon ^ (2 * k))⁻¹ * A
        let Hconvert : ℝ :=
          finiteFamilyEnvelopeBound
            ((Finset.univ : Finset (Finset (Fin (m + 1)))).card)
            n d R H
        let Bprime : ℝ := 2 * (B + 1)
        let theta : ℝ := sharpThetaScale (m + 1)
        let delta : ℝ := sharpDeltaScale (m + 1) Hconvert Bprime
        ∃ pkg : Package delta B theta,
          (pkg.ell : ℝ) ≤
              Real.log (theta / 4) / Real.log (1 / 9) + 1 ∧
            (pkg.J : ℝ) ≤
              Real.log (Real.sqrt (B + delta) / Real.sqrt delta) /
                Real.log 2 ∧
            Nonempty (BoundedQuadraticModuleCertificate
              (KrivineStengle.appendGenerator g
                (KrivineStengle.perturbationGenerator p epsilon))
              (-1 : MvPolynomial (Fin n) ℝ)
              (sharpConversionRefutationOrder pkg (m + 1) d
                (boundedCoeffEnvelopeOrder n t d) d
                (boundedCoeffEnvelopeOrder n t d))
              (boundedSharpBridgeRefutationBudget pkg (m + 1) n d
                R Hcoord G H Hconvert)) := by
  classical
  obtain ⟨k, r, A, hk, hA, hrefute⟩ :=
    exists_power_bounded_perturbation_refutation g p hp
  obtain ⟨R, t, Hcoord, hR, hHcoord, hcoordNE⟩ :=
    harch.exists_bounded_truncated_coordinate_square_bound
  let d : ℕ := r + perturbationGeneratorDegreeBound g p
  let G : ℝ := perturbationGeneratorCommonCoeffBound g p
  let B : ℝ := finiteFamilyEnvelopeBound (m + 1) n d R G
  have hG : 1 ≤ G := by
    dsimp [G]
    exact one_le_perturbationGeneratorCommonCoeffBound g p
  refine ⟨k, r, d, t, A, R, Hcoord, G, B,
    hk, hA, hR, hHcoord, hG, rfl, rfl, rfl, ?_⟩
  intro epsilon hepsilon hepsilon1
  obtain ⟨c⟩ := hrefute hepsilon hepsilon1
  let hpert := KrivineStengle.perturbationGenerator p epsilon
  let a : Fin (m + 1) → MvPolynomial (Fin n) ℝ :=
    KrivineStengle.appendGenerator g hpert
  have hrd : r ≤ d := by
    dsimp [d]
    omega
  have haDegree : ∀ i, (a i).totalDegree ≤ d := by
    intro i
    have hi := appendPerturbation_totalDegree_le g p epsilon i
    simpa [a, hpert, d] using hi.trans (Nat.le_add_left _ r)
  have haNorm : ∀ i, coeffL1Norm (a i) ≤ G := by
    intro i
    dsimp [a, hpert, G]
    exact appendPerturbation_coeffL1Norm_le_common
      g p hepsilon.le hepsilon1 i
  have hcoord : ∀ i : Fin n,
      BoundedQuadraticModuleCertificate a
        (C R - X i ^ 2) t Hcoord := by
    intro i
    let ci := Classical.choice (hcoordNE i)
    exact ci.liftAppendGenerator
  obtain ⟨B', Hconvert, hB', hHconvert, hpkg⟩ :=
    bounded_certificate_preordering_refutation_to_sharp_module_at_of_coordinate_bounds
      a hR hHcoord hcoord c hrd hG haDegree haNorm
  rw [hB', hHconvert] at hpkg
  simpa [a, hpert, B, G, d] using hpkg

end OptimalConvergenceRates.GeneralArchimedean

end
