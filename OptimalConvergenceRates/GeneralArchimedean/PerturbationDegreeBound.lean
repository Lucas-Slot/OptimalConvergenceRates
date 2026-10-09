/-
  The perturbation refutation with the rational-package parameters eliminated
  from its truncation order.
-/
import OptimalConvergenceRates.GeneralArchimedean.ConversionParameterBounds

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

/-- Explicit conversion order after replacing the package degree by its
quadratic logarithmic upper bound. -/
def perturbationConversionDegreeOrder
    (s d t : ℕ) (B H : ℝ) : ℕ :=
  conversionRefutationOrderOfDegree
    (Nat.ceil
      (packageDegreeConstant B
          (absorptionScaleConstant s (2 * (B + 1))) *
        (1 + Real.log (H + 1)) ^ 2))
    s d (t + 2 * d) d (t + 2 * d)

/-- The Krivine--Stengle perturbation refutation converts at an order whose
dependence on its explicit coefficient envelope is quadratic logarithmic.
Unlike `exists_quantitative_perturbation_module_refutation`, the conclusion's
order contains no package parameters. -/
theorem exists_perturbation_module_refutation_at_log_sq_order
    {m n : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (harch : IsArchimedean g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ (k r d t : ℕ) (A R G B : ℝ),
      1 ≤ k ∧ 0 ≤ A ∧ 1 ≤ R ∧ 0 ≤ G ∧
      d = r + perturbationGeneratorDegreeBound g p ∧
      G = perturbationGeneratorCommonCoeffBound g p ∧
      B = finiteFamilyEnvelopeBound (m + 1) n d R G ∧
      ∀ {epsilon : ℝ}, 0 < epsilon → epsilon ≤ 1 →
        let H : ℝ := (epsilon ^ (2 * k))⁻¹ * A
        let Hconvert : ℝ :=
          finiteFamilyEnvelopeBound
            ((Finset.univ :
              Finset (Finset (Fin (m + 1)))).card)
            n d R H
        ∃ pkg : Package
            (absorptionScale (m + 1) Hconvert (2 * (B + 1))) B
            (absorptionScale (m + 1) Hconvert (2 * (B + 1))),
          (pkg.ell : ℝ) ≤
              Real.log
                  (absorptionScale (m + 1) Hconvert (2 * (B + 1)) / 4) /
                Real.log (1 / 9) + 1 ∧
            (pkg.J : ℝ) ≤
              Real.log
                  (Real.sqrt
                      (B + absorptionScale (m + 1) Hconvert (2 * (B + 1))) /
                    Real.sqrt
                      (absorptionScale (m + 1) Hconvert (2 * (B + 1)))) /
                Real.log 2 ∧
            (-1 : MvPolynomial (Fin n) ℝ) ∈
              GenQuadraticModule
                (KrivineStengle.appendGenerator g
                  (KrivineStengle.perturbationGenerator p epsilon))
                (perturbationConversionDegreeOrder
                  (m + 1) d t B Hconvert) := by
  classical
  obtain ⟨k, r, d, t, A, R, G, B, hk, hA, hR, hG,
      hd, hGdef, hBdef, hrefute⟩ :=
    exists_quantitative_perturbation_module_refutation g p harch hp
  refine ⟨k, r, d, t, A, R, G, B, hk, hA, hR, hG,
    hd, hGdef, hBdef, ?_⟩
  intro epsilon hepsilon hepsilon1
  have hpkg := hrefute hepsilon hepsilon1
  dsimp only at hpkg ⊢
  obtain ⟨pkg, hell, hJ, hmem⟩ := hpkg
  refine ⟨pkg, hell, hJ, ?_⟩
  have hBnonneg : 0 ≤ B := by
    rw [hBdef]
    unfold finiteFamilyEnvelopeBound polynomialEnvelopeBound
    have hR0 : 0 ≤ R := zero_le_one.trans hR
    positivity
  have hHconvert :
      0 ≤ finiteFamilyEnvelopeBound
        ((Finset.univ : Finset (Finset (Fin (m + 1)))).card)
        n d R ((epsilon ^ (2 * k))⁻¹ * A) := by
    unfold finiteFamilyEnvelopeBound polynomialEnvelopeBound
    have hR0 : 0 ≤ R := zero_le_one.trans hR
    positivity
  have hBprime : 0 ≤ 2 * (B + 1) := by positivity
  exact converted_refutation_mem_log_sq_ceiling
    hHconvert hBnonneg hBprime pkg hell hJ
      d (t + 2 * d) d (t + 2 * d) hmem

end OptimalConvergenceRates.GeneralArchimedean

end
