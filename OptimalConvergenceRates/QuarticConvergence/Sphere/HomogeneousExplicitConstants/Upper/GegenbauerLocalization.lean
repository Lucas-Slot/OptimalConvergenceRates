import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.GegenbauerGaussian
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.DeletedNodeKernel

/-! An actual nonzero polynomial with fourth-order angular concentration.
All quadrature, spectrum, test-vector and degree inputs are constructed. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace GegenbauerLocalization

open scoped BigOperators
open Polynomial GegenbauerJacobi GegenbauerSpectralMoments FiniteSpectralMeasure
  JacobiSpectralSupport GegenbauerGaussian DeletedNodeKernel

/-- The two-node deletion kernel for the actual normalized angular
functional. The polynomial is selected without any conditional spectral
or orthogonality input. -/
theorem exists_concentrated_polynomial {N ell : ℕ} (hN : 15 ≤ N) (hell : 3 * N ≤ ell) :
    ∃ chi : Polynomial ℝ,chi ≠ 0 ∧ chi.natDegree ≤ ell-2 ∧
      4*normalizedZonalFunctional (N-2) ((1-X)^2*chi^2)/
        normalizedZonalFunctional (N-2) (chi^2) ≤
          (256/25:ℝ)*(N:ℝ)^4/(ell:ℝ)^4 := by
  have hN3 : 3 ≤ N := by omega
  have hell2 : 2 ≤ ell := by omega
  have hell0 : 0 < ell := by omega
  have hellR : (ell:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hell0)
  obtain ⟨i,j,hij,hci,hcj⟩ := JacobiTwoBlockLocalization.exists_two_localized_eigenvalues hN hell
  let nodes : Fin ell→ℝ := fun k ↦ (jacobi_hermitian N ell).eigenvalues k
  let chi := deletedPolynomial nodes i j
  let c : ℝ := 1-(8/5:ℝ)*(N:ℝ)^2/(ell:ℝ)^2
  have hci' : c ≤ nodes i := hci
  have hcj' : c ≤ nodes j := hcj
  have hupper : ∀ k : Fin ell,nodes k ≤ 1 := fun k ↦
    (eigenvalue_mem_Ioo hN3 (jacobi_hermitian N ell) k).2.le
  have hquad : ∀ p : Polynomial ℝ,p.natDegree ≤ 2*ell-2 →
      normalizedZonalFunctional (N-2) p=
        ∑ k : Fin ell,p.eval (nodes k)*
          weight (jacobi_hermitian N ell) (initialVector hell0) k :=
    exact_polynomial hN3 hell0
  refine ⟨chi,deletedPolynomial_ne_zero nodes i j,(deletedPolynomial_degree nodes i j hij).le,?_⟩
  calc
    _ ≤ 4*(1-c)^2 := ratio_bound_of_quadrature hell2 hquad i j hij c hci' hcj' hupper
    _ = _ := by
      dsimp only [c]
      field_simp [hellR]
      ring

end GegenbauerLocalization
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
