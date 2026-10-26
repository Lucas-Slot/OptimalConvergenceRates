import OptimalConvergenceRates.SphereDimensionBounds.GegenbauerCoordinates
import OptimalConvergenceRates.SphereDimensionBounds.GegenbauerSpectralMoments

/-! Actual Gaussian spectral quadrature for the normalized angular
functional. All polynomial coordinates and Krylov identities are proved;
there is no quadrature, positivity, or spectral-simplicity premise. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.GegenbauerGaussian

open scoped BigOperators InnerProductSpace
open Polynomial Matrix GegenbauerGram GegenbauerJacobi GegenbauerCoordinates
  GegenbauerSpectralMoments FiniteSpectralMeasure JacobiSpectralSupport

theorem krylov_polynomial {N ell : ℕ} (hN : 3 ≤ N) (hell : 0 < ell)
    (k : ℕ) (hk : k < ell) :
    polynomialMap N ell (fun i => iterateVector (jacobi N ell) k (initialVector hell) i)=X^k := by
  induction k with
  | zero => simpa only [iterateVector,Function.iterate_zero,Function.id_def,pow_zero]
      using initial_polynomialMap N hell
  | succ k ih =>
    have ih' := ih (by omega : k < ell)
    have hdegree : (X*polynomialMap N ell
        (fun i => iterateVector (jacobi N ell) k (initialVector hell) i)).degree <
        (ell : WithBot ℕ) := by
      rw [ih',←pow_succ',Polynomial.degree_X_pow]
      exact WithBot.coe_lt_coe.mpr hk
    rw [iterateVector_succ]
    change polynomialMap N ell (jacobi N ell *ᵥ
      (fun i => iterateVector (jacobi N ell) k (initialVector hell) i))=X^(k+1)
    rw [polynomialMap_jacobi hN _ hdegree,ih',pow_succ']

theorem exact_power {N ell : ℕ} (hN : 3 ≤ N) (hell : 0 < ell)
    (k : ℕ) (hk : k ≤ 2 * ell - 2) :
    normalizedZonalFunctional (N-2) (X^k)=
      ∑ i : Fin ell,((jacobi_hermitian N ell).eigenvalues i)^k*
        weight (jacobi_hermitian N ell) (initialVector hell) i :=
  exact_power_of_krylov hN hell (krylov_polynomial hN hell) k hk

theorem exact_polynomial {N ell : ℕ} (hN : 3 ≤ N) (hell : 0 < ell)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ 2 * ell - 2) :
    normalizedZonalFunctional (N-2) p=
      ∑ i : Fin ell,p.eval ((jacobi_hermitian N ell).eigenvalues i)*
        weight (jacobi_hermitian N ell) (initialVector hell) i :=
  exact_polynomial_of_krylov hN hell (krylov_polynomial hN hell) p hp

theorem weights_sum_one {N ell : ℕ} (hell : 0 < ell) :
    (∑ i : Fin ell,weight (jacobi_hermitian N ell) (initialVector hell) i)=1 := by
  rw [sum_weight,initial_norm,one_pow]

theorem initial_cyclic {N ell : ℕ} (hN : 3 ≤ N) (hell : 0 < ell) :
    CyclicSpectralMeasure.IsCyclic (jacobi N ell) (initialVector hell) := by
  apply cyclic_of_krylov hN hell (krylov_polynomial hN hell)
  intro w
  by_cases hz : polynomialMap N ell (fun i => w i)=0
  · simpa only [hz,natDegree_zero] using hell
  · exact (natDegree_lt_iff_degree_lt hz).mpr (polynomialMap_degree_lt N ell _)

theorem weights_positive {N ell : ℕ} (hN : 3 ≤ N) (hell : 0 < ell) (i : Fin ell) :
    0 < weight (jacobi_hermitian N ell) (initialVector hell) i :=
  CyclicSpectralMeasure.weight_pos _ _ (initial_cyclic hN hell) i

theorem nodes_injective {N ell : ℕ} (hN : 3 ≤ N) (hell : 0 < ell) :
    Function.Injective (jacobi_hermitian N ell).eigenvalues :=
  CyclicSpectralMeasure.eigenvalues_injective _ _ (initial_cyclic hN hell)

end OptimalConvergenceRates.SphereDimensionBounds.GegenbauerGaussian
