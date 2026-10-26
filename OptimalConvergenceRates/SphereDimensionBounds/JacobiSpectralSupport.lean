import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Notation.Pi.Basic
import OptimalConvergenceRates.SphereDimensionBounds.GegenbauerGram
import OptimalConvergenceRates.SphereDimensionBounds.FiniteSpectralMeasure

/-! Strict spectral support of the actual finite Gegenbauer Jacobi matrix,
proved using the actual positive angular polynomial integrals. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.JacobiSpectralSupport

open scoped BigOperators InnerProductSpace
open Polynomial Matrix GegenbauerJacobi GegenbauerGram GegenbauerNorms
  AngularPolynomialPositivity WeightedQuadraticTraceGeometry

theorem jacobi_hermitian (N ell : ℕ) : (jacobi N ell).IsHermitian := by
  simpa only [Matrix.IsHermitian,conjTranspose_eq_transpose_of_trivial] using
    (jacobi_symmetric N ell).eq

theorem eigenvalue_mem_Ioo {N ell : ℕ} (hN : 3 ≤ N)
    (hJ : (jacobi N ell).IsHermitian) (i : Fin ell) :
    hJ.eigenvalues i ∈ Set.Ioo (-1:ℝ) 1 := by
  let b := hJ.eigenvectorBasis
  let v : Fin ell → ℝ := fun j => b i j
  let p := polynomialMap N ell v
  have hbnorm : ‖b i‖=1 := b.orthonormal.norm_eq_one i
  have hv : v ≠ 0 := by
    intro hv0
    have hb0 : b i=0 := by
      ext j
      exact congrFun hv0 j
    simp only [hb0,norm_zero] at hbnorm
    norm_num at hbnorm
  have hp0 : p ≠ 0 := polynomialMap_ne_zero hN v hv
  have hvnorm : (∑ j,(v j)^2)=1 := by
    have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin ell => ℝ) (b i)
    rw [hbnorm] at h
    simpa only [v,one_pow,Real.norm_eq_abs,sq_abs] using h.symm
  have hnorm : normalizedZonalFunctional (N-2) (p^2)=1 := by
    have h := pair_polynomialMap hN v v
    change normalizedZonalFunctional (N-2) (p*p)=∑ j,v j*v j at h
    simpa only [←pow_two,hvnorm] using h
  have heig (j : Fin ell) : (jacobi N ell *ᵥ v) j=hJ.eigenvalues i*v j := by
    have h := toEuclideanLin_eigenvector (jacobi N ell) hJ i
    have hj := congrArg (fun z : EuclideanSpace ℝ (Fin ell) => z j) h
    simpa only [Matrix.toLpLin_apply,PiLp.toLp_apply,
      WithLp.equiv_apply,PiLp.smul_apply,Pi.smul_apply,smul_eq_mul,v,b] using hj
  have hmoment : normalizedZonalFunctional (N-2) (X*p^2)=hJ.eigenvalues i := by
    calc
      _=pair (N-2) (X*p) p := by unfold pair;congr 1;ring
      _=dotProduct v (jacobi N ell *ᵥ v) := multiplication_gram hN v v
      _=hJ.eigenvalues i*(∑ j,(v j)^2) := by
        simp only [dotProduct,heig,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _=hJ.eigenvalues i := by rw [hvnorm,mul_one]
  have hleft := zonal_left_weight_square_pos (N-2) p hp0
  rw [add_mul,one_mul,map_add,hnorm,hmoment] at hleft
  have hright := zonal_right_weight_square_pos (N-2) p hp0
  rw [sub_mul,one_mul,map_sub,hnorm,hmoment] at hright
  constructor <;> linarith

end OptimalConvergenceRates.SphereDimensionBounds.JacobiSpectralSupport
