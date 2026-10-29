import Mathlib.LinearAlgebra.Matrix.Defs
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.GegenbauerNorms

/-! Actual orthonormal Gegenbauer polynomials and positive Jacobi
coefficients. No quadrature or spectral localization is asserted here. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace GegenbauerJacobi

open Polynomial GegenbauerAlgebra GegenbauerOrthogonality GegenbauerNorms

def normalized (N j : ℕ) : Polynomial ℝ :=
  C (1/Real.sqrt (normSq N j))*gegenbauer (N:ℝ) j

theorem normalized_zero (N : ℕ) : normalized N 0=1 := by
  simp [normalized,normSq_zero,gegenbauer]

theorem pair_normalized (N s j k : ℕ) :
    pair s (normalized N j) (normalized N k)=
      (1/Real.sqrt (normSq N j))*(1/Real.sqrt (normSq N k))*
        pair s (gegenbauer (N:ℝ) j) (gegenbauer (N:ℝ) k) := by
  unfold normalized
  rw [pair_C_mul,pair_comm,pair_C_mul,pair_comm]
  ring

theorem normalized_self {N : ℕ} (hN : 3 ≤ N) (j : ℕ) :
    pair (N-2) (normalized N j) (normalized N j)=1 := by
  rw [pair_normalized]
  change (1/Real.sqrt (normSq N j))*(1/Real.sqrt (normSq N j))*normSq N j=1
  have hh := normSq_pos hN j
  rw [one_div_mul_one_div,←pow_two,Real.sq_sqrt hh.le]
  field_simp [hh.ne']

theorem normalized_orthogonal {N j k : ℕ} (hN : 3 ≤ N) (hjk : j ≠ k) :
    pair (N-2) (normalized N j) (normalized N k)=0 := by
  rw [pair_normalized]
  change _*normalizedZonalFunctional (N-2)
    (gegenbauer (N:ℝ) j*gegenbauer (N:ℝ) k)=0
  rw [orthogonal hN hjk,mul_zero]

theorem normalized_natDegree_le (N j : ℕ) : (normalized N j).natDegree ≤ j := by
  exact Polynomial.natDegree_mul_le.trans (by
    simpa only [Polynomial.natDegree_C,zero_add] using gegenbauer_natDegree_le (N:ℝ) j)

/-- This is the positive off-diagonal between normalized degrees j and j+1. -/
def coefficient (N j : ℕ) : ℝ :=
  (((j:ℝ)+(N:ℝ)-2)/(2*(j:ℝ)+(N:ℝ)-2))*
    (Real.sqrt (normSq N (j+1))/Real.sqrt (normSq N j))

theorem coefficient_pos {N : ℕ} (hN : 3 ≤ N) (j : ℕ) : 0 < coefficient N j := by
  have hNR : (3:ℝ) ≤ N := by exact_mod_cast hN
  have hjR : (0:ℝ) ≤ j := by positivity
  unfold coefficient
  exact mul_pos (div_pos (by linarith) (by linarith))
    (div_pos (Real.sqrt_pos.mpr (normSq_pos hN (j+1)))
      (Real.sqrt_pos.mpr (normSq_pos hN j)))

theorem coefficient_sq {N : ℕ} (hN : 3 ≤ N) (j : ℕ) :
    coefficient N j^2=(((j:ℝ)+1)*((j:ℝ)+(N:ℝ)-2))/
      ((2*(j:ℝ)+(N:ℝ)-2)*(2*(j:ℝ)+(N:ℝ))) := by
  have hNR : (3:ℝ) ≤ N := by exact_mod_cast hN
  have hjR : (0:ℝ) ≤ j := by positivity
  have hA : (j:ℝ)+(N:ℝ)-2 ≠ 0 := by linarith
  have hB : 2*(j:ℝ)+(N:ℝ)-2 ≠ 0 := by linarith
  have hC : 2*(j:ℝ)+(N:ℝ) ≠ 0 := by linarith
  unfold coefficient
  rw [mul_pow,div_pow,div_pow,Real.sq_sqrt (normSq_pos hN (j+1)).le,
    Real.sq_sqrt (normSq_pos hN j).le,normSq_succ hN j]
  field_simp [hA,hB,hC,(normSq_pos hN j).ne']

theorem four_coefficient_sq {N : ℕ} (hN : 3 ≤ N) (j : ℕ) :
    4*coefficient N j^2=1-(((N:ℝ)-2)*((N:ℝ)-4))/
      ((2*(j:ℝ)+(N:ℝ)-2)*(2*(j:ℝ)+(N:ℝ))) := by
  rw [coefficient_sq hN]
  have hNR : (3:ℝ) ≤ N := by exact_mod_cast hN
  have hjR : (0:ℝ) ≤ j := by positivity
  have hB : 2*(j:ℝ)+(N:ℝ)-2 ≠ 0 := by linarith
  have hC : 2*(j:ℝ)+(N:ℝ) ≠ 0 := by linarith
  rw [← mul_div_assoc, eq_sub_iff_add_eq, ← add_div,
    div_eq_one_iff_eq (mul_ne_zero hB hC)]
  ring

theorem two_coefficient_sqrt {N : ℕ} (hN : 3 ≤ N) (j : ℕ) :
    2*coefficient N j=Real.sqrt (1-(((N:ℝ)-2)*((N:ℝ)-4))/
      ((2*(j:ℝ)+(N:ℝ)-2)*(2*(j:ℝ)+(N:ℝ)))) := by
  have he : 1-(((N:ℝ)-2)*((N:ℝ)-4))/
      ((2*(j:ℝ)+(N:ℝ)-2)*(2*(j:ℝ)+(N:ℝ)))=(2*coefficient N j)^2 := by
    rw [mul_pow]
    norm_num only [show (2:ℝ)^2=4 by norm_num]
    exact (four_coefficient_sq hN j).symm
  rw [he,Real.sqrt_sq (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (coefficient_pos hN j).le)]

def jacobi (N ell : ℕ) : Matrix (Fin ell) (Fin ell) ℝ := fun i j ↦
  if i.val+1=j.val then coefficient N i.val else
    if j.val+1=i.val then coefficient N j.val else 0

theorem jacobi_symmetric (N ell : ℕ) : (jacobi N ell).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply,jacobi]
  by_cases h1 : i.val+1=j.val
  · have h2 : ¬j.val+1=i.val := by omega
    simp [h1,h2]
  · by_cases h2 : j.val+1=i.val <;> simp [h1,h2]

theorem jacobi_diagonal (N ell : ℕ) (i : Fin ell) : jacobi N ell i i=0 := by
  simp [jacobi]

end GegenbauerJacobi
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
