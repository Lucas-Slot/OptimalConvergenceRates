import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.GegenbauerRecurrence

/-! Finite orthonormal polynomial coordinates and their actual
multiplication Gram matrix. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace GegenbauerGram

open scoped BigOperators
open Polynomial Matrix GegenbauerNorms GegenbauerJacobi GegenbauerRecurrence

def polynomialMap (N ell : ℕ) (v : Fin ell → ℝ) : Polynomial ℝ :=
  ∑ i,C (v i)*normalized N i.val

theorem pair_sum_left {I : Type*} [Fintype I] (s : ℕ) (p : I → Polynomial ℝ)
    (q : Polynomial ℝ) : pair s (∑ i,p i) q=∑ i,pair s (p i) q := by
  unfold pair
  rw [Finset.sum_mul,map_sum]

theorem pair_sum_right {I : Type*} [Fintype I] (s : ℕ) (p : Polynomial ℝ)
    (q : I → Polynomial ℝ) : pair s p (∑ i,q i)=∑ i,pair s p (q i) := by
  rw [pair_comm,pair_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  exact pair_comm s _ _

theorem pair_C_mul_right (s : ℕ) (a : ℝ) (p q : Polynomial ℝ) :
    pair s p (C a*q)=a*pair s p q := by rw [pair_comm,pair_C_mul,pair_comm]

theorem normalized_gram {N ell : ℕ} (hN : 3 ≤ N) (i j : Fin ell) :
    pair (N-2) (normalized N i.val) (normalized N j.val)=if i=j then 1 else 0 := by
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl,normalized_self hN]
  · rw [ite_eq_right hij]
    exact normalized_orthogonal hN (by intro h;exact hij (Fin.ext h))

theorem pair_polynomialMap {N ell : ℕ} (hN : 3 ≤ N) (v w : Fin ell → ℝ) :
    pair (N-2) (polynomialMap N ell v) (polynomialMap N ell w)=∑ i,v i*w i := by
  unfold polynomialMap
  rw [pair_sum_left]
  simp_rw [pair_C_mul,pair_sum_right,pair_C_mul_right,normalized_gram hN]
  simp

theorem polynomialMap_zero (N ell : ℕ) : polynomialMap N ell 0=0 := by simp [polynomialMap]

theorem polynomialMap_ne_zero {N ell : ℕ} (hN : 3 ≤ N) (v : Fin ell → ℝ) (hv : v ≠ 0) :
    polynomialMap N ell v ≠ 0 := by
  intro hz
  have h := pair_polynomialMap hN v v
  rw [hz] at h
  have hs : (∑ i,(v i)^2)=0 := by simpa [pair,pow_two] using h.symm
  apply hv
  funext i
  have hi : (v i)^2 ≤ ∑ j,(v j)^2 := Finset.single_le_sum
    (fun j _ ↦ sq_nonneg (v j)) (Finset.mem_univ i)
  rw [hs] at hi
  exact sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg _))

theorem polynomialMap_single (N ell : ℕ) (i : Fin ell) :
    polynomialMap N ell (Pi.single i 1)=normalized N i.val := by
  classical
  simp [polynomialMap,Pi.single_apply]

theorem pair_X_next {N : ℕ} (hN : 3 ≤ N) (i : ℕ) :
    pair (N-2) (X*normalized N i) (normalized N (i+1))=coefficient N i := by
  rw [normalized_three_term_raw hN,pair_add_left,pair_C_mul,pair_C_mul,
    normalized_self hN,normalized_orthogonal hN (by omega : i-1 ≠ i+1)]
  ring

theorem pair_X_nonadjacent {N i j : ℕ} (hN : 3 ≤ N) (hu : i + 1 ≠ j) (hd : j + 1 ≠ i) :
    pair (N-2) (X*normalized N i) (normalized N j)=0 := by
  rw [normalized_three_term_raw hN,pair_add_left,pair_C_mul,pair_C_mul,
    normalized_orthogonal hN hu,mul_zero,zero_add]
  cases i with
  | zero => rw [lowerCoefficient_zero,zero_mul]
  | succ i =>
    have hij : i ≠ j := by omega
    simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel]
    rw [normalized_orthogonal hN hij,mul_zero]

theorem pair_X_normalized {N : ℕ} (hN : 3 ≤ N) (i j : ℕ) :
    pair (N-2) (X*normalized N i) (normalized N j)=
      if i+1=j then coefficient N i else if j+1=i then coefficient N j else 0 := by
  by_cases hu : i+1=j
  · rw [ite_eq_left hu,←hu,pair_X_next hN]
  · rw [ite_eq_right hu]
    by_cases hd : j+1=i
    · rw [ite_eq_left hd,←hd,pair_X_comm,pair_X_next hN]
    · rw [ite_eq_right hd]
      exact pair_X_nonadjacent hN hu hd

theorem pair_X_coordinates {N ell : ℕ} (hN : 3 ≤ N) (i j : Fin ell) :
    pair (N-2) (X*normalized N i.val) (normalized N j.val)=jacobi N ell i j :=
  pair_X_normalized hN i.val j.val

theorem multiplication_gram {N ell : ℕ} (hN : 3 ≤ N) (v w : Fin ell → ℝ) :
    pair (N-2) (X*polynomialMap N ell v) (polynomialMap N ell w)=
      dotProduct v (jacobi N ell *ᵥ w) := by
  unfold polynomialMap
  rw [Finset.mul_sum,pair_sum_left]
  simp_rw [show ∀ i : Fin ell,X*(C (v i)*normalized N i.val)=
      C (v i)*(X*normalized N i.val) by intro i;ring]
  simp_rw [pair_C_mul,pair_sum_right,pair_C_mul_right,pair_X_coordinates hN]
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end GegenbauerGram
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
