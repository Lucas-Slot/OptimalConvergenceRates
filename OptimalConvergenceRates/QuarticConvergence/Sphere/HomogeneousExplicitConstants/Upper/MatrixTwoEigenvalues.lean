import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Analysis.Matrix.Spectrum

/-! An explicit two-vector form of the two-dimensional spectral
min-max argument, with unordered actual matrix eigenvalue indices. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace MatrixTwoEigenvalues

open scoped BigOperators InnerProductSpace
open Matrix

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def form {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : E n) : ℝ :=
  ⟪x,Matrix.toEuclideanLin A x⟫_ℝ

theorem norm_sq_eigenbasis {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (x : E n) :
    ‖x‖^2=∑i, ⟪hA.eigenvectorBasis i,x⟫_ℝ^2 := by
  have h := hA.eigenvectorBasis.sum_inner_mul_inner x x
  simpa only [real_inner_comm x,←pow_two,real_inner_self_eq_norm_sq] using h.symm

theorem form_eigenbasis {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (x : E n) :
    form A x=∑i, hA.eigenvalues i*⟪hA.eigenvectorBasis i,x⟫_ℝ^2 := by
  have he (i : Fin n) : Matrix.toEuclideanLin A (hA.eigenvectorBasis i)=
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    apply PiLp.ext
    intro j
    exact congrFun (hA.mulVec_eigenvectorBasis i) j
  have h := congrArg (Matrix.toEuclideanLin A) (hA.eigenvectorBasis.sum_repr' x)
  simp only [map_sum,map_smul,he,smul_smul] at h
  rw [form,←h,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_right,real_inner_comm x]
  ring

theorem exists_nonzero_coordinate {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) {x : E n} (hx : x ≠ 0) :
    ∃i, ⟪hA.eigenvectorBasis i,x⟫_ℝ≠0 := by
  by_contra! hh
  have hs := hA.eigenvectorBasis.sum_repr' x
  simp only [hh,zero_smul,Finset.sum_const_zero] at hs
  exact hx hs.symm

theorem form_lt_of_coordinates {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) {x : E n} (hx : x ≠ 0) (c : ℝ)
    (hsmall : ∀ i, ⟪hA.eigenvectorBasis i, x⟫_ℝ ≠ 0 → hA.eigenvalues i < c) :
    form A x<c*‖x‖^2 := by
  rw [form_eigenbasis hA,norm_sq_eigenbasis hA,Finset.mul_sum]
  obtain ⟨i,hi⟩ := exists_nonzero_coordinate hA hx
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hj : ⟪hA.eigenvectorBasis j,x⟫_ℝ=0
    · simp only [hj,zero_pow (by decide : 2≠0),mul_zero,le_refl]
    · exact mul_le_mul_of_nonneg_right (hsmall j hj).le (sq_nonneg _)
  · exact ⟨i,Finset.mem_univ i,mul_lt_mul_of_pos_right (hsmall i hi) (sq_pos_of_ne_zero hi)⟩

theorem exists_eigenvalue_ge_of_form {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) {x : E n} (hx : x ≠ 0) (c : ℝ)
    (hform : c * ‖x‖ ^ 2 ≤ form A x) : ∃i,c≤hA.eigenvalues i := by
  by_contra! hh
  exact (not_lt_of_ge hform) (form_lt_of_coordinates hA hx c (fun i _ ↦ hh i))

/-- Two nonzero orthogonal vectors whose entire plane has Rayleigh
quotient at least c force two distinct actual eigenvalue indices ≥c. -/
theorem exists_two_eigenvalues {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (u v : E n) (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : ⟪u, v⟫_ℝ = 0) (c : ℝ)
    (hplane : ∀ α β : ℝ,c*‖α • u+β • v‖^2≤form A (α • u+β • v)) :
    ∃i j : Fin n,i≠j ∧ c≤hA.eigenvalues i ∧ c≤hA.eigenvalues j := by
  obtain ⟨i,hi⟩ := exists_eigenvalue_ge_of_form hA hu c (by simpa using hplane 1 0)
  by_contra! hh
  have hsmall (j : Fin n) (hji : j≠i) : hA.eigenvalues j<c := by
    exact hh i j (Ne.symm hji) hi
  let a : ℝ := ⟪hA.eigenvectorBasis i,u⟫_ℝ
  let b : ℝ := ⟪hA.eigenvectorBasis i,v⟫_ℝ
  have hstrict (w : E n) (hw : w≠0) (hc : ⟪hA.eigenvectorBasis i,w⟫_ℝ=0) :
      form A w<c*‖w‖^2 := by
    apply form_lt_of_coordinates hA hw c
    intro j hj
    exact hsmall j (by intro hji;subst j;exact hj hc)
  by_cases ha : a=0
  · have hc : ⟪hA.eigenvectorBasis i,u⟫_ℝ=0 := ha
    have hs := hstrict u hu hc
    have hp := hplane 1 0
    simp only [one_smul,zero_smul,add_zero] at hp
    exact not_lt_of_ge hp hs
  · let w : E n := b • u+(-a) • v
    have hnv : 0<‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
    have hw : w≠0 := by
      intro hw
      have hk := congrArg (fun z : E n ↦ ⟪v,z⟫_ℝ) hw
      have hvu : ⟪v,u⟫_ℝ=0 := by rw [real_inner_comm];exact huv
      simp only [w,inner_add_right,real_inner_smul_right,hvu,mul_zero,
        real_inner_self_eq_norm_sq,zero_add,inner_zero_right] at hk
      have : a=0 := by nlinarith
      exact ha this
    have hc : ⟪hA.eigenvectorBasis i,w⟫_ℝ=0 := by
      simp only [w,inner_add_right,real_inner_smul_right]
      change b*a+(-a)*b=0
      ring
    have hs := hstrict w hw hc
    exact not_lt_of_ge (hplane b (-a)) hs

end MatrixTwoEigenvalues
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
