import Mathlib.LinearAlgebra.Matrix.Defs
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.WeightedQuadraticTraceGeometry

/-! Actual finite spectral weights and moments of a symmetric real matrix. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace FiniteSpectralMeasure

open scoped BigOperators InnerProductSpace
open Matrix WeightedQuadraticTraceGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Point := EuclideanSpace ℝ ι
abbrev Mat := Matrix ι ι ℝ

def weight {M : Mat (ι := ι)} (hM : M.IsHermitian) (v : Point (ι := ι)) (i : ι) : ℝ :=
  ⟪hM.eigenvectorBasis i,v⟫_ℝ^2

theorem weight_nonnegative {M : Mat (ι := ι)} (hM : M.IsHermitian) (v : Point (ι := ι)) (i : ι) :
    0 ≤ weight hM v i := sq_nonneg _

theorem sum_weight {M : Mat (ι := ι)} (hM : M.IsHermitian) (v : Point (ι := ι)) :
    (∑ i,weight hM v i)=‖v‖^2 := by
  calc
    _=∑ i,⟪v,hM.eigenvectorBasis i⟫_ℝ * ⟪hM.eigenvectorBasis i,v⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [real_inner_comm (hM.eigenvectorBasis i) v]
      exact pow_two _
    _=⟪v,v⟫_ℝ := hM.eigenvectorBasis.sum_inner_mul_inner v v
    _=‖v‖^2 := real_inner_self_eq_norm_sq v

def iterateVector (M : Mat (ι := ι)) (k : ℕ) (v : Point (ι := ι)) : Point (ι:=ι) :=
  (Matrix.toEuclideanLin M)^[k] v

theorem iterateVector_succ (M : Mat (ι := ι)) (k : ℕ) (v : Point (ι := ι)) :
    iterateVector M (k+1) v=Matrix.toEuclideanLin M (iterateVector M k v) := by
  exact Function.iterate_succ_apply' _ _ _

theorem eigenmode_iterate {M : Mat (ι := ι)} (hM : M.IsHermitian)
    (v : Point (ι := ι)) (i : ι) (k : ℕ) :
    ⟪hM.eigenvectorBasis i,iterateVector M k v⟫_ℝ=
      (hM.eigenvalues i)^k*⟪hM.eigenvectorBasis i,v⟫_ℝ := by
  have hsym : (Matrix.toEuclideanLin M).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hM
  induction k with
  | zero => simp [iterateVector]
  | succ k ih =>
    rw [iterateVector_succ]
    calc
      _=⟪Matrix.toEuclideanLin M (hM.eigenvectorBasis i),iterateVector M k v⟫_ℝ :=
        (hsym _ _).symm
      _=(hM.eigenvalues i)*⟪hM.eigenvectorBasis i,iterateVector M k v⟫_ℝ := by
        rw [toEuclideanLin_eigenvector,real_inner_smul_left]
      _=_ := by rw [ih,pow_succ];ring

theorem inner_iterates {M : Mat (ι := ι)} (hM : M.IsHermitian)
    (v : Point (ι := ι)) (k l : ℕ) :
    ⟪iterateVector M k v,iterateVector M l v⟫_ℝ=
      ∑ i,(hM.eigenvalues i)^(k+l)*weight hM v i := by
  rw [←hM.eigenvectorBasis.sum_inner_mul_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (hM.eigenvectorBasis i) (iterateVector M k v),
    eigenmode_iterate,eigenmode_iterate]
  unfold weight
  rw [pow_add]
  ring

theorem norm_iterate_sq {M : Mat (ι := ι)} (hM : M.IsHermitian)
    (v : Point (ι := ι)) (k : ℕ) :
    ‖iterateVector M k v‖^2=∑ i,(hM.eigenvalues i)^(2*k)*weight hM v i := by
  rw [←real_inner_self_eq_norm_sq,inner_iterates hM]
  simp only [two_mul]

end FiniteSpectralMeasure
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
