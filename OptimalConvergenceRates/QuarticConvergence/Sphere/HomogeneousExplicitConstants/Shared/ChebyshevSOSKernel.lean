import OptimalConvergenceRates.BasicNotions.BoundedSOS
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.Hierarchy
import Mathlib.RingTheory.Polynomial.Chebyshev

/-! Explicit polynomial square identities for scalar padding certificates.
The second-kind variance identity is proved algebraically; no positivity
claim is converted to a sum of squares without explicit roots. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace ChebyshevSOSKernel

open scoped BigOperators
open MvPolynomial

abbrev P (n : ℕ) := Foundation.Polynomial n

def U {n : ℕ} (t : P n) (k : ℕ) : P n :=
  Polynomial.aeval t (Polynomial.Chebyshev.U ℝ (k : ℤ))

def T {n : ℕ} (t : P n) (k : ℕ) : P n :=
  Polynomial.aeval t (Polynomial.Chebyshev.T ℝ (k : ℤ))

@[simp] theorem U_zero {n : ℕ} (t : P n) : U t 0 = 1 := by simp [U]
@[simp] theorem U_one {n : ℕ} (t : P n) : U t 1 = 2*t := by
  simp only [U,Nat.cast_one,Polynomial.Chebyshev.U_one,map_mul,map_ofNat,
    Polynomial.aeval_X]
@[simp] theorem T_zero {n : ℕ} (t : P n) : T t 0 = 1 := by simp [T]
@[simp] theorem T_one {n : ℕ} (t : P n) : T t 1 = t := by simp [T]

theorem U_succ_succ {n : ℕ} (t : P n) (k : ℕ) :
    U t (k+2) = 2*t*U t (k+1)-U t k := by
  have h := congrArg (Polynomial.aeval t) (Polynomial.Chebyshev.U_add_two ℝ (k:ℤ))
  simpa only [U, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
    map_sub, map_mul, map_ofNat, Polynomial.aeval_X] using h

theorem T_succ_succ {n : ℕ} (t : P n) (k : ℕ) :
    T t (k+2) = 2*t*T t (k+1)-T t k := by
  have h := congrArg (Polynomial.aeval t) (Polynomial.Chebyshev.T_add_two ℝ (k:ℤ))
  simpa only [T, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
    map_sub, map_mul, map_ofNat, Polynomial.aeval_X] using h

theorem U_degree {n : ℕ} (t : P n) (ht : t.totalDegree ≤ 1) (k : ℕ) :
    (U t k).totalDegree ≤ k := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one =>
      rw [U_one]
      exact (totalDegree_mul _ _).trans (by
        simpa only [show (2:P n)=C (2:ℝ) from rfl,totalDegree_C,zero_add] using ht)
  | more k hk hk1 =>
      rw [U_succ_succ]
      apply (totalDegree_sub _ _).trans
      apply max_le
      · have htwo : (2*t).totalDegree ≤ 1 :=
          (totalDegree_mul _ _).trans (by
            simpa only [show (2:P n)=C (2:ℝ) from rfl,totalDegree_C,zero_add] using ht)
        exact (totalDegree_mul _ _).trans (by omega)
      · omega

theorem T_degree {n : ℕ} (t : P n) (ht : t.totalDegree ≤ 1) (k : ℕ) :
    (T t k).totalDegree ≤ k := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using ht
  | more k hk hk1 =>
      rw [T_succ_succ]
      apply (totalDegree_sub _ _).trans
      apply max_le
      · have htwo : (2*t).totalDegree ≤ 1 :=
          (totalDegree_mul _ _).trans (by
            simpa only [show (2:P n)=C (2:ℝ) from rfl,totalDegree_C,zero_add] using ht)
        exact (totalDegree_mul _ _).trans (by omega)
      · omega

theorem U_wronskian {n : ℕ} (t : P n) (k : ℕ) :
    U t (k+1)^2-2*t*U t (k+1)*U t k+U t k^2=1 := by
  induction k with
  | zero => simp; ring
  | succ k ih =>
      rw [show k+1+1=k+2 by omega, U_succ_succ]
      linear_combination ih

theorem T_U_identity {n : ℕ} (t : P n) (k : ℕ) :
    T t (k+1)^2+(1-t^2)*U t k^2=1 := by
  have h := congrArg (Polynomial.aeval t)
    (Polynomial.Chebyshev.U_eq_X_mul_U_add_T ℝ (k:ℤ))
  have hT : U t (k+1)=t*U t k+T t (k+1) := by
    simpa only [U,T,Nat.cast_add,Nat.cast_one,map_add,map_mul,
      Polynomial.aeval_X] using h
  have heq : T t (k+1)=U t (k+1)-t*U t k := by linear_combination -hT
  rw [heq]
  linear_combination U_wronskian t k

def varianceSum {n : ℕ} (t : P n) (k : ℕ) : P n :=
  ∑ d ∈ Finset.range k, ∑ j ∈ Finset.range (d+1), U t j^2

theorem varianceSum_zero {n : ℕ} (t : P n) : varianceSum t 0=0 := by
  simp [varianceSum]

theorem varianceSum_one {n : ℕ} (t : P n) : varianceSum t 1=1 := by
  simp [varianceSum]

theorem varianceSum_succ {n : ℕ} (t : P n) (k : ℕ) :
    varianceSum t (k+1)=varianceSum t k+
      ∑ j ∈ Finset.range (k+1), U t j^2 := by
  simp only [varianceSum,Finset.sum_range_succ]

theorem varianceSum_second_difference {n : ℕ} (t : P n) (k : ℕ) :
    varianceSum t (k+2)-2*varianceSum t (k+1)+varianceSum t k=U t (k+1)^2 := by
  have ha := varianceSum_succ t k
  have hb := varianceSum_succ t (k+1)
  rw [Finset.sum_range_succ] at hb
  linear_combination hb-ha

theorem U_square_second_difference {n : ℕ} (t : P n) (k : ℕ) :
    U t (k+2)^2-2*U t (k+1)^2+U t k^2=
      2-4*(1-t^2)*U t (k+1)^2 := by
  rw [U_succ_succ]
  linear_combination 2*(U_wronskian t k)

/-- A finite sum of actual squares, with each lower U polynomial repeated
the required number of times. This is the Chebyshev variance identity. -/
theorem variance_identity {n : ℕ} (t : P n) (k : ℕ) :
    ((k+1 : ℕ) : P n)^2-U t k^2=4*(1-t^2)*varianceSum t k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [varianceSum]
  | one => simp [varianceSum]; ring
  | more k hk hk1 =>
      have hsum := varianceSum_second_difference t k
      have hu := U_square_second_difference t k
      push_cast at hk hk1 ⊢
      linear_combination 2*hk1-hk-hu-4*(1-t^2)*hsum

theorem varianceSum_sos {n : ℕ} (t : P n) (ht : t.totalDegree ≤ 1) (k : ℕ) :
    BoundedSOS k (varianceSum t (k+1)) := by
  apply BoundedSOS.sum
  intro d hd
  apply BoundedSOS.sum
  intro j hj
  apply BoundedSOS.square
  have hd' := Finset.mem_range.mp hd
  have hj' := Finset.mem_range.mp hj
  exact (U_degree t ht j).trans (by omega)

/-- The normalizing denominator is nonzero even for the smallest index. -/
def kernelF {n : ℕ} (t : P n) (k : ℕ) : P n :=
  C (4/((k+2:ℕ):ℝ)^4)*
    (C (((k+2:ℕ):ℝ)^2)+U t (k+1)^2)*varianceSum t (k+1)

def kernelG {n : ℕ} (t : P n) (k : ℕ) : P n :=
  C (1/((k+2:ℕ):ℝ)^4)*U t (k+1)^4

theorem kernelF_sos {n : ℕ} (t : P n) (ht : t.totalDegree ≤ 1) (k : ℕ) :
    BoundedSOS (2*k+1) (kernelF t k) := by
  have hc : BoundedSOS (k+1) (C (((k+2:ℕ):ℝ)^2) : P n) := by
    simpa only [map_pow] using BoundedSOS.square (C (((k+2:ℕ):ℝ)))
      (by simpa only [totalDegree_C] using (Nat.zero_le (k+1)))
  have hu := BoundedSOS.square (U t (k+1)) (U_degree t ht (k+1))
  have h := ((hc.add hu).scale (4/((k+2:ℕ):ℝ)^4) (by positivity)).mul
    (varianceSum_sos t ht k)
  simpa only [kernelF,show k+1+k=2*k+1 by omega] using h

theorem kernelG_sos {n : ℕ} (t : P n) (ht : t.totalDegree ≤ 1) (k : ℕ) :
    BoundedSOS (2*k+2) (kernelG t k) := by
  have h := (BoundedSOS.square (U t (k+1)^2)
    ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (U_degree t ht (k+1))))).scale
      (1/((k+2:ℕ):ℝ)^4) (by positivity)
  simpa only [kernelG,show 2*(k+1)=2*k+2 by omega,←pow_mul] using h

theorem kernel_partition {n : ℕ} (t : P n) (k : ℕ) :
    (1-t^2)*kernelF t k+kernelG t k=1 := by
  let m : ℝ := ((k+2:ℕ):ℝ)
  have hm : m≠0 := by dsimp [m]; positivity
  have hvar := variance_identity t (k+1)
  have hcast : (((k+1+1:ℕ):P n))=C m := by
    dsimp [m]
    norm_cast
  rw [hcast] at hvar
  have hcancel : C (1/m^4)*(C m)^4=(1:P n) := by
    rw [←map_pow,←map_mul]
    field_simp <;> simp
  have hf : kernelF t k=C (1/m^4)*4*((C m)^2+U t (k+1)^2)*varianceSum t (k+1) := by
    change C (4/m^4)*(C (m^2)+U t (k+1)^2)*varianceSum t (k+1)=_
    rw [show (4/m^4)=(1/m^4)*4 by ring,map_mul,map_ofNat,map_pow]
  have hg : kernelG t k=C (1/m^4)*U t (k+1)^4 := by
    rfl
  rw [hf,hg]
  linear_combination -C (1/m^4)*((C m)^2+U t (k+1)^2)*hvar+hcancel

end ChebyshevSOSKernel
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
