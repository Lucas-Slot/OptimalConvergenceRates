import OptimalConvergenceRates.SphereDimensionBounds.SameDegreeRepair
import Mathlib.RingTheory.Polynomial.Chebyshev

/-! Explicit polynomial square identities for scalar padding certificates.
The second-kind variance identity is proved algebraically; no positivity
claim is converted to a sum of squares without explicit roots. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.ChebyshevSOSKernel

open scoped BigOperators
open MvPolynomial

abbrev P (n : ℕ) := OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial n

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

/-- A sum of explicit polynomial squares with a bound on each root. -/
def BoundedSOS {n : ℕ} (d : ℕ) (p : P n) : Prop :=
  ∃ (m : ℕ) (a : Fin m → P n),
    (∀ i, (a i).totalDegree ≤ d) ∧ p=∑ i, a i^2

namespace BoundedSOS

theorem of_family {n d : ℕ} {I : Type*} [Fintype I] (a : I → P n)
    (ha : ∀ i, (a i).totalDegree ≤ d) : BoundedSOS d (∑ i, a i^2) := by
  classical
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I,fun j => a (e.symm j),fun _ => ha _,?_⟩
  exact (e.symm.sum_comp (fun i => a i^2)).symm

theorem zero {n d : ℕ} : BoundedSOS d (0:P n) := by
  exact ⟨0,Fin.elim0,fun i => Fin.elim0 i,by simp⟩

theorem square {n d : ℕ} (p : P n) (hp : p.totalDegree ≤ d) :
    BoundedSOS d (p^2) := by
  simpa using of_family (fun _ : Fin 1 => p) (fun _ => hp)

theorem mono {n a b : ℕ} {p : P n} (hp : BoundedSOS a p) (hab : a ≤ b) :
    BoundedSOS b p := by
  rcases hp with ⟨m,v,hv,hid⟩
  exact ⟨m,v,fun i => (hv i).trans hab,hid⟩

theorem add {n d : ℕ} {p q : P n} (hp : BoundedSOS d p) (hq : BoundedSOS d q) :
    BoundedSOS d (p+q) := by
  classical
  rcases hp with ⟨m,a,ha,rfl⟩
  rcases hq with ⟨l,b,hb,rfl⟩
  refine ⟨m+l,Fin.addCases a b,?_,?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using ha j
    · simpa using hb j
  · rw [Fin.sum_univ_add]
    simp

theorem mul {n a b : ℕ} {p q : P n} (hp : BoundedSOS a p) (hq : BoundedSOS b q) :
    BoundedSOS (a+b) (p*q) := by
  classical
  rcases hp with ⟨m,v,hv,rfl⟩
  rcases hq with ⟨l,w,hw,rfl⟩
  have hdeg (ij : Fin m × Fin l) : (v ij.1*w ij.2).totalDegree≤a+b :=
    (totalDegree_mul _ _).trans (Nat.add_le_add (hv _) (hw _))
  have hid : (∑ i, v i^2)*(∑ j, w j^2)=∑ ij : Fin m × Fin l, (v ij.1*w ij.2)^2 := by
    simp only [Fintype.sum_prod_type,mul_pow,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hid]
  exact of_family _ hdeg

theorem scale {n d : ℕ} {p : P n} (hp : BoundedSOS d p) (c : ℝ) (hc : 0 ≤ c) :
    BoundedSOS d (C c*p) := by
  classical
  rcases hp with ⟨m,a,ha,rfl⟩
  have hdeg (i : Fin m) : (C (Real.sqrt c)*a i).totalDegree≤d :=
    (totalDegree_mul _ _).trans (by simpa using ha i)
  have hid : C c*(∑ i, a i^2)=∑ i, (C (Real.sqrt c)*a i)^2 := by
    simp only [mul_pow,←map_pow,Real.sq_sqrt hc,Finset.mul_sum]
  rw [hid]
  exact of_family _ hdeg

theorem sum {n d : ℕ} {I : Type*} (s : Finset I) (p : I → P n)
    (hp : ∀ i ∈ s, BoundedSOS d (p i)) : BoundedSOS d (∑ i∈s,p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (n:=n) (d:=d))
  | @insert i s his ih =>
      rw [Finset.sum_insert his]
      exact (hp i (Finset.mem_insert_self ..)).add
        (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem degree {n d : ℕ} {p : P n} (hp : BoundedSOS d p) : p.totalDegree≤2*d := by
  rcases hp with ⟨m,a,ha,rfl⟩
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (ha i))

theorem rename {n m d : ℕ} {p : P n} (hp : BoundedSOS d p) (f : Fin n → Fin m) :
    BoundedSOS d (MvPolynomial.rename f p) := by
  rcases hp with ⟨l,a,ha,hid⟩
  rw [hid,map_sum]
  simp only [map_pow]
  exact of_family _ (fun i => (totalDegree_rename_le f (a i)).trans (ha i))

end BoundedSOS

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

end OptimalConvergenceRates.SphereDimensionBounds.ChebyshevSOSKernel
