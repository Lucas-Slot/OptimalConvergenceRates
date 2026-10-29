import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.GegenbauerOrthogonality
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.AngularPolynomialPositivity

/-! Actual positive Gegenbauer square norms and their exact recurrence. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace GegenbauerNorms

open Polynomial GegenbauerAlgebra GegenbauerOrthogonality AngularPolynomialPositivity

def pair (s : ℕ) (p q : Polynomial ℝ) : ℝ := normalizedZonalFunctional s (p*q)
def normSq (N j : ℕ) : ℝ := pair (N-2) (gegenbauer (N:ℝ) j) (gegenbauer (N:ℝ) j)

theorem pair_comm (s : ℕ) (p q : Polynomial ℝ) : pair s p q=pair s q p := by
  unfold pair
  rw [mul_comm]

theorem pair_sub_left (s : ℕ) (p q r : Polynomial ℝ) :
    pair s (p-q) r=pair s p r-pair s q r := by
  unfold pair
  rw [sub_mul,map_sub]

theorem pair_C_mul (s : ℕ) (a : ℝ) (p q : Polynomial ℝ) :
    pair s (C a*p) q=a*pair s p q := by
  unfold pair
  rw [mul_assoc,←Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul]

theorem normSq_pos {N : ℕ} (hN : 3 ≤ N) (j : ℕ) : 0 < normSq N j := by
  unfold normSq pair
  rw [←pow_two]
  exact zonal_square_pos _ _ (gegenbauer_ne_zero _ (by exact_mod_cast hN) j)

theorem normSq_zero (N : ℕ) : normSq N 0=1 := by
  unfold normSq pair
  simp only [gegenbauer,one_mul]
  have h := normalizedZonalFunctional_X_pow (N-2) 0
  simpa only [pow_zero,normalizedCosineMoment_zero] using h

theorem recurrence_all {N : ℕ} (hN : 3 ≤ N) (j : ℕ) :
    C ((j:ℝ)+(N:ℝ)-2)*gegenbauer (N:ℝ) (j+1)=
      C (2*(j:ℝ)+(N:ℝ)-2)*X*gegenbauer (N:ℝ) j-
        C (j:ℝ)*gegenbauer (N:ℝ) (j-1) := by
  cases j with
  | zero => simp [gegenbauer]
  | succ m =>
    have h := recurrence_scaled (N:ℝ) (by exact_mod_cast hN) m
    have ha : ((m:ℝ)+1)+(N:ℝ)-2=(m:ℝ)+(N:ℝ)-1 := by ring
    have hb : 2*((m:ℝ)+1)+(N:ℝ)-2=2*(m:ℝ)+(N:ℝ) := by ring
    simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.cast_add,
      Nat.cast_one,ha,hb,show m+1+1=m+2 by omega] using h

theorem normSq_recurrence {N : ℕ} (hN : 3 ≤ N) (j : ℕ) :
    (((j:ℝ)+(N:ℝ)-2)*(2*(j:ℝ)+(N:ℝ)))*normSq N (j+1)=
      ((j:ℝ)+1)*(2*(j:ℝ)+(N:ℝ)-2)*normSq N j := by
  have h1 := congrArg (fun p ↦ pair (N-2) p (gegenbauer (N:ℝ) (j+1))) (recurrence_all hN j)
  rw [pair_C_mul,pair_sub_left,mul_assoc,pair_C_mul,pair_C_mul] at h1
  have ho1 : pair (N-2) (gegenbauer (N:ℝ) (j-1)) (gegenbauer (N:ℝ) (j+1))=0 :=
    orthogonal hN (by omega)
  rw [ho1,mul_zero,sub_zero] at h1
  have h2 := congrArg (fun p ↦ pair (N-2) p (gegenbauer (N:ℝ) j)) (recurrence_all hN (j+1))
  rw [pair_C_mul,pair_sub_left,mul_assoc,pair_C_mul,pair_C_mul] at h2
  have ho2 : pair (N-2) (gegenbauer (N:ℝ) (j+1+1)) (gegenbauer (N:ℝ) j)=0 :=
    orthogonal hN (by omega)
  rw [ho2,mul_zero,Nat.add_sub_cancel] at h2
  have hcross : pair (N-2) (X*gegenbauer (N:ℝ) (j+1)) (gegenbauer (N:ℝ) j)=
      pair (N-2) (X*gegenbauer (N:ℝ) j) (gegenbauer (N:ℝ) (j+1)) := by
    unfold pair
    congr 1
    ring
  rw [hcross] at h2
  change ((j:ℝ)+(N:ℝ)-2)*normSq N (j+1)=_ at h1
  change 0=(2*((j+1:ℕ):ℝ)+(N:ℝ)-2)*_
    -((j+1:ℕ):ℝ)*normSq N j at h2
  push_cast at h2
  linear_combination (2*(j:ℝ)+(N:ℝ))*h1-(2*(j:ℝ)+(N:ℝ)-2)*h2

theorem normSq_succ {N : ℕ} (hN : 3 ≤ N) (j : ℕ) :
    normSq N (j+1)=(((j:ℝ)+1)*(2*(j:ℝ)+(N:ℝ)-2)/
      (((j:ℝ)+(N:ℝ)-2)*(2*(j:ℝ)+(N:ℝ))))*normSq N j := by
  have hNR : (3:ℝ) ≤ N := by exact_mod_cast hN
  have hjR : (0:ℝ) ≤ j := by positivity
  have ha : (j:ℝ)+(N:ℝ)-2 ≠ 0 := by linarith
  have hb : 2*(j:ℝ)+(N:ℝ) ≠ 0 := by linarith
  have h := normSq_recurrence hN j
  field_simp [ha,hb]
  linear_combination h

theorem gegenbauer_natDegree_le (N : ℝ) (j : ℕ) : (gegenbauer N j).natDegree ≤ j := by
  induction j using Nat.twoStepInduction with
  | zero => simp [gegenbauer]
  | one => simp [gegenbauer]
  | more m hm hm1 =>
    rw [gegenbauer]
    apply Polynomial.natDegree_mul_le.trans
    simp only [Polynomial.natDegree_C,zero_add]
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · calc
        _ ≤ (C (2*(m:ℝ)+N)*X).natDegree+(gegenbauer N (m+1)).natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ 1+(m+1) := by
          apply Nat.add_le_add _ hm1
          simpa only [Polynomial.natDegree_C,Polynomial.natDegree_X,zero_add] using
            (Polynomial.natDegree_mul_le (p:=C (2*(m:ℝ)+N)) (q:=X))
        _=m+2 := by omega
    · exact Polynomial.natDegree_mul_le.trans (by
        simpa only [Polynomial.natDegree_C,zero_add] using hm.trans (by omega : m ≤ m+2))

end GegenbauerNorms
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
