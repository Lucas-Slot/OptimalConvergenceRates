import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.GegenbauerAlgebra

/-! Orthogonality for the actual angular functional, derived from the
proved polynomial Stokes identity and Gegenbauer differential equation. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace GegenbauerOrthogonality

open Polynomial GegenbauerAlgebra SphereAngularMoments

def differentialOperator (s : ℕ) (p : Polynomial ℝ) : Polynomial ℝ :=
  (1-X^2)*p.derivative.derivative-C ((s:ℝ)+1)*X*p.derivative

theorem integration_by_parts (s : ℕ) (p q : Polynomial ℝ) :
    normalizedZonalFunctional s (differentialOperator s p*q)=
      -normalizedZonalFunctional s ((1-X^2)*p.derivative*q.derivative) := by
  have h := angular_stokes s (p.derivative*q)
  have hid : differentialOperator s p*q=
      (1-X^2)*(p.derivative*q).derivative-
        (1-X^2)*p.derivative*q.derivative-
        C ((s:ℝ)+1)*(X*(p.derivative*q)) := by
    simp only [differentialOperator,Polynomial.derivative_mul]
    ring
  rw [hid,map_sub,map_sub,←Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul,h]
  ring

theorem green_identity (s : ℕ) (p q : Polynomial ℝ) :
    normalizedZonalFunctional s (differentialOperator s p*q)=
      normalizedZonalFunctional s (p*differentialOperator s q) := by
  rw [mul_comm p (differentialOperator s q),integration_by_parts,integration_by_parts]
  congr 2
  ring

def eigenvalue (N j : ℕ) : ℝ := (j:ℝ)*((j:ℝ)+(N:ℝ)-2)

theorem eigenvalue_sub (N j k : ℕ) :
    eigenvalue N j-eigenvalue N k=((j:ℝ)-(k:ℝ))*((j:ℝ)+(k:ℝ)+(N:ℝ)-2) := by
  unfold eigenvalue
  ring

theorem eigenvalue_ne {N j k : ℕ} (hN : 3 ≤ N) (hjk : j ≠ k) :
    eigenvalue N j ≠ eigenvalue N k := by
  have hNR : (3:ℝ) ≤ N := by exact_mod_cast hN
  have hjR : (0:ℝ) ≤ j := by positivity
  have hkR : (0:ℝ) ≤ k := by positivity
  apply sub_ne_zero.mp
  rw [eigenvalue_sub]
  exact mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast hjk)) (ne_of_gt (by linarith))

theorem eigenfunction {N : ℕ} (hN : 3 ≤ N) (j : ℕ) :
    differentialOperator (N-2) (gegenbauer (N:ℝ) j)=
      -C (eigenvalue N j)*gegenbauer (N:ℝ) j := by
  cases j with
  | zero => simp [differentialOperator,gegenbauer,eigenvalue]
  | succ m =>
    have h := differential_equation_succ (N:ℝ) (by exact_mod_cast hN) m
    have hc : (((N-2:ℕ):ℝ)+1)=(N:ℝ)-1 := by
      rw [Nat.cast_sub (by omega : 2 ≤ N),Nat.cast_ofNat]
      ring
    have he : eigenvalue N (m+1)=((m:ℝ)+1)*((m:ℝ)+(N:ℝ)-1) := by
      simp only [eigenvalue,Nat.cast_add,Nat.cast_one]
      ring
    simp only [Nat.succ_eq_add_one,differentialOperator,hc,he]
    linear_combination h

theorem orthogonal {N j k : ℕ} (hN : 3 ≤ N) (hjk : j ≠ k) :
    normalizedZonalFunctional (N-2) (gegenbauer (N:ℝ) j*gegenbauer (N:ℝ) k)=0 := by
  let p := gegenbauer (N:ℝ) j
  let q := gegenbauer (N:ℝ) k
  let L := normalizedZonalFunctional (N-2)
  have h := green_identity (N-2) p q
  rw [eigenfunction hN j,eigenfunction hN k] at h
  have hleft : (-C (eigenvalue N j)*p)*q=-(C (eigenvalue N j)*(p*q)) := by ring
  have hright : p*(-C (eigenvalue N k)*q)=-(C (eigenvalue N k)*(p*q)) := by ring
  rw [hleft,hright,map_neg,map_neg,←Polynomial.smul_eq_C_mul,
    ←Polynomial.smul_eq_C_mul,map_smul,map_smul,smul_eq_mul,smul_eq_mul] at h
  have heq : (eigenvalue N j-eigenvalue N k)*L (p*q)=0 := by linarith
  exact (mul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr (eigenvalue_ne hN hjk))

theorem gegenbauer_eval_one (N : ℝ) (hN : 3 ≤ N) (j : ℕ) :
    (gegenbauer N j).eval 1=1 := by
  induction j using Nat.twoStepInduction with
  | zero => simp [gegenbauer]
  | one => simp [gegenbauer]
  | more m hm hm1 =>
    have h := congrArg (Polynomial.eval 1) (recurrence_scaled N hN m)
    simp only [Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_C,
      Polynomial.eval_X,hm,hm1,mul_one] at h
    have ht : (m:ℝ)+N-1 ≠ 0 := by
      have hmR : (0:ℝ) ≤ m := by positivity
      linarith
    apply mul_left_cancel₀ ht
    linear_combination h

theorem gegenbauer_ne_zero (N : ℝ) (hN : 3 ≤ N) (j : ℕ) : gegenbauer N j ≠ 0 := by
  intro hzero
  have h := gegenbauer_eval_one N hN j
  rw [hzero,Polynomial.eval_zero] at h
  norm_num at h

end GegenbauerOrthogonality
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
