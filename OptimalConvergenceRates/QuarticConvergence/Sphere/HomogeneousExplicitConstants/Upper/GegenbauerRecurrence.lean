import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.GegenbauerJacobi

/-! Actual orthonormal three-term recurrence, including the boundary
degree zero, for constructing the finite Gaussian spectral measure. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace GegenbauerRecurrence

open Polynomial GegenbauerAlgebra GegenbauerNorms GegenbauerJacobi

def lowerCoefficient (N j : ℕ) : ℝ :=
  ((j:ℝ)/(2*(j:ℝ)+(N:ℝ)-2))*
    (Real.sqrt (normSq N (j-1))/Real.sqrt (normSq N j))

theorem normalized_scalar_recurrence (a b k x f g h r rn rp : ℝ)
    (hb : b ≠ 0) (hr : r ≠ 0) (hn : rn ≠ 0) (hp : rp ≠ 0)
    (hrec : a * h=b*x*g-k*f) :
    x*(g/r)=((a/b)*(rn/r))*(h/rn)+((k/b)*(rp/r))*(f/rp) := by
  have hterm (u rv v : ℝ) (hrv : rv ≠ 0) :
      ((u/b)*(rv/r))*(v/rv)=(u*v)/(b*r) := by
    field_simp [hb,hr,hrv]
  rw [hterm a rn h hn,hterm k rp f hp,←add_div]
  have hs : b*x*g=a*h+k*f := by linarith
  rw [←hs]
  field_simp [hb,hr]

theorem normalized_three_term_raw {N : ℕ} (hN : 3 ≤ N) (j : ℕ) :
    X*normalized N j=C (coefficient N j)*normalized N (j+1)+
      C (lowerCoefficient N j)*normalized N (j-1) := by
  apply Polynomial.funext
  intro x
  have h := congrArg (Polynomial.eval x) (recurrence_all hN j)
  simp only [Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_C,Polynomial.eval_X] at h
  simp only [normalized,coefficient,lowerCoefficient,Polynomial.eval_mul,
    Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X]
  have hNR : (3:ℝ) ≤ N := by exact_mod_cast hN
  have hjR : (0:ℝ) ≤ j := by positivity
  have hb : 2*(j:ℝ)+(N:ℝ)-2 ≠ 0 := by linarith
  have hc := (Real.sqrt_pos.mpr (normSq_pos hN j)).ne'
  have hd := (Real.sqrt_pos.mpr (normSq_pos hN (j+1))).ne'
  have he := (Real.sqrt_pos.mpr (normSq_pos hN (j-1))).ne'
  simpa only [one_div_mul_eq_div] using
    normalized_scalar_recurrence ((j:ℝ)+(N:ℝ)-2) (2*(j:ℝ)+(N:ℝ)-2)
      (j:ℝ) x _ _ _ _ _ _ hb hc hd he h

theorem pair_add_left (s : ℕ) (p q r : Polynomial ℝ) :
    pair s (p+q) r=pair s p r+pair s q r := by
  unfold pair
  rw [add_mul,map_add]

theorem pair_X_comm (s : ℕ) (p q : Polynomial ℝ) : pair s (X*p) q=pair s (X*q) p := by
  unfold pair
  congr 1
  ring

theorem lowerCoefficient_zero (N : ℕ) : lowerCoefficient N 0=0 := by simp [lowerCoefficient]

theorem lowerCoefficient_succ {N : ℕ} (hN : 3 ≤ N) (j : ℕ) :
    lowerCoefficient N (j+1)=coefficient N j := by
  have h := pair_X_comm (N-2) (normalized N (j+1)) (normalized N j)
  rw [normalized_three_term_raw hN (j+1),normalized_three_term_raw hN j,
    pair_add_left,pair_add_left,pair_C_mul,pair_C_mul,pair_C_mul,pair_C_mul] at h
  rw [normalized_orthogonal hN (by omega : j+1+1 ≠ j),
    normalized_self hN (j+1),Nat.add_sub_cancel,normalized_self hN j,
    normalized_orthogonal hN (by omega : j-1 ≠ j+1)] at h
  simpa only [mul_zero,zero_add,mul_one,add_zero] using h

theorem normalized_three_term_succ {N : ℕ} (hN : 3 ≤ N) (j : ℕ) :
    X*normalized N (j+1)=C (coefficient N (j+1))*normalized N (j+2)+
      C (coefficient N j)*normalized N j := by
  have h := normalized_three_term_raw hN (j+1)
  simpa only [Nat.add_sub_cancel,lowerCoefficient_succ hN,
    show j+1+1=j+2 by omega] using h

theorem normalized_three_term_zero {N : ℕ} (hN : 3 ≤ N) :
    X*normalized N 0=C (coefficient N 0)*normalized N 1 := by
  simpa only [lowerCoefficient_zero,map_zero,zero_mul,add_zero] using
    normalized_three_term_raw hN 0

end GegenbauerRecurrence
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
