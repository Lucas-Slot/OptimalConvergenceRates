import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.SphereAngularMoments

/-! Algebraic identities for normalized Gegenbauer polynomials. This module
does not assert a quadrature rule, a zero bound, or a localization estimate. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace GegenbauerAlgebra

open Polynomial

def gegenbauer (N : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => X
  | m+2 => C (1/((m:ℝ)+N-1))*
      (C (2*(m:ℝ)+N)*X*gegenbauer N (m+1)-C ((m:ℝ)+1)*gegenbauer N m)

theorem recurrence_scaled (N : ℝ) (hN : 3 ≤ N) (m : ℕ) :
    C ((m:ℝ)+N-1)*gegenbauer N (m+2)=
      C (2*(m:ℝ)+N)*X*gegenbauer N (m+1)-C ((m:ℝ)+1)*gegenbauer N m := by
  have ht : (m:ℝ)+N-1 ≠ 0 := by
    have hm : (0:ℝ) ≤ m := by positivity
    linarith
  rw [gegenbauer,←mul_assoc,←map_mul]
  have he : ((m:ℝ)+N-1)*(1/((m:ℝ)+N-1))=1 := by field_simp
  rw [he,map_one,one_mul]

theorem first_order_step (j N : ℝ) (f g h : Polynomial ℝ) (ht : j + N - 2 ≠ 0)
    (hrec : C (j + N - 2) * h = C (2 * j + N - 2) * X * g - C j * f)
    (hD : (1 - X ^ 2) * g.derivative = C j * (f - X * g))
    (hE : C j * f.derivative = C (j + N - 3) * (X * g.derivative - C j * g)) :
    (1-X^2)*h.derivative=C (j+1)*(g-X*h) ∧
      C (j+1)*g.derivative=C (j+N-2)*(X*h.derivative-C (j+1)*h) := by
  have hdrec := congrArg Polynomial.derivative hrec
  simp only [Polynomial.derivative_mul,Polynomial.derivative_C,
    Polynomial.derivative_sub,Polynomial.derivative_X,zero_mul,zero_add,one_mul] at hdrec
  have hder : C (j+N-2)*h.derivative=
      C (j+1)*C (j+N-2)*g+C (j+1)*X*g.derivative := by
    simp only [map_add,map_sub,map_mul,map_ofNat,map_one] at hdrec hE ⊢
    linear_combination hdrec-hE
  constructor
  · apply mul_left_cancel₀ (show C (j+N-2) ≠ (0:Polynomial ℝ) by exact C_ne_zero.mpr ht)
    simp only [map_add,map_sub,map_mul,map_ofNat,map_one] at hder hD hrec ⊢
    linear_combination (1-X^2)*hder+(C j+1)*X*hD+(C j+1)*X*hrec
  · simp only [map_add,map_sub,map_mul,map_ofNat,map_one] at hder hD hrec ⊢
    linear_combination -X*hder+(C j+1)*hrec+(C j+1)*hD

theorem first_order_identities (N : ℝ) (hN : 3 ≤ N) (m : ℕ) :
    (1-X^2)*(gegenbauer N (m+1)).derivative=
      C ((m:ℝ)+1)*(gegenbauer N m-X*gegenbauer N (m+1)) ∧
    C ((m:ℝ)+1)*(gegenbauer N m).derivative=
      C ((m:ℝ)+N-2)*(X*(gegenbauer N (m+1)).derivative-
        C ((m:ℝ)+1)*gegenbauer N (m+1)) := by
  induction m with
  | zero =>
    simp only [gegenbauer,Polynomial.derivative_one,Polynomial.derivative_X,
      Nat.cast_zero,zero_add,map_one,mul_one,mul_zero]
    constructor <;> ring
  | succ m ih =>
    have ht : ((m:ℝ)+1)+N-2 ≠ 0 := by
      have hm : (0:ℝ) ≤ m := by positivity
      linarith
    have hrec := recurrence_scaled N hN m
    have hrec' : C (((m:ℝ)+1)+N-2)*gegenbauer N (m+2)=
        C (2*((m:ℝ)+1)+N-2)*X*gegenbauer N (m+1)-C ((m:ℝ)+1)*gegenbauer N m := by
      have ha : ((m:ℝ)+1)+N-2=(m:ℝ)+N-1 := by ring
      have hb : 2*((m:ℝ)+1)+N-2=2*(m:ℝ)+N := by ring
      simpa only [ha,hb] using hrec
    have h := first_order_step ((m:ℝ)+1) N (gegenbauer N m)
      (gegenbauer N (m+1)) (gegenbauer N (m+2)) ht hrec' ih.1 (by
        have he : ((m:ℝ)+1)+N-3=(m:ℝ)+N-2 := by ring
        simpa only [he] using ih.2)
    simpa only [Nat.cast_add,Nat.cast_one,Nat.succ_eq_add_one,Nat.add_assoc] using h

theorem differential_equation_succ (N : ℝ) (hN : 3 ≤ N) (m : ℕ) :
    (1-X^2)*(gegenbauer N (m+1)).derivative.derivative-
      C (N-1)*X*(gegenbauer N (m+1)).derivative+
      C (((m:ℝ)+1)*((m:ℝ)+N-1))*gegenbauer N (m+1)=0 := by
  obtain ⟨hD,hE⟩ := first_order_identities N hN m
  have hd := congrArg Polynomial.derivative hD
  simp only [Polynomial.derivative_mul,Polynomial.derivative_C,Polynomial.derivative_sub,
    Polynomial.derivative_one,Polynomial.derivative_X,Polynomial.derivative_X_pow,
    zero_mul,zero_add,one_mul] at hd
  norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one] at hd
  simp only [map_add,map_sub,map_mul,map_ofNat,map_one] at hd hE ⊢
  linear_combination hd+hE

end GegenbauerAlgebra
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
