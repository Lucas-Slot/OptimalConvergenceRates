import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.BanachDiagonal
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.HomogeneousTensorSeries
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.SphereCurve
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.Hierarchy
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Actual symmetric tensors of homogeneous polynomial objectives and
degree-explicit Taylor estimates. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace DegreeTaylorBounds

open scoped BigOperators InnerProductSpace
open MvPolynomial Foundation

abbrev Point (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev P (n : ℕ) := Foundation.Polynomial n

def evalForm {n : ℕ} (p : P n) (x : Point n) : ℝ := eval (fun i ↦ x i) p

theorem evalForm_analytic {n : ℕ} (p : P n) : AnalyticOnNhd ℝ (evalForm p) Set.univ := by
  convert AnalyticOnNhd.eval_continuousLinearMap'
    (fun i : Fin n ↦ PiLp.proj (𝕜:=ℝ) (p:=2) (β:=fun _ : Fin n ↦ ℝ) i) p using 1
  rfl

theorem evalForm_contDiff {n : ℕ} (p : P n) : ContDiff ℝ ⊤ (evalForm p) := by
  exact (evalForm_analytic p).contDiff

theorem iteratedDeriv_polynomial_eval (q : Polynomial ℝ) (k : ℕ) :
    iteratedDeriv k q.eval=(Polynomial.derivative^[k] q).eval := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [iteratedDeriv_succ,ih,Function.iterate_succ_apply']
      funext x
      exact Polynomial.deriv (Polynomial.derivative^[k] q)

def lineMap {n : ℕ} (x : Point n) : ℝ →L[ℝ] Point n :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) x

theorem iteratedFDeriv_origin_diagonal {n d : ℕ} (p : P n) (hp : p.IsHomogeneous d)
    (x : Point n) :
    iteratedFDeriv ℝ d (evalForm p) 0 (fun _ ↦ x)=(d.factorial:ℝ)*evalForm p x := by
  let q : Polynomial ℝ := Polynomial.C (evalForm p x)*Polynomial.X^d
  have hline : evalForm p ∘ lineMap x=q.eval := by
    funext t
    change eval (fun i ↦ t*x i) p=q.eval t
    rw [homogeneous_eval_scale p d hp]
    simp only [q, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      evalForm]
    ring
  have hcomp := (lineMap x).iteratedFDeriv_comp_right (evalForm_contDiff p) 0
    (i:=d) (by simp)
  have hcomp' := congrArg (fun B ↦ B (fun _ : Fin d ↦ (1:ℝ))) hcomp
  rw [hline] at hcomp'
  have hscalar : iteratedDeriv d q.eval 0=(d.factorial:ℝ)*evalForm p x := by
    rw [iteratedDeriv_polynomial_eval]
    simp only [q,Polynomial.iterate_derivative_C_mul,
      Polynomial.iterate_derivative_X_pow_eq_C_mul,Nat.descFactorial_self,Nat.sub_self,
      pow_zero,mul_one,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_one]
    ring
  rw [←iteratedDeriv_eq_iteratedFDeriv] at hcomp'
  have hpoint : lineMap x 0=0 := by simp [lineMap]
  simpa only [hpoint,ContinuousMultilinearMap.compContinuousLinearMap_apply,
    lineMap, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, one_smul,
      zero_smul, hscalar]
    using hcomp'.symm

def associatedTensor {n : ℕ} (p : P n) (d : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin d ↦ Point n) ℝ :=
  (d.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ d (evalForm p) 0

theorem associatedTensor_diagonal {n d : ℕ} (p : P n) (hp : p.IsHomogeneous d)
    (x : Point n) : associatedTensor p d (fun _ ↦ x)=evalForm p x := by
  simp only [associatedTensor,smul_apply,smul_eq_mul,
    iteratedFDeriv_origin_diagonal p hp x]
  rw [←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero d),one_mul]

theorem associatedTensor_symmetric {n : ℕ} (p : P n) (d : ℕ)
    (v : Fin d → Point n) (i j : Fin d) :
    associatedTensor p d (v ∘ Equiv.swap i j)=associatedTensor p d v := by
  have hcont : ContDiffAt ℝ ⊤ (evalForm p) (0:Point n) := (evalForm_contDiff p).contDiffAt
  have hs := hcont.iteratedFDeriv_comp_perm v (Equiv.swap i j)
  simp only [associatedTensor,smul_apply,hs]

theorem associatedTensor_norm_bound {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (p : P n) (hp : p.IsHomogeneous d) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x : Fin n → ℝ,(∑ i,x i^2)=1 → |eval x p|≤M) :
    ‖associatedTensor p d‖≤M := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  apply BanachDiagonal.symmetric_opNorm_bound hd (associatedTensor p d)
    (associatedTensor_symmetric p d) M hM
  intro x hx
  rw [associatedTensor_diagonal p hp x]
  apply hbound
  have hs : ‖x‖^2=∑ i,‖x i‖^2 := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n ↦ ℝ) x
  simpa only [hx,one_pow,Real.norm_eq_abs,sq_abs] using hs.symm

/-- Exact degree-dependent derivatives of the actual polynomial, first on
a repeated direction. The integer descending factorial is d!/(d-j)!. -/
theorem actual_diagonal_derivative_bound {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (p : P n) (hp : p.IsHomogeneous d) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x : Fin n → ℝ,(∑ i,x i^2)=1 → |eval x p|≤M)
    (z h : Point n) (j : ℕ) (hj : j≤d) :
    |iteratedFDeriv ℝ j (evalForm p) z (fun _ ↦ h)|≤
      (d.descFactorial j:ℝ)*M*‖z‖^(d-j)*‖h‖^j := by
  have hrepr : evalForm p=(fun x ↦ associatedTensor p d (fun _ ↦ x)) := by
    funext x
    exact (associatedTensor_diagonal p hp x).symm
  have hb := HomogeneousTensorSeries.diagonal_iteratedFDeriv_bound (associatedTensor p d) z h j hj
  rw [←hrepr] at hb
  rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
  apply hb.trans
  have hnorm := associatedTensor_norm_bound hn hd p hp M hM hbound
  gcongr

theorem actual_taylor_coefficient_bound {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (p : P n) (hp : p.IsHomogeneous d) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x : Fin n → ℝ,(∑ i,x i^2)=1 → |eval x p|≤M)
    (z h : Point n) (j : ℕ) (hj : j≤d) :
    |(j.factorial:ℝ)⁻¹*iteratedFDeriv ℝ j (evalForm p) z (fun _ ↦ h)|≤
      (d.choose j:ℝ)*M*‖z‖^(d-j)*‖h‖^j := by
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  have hD := actual_diagonal_derivative_bound hn hd p hp M hM hbound z h j hj
  have hmul := mul_le_mul_of_nonneg_left hD (inv_nonneg.mpr (Nat.cast_nonneg j.factorial))
  convert hmul using 1
  rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
  rw [show (j.factorial:ℝ)⁻¹*((j.factorial:ℝ)*(d.choose j:ℝ)*M*‖z‖^(d-j)*‖h‖^j)=
    ((j.factorial:ℝ)⁻¹*(j.factorial:ℝ))*((d.choose j:ℝ)*M*‖z‖^(d-j)*‖h‖^j) by ring]
  rw [inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero j),one_mul]

/-- Full mixed derivative version of the exact real-Hilbert estimate. -/
theorem actual_mixed_derivative_bound {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (p : P n) (hp : p.IsHomogeneous d) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x : Fin n → ℝ,(∑ i,x i^2)=1 → |eval x p|≤M)
    (z : Point n) (j : ℕ) (hj0 : 0<j) (hj : j≤d) (v : Fin j → Point n) :
    |iteratedFDeriv ℝ j (evalForm p) z v|≤
      ((d.descFactorial j:ℝ)*M*‖z‖^(d-j))*∏ i,‖v i‖ := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hcont : ContDiffAt ℝ ⊤ (evalForm p) z := (evalForm_contDiff p).contDiffAt
  apply BanachDiagonal.symmetric_multilinear_bound hj0 (iteratedFDeriv ℝ j (evalForm p) z)
    (fun w i k ↦ hcont.iteratedFDeriv_comp_perm w (Equiv.swap i k))
    ((d.descFactorial j:ℝ)*M*‖z‖^(d-j)) (by positivity)
  intro x hx
  simpa only [hx,one_pow,mul_one] using
    actual_diagonal_derivative_bound hn hd p hp M hM hbound z x j hj

end DegreeTaylorBounds
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
