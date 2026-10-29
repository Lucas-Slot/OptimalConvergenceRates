import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.DegreeTaylorBounds
import Mathlib.Analysis.Calculus.Taylor

/-! Actual cubic Taylor polynomials and their fourth-order bounds. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace CubicTaylorBounds

open scoped BigOperators
open MvPolynomial Foundation DegreeTaylorBounds

def radialLinePolynomial {n : ℕ} (p : P n) (x : Point n) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (p.totalDegree+1),
    Polynomial.C (evalForm (homogeneousComponent k p) x)*Polynomial.X^k

theorem radialLinePolynomial_eval {n : ℕ} (p : P n) (x : Point n) (t : ℝ) :
    (radialLinePolynomial p x).eval t=evalForm p (t • x) := by
  classical
  calc
    (radialLinePolynomial p x).eval t=
        ∑ k ∈ Finset.range (p.totalDegree+1),t^k*evalForm (homogeneousComponent k p) x := by
      simp only [radialLinePolynomial,Polynomial.eval_finsetSum,Polynomial.eval_mul,
        Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _=eval (fun i ↦ t*x i) (∑ k ∈ Finset.range (p.totalDegree+1),homogeneousComponent k p) := by
      rw [eval_sum]
      apply Finset.sum_congr rfl
      intro k hk
      exact (homogeneous_eval_scale _ k (homogeneousComponent_isHomogeneous k p) t _).symm
    _=_ := by rw [sum_homogeneousComponent];rfl

theorem radialLinePolynomial_coeff {n : ℕ} (p : P n) (x : Point n) (j : ℕ) :
    (radialLinePolynomial p x).coeff j=evalForm (homogeneousComponent j p) x := by
  classical
  by_cases hj : j<p.totalDegree+1
  · simp [radialLinePolynomial,Polynomial.coeff_C_mul_X_pow,hj]
  · have hz := homogeneousComponent_eq_zero j p (by omega)
    simp [radialLinePolynomial,Polynomial.coeff_C_mul_X_pow,hj,hz,evalForm]

/-- For every actual polynomial, its homogeneous component at the origin
is exactly its factorial-normalized actual Fréchet Taylor coefficient. -/
theorem derivative_origin_component {n : ℕ} (p : P n) (x : Point n) (j : ℕ) :
    iteratedFDeriv ℝ j (evalForm p) 0 (fun _ ↦ x)=
      (j.factorial:ℝ)*evalForm (homogeneousComponent j p) x := by
  let q := radialLinePolynomial p x
  have hline : evalForm p ∘ lineMap x=q.eval := by
    funext t
    simpa only [q,lineMap,Function.comp_apply,ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply] using (radialLinePolynomial_eval p x t).symm
  have hcomp := (lineMap x).iteratedFDeriv_comp_right (evalForm_contDiff p) 0
    (i:=j) (by simp)
  have hcomp' := congrArg (fun B ↦ B (fun _ : Fin j ↦ (1:ℝ))) hcomp
  rw [hline] at hcomp'
  rw [←iteratedDeriv_eq_iteratedFDeriv,iteratedDeriv_polynomial_eval] at hcomp'
  dsimp only at hcomp'
  rw [←Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_iterate_derivative] at hcomp'
  simp only [zero_add,Nat.descFactorial_self,nsmul_eq_mul,q,radialLinePolynomial_coeff] at hcomp'
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,lineMap,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,one_smul,zero_smul]
    using hcomp'.symm

def shifted {n : ℕ} (y : Point n) (p : P n) : P n :=
  eval₂Hom C (fun i ↦ X i+C (y i)) p

theorem evalForm_shifted {n : ℕ} (y x : Point n) (p : P n) :
    evalForm (shifted y p) x=evalForm p (y+x) := by
  change eval (fun i ↦ x i) (eval₂ C (fun i ↦ X i+C (y i)) p)=_
  rw [←eval_assoc]
  apply congrArg (fun z ↦ eval z p)
  funext i
  simp only [Function.comp_apply,eval_add,eval_X,eval_C,PiLp.add_apply]
  ring

def cubicModel {n : ℕ} (y : Point n) (p : P n) : P n :=
  ∑ j ∈ Finset.range 4,homogeneousComponent j (shifted y p)

theorem cubicModel_degree {n : ℕ} (y : Point n) (p : P n) :
    (cubicModel y p).totalDegree≤3 := by
  apply totalDegree_finsetSum_le
  intro j hj
  exact (homogeneousComponent_isHomogeneous j (shifted y p)).totalDegree_le.trans
    (by have hh := Finset.mem_range.mp hj;omega)

theorem shifted_component_coefficient {n : ℕ} (y h : Point n) (p : P n) (j : ℕ) :
    evalForm (homogeneousComponent j (shifted y p)) h=
      (j.factorial:ℝ)⁻¹*iteratedFDeriv ℝ j (evalForm p) y (fun _ ↦ h) := by
  have h := derivative_origin_component (shifted y p) h j
  have hshift : evalForm (shifted y p)=(fun z ↦ evalForm p (y+z)) := by
    funext z
    exact evalForm_shifted y z p
  rw [hshift,iteratedFDeriv_comp_add_left,add_zero] at h
  rw [h,←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero j),one_mul]

theorem cubicModel_eval {n : ℕ} (y h : Point n) (p : P n) :
    evalForm (cubicModel y p) h=
      ∑ j ∈ Finset.range 4,(j.factorial:ℝ)⁻¹*iteratedFDeriv ℝ j (evalForm p) y (fun _ ↦ h) := by
  change eval (fun i ↦ h i) (∑ j ∈ Finset.range 4,homogeneousComponent j (shifted y p))=_
  rw [eval_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact shifted_component_coefficient y h p j

theorem line_iteratedDeriv {n : ℕ} (p : P n) (y h : Point n) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (fun u : ℝ ↦ evalForm p (y+u • h)) t=
      iteratedFDeriv ℝ j (evalForm p) (y+t • h) (fun _ ↦ h) := by
  have hcont : ContDiff ℝ ⊤ (fun z : Point n ↦ evalForm p (y+z)) :=
    (evalForm_contDiff p).comp (contDiff_const.add contDiff_id)
  have hcomp := (lineMap h).iteratedFDeriv_comp_right hcont t (i:=j) (by simp)
  have heval := congrArg (fun B ↦ B (fun _ : Fin j ↦ (1:ℝ))) hcomp
  rw [iteratedFDeriv_comp_add_left] at heval
  have hfun : ((fun z : Point n ↦ evalForm p (y+z)) ∘ lineMap h)=
      (fun u : ℝ ↦ evalForm p (y+u • h)) := by rfl
  rw [hfun] at heval
  rw [←iteratedDeriv_eq_iteratedFDeriv] at heval
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,lineMap,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,one_smul] using heval

theorem iteratedDerivWithin_eq_of_smooth {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f)
    (j : ℕ) {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {x : ℝ} (hx : x ∈ s) :
    iteratedDerivWithin j f s x=iteratedDeriv j f x := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin,iteratedDeriv_eq_iteratedFDeriv,
    iteratedFDerivWithin_eq_iteratedFDeriv hs ((hf.of_le (by simp)).contDiffAt) hx]

theorem line_contDiff {n : ℕ} (p : P n) (y h : Point n) :
    ContDiff ℝ ⊤ (fun t : ℝ ↦ evalForm p (y+t • h)) :=
  (evalForm_contDiff p).comp (contDiff_const.add (contDiff_id.smul contDiff_const))

theorem line_taylorWithin_eq_cubic {n : ℕ} (p : P n) (y h : Point n) :
    taylorWithinEval (fun t : ℝ ↦ evalForm p (y+t • h)) 3 (Set.Icc 0 1) 0 1=
      evalForm (cubicModel y p) h := by
  rw [taylor_within_apply,cubicModel_eval]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedDerivWithin_eq_of_smooth (line_contDiff p y h) j
    (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1)) (by norm_num : (0:ℝ)∈Set.Icc 0 1)]
  rw [line_iteratedDeriv]
  simp only [sub_zero,one_pow,mul_one,smul_eq_mul,zero_smul,add_zero]

/-- Sharp fourth-order remainder for an actual homogeneous polynomial on
any segment with a supplied radial bound. -/
theorem cubic_remainder_on_segment {n d : ℕ} (hn : 0 < n) (hd : 4 ≤ d)
    (p : P n) (hp : p.IsHomogeneous d) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x : Fin n → ℝ,(∑ i,x i^2)=1 → |eval x p|≤M)
    (y h : Point n) (R : ℝ)
    (hsegment : ∀ t∈Set.Icc (0:ℝ) 1,‖y+t • h‖≤R) :
    |evalForm p (y+h)-evalForm (cubicModel y p) h|≤
      (d.choose 4:ℝ)*M*R^(d-4)*‖h‖^4 := by
  let g : ℝ → ℝ := fun t ↦ evalForm p (y+t • h)
  have hg : ContDiff ℝ ⊤ g := line_contDiff p y h
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin 3 g (Set.Icc 0 1)) (Set.Ioo 0 1) := by
    apply (hg.differentiable_iteratedDeriv 3 (WithTop.coe_lt_top _)).differentiableOn.congr
    intro t ht
    exact (iteratedDerivWithin_eq_of_smooth hg 3
      (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1)) ⟨ht.1.le,ht.2.le⟩)
  have hcc : Set.uIcc (0:ℝ) 1=Set.Icc 0 1 := Set.uIcc_of_le (by norm_num)
  have hco : Set.uIoo (0:ℝ) 1=Set.Ioo 0 1 := Set.uIoo_of_le (by norm_num)
  obtain ⟨t,ht,hrem⟩ := taylor_mean_remainder_lagrange (n:=3)
    (by norm_num : (0:ℝ)≠1)
    (by simpa only [hcc] using (hg.of_le (by simp)).contDiffOn)
    (by simpa only [hcc,hco] using hdiff)
  rw [hco] at ht
  rw [hcc] at hrem
  have hwithin := iteratedDerivWithin_eq_of_smooth hg 4
    (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1)) (x:=t) ⟨ht.1.le,ht.2.le⟩
  rw [hwithin] at hrem
  have hmodel := line_taylorWithin_eq_cubic p y h
  change taylorWithinEval g 3 (Set.Icc 0 1) 0 1=evalForm (cubicModel y p) h at hmodel
  rw [hmodel] at hrem
  have hline := line_iteratedDeriv p y h 4 t
  change iteratedDeriv 4 g t=_ at hline
  rw [hline] at hrem
  have hg1 : g 1=evalForm p (y+h) := by simp [g]
  rw [hg1] at hrem
  have hcoef := actual_taylor_coefficient_bound hn (by omega) p hp M hM hbound
    (y+t • h) h 4 hd
  norm_num only [Nat.factorial, Nat.cast_ofNat,sub_zero,one_pow,mul_one] at hrem hcoef
  have herror : |evalForm p (y+h)-evalForm (cubicModel y p) h|≤
      (d.choose 4:ℝ)*M*‖y+t • h‖^(d-4)*‖h‖^4 := by
    rw [hrem]
    convert hcoef using 1
    congr 1
    ring
  apply herror.trans
  gcongr
  exact hsegment t ⟨ht.1.le,ht.2.le⟩

theorem sphere_segment_norm {n : ℕ} (x y : Point n) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖y+t • (x-y)‖≤1 := by
  have hid : y+t • (x-y)=(1-t) • y+t • x := by module
  rw [hid]
  calc
    ‖(1-t) • y+t • x‖≤‖(1-t) • y‖+‖t • x‖ := norm_add_le _ _
    _=(1-t)*1+t*1 := by
      rw [norm_smul,norm_smul,hy,hx,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg (by linarith [ht.2] : 0≤1-t),abs_of_nonneg ht.1]
    _=1 := by ring

/-- PDF Lemma1.13, with its sharp binomial coefficient and the actual
cubic polynomial in the original ambient displacement variables. -/
theorem cubic_sphere_remainder {n d : ℕ} (hn : 0 < n) (hd : 4 ≤ d)
    (p : P n) (hp : p.IsHomogeneous d) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x : Fin n → ℝ,(∑ i,x i^2)=1 → |eval x p|≤M)
    (x y : Point n) (hx : ‖x‖=1) (hy : ‖y‖=1) :
    |evalForm p x-evalForm (cubicModel y p) (x-y)|≤(d.choose 4:ℝ)*M*‖x-y‖^4 := by
  have h := cubic_remainder_on_segment hn hd p hp M hM hbound y (x-y) 1
    (sphere_segment_norm x y hx hy)
  simpa only [add_sub_cancel,one_pow,mul_one] using h

theorem cubic_signed_sphere_remainder {n d : ℕ} (hn : 0 < n) (hd : 4 ≤ d)
    (p : P n) (hp : p.IsHomogeneous d) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x : Fin n → ℝ,(∑ i,x i^2)=1 → |eval x p|≤M)
    (x y : Point n) (hx : ‖x‖=1) (hy : ‖y‖=1) :
    evalForm (cubicModel y p) (x-y)-evalForm p x≤(d.choose 4:ℝ)*M*‖x-y‖^4 := by
  have h := (abs_le.mp (cubic_sphere_remainder hn hd p hp M hM hbound x y hx hy)).1
  linarith

end CubicTaylorBounds
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
