import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Exponential
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.CubicTaylorBounds

/-! The global quartic correction for the actual cubic Taylor polynomial.
The constants are exactly 1 in degree four and d^4/3 in higher degree. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace GlobalCubicCorrection

open scoped BigOperators
open MvPolynomial Foundation DegreeTaylorBounds CubicTaylorBounds

def beta (d : ℕ) : ℝ := if d=4 then 1 else (d:ℝ)^4/3

theorem beta_pos {d : ℕ} (hd : 4 ≤ d) : 0<beta d := by
  unfold beta
  split_ifs <;> positivity

theorem beta_le_fourth {d : ℕ} (hd : 4 ≤ d) : beta d≤(d:ℝ)^4/3 := by
  unfold beta
  split_ifs with h
  · subst d
    norm_num
  · rfl

theorem choose_le_pow_div_factorial (d j : ℕ) :
    (d.choose j:ℝ)≤(d:ℝ)^j/(j.factorial:ℝ) := by
  have h := Nat.descFactorial_le_pow d j
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  have hr : (j.factorial:ℝ)*(d.choose j:ℝ)≤(d:ℝ)^j := by exact_mod_cast h
  apply (le_div_iff₀ (by positivity : (0:ℝ)<j.factorial)).2
  nlinarith

theorem exp_two_le_eight : Real.exp 2≤8 := by
  have he : Real.exp 1≤11/4 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hs := pow_le_pow_left₀ (Real.exp_nonneg 1) he 2
  have hid : Real.exp 2=(Real.exp 1)^2 := by
    rw [←Real.exp_nat_mul]
    norm_num
  rw [hid]
  nlinarith

theorem short_segment_growth {d : ℕ} (hd : 4 ≤ d) :
    (1+2/(d:ℝ))^(d-4)≤8 := by
  have hdpos : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hb : 1≤1+2/(d:ℝ) := by
    have hh : (0:ℝ)≤2/(d:ℝ) := by positivity
    linarith
  have he : 1+2/(d:ℝ)≤Real.exp (2/(d:ℝ)) := by
    simpa only [add_comm] using Real.add_one_le_exp (2/(d:ℝ))
  calc
    (1+2/(d:ℝ))^(d-4)≤(1+2/(d:ℝ))^d :=
      pow_le_pow_right₀ hb (Nat.sub_le _ _)
    _≤(Real.exp (2/(d:ℝ)))^d := pow_le_pow_left₀ (by positivity) he d
    _=Real.exp 2 := by
      rw [←Real.exp_nat_mul]
      congr 1
      field_simp
    _≤8 := exp_two_le_eight

theorem homogeneous_nonneg_global {n d : ℕ} (hd : 0 < d)
    (p : P n) (hp : p.IsHomogeneous d)
    (hpos : ∀ x : Fin n → ℝ,(∑ i,x i^2)=1 → 0≤eval x p)
    (z : Point n) : 0≤evalForm p z := by
  by_cases hz : z=0
  · subst z
    have hs := homogeneous_eval_scale p d hp (0:ℝ) (fun _ ↦ (0:ℝ))
    simpa [evalForm,zero_pow (by omega : d≠0)] using hs.ge
  · let u : Point n := ‖z‖⁻¹ • z
    have hu : ‖u‖=1 := norm_smul_inv_norm hz
    have husq : (∑ i,u i^2)=1 := by
      have hh := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n ↦ ℝ) u
      simpa only [hu,one_pow,Real.norm_eq_abs,sq_abs] using hh.symm
    have hpu : 0≤evalForm p u := hpos (fun i ↦ u i) husq
    have hscale := homogeneous_eval_scale p d hp ‖z‖ (fun i ↦ u i)
    have hzu : ‖z‖ • u=z := by
      dsimp only [u]
      rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz),one_smul]
    change evalForm p (‖z‖ • u)=‖z‖^d*evalForm p u at hscale
    rw [hzu] at hscale
    rw [hscale]
    exact mul_nonneg (pow_nonneg (norm_nonneg _) _) hpu

theorem segment_norm_le_sum {n : ℕ} (y h : Point n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖y+t • h‖≤‖y‖+‖h‖ := by
  calc
    ‖y+t • h‖≤‖y‖+‖t • h‖ := norm_add_le _ _
    _=‖y‖+t*‖h‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    _≤‖y‖+‖h‖ := by nlinarith [ht.2,norm_nonneg h]

/-- The exact quartic correction for degree-four forms, valid at every
center and every displacement. -/
theorem quartic_global_correction {n : ℕ} (hn : 0 < n)
    (p : P n) (hp : p.IsHomogeneous 4) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x : Fin n → ℝ,(∑ i,x i^2)=1 → |eval x p|≤M)
    (hpos : ∀ x : Fin n → ℝ,(∑ i,x i^2)=1 → 0≤eval x p)
    (y h : Point n) :
    0≤evalForm (cubicModel y p) h+M*‖h‖^4 := by
  have hrem := cubic_remainder_on_segment hn (by omega : 4≤4) p hp M hM hbound
    y h (‖y‖+‖h‖) (segment_norm_le_sum y h)
  norm_num only [Nat.choose_self,Nat.sub_self,pow_zero,mul_one,one_mul] at hrem
  have hF := homogeneous_nonneg_global (by omega : 0<4) p hp hpos (y+h)
  have hh := (abs_le.mp hrem).2
  linarith

theorem cubic_coefficient_zero {n : ℕ} (p : P n) (y h : Point n) :
    evalForm (homogeneousComponent 0 (shifted y p)) h=evalForm p y := by
  rw [shifted_component_coefficient]
  simp

theorem cubicModel_eval_four {n : ℕ} (p : P n) (y h : Point n) :
    evalForm (cubicModel y p) h=
      evalForm (homogeneousComponent 0 (shifted y p)) h+
      evalForm (homogeneousComponent 1 (shifted y p)) h+
      evalForm (homogeneousComponent 2 (shifted y p)) h+
      evalForm (homogeneousComponent 3 (shifted y p)) h := by
  change eval (fun i ↦ h i) (∑ j ∈ Finset.range 4,homogeneousComponent j (shifted y p))=_
  rw [eval_sum]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  rfl

theorem cubic_coefficient_bound {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (p : P n) (hp : p.IsHomogeneous d) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x : Fin n → ℝ,(∑ i,x i^2)=1 → |eval x p|≤M)
    (y h : Point n) (hy : ‖y‖=1) (j : ℕ) (hj : j≤d) :
    |evalForm (homogeneousComponent j (shifted y p)) h|≤
      ((d:ℝ)^j/(j.factorial:ℝ))*M*‖h‖^j := by
  rw [shifted_component_coefficient]
  have hh := actual_taylor_coefficient_bound hn hd p hp M hM hbound y h j hj
  rw [hy,one_pow,mul_one] at hh
  apply hh.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (choose_le_pow_div_factorial d j) hM)
    (pow_nonneg (norm_nonneg _) _)

theorem far_cubic_majorant {u : ℝ} (hu : 2 ≤ u) :
    u+u^2/2+u^3/6≤u^4/3 := by
  have h0 : 0≤u := by linarith
  have hprod : 0≤u*(u-2)*(2*u^2+3*u+3) :=
    mul_nonneg (mul_nonneg h0 (sub_nonneg.mpr hu)) (by positivity)
  nlinarith

theorem cubic_global_correction_far {n d : ℕ} (hn : 0 < n) (hd : 4 ≤ d)
    (p : P n) (hp : p.IsHomogeneous d) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x : Fin n → ℝ,(∑ i,x i^2)=1 → |eval x p|≤M)
    (hpos : ∀ x : Fin n → ℝ,(∑ i,x i^2)=1 → 0≤eval x p)
    (y h : Point n) (hy : ‖y‖=1) (hfar : 2/(d:ℝ)≤‖h‖) :
    0≤evalForm (cubicModel y p) h+((d:ℝ)^4/3)*M*‖h‖^4 := by
  have hd0 : 0<d := by omega
  have hdpos : (0:ℝ)<d := by exact_mod_cast hd0
  have h1 := cubic_coefficient_bound hn hd0 p hp M hM hbound y h hy 1 (by omega)
  have h2 := cubic_coefficient_bound hn hd0 p hp M hM hbound y h hy 2 (by omega)
  have h3 := cubic_coefficient_bound hn hd0 p hp M hM hbound y h hy 3 (by omega)
  norm_num only [Nat.factorial,Nat.cast_ofNat,pow_one,div_one] at h1 h2 h3
  have h0 : 0≤evalForm (homogeneousComponent 0 (shifted y p)) h := by
    rw [cubic_coefficient_zero]
    exact homogeneous_nonneg_global hd0 p hp hpos y
  have hu : 2≤(d:ℝ)*‖h‖ := by
    have hh := (div_le_iff₀ hdpos).mp hfar
    nlinarith
  have hmajor := mul_le_mul_of_nonneg_right (far_cubic_majorant hu) hM
  rw [cubicModel_eval_four]
  have hc1 := (abs_le.mp h1).1
  have hc2 := (abs_le.mp h2).1
  have hc3 := (abs_le.mp h3).1
  nlinarith

theorem cubic_global_correction_near {n d : ℕ} (hn : 0 < n) (hd : 4 ≤ d)
    (p : P n) (hp : p.IsHomogeneous d) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x : Fin n → ℝ,(∑ i,x i^2)=1 → |eval x p|≤M)
    (hpos : ∀ x : Fin n → ℝ,(∑ i,x i^2)=1 → 0≤eval x p)
    (y h : Point n) (hy : ‖y‖=1) (hnear : ‖h‖≤2/(d:ℝ)) :
    0≤evalForm (cubicModel y p) h+((d:ℝ)^4/3)*M*‖h‖^4 := by
  have hsegment : ∀ t∈Set.Icc (0:ℝ) 1,‖y+t • h‖≤1+2/(d:ℝ) := by
    intro t ht
    exact (segment_norm_le_sum y h t ht).trans (by rw [hy];linarith)
  have hrem := cubic_remainder_on_segment hn hd p hp M hM hbound y h
    (1+2/(d:ℝ)) hsegment
  have hchoose := choose_le_pow_div_factorial d 4
  norm_num only [Nat.factorial,Nat.cast_ofNat] at hchoose
  have hgrowth := short_segment_growth hd
  have hcoefficient : (d.choose 4:ℝ)*(1+2/(d:ℝ))^(d-4)≤(d:ℝ)^4/3 := by
    calc
      (d.choose 4:ℝ)*(1+2/(d:ℝ))^(d-4)≤((d:ℝ)^4/24)*8 :=
        mul_le_mul hchoose hgrowth (by positivity) (by positivity)
      _=(d:ℝ)^4/3 := by ring
  have htotal := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoefficient hM) (pow_nonneg (norm_nonneg h) 4)
  have hF := homogeneous_nonneg_global (by omega : 0<d) p hp hpos (y+h)
  have herr := (abs_le.mp hrem).2
  nlinarith

/-- PDF Lemma1.14: actual cubic Taylor polynomial, full ambient
nonnegativity, and the exact stated correction constants. -/
theorem cubic_global_correction {n d : ℕ} (hn : 0 < n) (hd : 4 ≤ d)
    (p : P n) (hp : p.IsHomogeneous d) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x : Fin n → ℝ,(∑ i,x i^2)=1 → |eval x p|≤M)
    (hpos : ∀ x : Fin n → ℝ,(∑ i,x i^2)=1 → 0≤eval x p)
    (y h : Point n) (hy : ‖y‖=1) :
    0≤evalForm (cubicModel y p) h+beta d*M*‖h‖^4 := by
  by_cases hd4 : d=4
  · subst d
    simpa [beta] using quartic_global_correction hn p hp M hM hbound hpos y h
  · simp only [beta,ite_eq_right hd4]
    by_cases hnear : ‖h‖≤2/(d:ℝ)
    · exact cubic_global_correction_near hn hd p hp M hM hbound hpos y h hy hnear
    · exact cubic_global_correction_far hn hd p hp M hM hbound hpos y h hy (le_of_not_ge hnear)

def correctedCubic {n : ℕ} (y : Point n) (p : P n) (eta : ℝ) : P n :=
  cubicModel y p+C eta*(radiusPolynomial n)^2

theorem norm_fourth_eq_sumsq_sq {n : ℕ} (h : Point n) :
    ‖h‖^4=(∑ i,h i^2)^2 := by
  have hh := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n ↦ ℝ) h
  simp only [Real.norm_eq_abs,sq_abs] at hh
  calc
    ‖h‖^4=(‖h‖^2)^2 := by ring
    _=(∑ i,h i^2)^2 := by rw [hh]

theorem correctedCubic_eval {n : ℕ} (y h : Point n) (p : P n) (eta : ℝ) :
    evalForm (correctedCubic y p eta) h=
      evalForm (cubicModel y p) h+eta*‖h‖^4 := by
  change eval (fun i ↦ h i) (cubicModel y p+C eta*(radiusPolynomial n)^2)=_
  rw [eval_add,eval_mul,eval_C,eval_pow,radiusPolynomial_eval,norm_fourth_eq_sumsq_sq]
  rfl

theorem correctedCubic_degree {n : ℕ} (y : Point n) (p : P n) (eta : ℝ) :
    (correctedCubic y p eta).totalDegree≤4 := by
  have hr : (radiusPolynomial n).IsHomogeneous 2 := by
    apply IsHomogeneous.sum
    intro i hi
    exact (isHomogeneous_X ℝ i).pow 2
  have hterm : (C eta*(radiusPolynomial n)^2).IsHomogeneous 4 := by
    exact (hr.pow 2).C_mul eta
  exact (totalDegree_add _ _).trans (max_le ((cubicModel_degree y p).trans (by omega))
    hterm.totalDegree_le)

/-- The literal quartic polynomial used as input to the local SOS theorem
is nonnegative on the entire ambient real vector space. -/
theorem correctedCubic_nonneg {n d : ℕ} (hn : 0 < n) (hd : 4 ≤ d)
    (p : P n) (hp : p.IsHomogeneous d) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x : Fin n → ℝ,(∑ i,x i^2)=1 → |eval x p|≤M)
    (hpos : ∀ x : Fin n → ℝ,(∑ i,x i^2)=1 → 0≤eval x p)
    (y : Point n) (hy : ‖y‖=1) (x : Fin n → ℝ) :
    0≤eval x (correctedCubic y p (beta d*M)) := by
  let h : Point n := (WithLp.equiv 2 (Fin n → ℝ)).symm x
  have hh := cubic_global_correction hn hd p hp M hM hbound hpos y h hy
  rw [←correctedCubic_eval y h p (beta d*M)] at hh
  exact hh

end GlobalCubicCorrection
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
