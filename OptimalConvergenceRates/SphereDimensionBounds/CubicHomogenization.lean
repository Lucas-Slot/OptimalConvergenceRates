import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.SphereDimensionBounds.HomogeneousSOSFromSphere
import OptimalConvergenceRates.SphereDimensionBounds.SelectorSchur

/-! The actual quartic homogenization of a cubic displacement model.
This supplies the precise input for the local quartic selector theorem. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.CubicHomogenization

open scoped BigOperators
open MvPolynomial OptimalConvergenceRates.SphereDimensionBounds.Foundation HomogeneousSOSFromSphere

abbrev P (n : ℕ) := OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial n
abbrev Lift (n : ℕ) := MvPolynomial (Option (Fin n)) ℝ

def lowerRadius (n : ℕ) : Lift n := rename some (radiusPolynomial n)

def model {n : ℕ} (v : P n) (eta : ℝ) : Lift n :=
  C (v.coeff 0)*X none^4+
    rename some (homogeneousComponent 1 v)*X none^3+
    rename some (homogeneousComponent 2 v)*X none^2+
    rename some (homogeneousComponent 3 v)*X none+
    C eta*(lowerRadius n)^2

theorem cubic_component_decomposition {n : ℕ} (v : P n) (hv : v.totalDegree ≤ 3) :
    v=C (v.coeff 0)+homogeneousComponent 1 v+
      homogeneousComponent 2 v+homogeneousComponent 3 v := by
  have h := sum_components_to_bound v hv
  simpa only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    homogeneousComponent_zero] using h.symm

theorem cubic_eval_decomposition {n : ℕ} (v : P n) (hv : v.totalDegree ≤ 3)
    (y : Fin n → ℝ) : eval y v=v.coeff 0+eval y (homogeneousComponent 1 v)+
      eval y (homogeneousComponent 2 v)+eval y (homogeneousComponent 3 v) := by
  have h := congrArg (eval y) (cubic_component_decomposition v hv)
  simpa only [eval_add,eval_C] using h

theorem lowerRadius_homogeneous (n : ℕ) : (lowerRadius n).IsHomogeneous 2 :=
  (HomogeneousSphereBounds.radius_homogeneous n).rename_isHomogeneous

theorem model_homogeneous {n : ℕ} (v : P n) (eta : ℝ) :
    (model v eta).IsHomogeneous 4 := by
  have h1 : (rename (some : Fin n → Option (Fin n)) (homogeneousComponent 1 v)).IsHomogeneous 1 :=
    (homogeneousComponent_isHomogeneous 1 v).rename_isHomogeneous
  have h2 : (rename (some : Fin n → Option (Fin n)) (homogeneousComponent 2 v)).IsHomogeneous 2 :=
    (homogeneousComponent_isHomogeneous 2 v).rename_isHomogeneous
  have h3 : (rename (some : Fin n → Option (Fin n)) (homogeneousComponent 3 v)).IsHomogeneous 3 :=
    (homogeneousComponent_isHomogeneous 3 v).rename_isHomogeneous
  have hx : (X (none : Option (Fin n)) : Lift n).IsHomogeneous 1 := isHomogeneous_X ℝ _
  exact ((((hx.pow 4).C_mul _).add (h1.mul (hx.pow 3))).add
    (h2.mul (hx.pow 2))).add (h3.mul hx) |>.add (((lowerRadius_homogeneous n).pow 2).C_mul eta)

theorem model_eval {n : ℕ} (v : P n) (eta : ℝ) (x : Option (Fin n) → ℝ) :
    eval x (model v eta)=
      v.coeff 0*(x none)^4+
        eval (fun i => x (some i)) (homogeneousComponent 1 v)*(x none)^3+
        eval (fun i => x (some i)) (homogeneousComponent 2 v)*(x none)^2+
        eval (fun i => x (some i)) (homogeneousComponent 3 v)*(x none)+
        eta*(∑ i,x (some i)^2)^2 := by
  simp [model,lowerRadius,eval_rename,Function.comp_def]

theorem model_eval_at_one {n : ℕ} (v : P n) (hv : v.totalDegree ≤ 3)
    (eta : ℝ) (h : Fin n → ℝ) :
    eval (Option.elim' 1 h) (model v eta)=eval h v+eta*(∑ i,h i^2)^2 := by
  rw [model_eval,cubic_eval_decomposition v hv h]
  simp

theorem model_eval_at_zero {n : ℕ} (v : P n) (eta : ℝ) (h : Fin n → ℝ) :
    eval (Option.elim' 0 h) (model v eta)=eta*(∑ i,h i^2)^2 := by
  simp [model_eval]

theorem model_nonnegative {n : ℕ} (v : P n) (hv : v.totalDegree ≤ 3)
    (eta : ℝ) (heta : 0 ≤ eta)
    (hsource : ∀ h : Fin n → ℝ, 0 ≤ eval h v+eta*(∑ i,h i^2)^2)
    (x : Option (Fin n) → ℝ) : 0 ≤ eval x (model v eta) := by
  let s : ℝ := x none
  let h : Fin n → ℝ := fun i => x (some i)
  by_cases hs : s=0
  · rw [model_eval]
    change 0 ≤ v.coeff 0*s^4+eval h (homogeneousComponent 1 v)*s^3+
      eval h (homogeneousComponent 2 v)*s^2+eval h (homogeneousComponent 3 v)*s+
      eta*(∑ i,h i^2)^2
    simp only [hs,zero_pow (by decide : 4≠0),zero_pow (by decide : 3≠0),
      zero_pow (by decide : 2≠0),mul_zero,zero_add]
    positivity
  · let y : Fin n → ℝ := fun i => h i/s
    have hcomponent (j : ℕ) : eval y (homogeneousComponent j v)=
        (1/s)^j*eval h (homogeneousComponent j v) := by
      simpa only [y,div_eq_mul_inv,one_mul,mul_comm] using
        homogeneous_eval_scale (homogeneousComponent j v) j
          (homogeneousComponent_isHomogeneous j v) (1/s) h
    have hR : (∑ i,y i^2)=(∑ i,h i^2)/s^2 := by
      simp only [y,div_pow,Finset.sum_div]
    have heval : eval x (model v eta)=s^4*(eval y v+eta*(∑ i,y i^2)^2) := by
      rw [model_eval,cubic_eval_decomposition v hv y]
      rw [hcomponent 1,hcomponent 2,hcomponent 3,hR]
      change v.coeff 0*s^4+eval h (homogeneousComponent 1 v)*s^3+
        eval h (homogeneousComponent 2 v)*s^2+eval h (homogeneousComponent 3 v)*s+
        eta*(∑ i,h i^2)^2 = _
      field_simp [hs]
    rw [heval]
    exact mul_nonneg (by positivity) (hsource y)

end OptimalConvergenceRates.SphereDimensionBounds.CubicHomogenization
