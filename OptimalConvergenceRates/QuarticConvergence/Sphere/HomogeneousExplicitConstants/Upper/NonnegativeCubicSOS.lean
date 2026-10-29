import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.CubicHomogenization
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.QuadraticBoundSOS
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.AffineKernelBridge

/-! The zero quartic-correction branch: a globally nonnegative actual
polynomial of degree at most three is a sum of affine squares. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace NonnegativeCubicSOS

open scoped BigOperators Topology
open MvPolynomial Foundation ChebyshevSOSKernel CubicHomogenization

abbrev Poly (n : ℕ) := Foundation.Polynomial n

theorem linear_coefficient_zero_of_nonnegative (a b c e : ℝ)
    (hpos : ∀ t : ℝ,0≤a*t^4+b*t^3+c*t^2+e*t) : e=0 := by
  let q : Polynomial ℝ := Polynomial.C a*Polynomial.X^4+
    Polynomial.C b*Polynomial.X^3+Polynomial.C c*Polynomial.X^2+
    Polynomial.C e*Polynomial.X
  have hmin : IsLocalMin q.eval (0:ℝ) := by
    apply (show IsMinOn q.eval Set.univ 0 from ?_).isLocalMin (by simp)
    intro t ht
    simpa only [q,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_pow,Polynomial.eval_X,zero_pow (by decide : 4≠0),
      zero_pow (by decide : 3≠0),zero_pow (by decide : 2≠0),mul_zero,add_zero]
      using! hpos t
  have hderiv : HasDerivAt q.eval e 0 := by
    convert q.hasDerivAt 0 using 1
    simp [q,Polynomial.derivative_mul]
  exact hmin.hasDerivAt_eq_zero hderiv

theorem cubic_component_zero {n : ℕ} (v : Poly n) (hv : v.totalDegree ≤ 3)
    (hpos : ∀ x : Fin n → ℝ,0≤eval x v) : homogeneousComponent 3 v=0 := by
  apply MvPolynomial.funext
  intro h
  have hmodel := model_nonnegative v hv 0 (by norm_num) (by simpa using hpos)
  have hscalar : ∀ t : ℝ,0≤v.coeff 0*t^4+
      eval h (homogeneousComponent 1 v)*t^3+
      eval h (homogeneousComponent 2 v)*t^2+
      eval h (homogeneousComponent 3 v)*t := by
    intro t
    have hh := hmodel (Option.elim' t h)
    simpa only [model_eval,Option.elim'_none,Option.elim'_some,zero_mul,add_zero] using hh
  simpa only [map_zero] using linear_coefficient_zero_of_nonnegative _ _ _ _ hscalar

theorem nonnegative_cubic_degree_le_two {n : ℕ} (v : Poly n) (hv : v.totalDegree ≤ 3)
    (hpos : ∀ x : Fin n → ℝ,0≤eval x v) : v.totalDegree≤2 := by
  have h3 := cubic_component_zero v hv hpos
  rw [cubic_component_decomposition v hv,h3,add_zero]
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_add _ _).trans (max_le (by simp)
      ((homogeneousComponent_isHomogeneous 1 v).totalDegree_le.trans (by omega)))
  · exact (homogeneousComponent_isHomogeneous 2 v).totalDegree_le

theorem quadratic_component_decomposition {n : ℕ} (v : Poly n) (hv : v.totalDegree ≤ 2) :
    v=C (v.coeff 0)+homogeneousComponent 1 v+homogeneousComponent 2 v := by
  have h := HomogeneousSOSFromSphere.sum_components_to_bound v hv
  simpa only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    homogeneousComponent_zero] using h.symm

theorem quadratic_eval_decomposition {n : ℕ} (v : Poly n) (hv : v.totalDegree ≤ 2)
    (h : Fin n → ℝ) : eval h v=v.coeff 0+eval h (homogeneousComponent 1 v)+
      eval h (homogeneousComponent 2 v) := by
  have he := congrArg (eval h) (quadratic_component_decomposition v hv)
  simpa only [eval_add,eval_C] using he

def quadraticModel {n : ℕ} (v : Poly n) : Poly (n+1) :=
  C (v.coeff 0)*X 0^2+rename Fin.succ (homogeneousComponent 1 v)*X 0+
    rename Fin.succ (homogeneousComponent 2 v)

theorem quadraticModel_homogeneous {n : ℕ} (v : Poly n) :
    (quadraticModel v).IsHomogeneous 2 := by
  have h1 := (homogeneousComponent_isHomogeneous 1 v).rename_isHomogeneous
    (f:=Fin.succ)
  have h2 := (homogeneousComponent_isHomogeneous 2 v).rename_isHomogeneous
    (f:=Fin.succ)
  have hx : (X (0:Fin (n+1)) : Poly (n+1)).IsHomogeneous 1 := isHomogeneous_X ℝ _
  exact (((hx.pow 2).C_mul _).add (h1.mul hx)).add h2

theorem quadraticModel_eval {n : ℕ} (v : Poly n) (x : Fin (n + 1) → ℝ) :
    eval x (quadraticModel v)=v.coeff 0*(x 0)^2+
      eval (fun i ↦ x i.succ) (homogeneousComponent 1 v)*(x 0)+
      eval (fun i ↦ x i.succ) (homogeneousComponent 2 v) := by
  simp [quadraticModel,eval_rename,Function.comp_def]

theorem continuous_nonneg_at_zero_of_punctured (f : ℝ → ℝ)
    (hf : ContinuousAt f 0) (hpos : ∀ t : ℝ,t≠0 → 0≤f t) : 0≤f 0 := by
  have hlim : Filter.Tendsto f (𝓝[≠] (0:ℝ)) (𝓝 (f 0)) :=
    hf.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hpos t ht

theorem quadraticModel_nonnegative {n : ℕ} (v : Poly n) (hv : v.totalDegree ≤ 2)
    (hpos : ∀ h : Fin n → ℝ,0≤eval h v) (x : Fin (n+1) → ℝ) :
    0≤eval x (quadraticModel v) := by
  let h : Fin n → ℝ := fun i ↦ x i.succ
  let f : ℝ → ℝ := fun t ↦ v.coeff 0*t^2+
    eval h (homogeneousComponent 1 v)*t+eval h (homogeneousComponent 2 v)
  have hnonzero : ∀ t : ℝ,t≠0 → 0≤f t := by
    intro t ht
    let y : Fin n → ℝ := fun i ↦ h i/t
    have hcomponent (j : ℕ) : eval y (homogeneousComponent j v)=
        (1/t)^j*eval h (homogeneousComponent j v) := by
      simpa only [y,div_eq_mul_inv,one_mul,mul_comm,mul_one] using
        homogeneous_eval_scale (homogeneousComponent j v) j
          (homogeneousComponent_isHomogeneous j v) (1/t) h
    have hid : f t=t^2*eval y v := by
      rw [quadratic_eval_decomposition v hv y,hcomponent 1,hcomponent 2]
      dsimp only [f]
      field_simp [ht]
    rw [hid]
    exact mul_nonneg (sq_nonneg _) (hpos y)
  rw [quadraticModel_eval]
  change 0≤f (x 0)
  by_cases hx : x 0=0
  · rw [hx]
    exact continuous_nonneg_at_zero_of_punctured f (by fun_prop) hnonzero
  · exact hnonzero (x 0) hx

def dehomogenizeVariables (n : ℕ) : Fin (n+1) → Poly n := Fin.cases 1 X

def dehomogenize {n : ℕ} : Poly (n+1) →+* Poly n := eval₂Hom C (dehomogenizeVariables n)

theorem dehomogenizeVariables_degree (n : ℕ) (j : Fin (n + 1)) :
    (dehomogenizeVariables n j).totalDegree≤1 := by
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · simp [dehomogenizeVariables]
  · simp [dehomogenizeVariables]

theorem dehomogenize_eval {n : ℕ} (p : Poly (n + 1)) (x : Fin n → ℝ) :
    eval x (dehomogenize p)=eval (Fin.cases 1 x) p := by
  change eval x (eval₂ C (dehomogenizeVariables n) p)=_
  rw [←eval_assoc]
  apply congrArg (fun z ↦ eval z p)
  funext j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · simp [dehomogenizeVariables]
  · simp [dehomogenizeVariables]

theorem dehomogenize_quadraticModel {n : ℕ} (v : Poly n) (hv : v.totalDegree ≤ 2) :
    dehomogenize (quadraticModel v)=v := by
  apply MvPolynomial.funext
  intro x
  rw [dehomogenize_eval,quadraticModel_eval,quadratic_eval_decomposition v hv x]
  simp

/-- Every actual globally nonnegative quadratic polynomial is a finite
sum of affine squares, including singular and constant polynomials. -/
theorem nonnegative_quadratic_boundedSOS {n : ℕ} (v : Poly n) (hv : v.totalDegree ≤ 2)
    (hpos : ∀ x : Fin n → ℝ,0≤eval x v) : BoundedSOS 1 v := by
  obtain ⟨q,hq,hid⟩ := QuadraticBoundSOS.nonnegative_quadratic_exists_squares
    (quadraticModel v) (quadraticModel_homogeneous v) (quadraticModel_nonnegative v hv hpos)
  have hsos : BoundedSOS 1 (quadraticModel v) := by
    rw [hid]
    exact BoundedSOS.of_family q (fun i ↦ (hq i).totalDegree_le)
  have hdehom := AffineKernelBridge.boundedSOS_affine_substitution
    (dehomogenizeVariables n) (dehomogenizeVariables_degree n) hsos
  change BoundedSOS 1 (dehomogenize (quadraticModel v)) at hdehom
  rw [dehomogenize_quadraticModel v hv] at hdehom
  exact hdehom

/-- The unconditional eta=0 branch of the local cubic SOS theorem. -/
theorem nonnegative_cubic_boundedSOS {n : ℕ} (v : Poly n) (hv : v.totalDegree ≤ 3)
    (hpos : ∀ x : Fin n → ℝ,0≤eval x v) : BoundedSOS 1 v :=
  nonnegative_quadratic_boundedSOS v (nonnegative_cubic_degree_le_two v hv hpos) hpos

theorem boundedSOS_even_radial_mul {n d : ℕ} {v : Poly n}
    (hv : BoundedSOS d v) (m : ℕ) :
    BoundedSOS (2*m+d) ((radiusPolynomial n)^(2*m)*v) := by
  have hroot : ((radiusPolynomial n)^m).totalDegree≤2*m :=
    ((HomogeneousSphereBounds.radius_homogeneous n).pow m).totalDegree_le
  have hsquare := BoundedSOS.square ((radiusPolynomial n)^m) hroot
  have hradial : BoundedSOS (2*m) ((radiusPolynomial n)^(2*m)) := by
    simpa only [←pow_mul,Nat.mul_comm m 2] using hsquare
  exact hradial.mul hv

/-- The zero-correction branch retains a stronger root budget 2m+1. -/
theorem nonnegative_cubic_radial_boundedSOS {n : ℕ} (v : Poly n)
    (hv : v.totalDegree ≤ 3) (hpos : ∀ x : Fin n → ℝ,0≤eval x v) (m : ℕ) :
    BoundedSOS (2*m+1) ((radiusPolynomial n)^(2*m)*v) :=
  boundedSOS_even_radial_mul (nonnegative_cubic_boundedSOS v hv hpos) m

theorem zero_correction_local_boundedSOS {n : ℕ} (v : Poly n)
    (hv : v.totalDegree ≤ 3) (hpos : ∀ x : Fin n → ℝ,0≤eval x v) (m : ℕ) :
    BoundedSOS (2*m+2) ((radiusPolynomial n)^(2*m)*
      (v+C (0:ℝ)*(radiusPolynomial n)^2)) := by
  simpa only [map_zero,zero_mul,add_zero] using
    (nonnegative_cubic_radial_boundedSOS v hv hpos m).mono (by omega : 2*m+1≤2*m+2)

end NonnegativeCubicSOS
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
