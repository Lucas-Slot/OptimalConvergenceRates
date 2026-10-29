import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Funext
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.Homogeneity
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.Compactness

/-! Global radial bounds and oscillation centering for homogeneous forms.
These retain the actual polynomial and original full sphere. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace HomogeneousSphereBounds

open scoped BigOperators
open MvPolynomial Foundation

theorem radius_homogeneous (n : ℕ) : (radiusPolynomial n).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_X_pow i 2

theorem homogeneous_global_bounds {n m : ℕ} (hm : 0 < m)
    (p : Foundation.Polynomial n) (hp : p.IsHomogeneous (2 * m))
    (M : ℝ) (hM : 0 ≤ M)
    (hunit : ∀ x ∈ unitSphere n, 0 ≤ eval x p ∧ eval x p ≤ M)
    (x : Fin n → ℝ) :
    0 ≤ eval x p ∧ eval x p ≤ M*(∑ i,x i^2)^m := by
  classical
  let S : ℝ := ∑ i,x i^2
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  by_cases hz : S=0
  · have hx : x=fun _ ↦ 0 := by
      funext i
      have hi : x i^2 ≤ S := Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j)) (Finset.mem_univ i)
      have hxi : x i=0 := by nlinarith [sq_nonneg (x i)]
      exact hxi
    have hzero := homogeneous_eval_scale p (2*m) hp 0 x
    simp only [zero_mul,zero_pow (by omega : 2*m≠0)] at hzero
    rw [hx,hzero]
    constructor
    · exact le_refl 0
    · positivity
  · have hSpos : 0<S := lt_of_le_of_ne hS (Ne.symm hz)
    let c : ℝ := Real.sqrt S
    have hc : 0<c := Real.sqrt_pos.mpr hSpos
    have hcsq : c^2=S := Real.sq_sqrt hS
    let y : Fin n → ℝ := fun i ↦ x i/c
    have hy : y ∈unitSphere n := by
      change (∑ i,y i^2)=1
      simp only [y,div_pow,←Finset.sum_div]
      rw [hcsq]
      exact div_self hz
    have hscale := homogeneous_eval_scale p (2*m) hp c y
    have hcy : (fun i ↦ c*y i)=x := by
      funext i
      dsimp [y]
      field_simp
    rw [hcy] at hscale
    have hpower : c^(2*m)=S^m := by rw [pow_mul,hcsq]
    rw [hscale,hpower]
    constructor
    · exact mul_nonneg (pow_nonneg hS m) (hunit y hy).1
    · exact mul_le_mul_of_nonneg_left (hunit y hy).2 (pow_nonneg hS m) |>.trans_eq (mul_comm _ _)

def centeredForm {n : ℕ} (p : Foundation.Polynomial n) (mu : ℝ) (m : ℕ) :
    Foundation.Polynomial n := p-C mu*(radiusPolynomial n)^m

theorem centeredForm_homogeneous {n m : ℕ} (p : Foundation.Polynomial n)
    (hp : p.IsHomogeneous (2 * m)) (mu : ℝ) :
    (centeredForm p mu m).IsHomogeneous (2*m) := by
  exact hp.sub (by simpa using ((radius_homogeneous n).pow m).C_mul mu)

theorem centeredForm_eval_sphere {n m : ℕ} (p : Foundation.Polynomial n)
    (mu : ℝ) (x : Fin n → ℝ) (hx : x ∈ unitSphere n) :
    eval x (centeredForm p mu m)=eval x p-mu := by
  have hR : eval x (radiusPolynomial n)=1 := by simpa [unitSphere] using hx
  simp [centeredForm,hR]

theorem centeredForm_minimum_zero {n m : ℕ} (p : Foundation.Polynomial n)
    {mu : ℝ} (hmin : IsSphereMinimum p mu) :
    IsSphereMinimum (centeredForm p mu m) 0 := by
  constructor
  · intro x hx
    rw [centeredForm_eval_sphere p mu x hx]
    linarith [(hmin.1 x hx)]
  · obtain ⟨x,hx,heq⟩ := hmin.2
    exact ⟨x,hx,by rw [centeredForm_eval_sphere p mu x hx,heq,sub_self]⟩

theorem centeredForm_global_bounds {n m : ℕ} (hm : 0 < m)
    (p : Foundation.Polynomial n) (hp : p.IsHomogeneous (2 * m))
    {mu M : ℝ} (hmin : IsSphereMinimum p mu) (hM : 0 ≤ M)
    (hupper : ∀ x ∈ unitSphere n, eval x p ≤ mu + M) (x : Fin n → ℝ) :
    0 ≤ eval x (centeredForm p mu m) ∧
      eval x (centeredForm p mu m) ≤ M*(∑ i,x i^2)^m := by
  apply homogeneous_global_bounds hm _ (centeredForm_homogeneous p hp mu) M hM
  intro y hy
  rw [centeredForm_eval_sphere p mu y hy]
  constructor <;> linarith [hmin.1 y hy,hupper y hy]

theorem homogeneous_eq_of_sphere_eq {n m : ℕ} (hm : 0 < m)
    (p q : Foundation.Polynomial n) (hp : p.IsHomogeneous (2 * m))
    (hq : q.IsHomogeneous (2 * m))
    (heq : ∀ x ∈ unitSphere n, eval x p = eval x q) : p=q := by
  apply MvPolynomial.funext
  intro x
  have hb := homogeneous_global_bounds hm (p-q) (hp.sub hq) 0 (by norm_num)
    (by
      intro y hy
      simp only [eval_sub,heq y hy,sub_self]
      exact ⟨le_refl 0,le_refl 0⟩) x
  simp only [eval_sub,zero_mul] at hb
  linarith [hb.1,hb.2]

theorem centeredForm_sphereSupNorm_le {n m : ℕ} (hn : 0 < n)
    (p : Foundation.Polynomial n) {mu M : ℝ} (hmin : IsSphereMinimum p mu)
    (hupper : ∀ x ∈ unitSphere n, eval x p ≤ mu + M) :
    sphereSupNorm (centeredForm p mu m) ≤ M := by
  obtain ⟨x,hx,hvalue⟩ := sphereSupNorm_attained hn (centeredForm p mu m)
  have hmin0 := centeredForm_minimum_zero (m:=m) p hmin
  change Foundation.sphereSupNorm (centeredForm p mu m) ≤ M
  rw [←hvalue,abs_of_nonneg (hmin0.1 x hx),centeredForm_eval_sphere p mu x hx]
  linarith [hupper x hx]

end HomogeneousSphereBounds
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
