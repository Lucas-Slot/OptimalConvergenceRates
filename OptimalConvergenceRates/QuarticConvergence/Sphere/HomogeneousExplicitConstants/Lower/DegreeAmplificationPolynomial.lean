import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.SphereCurve
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.FiniteReindex
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.ChebyshevSOSKernel

/-! Actual homogeneous Chebyshev amplification of a quartic. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace DegreeAmplification

open scoped BigOperators
open MvPolynomial Foundation

variable {σ : Type*}

/-- The pair is `(homogeneous T_(k+1), homogeneous U_k)`. -/
def chebPair (t s : MvPolynomial σ ℝ) : ℕ →
    MvPolynomial σ ℝ × MvPolynomial σ ℝ
  | 0 => (t, 1)
  | k+1 => let v := chebPair t s k
      (t*v.1-(s-t^2)*v.2, v.1+t*v.2)

def chebA (t s : MvPolynomial σ ℝ) (k : ℕ) := (chebPair t s k).1
def chebV (t s : MvPolynomial σ ℝ) (k : ℕ) := (chebPair t s k).2

@[simp] theorem chebA_zero (t s : MvPolynomial σ ℝ) : chebA t s 0=t := rfl
@[simp] theorem chebV_zero (t s : MvPolynomial σ ℝ) : chebV t s 0=1 := rfl
theorem chebA_succ (t s : MvPolynomial σ ℝ) (k : ℕ) :
    chebA t s (k+1)=t*chebA t s k-(s-t^2)*chebV t s k := rfl
theorem chebV_succ (t s : MvPolynomial σ ℝ) (k : ℕ) :
    chebV t s (k+1)=chebA t s k+t*chebV t s k := rfl

theorem cheb_pell (t s : MvPolynomial σ ℝ) (k : ℕ) :
    chebA t s k^2+(s-t^2)*chebV t s k^2=s^(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [chebA_succ,chebV_succ,pow_succ]
      linear_combination s*ih

theorem cheb_rename {τ : Type*} (f : σ → τ) (t s : MvPolynomial σ ℝ) (k : ℕ) :
    rename f (chebA t s k)=chebA (rename f t) (rename f s) k ∧
    rename f (chebV t s k)=chebV (rename f t) (rename f s) k := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp [chebA_succ,chebV_succ,ih.1,ih.2]

theorem cheb_homogeneous (t s : MvPolynomial σ ℝ)
    (ht : t.IsHomogeneous 1) (hs : s.IsHomogeneous 2) (k : ℕ) :
    (chebA t s k).IsHomogeneous (k+1) ∧ (chebV t s k).IsHomogeneous k := by
  induction k with
  | zero => exact ⟨ht, by simpa using (isHomogeneous_C (σ := σ) (1:ℝ))⟩
  | succ k ih =>
      rw [chebA_succ,chebV_succ]
      constructor
      · apply (show (t*chebA t s k).IsHomogeneous (k+1+1) by
          simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ht.mul ih.1).sub
        simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
          (hs.sub (by simpa using ht.pow 2)).mul ih.2
      · exact ih.1.add (by simpa [Nat.add_comm] using ht.mul ih.2)

theorem genericRadius_homogeneous [Fintype σ] :
    (genericRadius (σ := σ)).IsHomogeneous 2 := by
  classical
  apply IsHomogeneous.sum
  intro i hi
  exact isHomogeneous_X_pow i 2

theorem cheb_angular_eval [Fintype σ] (y : σ → ℝ)
    (hy : ∑ i, y i ^ 2 = 1) (u : ℝ) (k : ℕ) :
    eval (realAngularPoint y u) (chebA (X none) genericRadius k)=
      Real.cos ((k+1:ℕ)*u) ∧
    Real.sin u * eval (realAngularPoint y u) (chebV (X none) genericRadius k)=
      Real.sin ((k+1:ℕ)*u) := by
  have hs : eval (realAngularPoint y u) genericRadius=1 := by
    rw [genericRadius_eval,realAngularPoint_sphere y hy]
  have ht : eval (realAngularPoint y u) (X none)=Real.cos u := by
    simp [realAngularPoint]
  induction k with
  | zero => simp [ht]
  | succ k ih =>
      rw [chebA_succ,chebV_succ]
      simp only [eval_sub,eval_mul,eval_pow,hs,ht,eval_add]
      have hangle : ((k+1+1:ℕ):ℝ)*u=((k+1:ℕ):ℝ)*u+u := by push_cast; ring
      rw [hangle,Real.cos_add,Real.sin_add]
      constructor
      · rw [ih.1]
        linear_combination (eval (realAngularPoint y u)
          (chebV (X none) genericRadius k)) * Real.sin_sq_add_cos_sq u - Real.sin u*ih.2
      · rw [ih.1]
        linear_combination Real.cos u*ih.2

def amplified [Fintype σ] (q : MvPolynomial σ ℝ) (k j : ℕ) :
    MvPolynomial (Option σ) ℝ :=
  genericRadius^j * paddedPolynomial q * chebV (X none) genericRadius k^4

theorem amplified_homogeneous [Fintype σ] (q : MvPolynomial σ ℝ)
    (hq : q.IsHomogeneous 4) (k j : ℕ) :
    (amplified q k j).IsHomogeneous (4*(k+1)+2*j) := by
  have hV := (cheb_homogeneous (X (none : Option σ)) genericRadius
    (isHomogeneous_X ℝ _) genericRadius_homogeneous k).2
  have hqpad : (paddedPolynomial q).IsHomogeneous 4 := hq.rename_isHomogeneous
  simpa only [amplified, show 2*j+4+k*4=4*(k+1)+2*j by omega] using
    ((genericRadius_homogeneous.pow j).mul hqpad).mul (hV.pow 4)

theorem amplified_nonneg [Fintype σ] (q : MvPolynomial σ ℝ)
    (hq : ∀ y, 0 ≤ eval y q) (k j : ℕ) (x : Option σ → ℝ) :
    0≤eval x (amplified q k j) := by
  simp only [amplified,eval_mul,eval_pow,paddedPolynomial,eval_rename]
  apply mul_nonneg
  · apply mul_nonneg
    · apply pow_nonneg
      rw [genericRadius_eval]
      exact Finset.sum_nonneg fun i _ ↦ sq_nonneg _
    · exact hq _
  · positivity

theorem amplified_angular_eval [Fintype σ] (q : MvPolynomial σ ℝ)
    (hq : q.IsHomogeneous 4) (k j : ℕ) (y : σ → ℝ)
    (hy : ∑ i, y i ^ 2 = 1) (u : ℝ) :
    eval (realAngularPoint y u) (amplified q k j)=
      Real.sin ((k+1:ℕ)*u)^4 * eval y q := by
  simp only [amplified,eval_mul,eval_pow]
  rw [genericRadius_eval,realAngularPoint_sphere y hy,one_pow,one_mul,
    paddedPolynomial_angular_eval q hq]
  rw [← (cheb_angular_eval y hy u k).2,mul_pow]
  ring

@[simp] theorem amplified_pole_eval [Fintype σ] (q : MvPolynomial σ ℝ)
    (hq : q.IsHomogeneous 4) (k j : ℕ) :
    eval paddingPole (amplified q k j)=0 := by
  simp [amplified,paddedPolynomial_pole_eval q hq]

theorem homogeneous_quartic_radius_upper [Fintype σ] (q : MvPolynomial σ ℝ)
    (hq : q.IsHomogeneous 4)
    (hbound : ∀ y : σ → ℝ, (∑ i,y i^2)=1 → eval y q≤1)
    (y : σ → ℝ) : eval y q≤(∑ i,y i^2)^2 := by
  classical
  let S : ℝ := ∑ i,y i^2
  have hS : 0≤S := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  by_cases hz : S=0
  · have hy : y=fun _ ↦ 0 := by
      funext i
      have hi : y i^2≤S := Finset.single_le_sum (fun j _ ↦ sq_nonneg (y j)) (Finset.mem_univ i)
      have hyi : y i=0 := by nlinarith [sq_nonneg (y i)]
      exact hyi
    have hzero := homogeneous_eval_scale q 4 hq 0 y
    simp only [zero_mul,zero_pow (by decide : 4≠0)] at hzero
    rw [hy,hzero]
    positivity
  · have hSpos : 0<S := lt_of_le_of_ne hS (Ne.symm hz)
    let c : ℝ := Real.sqrt S
    have hc : 0<c := Real.sqrt_pos.mpr hSpos
    have hcsq : c^2=S := Real.sq_sqrt hS
    let z : σ → ℝ := fun i ↦ y i/c
    have hzunit : (∑ i,z i^2)=1 := by
      simp only [z,div_pow,← Finset.sum_div]
      rw [hcsq]
      exact div_self hz
    have hscale := homogeneous_eval_scale q 4 hq c z
    have hcz : (fun i ↦ c*z i)=y := by
      funext i
      dsimp [z]
      field_simp
    rw [hcz] at hscale
    rw [hscale]
    calc
      c^4*eval z q≤c^4 := mul_le_of_le_one_right (by positivity) (hbound z hzunit)
      _=S^2 := by rw [show c^4=(c^2)^2 by ring,hcsq]

theorem genericRadius_option [Fintype σ] :
    (genericRadius : MvPolynomial (Option σ) ℝ)=
      X none^2+paddedPolynomial (genericRadius (σ := σ)) := by
  classical
  simp [genericRadius,Fintype.sum_option,paddedPolynomial,map_sum,map_pow]

theorem amplified_sphere_upper [Fintype σ] (q : MvPolynomial σ ℝ)
    (hq : q.IsHomogeneous 4)
    (hbound : ∀ y : σ → ℝ, (∑ i,y i^2)=1 → eval y q≤1)
    (k j : ℕ) (x : Option σ → ℝ) (hx : ∑ i,x i^2=1) :
    eval x (amplified q k j)≤1 := by
  let S : ℝ := ∑ i : σ,x (some i)^2
  let v : ℝ := eval x (chebV (X none) genericRadius k)
  have hS : 0≤S := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hxS : 1-x none^2=S := by
    rw [Fintype.sum_option] at hx
    dsimp [S]
    linarith
  have hpell := congrArg (eval x) (cheb_pell (X none) genericRadius k)
  have hs : eval x genericRadius=1 := by rw [genericRadius_eval,hx]
  simp only [eval_add,eval_pow,eval_mul,eval_sub,eval_X,hs,one_pow,hxS] at hpell
  have hvupper : S*v^2≤1 := by
    dsimp [v]
    nlinarith [sq_nonneg (eval x (chebA (X none) genericRadius k))]
  have hvlower : 0≤S*v^2 := mul_nonneg hS (sq_nonneg v)
  have hpower : (S*v^2)^2≤1 := by nlinarith
  have hqupper := homogeneous_quartic_radius_upper q hq hbound (fun i ↦ x (some i))
  simp only [amplified,eval_mul,eval_pow,paddedPolynomial,eval_rename,hs,one_pow,one_mul]
  calc
    eval (x ∘ some) q * eval x (chebV (X none) genericRadius k)^4≤
        S^2*v^4 := mul_le_mul_of_nonneg_right hqupper (by positivity)
    _=(S*v^2)^2 := by ring
    _≤1 := hpower

theorem amplified_positive_value [Fintype σ] (q : MvPolynomial σ ℝ)
    (hq : q.IsHomogeneous 4) (k j : ℕ) (y : σ → ℝ)
    (hy : ∑ i, y i ^ 2 = 1) (hqy : 0 < eval y q) :
    ∃ x : Option σ → ℝ, (∑ i,x i^2)=1 ∧ 0<eval x (amplified q k j) := by
  let u : ℝ := Real.pi/(2*(k+1:ℕ))
  have hangle : (k+1:ℕ)*u=Real.pi/2 := by
    dsimp [u]
    field_simp <;> ring
  refine ⟨realAngularPoint y u,realAngularPoint_sphere y hy u,?_⟩
  rw [amplified_angular_eval q hq k j y hy u,hangle,Real.sin_pi_div_two]
  simpa using hqy

end DegreeAmplification
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
