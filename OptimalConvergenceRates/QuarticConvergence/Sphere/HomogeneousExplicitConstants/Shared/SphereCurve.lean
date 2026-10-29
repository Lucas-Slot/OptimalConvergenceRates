import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.Homogeneity
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.AngularFrequencies
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The actual great-circle restriction of a padded quartic certificate. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Foundation

open scoped BigOperators

variable {σ : Type*}

def paddedPolynomial (q : MvPolynomial σ ℝ) : MvPolynomial (Option σ) ℝ :=
  MvPolynomial.rename some q

def realAngularPoint (y : σ → ℝ) (t : ℝ) : Option σ → ℝ
  | none => Real.cos t
  | some i => Real.sin t * y i

def paddingPole : Option σ → ℝ
  | none => 1
  | some _ => 0

def genericRadius [Fintype σ] : MvPolynomial σ ℝ :=
  ∑ i : σ, MvPolynomial.X i ^ 2

@[simp] theorem genericRadius_eval [Fintype σ] (x : σ → ℝ) :
    MvPolynomial.eval x genericRadius = ∑ i : σ, x i ^ 2 := by
  simp [genericRadius]

theorem realAngularPoint_sphere [Fintype σ] (y : σ → ℝ)
    (hy : ∑ i : σ, y i ^ 2 = 1) (t : ℝ) :
    (∑ i : Option σ, realAngularPoint y t i ^ 2) = 1 := by
  simp only [Fintype.sum_option, realAngularPoint, mul_pow, ← Finset.mul_sum, hy, mul_one]
  nlinarith [Real.sin_sq_add_cos_sq t]

@[simp] theorem paddingPole_sphere [Fintype σ] :
    (∑ i : Option σ, (paddingPole (σ := σ) i) ^ 2) = 1 := by
  simp [paddingPole, Fintype.sum_option]

theorem paddedPolynomial_angular_eval (q : MvPolynomial σ ℝ)
    (hq : q.IsHomogeneous 4) (y : σ → ℝ) (t : ℝ) :
    MvPolynomial.eval (realAngularPoint y t) (paddedPolynomial q) =
      Real.sin t ^ 4 * MvPolynomial.eval y q := by
  rw [paddedPolynomial, MvPolynomial.eval_rename]
  exact homogeneous_eval_scale q 4 hq (Real.sin t) y

@[simp] theorem paddedPolynomial_pole_eval (q : MvPolynomial σ ℝ)
    (hq : q.IsHomogeneous 4) :
    MvPolynomial.eval paddingPole (paddedPolynomial q) = 0 := by
  have h := paddedPolynomial_angular_eval q hq (fun _ ↦ 0) 0
  have hp : realAngularPoint (fun _ : σ ↦ 0) 0 = paddingPole := by
    funext i
    cases i <;> simp [realAngularPoint, paddingPole]
  rw [hp] at h
  simpa using h

section Certificate

variable [Fintype σ] {J : Type*} [Fintype J]

/-- At the unused-coordinate pole the quartic vanishes, so every ordinary
sphere certificate has a nonnegative additive shift. -/
theorem paddedCertificate_eps_nonneg (q : MvPolynomial σ ℝ)
    (hq : q.IsHomogeneous 4) (eps : ℝ) (h : J → MvPolynomial (Option σ) ℝ)
    (g : MvPolynomial (Option σ) ℝ)
    (certificate : paddedPolynomial q + MvPolynomial.C eps =
      (∑ j : J, h j ^ 2) + (1 - genericRadius) * g) : 0 ≤ eps := by
  have he := congrArg (MvPolynomial.eval (paddingPole (σ := σ))) certificate
  have heval : eps = ∑ j : J, MvPolynomial.eval paddingPole (h j) ^ 2 := by
    simpa [paddedPolynomial_pole_eval q hq, paddingPole] using he
  rw [heval]
  exact Finset.sum_nonneg fun j hj ↦ sq_nonneg _

theorem paddedCertificate_angular_squares (q : MvPolynomial σ ℝ)
    (hq : q.IsHomogeneous 4) (eps : ℝ) (h : J → MvPolynomial (Option σ) ℝ)
    (g : MvPolynomial (Option σ) ℝ)
    (certificate : paddedPolynomial q + MvPolynomial.C eps =
      (∑ j : J, h j ^ 2) + (1 - genericRadius) * g)
    (y : σ → ℝ) (hy : ∑ i : σ, y i ^ 2 = 1) (t : ℝ) :
    (∑ j : J, MvPolynomial.eval (realAngularPoint y t) (h j) ^ 2) =
      eps + Real.sin t ^ 4 * MvPolynomial.eval y q := by
  have he := congrArg (MvPolynomial.eval (realAngularPoint y t)) certificate
  have hrad : MvPolynomial.eval (realAngularPoint y t) genericRadius = 1 := by
    rw [genericRadius_eval, realAngularPoint_sphere y hy]
  simpa [paddedPolynomial_angular_eval q hq y t, hrad, add_comm] using he.symm

omit [Fintype σ] in
theorem angularCoordinate_ofReal (y : σ → ℝ) (t : ℝ) (i : Option σ) :
    angularCoordinate y (t : ℂ) i = (realAngularPoint y t i : ℂ) := by
  cases i <;> simp [angularCoordinate, realAngularPoint]

omit [Fintype σ] in
theorem angular_polynomial_ofReal (p : MvPolynomial (Option σ) ℝ)
    (y : σ → ℝ) (t : ℝ) :
    p.eval₂ Complex.ofRealHom (angularCoordinate y (t : ℂ)) =
      (MvPolynomial.eval (realAngularPoint y t) p : ℂ) := by
  calc
    p.eval₂ Complex.ofRealHom (angularCoordinate y (t : ℂ)) =
        p.eval₂ Complex.ofRealHom (Complex.ofRealHom ∘ realAngularPoint y t) := by
      apply congrArg (fun x ↦ p.eval₂ Complex.ofRealHom x)
      funext i
      exact angularCoordinate_ofReal y t i
    _ = (MvPolynomial.eval (realAngularPoint y t) p : ℂ) :=
      (MvPolynomial.eval₂_comp Complex.ofRealHom (realAngularPoint y t) p).symm

omit [Fintype σ] in
/-- The angular vector's norm is the actual Euclidean norm of the entire
finite certificate, including the empty-square-family case. -/
theorem angularVector_real_norm_sq (h : J → MvPolynomial (Option σ) ℝ)
    (y : σ → ℝ) (t : ℝ) :
    ‖angularVector h y (t : ℂ)‖ ^ 2 =
      ∑ j : J, MvPolynomial.eval (realAngularPoint y t) (h j) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro j hj
  rw [angularVector_apply, angular_polynomial_ofReal, Complex.norm_real]
  simp only [Real.norm_eq_abs, sq_abs]

theorem paddedCertificate_angular_norm_sq (q : MvPolynomial σ ℝ)
    (hq : q.IsHomogeneous 4) (eps : ℝ) (h : J → MvPolynomial (Option σ) ℝ)
    (g : MvPolynomial (Option σ) ℝ)
    (certificate : paddedPolynomial q + MvPolynomial.C eps =
      (∑ j : J, h j ^ 2) + (1 - genericRadius) * g)
    (y : σ → ℝ) (hy : ∑ i : σ, y i ^ 2 = 1) (t : ℝ) :
    ‖angularVector h y (t : ℂ)‖ ^ 2 =
      eps + Real.sin t ^ 4 * MvPolynomial.eval y q := by
  rw [angularVector_real_norm_sq]
  exact paddedCertificate_angular_squares q hq eps h g certificate y hy t

theorem paddedCertificate_real_envelope (q : MvPolynomial σ ℝ)
    (hq : q.IsHomogeneous 4) (eps : ℝ) (h : J → MvPolynomial (Option σ) ℝ)
    (g : MvPolynomial (Option σ) ℝ)
    (certificate : paddedPolynomial q + MvPolynomial.C eps =
      (∑ j : J, h j ^ 2) + (1 - genericRadius) * g)
    (y : σ → ℝ) (hy : ∑ i : σ, y i ^ 2 = 1)
    (hqbound : MvPolynomial.eval y q ≤ 1) (t : ℝ) :
    ‖angularVector h y (t : ℂ)‖ ≤ Real.sqrt eps + t ^ 2 := by
  have heps := paddedCertificate_eps_nonneg q hq eps h g certificate
  have hnorm := paddedCertificate_angular_norm_sq q hq eps h g certificate y hy t
  have hsin : Real.sin t ^ 4 ≤ t ^ 4 := by
    have hs := pow_le_pow_left₀ (sq_nonneg (Real.sin t)) (Real.sin_sq_le_sq (x := t)) 2
    simpa only [← pow_mul] using hs
  have hobj : Real.sin t ^ 4 * MvPolynomial.eval y q ≤ Real.sin t ^ 4 :=
    mul_le_of_le_one_right (by positivity : 0 ≤ Real.sin t ^ 4) hqbound
  have hsqrt := Real.sq_sqrt heps
  have hcross : 0 ≤ Real.sqrt eps * t ^ 2 :=
    mul_nonneg (Real.sqrt_nonneg eps) (sq_nonneg t)
  have hrhs : 0 ≤ Real.sqrt eps + t ^ 2 := by positivity
  nlinarith [norm_nonneg (angularVector h y (t : ℂ)), sq_nonneg t]

end Certificate

end Foundation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
