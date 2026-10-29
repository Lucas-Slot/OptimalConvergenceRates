import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.SpherePolynomialSpace
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.GlobalCubicCorrection
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.AffineKernelBridge

/-! Actual normalization and fourth moment of an arbitrary polynomial
localization kernel incorporating the local radial multiplier. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace TaylorKernelData

open scoped BigOperators InnerProductSpace
open MeasureTheory MvPolynomial SphereMeasure SphereMoments SphereZonalPolynomialRange
  KernelAbsorption

abbrev Poly (n : ℕ) := Foundation.Polynomial n

def rawRoot (m : ℕ) (chi : Polynomial ℝ) : Polynomial ℝ := (1-Polynomial.X^2)^m*chi
def rawKernel (m : ℕ) (chi : Polynomial ℝ) : Polynomial ℝ := rawRoot m chi^2

def normalizingMass {n : ℕ} (hn : 0 < n) (m : ℕ) (chi : Polynomial ℝ) : ℝ :=
  ∫ y : Sphere n,(rawKernel m chi).eval ⟪axis ⟨0,hn⟩,y.1⟫_ℝ ∂surface n

def normalizedKernel {n : ℕ} (hn : 0 < n) (m : ℕ) (chi : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C ((normalizingMass hn m chi)⁻¹)*rawKernel m chi

def fourthMoment {n : ℕ} (hn : 0 < n) (m : ℕ) (chi : Polynomial ℝ) : ℝ :=
  ∫ y : Sphere n,‖axis ⟨0,hn⟩-y.1‖^4*
    (normalizedKernel hn m chi).eval ⟪axis ⟨0,hn⟩,y.1⟫_ℝ ∂surface n

theorem sphere_norm_one {n : ℕ} (x : Sphere n) : ‖x.1‖=1 := by
  simpa only [Metric.mem_sphere,dist_zero_right] using x.2

theorem zonal_integral_independent {n : ℕ} (hn : 0 < n) (P : Polynomial ℝ) (x : Sphere n) :
    (∫ y : Sphere n,P.eval ⟪x.1,y.1⟫_ℝ ∂surface n)=
      ∫ y : Sphere n,P.eval ⟪axis ⟨0,hn⟩,y.1⟫_ℝ ∂surface n := by
  rw [integral_polynomial_zonal hn ⟨0,hn⟩ x P]
  exact (integral_polynomial_zonal hn ⟨0,hn⟩ (axisSphere ⟨0,hn⟩) P).symm

theorem raw_mass_eq {n : ℕ} (hn : 0 < n) (m : ℕ) (chi : Polynomial ℝ) (x : Sphere n) :
    (∫ y : Sphere n,(rawKernel m chi).eval ⟪x.1,y.1⟫_ℝ ∂surface n)=
      normalizingMass hn m chi := zonal_integral_independent hn _ x

theorem rawKernel_nonneg (m : ℕ) (chi : Polynomial ℝ) (t : ℝ) :
    0≤(rawKernel m chi).eval t := by
  rw [rawKernel,Polynomial.eval_pow]
  exact sq_nonneg _

theorem normalizingMass_nonneg {n : ℕ} (hn : 0 < n) (m : ℕ) (chi : Polynomial ℝ) :
    0≤normalizingMass hn m chi := integral_nonneg (fun _ ↦ rawKernel_nonneg _ _ _)

theorem normalizedKernel_nonneg {n : ℕ} (hn : 0 < n) (m : ℕ) (chi : Polynomial ℝ) (t : ℝ) :
    0≤(normalizedKernel hn m chi).eval t := by
  rw [normalizedKernel,Polynomial.eval_mul,Polynomial.eval_C]
  exact mul_nonneg (inv_nonneg.mpr (normalizingMass_nonneg hn m chi)) (rawKernel_nonneg _ _ _)

theorem normalized_mass {n : ℕ} (hn : 0 < n) (m : ℕ) (chi : Polynomial ℝ)
    (hZ : 0 < normalizingMass hn m chi) (x : Sphere n) :
    (∫ y : Sphere n,(normalizedKernel hn m chi).eval ⟪x.1,y.1⟫_ℝ ∂surface n)=1 := by
  simp only [normalizedKernel,Polynomial.eval_mul,Polynomial.eval_C]
  rw [integral_const_mul,raw_mass_eq hn m chi x,inv_mul_cancel₀ hZ.ne']

theorem unit_chord_fourth {n : ℕ} (x y : E n) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x-y‖^4=4*(1-⟪x,y⟫_ℝ)^2 := by
  have hh := norm_sub_sq_real x y
  rw [hx,hy,one_pow] at hh
  calc
    ‖x-y‖^4=(‖x-y‖^2)^2 := by ring
    _=4*(1-⟪x,y⟫_ℝ)^2 := by rw [hh];ring

def chordMomentPolynomial {n : ℕ} (hn : 0 < n) (m : ℕ) (chi : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C 4*(1-Polynomial.X)^2*normalizedKernel hn m chi

theorem chordMomentPolynomial_eval {n : ℕ} (hn : 0 < n) (m : ℕ) (chi : Polynomial ℝ)
    (x y : Sphere n) :
    (chordMomentPolynomial hn m chi).eval ⟪x.1,y.1⟫_ℝ=
      ‖x.1-y.1‖^4*(normalizedKernel hn m chi).eval ⟪x.1,y.1⟫_ℝ := by
  rw [unit_chord_fourth x.1 y.1 (sphere_norm_one x) (sphere_norm_one y)]
  simp [chordMomentPolynomial]

theorem fourthMoment_eq_zonal {n : ℕ} (hn : 0 < n) (m : ℕ) (chi : Polynomial ℝ) :
    fourthMoment hn m chi=
      ∫ y : Sphere n,(chordMomentPolynomial hn m chi).eval ⟪axis ⟨0,hn⟩,y.1⟫_ℝ ∂surface n := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  exact (chordMomentPolynomial_eval hn m chi (axisSphere ⟨0,hn⟩) y).symm

theorem fourthMoment_independent {n : ℕ} (hn : 0 < n) (m : ℕ) (chi : Polynomial ℝ)
    (x : Sphere n) :
    (∫ y : Sphere n,‖x.1-y.1‖^4*(normalizedKernel hn m chi).eval ⟪x.1,y.1⟫_ℝ ∂surface n)=
      fourthMoment hn m chi := by
  rw [fourthMoment_eq_zonal]
  have heq : (∫ y : Sphere n,‖x.1-y.1‖^4*(normalizedKernel hn m chi).eval ⟪x.1,y.1⟫_ℝ ∂surface n)=
      ∫ y : Sphere n,(chordMomentPolynomial hn m chi).eval ⟪x.1,y.1⟫_ℝ ∂surface n := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y ↦ (chordMomentPolynomial_eval hn m chi x y).symm)
  rw [heq]
  exact zonal_integral_independent hn _ x

theorem fourthMoment_nonneg {n : ℕ} (hn : 0 < n) (m : ℕ) (chi : Polynomial ℝ) :
    0≤fourthMoment hn m chi := by
  apply integral_nonneg
  intro y
  exact mul_nonneg (pow_nonneg (norm_nonneg _) _) (normalizedKernel_nonneg hn m chi _)

theorem polynomial_section_degree {n : ℕ} (P : Polynomial ℝ) (q : Poly n) :
    (Polynomial.eval₂ C q P).totalDegree≤P.natDegree*q.totalDegree := by
  rw [Polynomial.eval₂_eq_sum_range]
  apply totalDegree_finsetSum_le
  intro i hi
  have hii : i≤P.natDegree := by have hh := Finset.mem_range.mp hi;omega
  exact (totalDegree_mul _ _).trans (by
    simpa only [totalDegree_C,zero_add] using
      (totalDegree_pow q i).trans (Nat.mul_le_mul_right q.totalDegree hii))

def chiSection {n : ℕ} (y : E n) (chi : Polynomial ℝ) : Poly n :=
  Polynomial.eval₂ C (dotPole (fun i ↦ y i)) chi

theorem chiSection_degree {n ell : ℕ} (y : E n) (chi : Polynomial ℝ)
    (hchi : chi.natDegree ≤ ell - 2) : (chiSection y chi).totalDegree≤ell-2 := by
  have hh := polynomial_section_degree chi (dotPole (fun i ↦ y i))
  exact hh.trans ((Nat.mul_le_mul_left chi.natDegree (dotPole_degree _)).trans
    (by simpa only [Nat.mul_one] using hchi))

theorem dotPole_eval {n : ℕ} (x y : E n) :
    eval (fun i ↦ x i) (dotPole (fun i ↦ y i))=⟪y,x⟫_ℝ :=
  linearFormPolynomial_inner y x

theorem chiSection_eval {n : ℕ} (y x : E n) (chi : Polynomial ℝ) :
    eval (fun i ↦ x i) (chiSection y chi)=chi.eval ⟪x,y⟫_ℝ := by
  rw [chiSection,Polynomial.hom_eval₂]
  have hcomp : (eval (fun i ↦ x i)).comp C=RingHom.id ℝ := by ext c;simp
  rw [hcomp,Polynomial.eval₂_eq_eval_map]
  simp only [Polynomial.map_id,dotPole_eval,real_inner_comm]

theorem numeratorSection_eval {n : ℕ} (y x : E n) (m : ℕ) (chi : Polynomial ℝ) :
    eval (fun i ↦ x i) (kernelNumerator (dotPole (fun i ↦ y i)) (chiSection y chi) m)=
      (rawRoot m chi).eval ⟪x,y⟫_ℝ := by
  simp only [kernelNumerator,eval_mul,eval_pow,eval_sub,map_one,dotPole_eval,chiSection_eval,
    rawRoot,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_one,
    Polynomial.eval_X,real_inner_comm]

end TaylorKernelData
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
