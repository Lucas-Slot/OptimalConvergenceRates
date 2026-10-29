import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.WeightedCubicSplit

/-! Bilinear lower-slot estimates for the explicit inverse-weighted cubic
vector. All estimates below are deduced from the original cubic domination.
The external-prefix contribution is the building block of the logarithmic
largest-index division; this module does not assume that division theorem. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace WeightedCubicBilinear

open scoped BigOperators InnerProductSpace
open WeightedQuadraticSplit WeightedCubicSplit

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A symmetric vector-valued quadratic bound polarizes without losing its
constant. The proof uses real polarization and equal-norm rescaling. -/
theorem bilinear_norm_le (d : E →ₗ[ℝ] E →ₗ[ℝ] F)
    (hsym : ∀ x y, d x y = d y x) {K : ℝ} (hK : 0 ≤ K)
    (hdiag : ∀ x, ‖d x x‖ ≤ K * ‖x‖ ^ 2) (u w : E) :
    ‖d u w‖ ≤ K * ‖u‖ * ‖w‖ := by
  have hunit (x y : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ‖d x y‖ ≤ K := by
    have hid : (4:ℝ) • d x y = d (x+y) (x+y)-d (x-y) (x-y) := by
      simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
      rw [hsym y x]
      module
    have hb := norm_sub_le (d (x+y) (x+y)) (d (x-y) (x-y))
    rw [← hid, norm_smul, Real.norm_eq_abs] at hb
    rw [abs_of_pos (by norm_num : (0:ℝ)<4)] at hb
    have hp := hdiag (x+y)
    have hm := hdiag (x-y)
    have hpar : ‖x+y‖^2+‖x-y‖^2=4 := by
      rw [norm_add_sq_real, norm_sub_sq_real, hx,hy]
      ring
    nlinarith
  by_cases hu : u=0
  · simp [hu]
  by_cases hw : w=0
  · simp [hw]
  have hup : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hwp : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let u' : E := ‖u‖⁻¹ • u
  let w' : E := ‖w‖⁻¹ • w
  have hu' : ‖u'‖=1 := norm_smul_inv_norm hu
  have hw' : ‖w'‖=1 := norm_smul_inv_norm hw
  have hu_eq : u = ‖u‖ • u' := by simp [u',smul_smul,hup.ne']
  have hw_eq : w = ‖w‖ • w' := by simp [w',smul_smul,hwp.ne']
  calc
    ‖d u w‖ = ‖u‖*‖w‖*‖d u' w'‖ := by
      rw [hu_eq,hw_eq]
      simp only [map_smul, LinearMap.smul_apply, norm_smul, Real.norm_eq_abs,
        abs_norm]
      rw [hu',hw']
      ring
    _ ≤ ‖u‖*‖w‖*K := mul_le_mul_of_nonneg_left (hunit u' w' hu' hw') (by positivity)
    _ = K*‖u‖*‖w‖ := by ring

section Finite

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def inverseBilinear (a : ι → ℝ)
    (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ) :
    Point κ →ₗ[ℝ] Point κ →ₗ[ℝ] Point ι :=
  LinearMap.mk₂ ℝ
    (fun y z ↦ (WithLp.equiv 2 (ι → ℝ)).symm
      (fun i ↦ ∑ j, ∑ k, hllCoefficients a t i j k * y j * z k))
    (by intro x y z; ext i; simp [Finset.sum_add_distrib,add_mul,mul_add])
    (by intro r x y; ext i; simp [Finset.mul_sum,Finset.sum_mul,mul_assoc,mul_left_comm])
    (by intro x y z; ext i; simp [Finset.sum_add_distrib,add_mul,mul_add])
    (by intro r x y; ext i; simp [Finset.mul_sum,Finset.sum_mul,mul_assoc,mul_left_comm])

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem inverseBilinear_apply (a : ι → ℝ)
    (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ) (y z : Point κ) (i : ι) :
    inverseBilinear a t y z i = ∑ j, ∑ k, hllCoefficients a t i j k*y j*z k := rfl

omit [DecidableEq ι] [DecidableEq κ] in
theorem inverseBilinear_diagonal (a : ι → ℝ)
    (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ) (y : Point κ) :
    inverseBilinear a t y y = hllVector a t y := rfl

omit [DecidableEq ι] [DecidableEq κ] in
theorem inverseBilinear_symmetric (a : ι → ℝ)
    (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ)
    (ht23 : ∀ i j k, t i j k = t i k j) (y z : Point κ) :
    inverseBilinear a t y z = inverseBilinear a t z y := by
  ext i
  simp only [inverseBilinear_apply,hllCoefficients]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [ht23]
  ring

/-- The mixed lower-slot estimate, including zero low eigenvalues, follows
from the actual source cubic and the explicit inverse coefficient vector. -/
theorem inverseBilinear_norm_le
    (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ)
    (a : ι → ℝ) (b : κ → ℝ) {tau : ℝ} (htau : 0 < tau)
    (ha : ∀ i, tau ≤ a i) (hb0 : ∀ j, 0 ≤ b j) (hb : ∀ j, b j ≤ tau)
    (ht12 : ∀ i j k, t i j k = t j i k) (ht23 : ∀ i j k, t i j k = t i k j)
    (hdom : ∀ z : Point (ι ⊕ κ),
      |MvPolynomial.eval (fun i ↦ z i) (cubicPolynomial t)| ≤
        2*‖diagonal (Sum.elim a b) z‖*‖z‖^2) (y z : Point κ) :
    ‖inverseBilinear a t y z‖ ≤ 4*‖y‖*‖z‖ := by
  apply bilinear_norm_le (inverseBilinear a t)
    (inverseBilinear_symmetric a t ht23) (by norm_num : (0:ℝ)≤4)
  intro x
  rw [inverseBilinear_diagonal]
  exact hllVector_norm_le t a b htau ha hb0 hb ht12 ht23 hdom x

/-- At a tree node the previous-prefix vector is orthogonal to the lower
sibling. The actual inverse contribution has a dimension-free squared
bound in the combined lower-prefix radius. -/
theorem prefix_contribution_sq_le
    (t : (ι ⊕ κ) → (ι ⊕ κ) → (ι ⊕ κ) → ℝ)
    (a : ι → ℝ) (b : κ → ℝ) {tau : ℝ} (htau : 0 < tau)
    (ha : ∀ i, tau ≤ a i) (hb0 : ∀ j, 0 ≤ b j) (hb : ∀ j, b j ≤ tau)
    (ht12 : ∀ i j k, t i j k = t j i k) (ht23 : ∀ i j k, t i j k = t i k j)
    (hdom : ∀ z : Point (ι ⊕ κ),
      |MvPolynomial.eval (fun i ↦ z i) (cubicPolynomial t)| ≤
        2*‖diagonal (Sum.elim a b) z‖*‖z‖^2)
    (u w : Point κ) (horth : ⟪u,w⟫_ℝ=0) :
    ‖(3:ℝ) • inverseBilinear a t u (u+(2:ℝ)•w)‖^2 ≤
      576*(‖u‖^2+‖w‖^2)*‖u‖^2 := by
  have hn := inverseBilinear_norm_le t a b htau ha hb0 hb ht12 ht23 hdom u (u+(2:ℝ)•w)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤4*‖u‖*‖u+(2:ℝ)•w‖)).2 hn
  have hnorm : ‖u+(2:ℝ)•w‖^2=‖u‖^2+4*‖w‖^2 := by
    rw [norm_add_sq_real]
    simp only [inner_smul_right,horth,mul_zero,zero_add,add_zero,norm_smul]
    norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
    ring
  have h3norm : ‖(3:ℝ)‖=3 := by norm_num
  rw [norm_smul,h3norm]
  simp only [mul_pow] at hsq
  rw [hnorm] at hsq
  nlinarith [sq_nonneg ‖u‖,sq_nonneg ‖w‖]

end Finite
end WeightedCubicBilinear
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
