import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.TaylorPolynomials
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.BooleanPolynomial

/-!
# Real and imaginary polynomial components

Coefficientwise real and imaginary parts preserve total degree. Consequently
complex polynomial vectors of degree at most `K` have squared norm positive
under any order-`K` truncated Boolean pseudoexpectation after substitution of
real coordinate functions of Boolean degree one.
-/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Foundation

open scoped BigOperators

def rePolynomial {σ : Type*} (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapRange Complex.re (by simp) p.coeff)

def imPolynomial {σ : Type*} (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapRange Complex.im (by simp) p.coeff)

@[simp] theorem coeff_rePolynomial {σ : Type*} (p : MvPolynomial σ ℂ) (d : σ →₀ ℕ) :
    (rePolynomial p).coeff d = (p.coeff d).re := rfl

@[simp] theorem coeff_imPolynomial {σ : Type*} (p : MvPolynomial σ ℂ) (d : σ →₀ ℕ) :
    (imPolynomial p).coeff d = (p.coeff d).im := rfl

theorem rePolynomial_totalDegree_le {σ : Type*} (p : MvPolynomial σ ℂ) :
    (rePolynomial p).totalDegree ≤ p.totalDegree := by
  classical
  exact Finset.sup_mono (Finsupp.support_mapRange (hf := by simp))

theorem imPolynomial_totalDegree_le {σ : Type*} (p : MvPolynomial σ ℂ) :
    (imPolynomial p).totalDegree ≤ p.totalDegree := by
  classical
  exact Finset.sup_mono (Finsupp.support_mapRange (hf := by simp))

theorem eval_rePolynomial {σ : Type*} (p : MvPolynomial σ ℂ) (x : σ → ℝ) :
    MvPolynomial.eval x (rePolynomial p) =
      (MvPolynomial.eval (fun i ↦ (x i : ℂ)) p).re := by
  classical
  rw [MvPolynomial.eval_eq]
  change (Finsupp.mapRange Complex.re (by simp) p.coeff).sum
    (fun d c ↦ c * ∏ i ∈ d.support, x i ^ d i) = _
  rw [Finsupp.sum_mapRange_index (by intro d; simp)]
  rw [MvPolynomial.eval_eq, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hprod : (∏ i ∈ d.support, (x i : ℂ) ^ d i) =
      ((∏ i ∈ d.support, x i ^ d i : ℝ) : ℂ) := by
    simp only [Complex.ofReal_prod, Complex.ofReal_pow]
  rw [hprod]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem eval_imPolynomial {σ : Type*} (p : MvPolynomial σ ℂ) (x : σ → ℝ) :
    MvPolynomial.eval x (imPolynomial p) =
      (MvPolynomial.eval (fun i ↦ (x i : ℂ)) p).im := by
  classical
  rw [MvPolynomial.eval_eq]
  change (Finsupp.mapRange Complex.im (by simp) p.coeff).sum
    (fun d c ↦ c * ∏ i ∈ d.support, x i ^ d i) = _
  rw [Finsupp.sum_mapRange_index (by intro d; simp)]
  rw [MvPolynomial.eval_eq, Complex.im_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hprod : (∏ i ∈ d.support, (x i : ℂ) ^ d i) =
      ((∏ i ∈ d.support, x i ^ d i : ℝ) : ℂ) := by
    simp only [Complex.ofReal_prod, Complex.ofReal_pow]
  rw [hprod]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]

theorem complex_vector_norm_sq {J : Type*} [Fintype J] (v : EuclideanSpace ℂ J) :
    ‖v‖ ^ 2 = ∑ j : J, ((v j).re ^ 2 + (v j).im ^ 2) := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

section BooleanPositivity

variable {V J σ : Type*} [Fintype V] [DecidableEq V] [Fintype J]

theorem hasBooleanDegree_re_eval (p : MvPolynomial σ ℂ)
    (a : σ → (V → Bool) → ℝ) (ha : ∀ i, HasBooleanDegree 1 (a i))
    (K : ℕ) (hp : p.totalDegree ≤ K) :
    HasBooleanDegree K
      (fun z ↦ (MvPolynomial.eval (fun i ↦ (a i z : ℂ)) p).re) := by
  have h := hasBooleanDegree_eval_of_totalDegree_le (rePolynomial p) a ha K
    ((rePolynomial_totalDegree_le p).trans hp)
  simpa only [eval_rePolynomial] using h

theorem hasBooleanDegree_im_eval (p : MvPolynomial σ ℂ)
    (a : σ → (V → Bool) → ℝ) (ha : ∀ i, HasBooleanDegree 1 (a i))
    (K : ℕ) (hp : p.totalDegree ≤ K) :
    HasBooleanDegree K
      (fun z ↦ (MvPolynomial.eval (fun i ↦ (a i z : ℂ)) p).im) := by
  have h := hasBooleanDegree_eval_of_totalDegree_le (imPolynomial p) a ha K
    ((imPolynomial_totalDegree_le p).trans hp)
  simpa only [eval_imPolynomial] using h

theorem hasBooleanDegree_norm_sq (g : (V → Bool) → EuclideanSpace ℂ J) (K : ℕ)
    (hre : ∀ j, HasBooleanDegree K (fun z ↦ (g z j).re))
    (him : ∀ j, HasBooleanDegree K (fun z ↦ (g z j).im)) :
    HasBooleanDegree (2 * K) (fun z ↦ ‖g z‖ ^ 2) := by
  simp_rw [complex_vector_norm_sq]
  apply hasBooleanDegree_finset_sum
  intro j hj
  exact hasBooleanDegree_add _ _ _
    (hasBooleanDegree_square K _ (hre j)) (hasBooleanDegree_square K _ (him j))

theorem truncatedPseudoexpectation_norm_sq_nonneg
    (E : TruncatedBooleanPseudoexpectation V K)
    (g : (V → Bool) → EuclideanSpace ℂ J)
    (hre : ∀ j, HasBooleanDegree K (fun z ↦ (g z j).re))
    (him : ∀ j, HasBooleanDegree K (fun z ↦ (g z j).im)) :
    0 ≤ E.functional ⟨fun z ↦ ‖g z‖ ^ 2, hasBooleanDegree_norm_sq g K hre him⟩ := by
  let R : J → booleanDegreeSpace (I := V) (2 * K) := fun j ↦
    ⟨fun z ↦ (g z j).re ^ 2, hasBooleanDegree_square K _ (hre j)⟩
  let I : J → booleanDegreeSpace (I := V) (2 * K) := fun j ↦
    ⟨fun z ↦ (g z j).im ^ 2, hasBooleanDegree_square K _ (him j)⟩
  have hsum : (⟨fun z ↦ ‖g z‖ ^ 2, hasBooleanDegree_norm_sq g K hre him⟩ :
      booleanDegreeSpace (I := V) (2 * K)) = ∑ j : J, (R j + I j) := by
    apply Subtype.ext
    funext z
    simp only [Submodule.coe_sum, Submodule.coe_add, Finset.sum_apply,
      Pi.add_apply, R, I]
    exact complex_vector_norm_sq (g z)
  rw [hsum, map_sum]
  apply Finset.sum_nonneg
  intro j hj
  rw [map_add]
  exact add_nonneg (E.square_nonneg _ (hre j)) (E.square_nonneg _ (him j))

theorem angularTaylorVector_boolean_re_degree
    (p : J → MvPolynomial (Option σ) ℝ) (τ : ℂ) (K : ℕ)
    (a : σ → (V → Bool) → ℝ) (ha : ∀ i, HasBooleanDegree 1 (a i)) (j : J) :
    HasBooleanDegree K
      (fun z ↦ (angularTaylorVector p τ K (fun i ↦ a i z) j).re) := by
  simpa only [angularTaylorVector_apply] using
    hasBooleanDegree_re_eval (angularTaylorPolynomial (p j) τ K) a ha K
      (angularTaylorPolynomial_degree_le (p j) τ K)

theorem angularTaylorVector_boolean_im_degree
    (p : J → MvPolynomial (Option σ) ℝ) (τ : ℂ) (K : ℕ)
    (a : σ → (V → Bool) → ℝ) (ha : ∀ i, HasBooleanDegree 1 (a i)) (j : J) :
    HasBooleanDegree K
      (fun z ↦ (angularTaylorVector p τ K (fun i ↦ a i z) j).im) := by
  simpa only [angularTaylorVector_apply] using
    hasBooleanDegree_im_eval (angularTaylorPolynomial (p j) τ K) a ha K
      (angularTaylorPolynomial_degree_le (p j) τ K)

theorem angularTaylorVector_boolean_norm_sq_degree
    (p : J → MvPolynomial (Option σ) ℝ) (τ : ℂ) (K : ℕ)
    (a : σ → (V → Bool) → ℝ) (ha : ∀ i, HasBooleanDegree 1 (a i)) :
    HasBooleanDegree (2 * K)
      (fun z ↦ ‖angularTaylorVector p τ K (fun i ↦ a i z)‖ ^ 2) :=
  hasBooleanDegree_norm_sq _ K
    (angularTaylorVector_boolean_re_degree p τ K a ha)
    (angularTaylorVector_boolean_im_degree p τ K a ha)

/-- The actual polynomial Taylor vector is positive under the truncated
functional on every real Boolean map with coordinate degree one. -/
theorem truncatedPseudoexpectation_angularTaylorVector_norm_sq_nonneg
    (E : TruncatedBooleanPseudoexpectation V K)
    (p : J → MvPolynomial (Option σ) ℝ) (τ : ℂ)
    (a : σ → (V → Bool) → ℝ) (ha : ∀ i, HasBooleanDegree 1 (a i)) :
    0 ≤ E.functional ⟨fun z ↦ ‖angularTaylorVector p τ K (fun i ↦ a i z)‖ ^ 2,
      angularTaylorVector_boolean_norm_sq_degree p τ K a ha⟩ :=
  truncatedPseudoexpectation_norm_sq_nonneg E _
    (angularTaylorVector_boolean_re_degree p τ K a ha)
    (angularTaylorVector_boolean_im_degree p τ K a ha)

end BooleanPositivity

end Foundation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
