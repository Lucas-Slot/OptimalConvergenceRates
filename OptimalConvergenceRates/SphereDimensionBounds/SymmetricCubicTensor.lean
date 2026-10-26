import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.SphereDimensionBounds.WeightedCubicSplit
import OptimalConvergenceRates.SphereDimensionBounds.TensorMomentFunctional

/-! Every actual homogeneous cubic has an actual symmetric finite tensor
representation. This supplies the structural input of WeightedCubicSplit. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.SymmetricCubicTensor

open scoped BigOperators InnerProductSpace
open MvPolynomial WeightedCubicSplit WeightedQuadraticSplit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Tensor (ι : Type*) := ι → ι → ι → ℝ

def polynomialMap : Tensor ι →ₗ[ℝ] MvPolynomial ι ℝ :=
  ∑ i, ∑ j, ∑ k,
    (((LinearMap.proj k : (ι → ℝ) →ₗ[ℝ] ℝ).comp
      (LinearMap.proj j : (ι → ι → ℝ) →ₗ[ℝ] (ι → ℝ))).comp
      (LinearMap.proj i : Tensor ι →ₗ[ℝ] (ι → ι → ℝ))).smulRight (X i * X j * X k)

omit [DecidableEq ι] in
theorem polynomialMap_apply (t : Tensor ι) : polynomialMap t = cubicPolynomial t := by
  simp only [polynomialMap, cubicPolynomial, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, smul_eq_C_mul, mul_assoc]

def basisTensor (i j k : ι) (a : ℝ) : Tensor ι :=
  Pi.single i (Pi.single j (Pi.single k a))

omit [Fintype ι] in
theorem basisTensor_swap12 (i j k x y z : ι) (a : ℝ) :
    basisTensor i j k a x y z = basisTensor j i k a y x z := by
  by_cases hx : x = i <;> by_cases hy : y = j <;> by_cases hz : z = k <;>
    simp [basisTensor, Pi.single_apply, hx, hy, hz]

omit [Fintype ι] in
theorem basisTensor_swap23 (i j k x y z : ι) (a : ℝ) :
    basisTensor i j k a x y z = basisTensor i k j a x z y := by
  by_cases hx : x = i <;> by_cases hy : y = j <;> by_cases hz : z = k <;>
    simp [basisTensor, Pi.single_apply, hx, hy, hz]

theorem polynomialMap_basis (i j k : ι) (a : ℝ) :
    polynomialMap (basisTensor i j k a) = C a * X i * X j * X k := by
  rw [polynomialMap_apply]
  simp [cubicPolynomial, basisTensor, Pi.single_apply, ite_apply, apply_ite, ite_mul]

/-- Average all six ordered slot permutations, with multiplicities
retained when indices coincide. -/
def symBasis (i j k : ι) (a : ℝ) : Tensor ι :=
  basisTensor i j k (a/6) + basisTensor i k j (a/6) +
  basisTensor j i k (a/6) + basisTensor j k i (a/6) +
  basisTensor k i j (a/6) + basisTensor k j i (a/6)

omit [Fintype ι] in
theorem symBasis_symm12 (i j k : ι) (a : ℝ) (x y z : ι) :
    symBasis i j k a x y z = symBasis i j k a y x z := by
  simp only [symBasis, Pi.add_apply]
  rw [basisTensor_swap12 i j k x y z, basisTensor_swap12 i k j x y z,
    basisTensor_swap12 j i k x y z, basisTensor_swap12 j k i x y z,
    basisTensor_swap12 k i j x y z, basisTensor_swap12 k j i x y z]
  ring

omit [Fintype ι] in
theorem symBasis_symm23 (i j k : ι) (a : ℝ) (x y z : ι) :
    symBasis i j k a x y z = symBasis i j k a x z y := by
  simp only [symBasis, Pi.add_apply]
  rw [basisTensor_swap23 i j k x y z, basisTensor_swap23 i k j x y z,
    basisTensor_swap23 j i k x y z, basisTensor_swap23 j k i x y z,
    basisTensor_swap23 k i j x y z, basisTensor_swap23 k j i x y z]
  ring

theorem polynomialMap_symBasis (i j k : ι) (a : ℝ) :
    polynomialMap (symBasis i j k a) = C a * X i * X j * X k := by
  simp only [symBasis, map_add, polynomialMap_basis]
  apply MvPolynomial.funext
  intro x
  simp only [map_add, map_mul, eval_C, eval_X]
  ring

def symmetricTensors : Submodule ℝ (Tensor ι) where
  carrier := {t | (∀ i j k, t i j k = t j i k) ∧ (∀ i j k, t i j k = t i k j)}
  zero_mem' := by constructor <;> intros <;> rfl
  add_mem' ht hs := by
    constructor
    · intro i j k
      simp only [Pi.add_apply, ht.1 i j k, hs.1 i j k]
    · intro i j k
      simp only [Pi.add_apply, ht.2 i j k, hs.2 i j k]
  smul_mem' c t ht := by
    constructor
    · intro i j k
      simp only [Pi.smul_apply, smul_eq_mul, ht.1 i j k]
    · intro i j k
      simp only [Pi.smul_apply, smul_eq_mul, ht.2 i j k]

/-- No tensor-representation premise is needed for an actual homogeneous
cubic. The output tensor is symmetric in all three slots. -/
theorem exists_symmetric_tensor (p : MvPolynomial ι ℝ) (hp : p.IsHomogeneous 3) :
    ∃ t : Tensor ι, (∀ i j k, t i j k = t j i k) ∧
      (∀ i j k, t i j k = t i k j) ∧ cubicPolynomial t = p := by
  classical
  let f : symmetricTensors (ι:=ι) →ₗ[ℝ] MvPolynomial ι ℝ :=
    polynomialMap.comp (symmetricTensors (ι:=ι)).subtype
  have hmem : p ∈ LinearMap.range f := by
    rw [← p.support_sum_monomial_coeff]
    apply Submodule.sum_mem
    intro e he
    have hd : e.sum (fun _ k => k) = 3 := by
      simpa only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] using
        hp (mem_support_iff.mp he)
    obtain ⟨v,hv⟩ := TensorMomentFunctional.exists_tupleExponent 3 e hd
    let t := symBasis (v 0) (v 1) (v 2) (p.coeff e)
    have ht : t ∈ symmetricTensors (ι:=ι) :=
      ⟨symBasis_symm12 _ _ _ _, symBasis_symm23 _ _ _ _⟩
    refine ⟨⟨t,ht⟩,?_⟩
    change polynomialMap t = monomial e (p.coeff e)
    rw [polynomialMap_symBasis]
    have hprod : (X (v 0) : MvPolynomial ι ℝ) * X (v 1) * X (v 2) =
        monomial (TensorMomentFunctional.tupleExponent v) 1 := by
      simpa only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one,
        Fin.succ_zero_eq_one, Fin.succ_one_eq_two, mul_assoc] using
          TensorMomentFunctional.prod_X_tupleExponent v
    calc
      C (p.coeff e) * X (v 0) * X (v 1) * X (v 2) =
          C (p.coeff e) * (X (v 0) * X (v 1) * X (v 2)) := by ring
      _ = _ := by rw [hprod, hv, C_mul_monomial, mul_one]
  obtain ⟨t,ht⟩ := hmem
  exact ⟨t.1,t.2.1,t.2.2,(polynomialMap_apply t.1).symm.trans ht⟩

/-- Universal mixed estimates for an arbitrary ACTUAL homogeneous cubic,
with no supplied tensor representation or mixed-domination hypothesis. -/
theorem exists_weighted_mixed_tensor (p : MvPolynomial ι ℝ) (hp : p.IsHomogeneous 3)
    (L : Point ι →ₗ[ℝ] Point ι)
    (hdom : ∀ x : Point ι, |eval (fun i => x i) p| ≤ 2 * ‖L x‖ * ‖x‖^2) :
    ∃ t : Tensor ι, (∀ i j k, t i j k = t j i k) ∧
      (∀ i j k, t i j k = t i k j) ∧ cubicPolynomial t = p ∧
      ∀ (v u : Point ι), ⟪v,u⟫_ℝ = 0 → ‖L u‖ * ‖v‖ ≤ ‖L v‖ * ‖u‖ →
        |tensorForm t v u u| ≤ 4 * ‖L v‖ * ‖u‖^2 ∧
        |tensorForm t v v u| ≤ 4 * ‖L v‖ * ‖v‖ * ‖u‖ := by
  obtain ⟨t,ht12,ht23,ht⟩ := exists_symmetric_tensor p hp
  refine ⟨t,ht12,ht23,ht,?_⟩
  intro v u horth horder
  apply mixed_bounds (tensorForm t) L (tensorForm_symm12 t ht12) (tensorForm_symm23 t ht23)
  · intro x
    rw [← cubicPolynomial_eval, ht]
    exact hdom x
  · exact horth
  · exact horder

section Split

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A true quadratic polynomial HLL completion for EVERY actual cubic
input satisfying the original weighted estimate. The tensor and polynomial
vector are produced; neither is a premise. -/
theorem exists_hll_completion (p : MvPolynomial (ι ⊕ κ) ℝ) (hp : p.IsHomogeneous 3)
    (a : ι → ℝ) (b : κ → ℝ) {tau : ℝ} (htau : 0 < tau)
    (ha : ∀ i, tau ≤ a i) (hb0 : ∀ j, 0 ≤ b j) (hb : ∀ j, b j ≤ tau)
    (hdom : ∀ z : Point (ι ⊕ κ), |eval (fun i => z i) p| ≤
      2 * ‖diagonal (Sum.elim a b) z‖ * ‖z‖^2) :
    ∃ (t : Tensor (ι ⊕ κ)) (d : ι → MvPolynomial (ι ⊕ κ) ℝ),
      (∀ i j k, t i j k = t j i k) ∧ (∀ i j k, t i j k = t i k j) ∧
      cubicPolynomial t = p ∧ (∀ i, d i = hllCompletionPolynomial a t i) ∧
      (∀ i, (d i).IsHomogeneous 2) ∧
      (∑ i, C (a i) * X (Sum.inl i) * d i) = hllPolynomial t ∧
      ∀ (x : Point ι) (y : Point κ),
        ‖(WithLp.equiv 2 (ι → ℝ)).symm (fun i =>
          eval (Sum.elim (fun k => x k) (fun j => y j)) (d i))‖ ≤ 4 * ‖y‖^2 := by
  obtain ⟨t,ht12,ht23,ht⟩ := exists_symmetric_tensor p hp
  have hd : ∀ z : Point (ι ⊕ κ), |eval (fun i => z i) (cubicPolynomial t)| ≤
      2 * ‖diagonal (Sum.elim a b) z‖ * ‖z‖^2 := by
    intro z
    rw [ht]
    exact hdom z
  refine ⟨t,hllCompletionPolynomial a t,ht12,ht23,ht,fun _ => rfl,
    hllCompletionPolynomial_homogeneous a t,?_,?_⟩
  · exact hll_polynomial_identity a (fun i => (htau.trans_le (ha i)).ne') t
  · intro x y
    exact hllCompletionPolynomial_norm_le t a b htau ha hb0 hb ht12 ht23 hd x y

end Split

end OptimalConvergenceRates.SphereDimensionBounds.SymmetricCubicTensor
