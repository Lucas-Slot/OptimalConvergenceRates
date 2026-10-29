import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Matrix.Order
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.Hierarchy

/-! Nonnegative radial-leading quartics with no cubic part.  Experimental
standalone module; no dimension-uniform upper bound is asserted here. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace RadialQuarticSOS

open scoped BigOperators InnerProductSpace Topology Matrix MatrixOrder Matrix.Norms.L2Operator
open Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def realInnerBilinear : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerₗ E).mkContinuous₂ 1 (by
    intro x y
    simpa only [one_mul, innerₗ_apply_apply] using norm_inner_le_norm x y)

@[simp] theorem realInnerBilinear_apply (x y : E) :
    realInnerBilinear x y = ⟪x,y⟫_ℝ := rfl

def value (c : ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ) (b : E →L[ℝ] ℝ)
    (a : ℝ) (x : E) : ℝ :=
  c * ⟪x, x⟫_ℝ ^ 2 + H x x + b x + a

def homogeneousValue (c : ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (b : E →L[ℝ] ℝ) (a : ℝ) (x : E) (t : ℝ) : ℝ :=
  c * ⟪x, x⟫_ℝ ^ 2 + t ^ 2 * H x x + t ^ 3 * b x + a * t ^ 4

def shiftedForm (c : ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ) (u : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  H + (2 * c * ⟪u, u⟫_ℝ) • realInnerBilinear

@[simp] theorem shiftedForm_apply (c : ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (u x y : E) : shiftedForm c H u x y = H x y + 2 * c * ⟪u, u⟫_ℝ * ⟪x, y⟫_ℝ := by
  simp [shiftedForm]

theorem value_continuous (c : ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (b : E →L[ℝ] ℝ) (a : ℝ) : Continuous (value c H b a) := by
  unfold value
  fun_prop

theorem value_lower_bound (c : ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (b : E →L[ℝ] ℝ) (a : ℝ) (x : E) :
    c * ‖x‖ ^ 4 - ‖H‖ * ‖x‖ ^ 2 - ‖b‖ * ‖x‖ + a ≤ value c H b a x := by
  have hH : - (‖H‖ * ‖x‖ * ‖x‖) ≤ H x x := by
    have h := H.le_opNorm₂ x x
    rw [Real.norm_eq_abs] at h
    exact (abs_le.mp h).1
  have hb : -(‖b‖ * ‖x‖) ≤ b x := by
    have h := b.le_opNorm x
    rw [Real.norm_eq_abs] at h
    exact (abs_le.mp h).1
  simp only [value, real_inner_self_eq_norm_sq]
  nlinarith

theorem value_exists_globalMin [FiniteDimensional ℝ E]
    (c : ℝ) (hc : 0 < c) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (b : E →L[ℝ] ℝ) (a : ℝ) :
    ∃ u : E, ∀ x, value c H b a u ≤ value c H b a x := by
  apply (value_continuous c H b a).exists_forall_le' (0 : E)
  have ht := tendsto_norm_cocompact_atTop (E := E)
  filter_upwards [ht.eventually (eventually_ge_atTop (max 1 ((‖H‖ + ‖b‖) / c)))] with x hx
  have h1 : 1 ≤ ‖x‖ := (le_max_left _ _).trans hx
  have hcT : ‖H‖ + ‖b‖ ≤ c * ‖x‖ := by
    have h := (le_max_right 1 ((‖H‖ + ‖b‖) / c)).trans hx
    exact (div_le_iff₀ hc).mp h |>.trans_eq (mul_comm _ _)
  have hT2 : ‖x‖ ≤ ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]
  have hT3 : ‖x‖ ^ 3 ≤ ‖x‖ ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (pow_nonneg (norm_nonneg x) 3)]
  have hcomp : ‖H‖ * ‖x‖ ^ 2 + ‖b‖ * ‖x‖ ≤ c * ‖x‖ ^ 4 := by
    calc
      _ ≤ (‖H‖ + ‖b‖) * ‖x‖ ^ 2 := by
        nlinarith [mul_nonneg (norm_nonneg b) (sub_nonneg.mpr hT2)]
      _ ≤ (c * ‖x‖) * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcT (sq_nonneg _)
      _ = c * ‖x‖ ^ 3 := by ring
      _ ≤ c * ‖x‖ ^ 4 := mul_le_mul_of_nonneg_left hT3 hc.le
  have hl := value_lower_bound c H b a x
  simpa only [value, inner_zero_left, map_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    mul_zero, zero_add, add_zero] using (show a ≤ value c H b a x by linarith)

theorem value_line_hasDerivAt (c : ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (b : E →L[ℝ] ℝ) (a : ℝ) (u v : E)
    (hH : ∀ x y, H x y = H y x) :
    HasDerivAt (fun s : ℝ ↦ value c H b a (u + s • v))
      (4 * c * ⟪u,u⟫_ℝ * ⟪u,v⟫_ℝ + 2 * H u v + b v) 0 := by
  have hg : HasDerivAt (fun s : ℝ ↦ u + s • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add u
  have hq := hg.inner ℝ hg
  have hlin := H.hasFDerivAt.comp_hasDerivAt 0 hg
  have hbil := hlin.clm_apply hg
  have hbl := b.hasFDerivAt.comp_hasDerivAt 0 hg
  have h := (((hq.pow 2).const_mul c).add hbil).add hbl |>.add_const a
  convert h using 1 <;>
    simp only [value, Function.comp_apply, Pi.add_apply, Pi.pow_apply,
      zero_smul, add_zero, hH v u, real_inner_comm v u] <;>
    first | (funext s; ring) | ring

theorem globalMin_stationary (c : ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (b : E →L[ℝ] ℝ) (a : ℝ) (u : E)
    (hH : ∀ x y, H x y = H y x)
    (hmin : ∀ x, value c H b a u ≤ value c H b a x) (v : E) :
    4 * c * ⟪u,u⟫_ℝ * ⟪u,v⟫_ℝ + 2 * H u v + b v = 0 := by
  have hlocal : IsLocalMin (fun s : ℝ ↦ value c H b a (u + s • v)) 0 := by
    apply Filter.Eventually.of_forall
    intro s
    simpa using hmin (u + s • v)
  exact hlocal.hasDerivAt_eq_zero (value_line_hasDerivAt c H b a u v hH)

theorem globalMin_completion (c : ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (b : E →L[ℝ] ℝ) (a : ℝ) (u : E)
    (hH : ∀ x y, H x y = H y x)
    (hmin : ∀ x, value c H b a u ≤ value c H b a x) (x : E) :
    value c H b a x - value c H b a u =
      c * (⟪x,x⟫_ℝ - ⟪u,u⟫_ℝ) ^ 2 + shiftedForm c H u (x-u) (x-u) := by
  have hsx := globalMin_stationary c H b a u hH hmin x
  have hsu := globalMin_stationary c H b a u hH hmin u
  have hxu : ⟪x,u⟫_ℝ = ⟪u,x⟫_ℝ := real_inner_comm _ _
  simp only [value, shiftedForm_apply, map_sub, ContinuousLinearMap.sub_apply,
    inner_sub_left, inner_sub_right, hH x u, hxu]
  nlinarith

theorem quadratic_coefficient_nonneg (A B : ℝ)
    (h : ∀ t : ℝ, 0 ≤ A * t ^ 4 + B * t ^ 2) : 0 ≤ B := by
  have hlim : Tendsto (fun t : ℝ ↦ A * t ^ 2 + B) (𝓝[≠] 0) (𝓝 B) := by
    have hc : Continuous (fun t : ℝ ↦ A * t ^ 2 + B) := by fun_prop
    simpa using! (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left inf_le_left
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  have hmul : 0 ≤ t ^ 2 * (A * t ^ 2 + B) := by nlinarith [h t]
  exact nonneg_of_mul_nonneg_right hmul (sq_pos_of_ne_zero ht0)

/-- A global minimum forces positivity of the shifted quadratic form,
including the directions orthogonal to the minimum. -/
theorem globalMin_shiftedForm_nonneg (c : ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (b : E →L[ℝ] ℝ) (a : ℝ) (u : E)
    (hH : ∀ x y, H x y = H y x)
    (hmin : ∀ x, value c H b a u ≤ value c H b a x) (v : E) :
    0 ≤ shiftedForm c H u v v := by
  have hcomplete := globalMin_completion c H b a u hH hmin
  by_cases huv : ⟪u,v⟫_ℝ = 0
  · apply quadratic_coefficient_nonneg (c * ⟪v,v⟫_ℝ ^ 2)
    intro t
    have h := sub_nonneg.mpr (hmin (u + t • v))
    rw [hcomplete] at h
    have hvu : ⟪v,u⟫_ℝ = 0 := by rw [real_inner_comm]; exact huv
    simp only [add_sub_cancel_left, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, huv, hvu, mul_zero, add_zero,
      zero_add, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul] at h
    nlinarith [h]
  · have hv : v ≠ 0 := by intro hv; simp [hv] at huv
    have hvv : 0 < ⟪v,v⟫_ℝ := real_inner_self_pos.mpr hv
    let t : ℝ := -2 * ⟪u,v⟫_ℝ / ⟪v,v⟫_ℝ
    have ht : t ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) huv) hvv.ne'
    have hvu : ⟪v,u⟫_ℝ = ⟪u,v⟫_ℝ := real_inner_comm _ _
    have hradius : ⟪u+t • v,u+t • v⟫_ℝ = ⟪u,u⟫_ℝ := by
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, hvu]
      dsimp [t]
      field_simp
      ring
    have h := sub_nonneg.mpr (hmin (u+t • v))
    rw [hcomplete, hradius] at h
    simp only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_add,
      add_sub_cancel_left, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul] at h
    have hmul : 0 ≤ shiftedForm c H u v v * t ^ 2 := by nlinarith [h]
    exact nonneg_of_mul_nonneg_left hmul (sq_pos_of_ne_zero ht)

theorem homogeneous_completion (c : ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (b : E →L[ℝ] ℝ) (a : ℝ) (u : E)
    (hH : ∀ x y, H x y = H y x)
    (hmin : ∀ x, value c H b a u ≤ value c H b a x) (x : E) (t : ℝ) :
    homogeneousValue c H b a x t =
      c * (⟪x,x⟫_ℝ - ⟪u,u⟫_ℝ * t ^ 2) ^ 2 +
      t ^ 2 * shiftedForm c H u (x-t • u) (x-t • u) + value c H b a u * t ^ 4 := by
  have hsx := globalMin_stationary c H b a u hH hmin x
  have hsu := globalMin_stationary c H b a u hH hmin u
  have hxu : ⟪x,u⟫_ℝ = ⟪u,x⟫_ℝ := real_inner_comm _ _
  simp only [homogeneousValue, value, shiftedForm_apply, map_sub, map_smul,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    hH x u, hxu]
  linear_combination t ^ 3 * hsx - t ^ 4 * hsu

section Coordinates

variable {n : ℕ}
abbrev Point (n : ℕ) := EuclideanSpace ℝ (Fin n)

def coordinateMatrix (H : Point n →L[ℝ] Point n →L[ℝ] ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ H (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j)

theorem coordinateMatrix_eval (H : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (x y : Point n) :
    (fun i ↦ x i) ⬝ᵥ (coordinateMatrix H *ᵥ fun i ↦ y i) = H x y := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hx : ∑ i, x i • e i = x := e.sum_repr x
  have hy : ∑ i, y i • e i = y := e.sum_repr y
  calc
    _ = H (∑ i, x i • e i) (∑ i, y i • e i) := by
      simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
        Finset.mul_sum, coordinateMatrix]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [e]
      ring
    _ = H x y := by rw [hx, hy]

theorem coordinateMatrix_posSemidef (H : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (hH : ∀ x y, H x y = H y x) (hpos : ∀ x, 0 ≤ H x x) :
    (coordinateMatrix H).PosSemidef := by
  classical
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, coordinateMatrix]
    exact hH _ _
  · intro x
    let v : Point n := (WithLp.equiv 2 (Fin n → ℝ)).symm x
    have hv : (fun i ↦ v i) = x := rfl
    rw [star_trivial, ← hv, coordinateMatrix_eval]
    exact hpos v

theorem nonnegative_form_exists_squares
    (H : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (hH : ∀ x y, H x y = H y x) (hpos : ∀ x, 0 ≤ H x x) :
    ∃ S : Matrix (Fin n) (Fin n) ℝ,
      ∀ x : Point n, H x x = ∑ i, ((S *ᵥ fun j ↦ x j) i) ^ 2 := by
  classical
  obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    (coordinateMatrix_posSemidef H hH hpos).nonneg
  rw [Matrix.star_eq_conjTranspose] at hS
  refine ⟨S, ?_⟩
  intro x
  rw [← coordinateMatrix_eval H x x, hS, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose]
  simp only [star_trivial, dotProduct, pow_two]

/-- Actual finite sums of quadratic expressions, with positivity of the
shifted form proved from global minimality rather than assumed. -/
theorem homogeneous_nonnegative_exists_squares
    (c : ℝ) (hc : 0 < c) (H : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (b : Point n →L[ℝ] ℝ) (a : ℝ) (hH : ∀ x y, H x y = H y x)
    (hF : ∀ x t, 0 ≤ homogeneousValue c H b a x t) :
    ∃ (u : Point n) (S : Matrix (Fin n) (Fin n) ℝ),
      0 ≤ value c H b a u ∧
      ∀ x t, homogeneousValue c H b a x t =
        (Real.sqrt c * (⟪x,x⟫_ℝ - ⟪u,u⟫_ℝ * t ^ 2)) ^ 2 +
        (Real.sqrt (value c H b a u) * t ^ 2) ^ 2 +
        ∑ i, (t * (S *ᵥ fun j ↦ (x-t • u) j) i) ^ 2 := by
  obtain ⟨u, hmin⟩ := value_exists_globalMin c hc H b a
  have hv : 0 ≤ value c H b a u := by simpa [value, homogeneousValue] using hF u 1
  have hshift : ∀ x y, shiftedForm c H u x y = shiftedForm c H u y x := by
    intro x y
    simp only [shiftedForm_apply, hH x y, real_inner_comm x y]
  obtain ⟨S, hS⟩ := nonnegative_form_exists_squares (shiftedForm c H u) hshift
    (globalMin_shiftedForm_nonneg c H b a u hH hmin)
  refine ⟨u, S, hv, ?_⟩
  intro x t
  rw [homogeneous_completion c H b a u hH hmin x t, hS]
  simp only [mul_pow, Real.sq_sqrt hc.le, Real.sq_sqrt hv]
  rw [Finset.mul_sum]
  ring

end Coordinates

section Polynomial

open MvPolynomial
variable {n : ℕ}

def tangentRadius (n : ℕ) : MvPolynomial (Fin (n+1)) ℝ :=
  ∑ i : Fin n, X i.succ ^ 2

def tangentLinear (v : Fin n → ℝ) : MvPolynomial (Fin (n+1)) ℝ :=
  ∑ i, C (v i) * X i.succ

def polynomial (c : ℝ) (H : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (b : Point n →L[ℝ] ℝ) (a : ℝ) : MvPolynomial (Fin (n+1)) ℝ :=
  C c * tangentRadius n ^ 2 + X 0 ^ 2 *
      (∑ i, ∑ j, C (coordinateMatrix H i j) * X i.succ * X j.succ) +
    X 0 ^ 3 * tangentLinear (fun i ↦ b (EuclideanSpace.basisFun (Fin n) ℝ i)) +
    C a * X 0 ^ 4

theorem tangentRadius_eval (x : Fin (n + 1) → ℝ) :
    eval x (tangentRadius n) =
      ⟪(WithLp.equiv 2 (Fin n → ℝ)).symm (fun i ↦ x i.succ),
        (WithLp.equiv 2 (Fin n → ℝ)).symm (fun i ↦ x i.succ)⟫_ℝ := by
  rw [real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
  simp [tangentRadius]

theorem tangentLinear_eval (b : Point n →L[ℝ] ℝ) (x : Fin (n + 1) → ℝ) :
    eval x (tangentLinear (fun i ↦ b (EuclideanSpace.basisFun (Fin n) ℝ i))) =
      b ((WithLp.equiv 2 (Fin n → ℝ)).symm (fun i ↦ x i.succ)) := by
  let v : Point n := (WithLp.equiv 2 (Fin n → ℝ)).symm (fun i ↦ x i.succ)
  have hv : ∑ i, v i • EuclideanSpace.basisFun (Fin n) ℝ i = v :=
    (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  calc
    _ = b (∑ i, v i • EuclideanSpace.basisFun (Fin n) ℝ i) := by
      simp only [tangentLinear, map_sum, map_mul, eval_C, eval_X, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [v]
      ring
    _ = b v := congrArg b hv

theorem polynomial_eval (c : ℝ) (H : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (b : Point n →L[ℝ] ℝ) (a : ℝ) (x : Fin (n + 1) → ℝ) :
    eval x (polynomial c H b a) =
      homogeneousValue c H b a
        ((WithLp.equiv 2 (Fin n → ℝ)).symm (fun i ↦ x i.succ)) (x 0) := by
  let v : Point n := (WithLp.equiv 2 (Fin n → ℝ)).symm (fun i ↦ x i.succ)
  have h := coordinateMatrix_eval H v v
  dsimp [v] at h
  have hq : (∑ i, ∑ j, coordinateMatrix H i j * x i.succ * x j.succ) = H v v := by
    simpa only [v, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_comm,
      mul_left_comm] using! h
  simp only [polynomial, map_add, map_mul, map_pow, map_sum, eval_C, eval_X,
    tangentRadius_eval, tangentLinear_eval, homogeneousValue]
  rw [hq]

theorem tangentRadius_homogeneous : (tangentRadius n).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i _
  exact (isHomogeneous_X ℝ i.succ).pow 2

theorem tangentLinear_homogeneous (v : Fin n → ℝ) :
    (tangentLinear v).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact (isHomogeneous_X ℝ i.succ).C_mul _

def firstRoot (c : ℝ) (u : Point n) : MvPolynomial (Fin (n+1)) ℝ :=
  C (Real.sqrt c) * (tangentRadius n - C ⟪u,u⟫_ℝ * X 0 ^ 2)

def lastRoot (d : ℝ) : MvPolynomial (Fin (n+1)) ℝ :=
  C (Real.sqrt d) * X 0 ^ 2

def middleRoot (S : Matrix (Fin n) (Fin n) ℝ) (u : Point n) (i : Fin n) :
    MvPolynomial (Fin (n+1)) ℝ :=
  X 0 * (∑ j, C (S i j) * (X j.succ - C (u j) * X 0))

theorem firstRoot_homogeneous (c : ℝ) (u : Point n) :
    (firstRoot c u).IsHomogeneous 2 := by
  exact (tangentRadius_homogeneous.sub
    (((isHomogeneous_X ℝ (0 : Fin (n+1))).pow 2).C_mul _)).C_mul _

theorem lastRoot_homogeneous (d : ℝ) :
    (lastRoot (n := n) d).IsHomogeneous 2 :=
  ((isHomogeneous_X ℝ (0 : Fin (n+1))).pow 2).C_mul _

theorem middleRoot_homogeneous (S : Matrix (Fin n) (Fin n) ℝ)
    (u : Point n) (i : Fin n) : (middleRoot S u i).IsHomogeneous 2 := by
  change (X 0 * (∑ j, C (S i j) * (X j.succ - C (u j) * X 0))).IsHomogeneous (1+1)
  apply (isHomogeneous_X ℝ (0 : Fin (n+1))).mul
  apply IsHomogeneous.sum
  intro j _
  exact ((isHomogeneous_X ℝ j.succ).sub
    ((isHomogeneous_X ℝ (0 : Fin (n+1))).C_mul _)).C_mul _

def roots (c d : ℝ) (S : Matrix (Fin n) (Fin n) ℝ) (u : Point n) :
    Fin (2+n) → MvPolynomial (Fin (n+1)) ℝ :=
  Fin.addCases (fun j : Fin 2 ↦ if j=0 then firstRoot c u else lastRoot d)
    (middleRoot S u)

theorem roots_homogeneous (c d : ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (u : Point n) (i : Fin (2 + n)) : (roots c d S u i).IsHomogeneous 2 := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [roots, Fin.addCases_left]
    split_ifs
    · exact firstRoot_homogeneous c u
    · exact lastRoot_homogeneous d
  · intro j
    simpa only [roots, Fin.addCases_right] using middleRoot_homogeneous S u j

theorem firstRoot_eval (c : ℝ) (u : Point n) (x : Fin (n + 1) → ℝ) :
    eval x (firstRoot c u) = Real.sqrt c *
      (⟪(WithLp.equiv 2 (Fin n → ℝ)).symm (fun i ↦ x i.succ),
        (WithLp.equiv 2 (Fin n → ℝ)).symm (fun i ↦ x i.succ)⟫_ℝ -
      ⟪u,u⟫_ℝ * (x 0)^2) := by
  simp only [firstRoot, map_mul, map_sub, map_pow, eval_C, eval_X, tangentRadius_eval]

theorem lastRoot_eval (d : ℝ) (x : Fin (n + 1) → ℝ) :
    eval x (lastRoot d) = Real.sqrt d * (x 0)^2 := by
  simp only [lastRoot, map_mul, map_pow, eval_C, eval_X]

theorem middleRoot_eval (S : Matrix (Fin n) (Fin n) ℝ) (u : Point n)
    (i : Fin n) (x : Fin (n + 1) → ℝ) :
    eval x (middleRoot S u i) =
      x 0 * (S *ᵥ fun j ↦
        ((WithLp.equiv 2 (Fin n → ℝ)).symm (fun k ↦ x k.succ) - (x 0) • u) j) i := by
  simp only [middleRoot, map_mul, map_sub, map_sum, eval_C, eval_X,
    Matrix.mulVec, dotProduct, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change S i j * (x j.succ-u j*x 0) = S i j * (x j.succ-x 0*u j)
  ring

theorem roots_eval_sum (c d : ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (u : Point n) (x : Fin (n + 1) → ℝ) :
    (∑ i : Fin (2+n), (eval x (roots c d S u i)) ^ 2) =
      (eval x (firstRoot c u)) ^ 2 + (eval x (lastRoot d)) ^ 2 +
        ∑ i, (eval x (middleRoot S u i)) ^ 2 := by
  simp [roots, Fin.sum_univ_add, Fin.sum_univ_two]

/-- A globally nonnegative actual radial-leading quartic is an exact sum
of homogeneous quadratic polynomials.  The minimum and shifted PSD form
are constructed in the proof, not assumed as certificate hypotheses. -/
theorem polynomial_nonnegative_exists_SOS
    (c : ℝ) (hc : 0 < c) (H : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (b : Point n →L[ℝ] ℝ) (a : ℝ) (hH : ∀ x y, H x y = H y x)
    (hF : ∀ x : Fin (n+1) → ℝ, 0 ≤ eval x (polynomial c H b a)) :
    ∃ q : Fin (2+n) → MvPolynomial (Fin (n+1)) ℝ,
      (∀ j, (q j).IsHomogeneous 2) ∧ polynomial c H b a = ∑ j, q j ^ 2 := by
  classical
  have hval : ∀ x : Point n, ∀ t : ℝ, 0 ≤ homogeneousValue c H b a x t := by
    intro x t
    have h := hF (Fin.cases t (fun i ↦ x i))
    rw [polynomial_eval] at h
    simpa only [Fin.cases_zero, Fin.cases_succ] using! h
  obtain ⟨u, S, _, hsos⟩ := homogeneous_nonnegative_exists_squares c hc H b a hH hval
  refine ⟨roots c (value c H b a u) S u, roots_homogeneous _ _ _ _, ?_⟩
  apply MvPolynomial.funext
  intro x
  simp only [map_sum, map_pow]
  rw [roots_eval_sum, polynomial_eval, firstRoot_eval, lastRoot_eval]
  simp_rw [middleRoot_eval]
  exact hsos _ _

/-- The standard full-sphere order-two certificate, with zero multiplier
and no dimension-dependent shift. -/
theorem polynomial_nonnegative_feasible_two
    (c : ℝ) (hc : 0 < c) (H : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (b : Point n →L[ℝ] ℝ) (a : ℝ) (hH : ∀ x y, H x y = H y x)
    (hF : ∀ x : Fin (n+1) → ℝ, 0 ≤ eval x (polynomial c H b a)) :
    Foundation.Feasible 2 (polynomial c H b a) 0 := by
  obtain ⟨q, hq, heq⟩ := polynomial_nonnegative_exists_SOS c hc H b a hH hF
  apply Foundation.feasible_of_squares q 0 (fun j ↦ (hq j).totalDegree_le)
  · simp
  · simpa only [C_0, sub_zero, mul_zero, add_zero] using heq

def matrixBilinear (H : Matrix (Fin n) (Fin n) ℝ) :
    Point n →L[ℝ] Point n →L[ℝ] ℝ :=
  realInnerBilinear.comp (Matrix.toEuclideanLin H.transpose).toContinuousLinearMap

def matrixLinear (b : Fin n → ℝ) : Point n →L[ℝ] ℝ :=
  realInnerBilinear ((WithLp.equiv 2 (Fin n → ℝ)).symm b)

theorem coordinateMatrix_matrixBilinear (H : Matrix (Fin n) (Fin n) ℝ) :
    coordinateMatrix (matrixBilinear H) = H := by
  ext i j
  simp [coordinateMatrix, matrixBilinear, Matrix.toLpLin_apply,
    EuclideanSpace.basisFun_apply, PiLp.inner_apply, Matrix.mulVec, dotProduct]

theorem matrixLinear_basis (b : Fin n → ℝ) (i : Fin n) :
    matrixLinear b (EuclideanSpace.basisFun (Fin n) ℝ i) = b i := by
  simp [matrixLinear, EuclideanSpace.basisFun_apply, PiLp.inner_apply]

theorem matrixBilinear_symmetric (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    ∀ x y : Point n, matrixBilinear H x y = matrixBilinear H y x := by
  intro x y
  rw [← coordinateMatrix_eval (matrixBilinear H) x y,
    ← coordinateMatrix_eval (matrixBilinear H) y x, coordinateMatrix_matrixBilinear]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ ↦ M i j) hH
  simp only [Matrix.transpose_apply] at h
  rw [h]
  ring

def matrixPolynomial (c : ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (a : ℝ) : MvPolynomial (Fin (n+1)) ℝ :=
  C c * tangentRadius n ^ 2 + X 0 ^ 2 *
      (∑ i, ∑ j, C (H i j) * X i.succ * X j.succ) +
    X 0 ^ 3 * tangentLinear b + C a * X 0 ^ 4

theorem matrixPolynomial_eq (c : ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (a : ℝ) :
    matrixPolynomial c H b a = polynomial c (matrixBilinear H) (matrixLinear b) a := by
  simp only [matrixPolynomial, polynomial, coordinateMatrix_matrixBilinear, matrixLinear_basis]

theorem matrixPolynomial_homogeneous (c : ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (a : ℝ) : (matrixPolynomial c H b a).IsHomogeneous 4 := by
  have hquad : (∑ i, ∑ j, C (H i j) * X i.succ * X j.succ :
      MvPolynomial (Fin (n+1)) ℝ).IsHomogeneous 2 := by
    apply IsHomogeneous.sum
    intro i _
    apply IsHomogeneous.sum
    intro j _
    exact ((isHomogeneous_X ℝ i.succ).C_mul _).mul (isHomogeneous_X ℝ j.succ)
  have h1 : (C c * tangentRadius n ^ 2).IsHomogeneous 4 := by
    simpa using (tangentRadius_homogeneous (n := n)).pow 2 |>.C_mul c
  have h2 : (X 0 ^ 2 * (∑ i, ∑ j, C (H i j) * X i.succ * X j.succ) :
      MvPolynomial (Fin (n+1)) ℝ).IsHomogeneous 4 := by
    exact ((isHomogeneous_X ℝ (0 : Fin (n+1))).pow 2).mul hquad
  have h3 : (X 0 ^ 3 * tangentLinear b).IsHomogeneous 4 :=
    ((isHomogeneous_X ℝ (0 : Fin (n+1))).pow 3).mul (tangentLinear_homogeneous b)
  have h4 : (C a * X 0 ^ 4 : MvPolynomial (Fin (n+1)) ℝ).IsHomogeneous 4 :=
    ((isHomogeneous_X ℝ (0 : Fin (n+1))).pow 4).C_mul a
  exact ((h1.add h2).add h3).add h4

/-- Explicit matrix-coefficient version of the homogeneous quadratic SOS
theorem, in every finite dimension and without a shift. -/
theorem matrixPolynomial_nonnegative_exists_SOS
    (c : ℝ) (hc : 0 < c) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (b : Fin n → ℝ) (a : ℝ)
    (hF : ∀ x : Fin (n+1) → ℝ, 0 ≤ eval x (matrixPolynomial c H b a)) :
    ∃ q : Fin (2+n) → MvPolynomial (Fin (n+1)) ℝ,
      (∀ j, (q j).IsHomogeneous 2) ∧ matrixPolynomial c H b a = ∑ j, q j ^ 2 := by
  rw [matrixPolynomial_eq] at hF ⊢
  exact polynomial_nonnegative_exists_SOS c hc (matrixBilinear H) (matrixLinear b) a
    (matrixBilinear_symmetric H hH) hF

/-- The exact original sphere hierarchy certifies these actual matrix-form
quartics at order two, with zero multiplier and no dimension loss. -/
theorem matrixPolynomial_nonnegative_feasible_two
    (c : ℝ) (hc : 0 < c) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (b : Fin n → ℝ) (a : ℝ)
    (hF : ∀ x : Fin (n+1) → ℝ, 0 ≤ eval x (matrixPolynomial c H b a)) :
    Foundation.Feasible 2 (matrixPolynomial c H b a) 0 := by
  rw [matrixPolynomial_eq] at hF ⊢
  exact polynomial_nonnegative_feasible_two c hc (matrixBilinear H) (matrixLinear b) a
    (matrixBilinear_symmetric H hH) hF

theorem matrixPolynomial_nonnegative_iff_SOS
    (c : ℝ) (hc : 0 < c) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (b : Fin n → ℝ) (a : ℝ) :
    (∀ x : Fin (n+1) → ℝ, 0 ≤ eval x (matrixPolynomial c H b a)) ↔
      ∃ q : Fin (2+n) → MvPolynomial (Fin (n+1)) ℝ,
        (∀ j, (q j).IsHomogeneous 2) ∧ matrixPolynomial c H b a = ∑ j, q j ^ 2 := by
  constructor
  · exact matrixPolynomial_nonnegative_exists_SOS c hc H hH b a
  · rintro ⟨q, _, hq⟩ x
    rw [hq]
    simp only [map_sum, map_pow]
    exact Finset.sum_nonneg (fun j _ ↦ sq_nonneg _)

end Polynomial

end RadialQuarticSOS
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
