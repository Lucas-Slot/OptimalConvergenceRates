import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic
/-! Elementary tensor stability of real matrix `2 → 4` domination.

The statements use finite sums only. They permit arbitrary finite index
sets, including empty ones, and actual matrix inputs rather than product
vectors. No assertion about tensor nuclear norms is used.
-/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace QuarticTensorAmplification

open scoped BigOperators Matrix Kronecker

variable {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]

/-- The fourth-power form of an actual matrix is bounded by the squared
Euclidean radius of its input. -/
def FourthBound (A : α → ι → ℝ) : Prop :=
  ∀ x : ι → ℝ, (∑ j, (∑ i, A j i * x i)^4) ≤ (∑ i, x i^2)^2

omit [Fintype κ] in
/-- Squared Cauchy--Schwarz, with the two column fourth moments bounded by
actual matrix domination. -/
theorem column_cross_bound (A : α → ι → ℝ) (hA : FourthBound A)
    (X : ι → κ → ℝ) (l r : κ) :
    (∑ j, (∑ i, A j i * X i l)^2 * (∑ i, A j i * X i r)^2) ≤
      (∑ i, X i l^2) * (∑ i, X i r^2) := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j ↦ (∑ i, A j i * X i l)^2)
    (fun j ↦ (∑ i, A j i * X i r)^2)
  have hAl := hA (fun i ↦ X i l)
  have hAr := hA (fun i ↦ X i r)
  have hprod := mul_le_mul hAl hAr
    (by positivity : 0 ≤ ∑ j, (∑ i, A j i * X i r)^4)
    (sq_nonneg (∑ i, X i l^2))
  have hsq :
      (∑ j, (∑ i, A j i * X i l)^2 * (∑ i, A j i * X i r)^2)^2 ≤
        ((∑ i, X i l^2) * (∑ i, X i r^2))^2 := by
    simp only [← pow_mul] at hcs
    nlinarith only [hcs, hprod]
  have hleft : 0 ≤
      ∑ j, (∑ i, A j i * X i l)^2 * (∑ i, A j i * X i r)^2 := by
    positivity
  have hright : 0 ≤ (∑ i, X i l^2) * (∑ i, X i r^2) := by positivity
  exact (sq_le_sq₀ hleft hright).mp hsq

/-- The finite-sum mixed-norm argument for `Y = A X Bᵀ`.
This is valid for every matrix `X`, with no product-input restriction. -/
theorem matrix_fourth_bound (A : α → ι → ℝ) (B : β → κ → ℝ)
    (hA : FourthBound A) (hB : FourthBound B) (X : ι → κ → ℝ) :
    (∑ j, ∑ k, (∑ l, B k l * (∑ i, A j i * X i l))^4) ≤
      (∑ i, ∑ l, X i l^2)^2 := by
  classical
  calc
    _ ≤ ∑ j, (∑ l, (∑ i, A j i * X i l)^2)^2 := by
      apply Finset.sum_le_sum
      intro j _
      exact hB (fun l ↦ ∑ i, A j i * X i l)
    _ = ∑ j, ∑ l, ∑ r,
        (∑ i, A j i * X i l)^2 * (∑ i, A j i * X i r)^2 := by
      simp only [pow_two, Fintype.sum_mul_sum]
    _ = ∑ l, ∑ r, ∑ j,
        (∑ i, A j i * X i l)^2 * (∑ i, A j i * X i r)^2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm
    _ ≤ ∑ l, ∑ r, (∑ i, X i l^2) * (∑ i, X i r^2) := by
      apply Finset.sum_le_sum
      intro l _
      apply Finset.sum_le_sum
      intro r _
      exact column_cross_bound A hA X l r
    _ = (∑ l, ∑ i, X i l^2)^2 := by
      rw [pow_two, Fintype.sum_mul_sum]
    _ = _ := by rw [Finset.sum_comm]

/-- The ordinary entrywise Kronecker matrix. -/
def tensorMatrix (A : α → ι → ℝ) (B : β → κ → ℝ) :
    Matrix (α × β) (ι × κ) ℝ :=
  fun jk il ↦ A jk.1 il.1 * B jk.2 il.2

/-- Fourth-power domination is closed under the actual Kronecker product. -/
theorem tensorMatrix_fourthBound (A : α → ι → ℝ) (B : β → κ → ℝ)
    (hA : FourthBound A) (hB : FourthBound B) :
    FourthBound (tensorMatrix A B) := by
  classical
  intro x
  have h := matrix_fourth_bound A B hA hB (fun i l ↦ x (i, l))
  convert h using 1
  · simp only [tensorMatrix, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp only [Fintype.sum_prod_type]

/-- The actual product input vector. -/
def tensorVector (v : ι → ℝ) (w : κ → ℝ) : ι × κ → ℝ :=
  fun il ↦ v il.1 * w il.2

/-- Squared Euclidean radii factor at actual product input vectors. -/
theorem tensorVector_radius (v : ι → ℝ) (w : κ → ℝ) :
    (∑ il, tensorVector v w il ^ 2) = (∑ i, v i ^ 2) * ∑ l, w l ^ 2 := by
  classical
  simp only [tensorVector, Fintype.sum_prod_type, mul_pow, Fintype.sum_mul_sum]

omit [Fintype α] [Fintype β] in
/-- Ordinary matrix application factors on an actual product vector. -/
theorem tensorMatrix_mulVec_tensorVector (A : α → ι → ℝ) (B : β → κ → ℝ)
    (v : ι → ℝ) (w : κ → ℝ) :
    tensorMatrix A B *ᵥ tensorVector v w = tensorVector (A *ᵥ v) (B *ᵥ w) := by
  classical
  funext jk
  simp only [Matrix.mulVec, dotProduct, tensorMatrix, tensorVector,
    Fintype.sum_prod_type, Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Exact objective factorization, useful for preserving an attained maximum. -/
theorem tensorMatrix_fourth_tensorVector (A : α → ι → ℝ) (B : β → κ → ℝ)
    (v : ι → ℝ) (w : κ → ℝ) :
    (∑ jk, ((tensorMatrix A B *ᵥ tensorVector v w) jk)^4) =
      (∑ j, ((A *ᵥ v) j)^4) * ∑ k, ((B *ᵥ w) k)^4 := by
  classical
  rw [tensorMatrix_mulVec_tensorVector]
  simp only [tensorVector, Fintype.sum_prod_type, mul_pow, Fintype.sum_mul_sum]

/-- An ordinary Kronecker product of real PSD matrices is PSD. -/
theorem tensorMatrix_posSemidef (M : Matrix ι ι ℝ) (N : Matrix κ κ ℝ)
    (hM : M.PosSemidef) (hN : N.PosSemidef) :
    Matrix.PosSemidef (tensorMatrix M N) := by
  classical
  exact hM.kronecker hN

/-- Fourth homogeneous moments, indexed by their four variable slots. -/
abbrev FourthMoment (ι : Type*) := ι → ι → ι → ι → ℝ

/-- Quadratic-square Gram matrix of a fourth moment tensor. -/
def momentGram (M : FourthMoment ι) : Matrix (ι × ι) (ι × ι) ℝ :=
  fun ij kl ↦ M ij.1 ij.2 kl.1 kl.2

/-- Product moments on the actual tensor-coordinate space. -/
def tensorMoment (M : FourthMoment ι) (N : FourthMoment κ) :
    FourthMoment (ι × κ) :=
  fun i j k l ↦ M i.1 j.1 k.1 l.1 * N i.2 j.2 k.2 l.2

/-- All global permutations of the four variable slots preserve a moment. -/
def FullSymmetricMoment (M : FourthMoment ι) : Prop :=
  ∀ (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → ι),
    M (v 0) (v 1) (v 2) (v 3) =
      M (v (σ 0)) (v (σ 1)) (v (σ 2)) (v (σ 3))

omit [Fintype ι] [Fintype κ] in
/-- Product moments remain fully symmetric in the four ambient slots. -/
theorem tensorMoment_fullSymmetric (M : FourthMoment ι) (N : FourthMoment κ)
    (hM : FullSymmetricMoment M) (hN : FullSymmetricMoment N) :
    FullSymmetricMoment (tensorMoment M N) := by
  intro σ v
  dsimp only [tensorMoment]
  rw [hM σ (fun i ↦ (v i).1), hN σ (fun i ↦ (v i).2)]

/-- Product moment Gram positivity includes arbitrary quadratic roots on
the tensor-coordinate space, not just products of roots. -/
theorem tensorMoment_gram_posSemidef (M : FourthMoment ι) (N : FourthMoment κ)
    (hM : (momentGram M).PosSemidef) (hN : (momentGram N).PosSemidef) :
    (momentGram (tensorMoment M N)).PosSemidef := by
  have h := tensorMatrix_posSemidef (momentGram M) (momentGram N) hM hN
  simpa only [momentGram, tensorMoment, tensorMatrix, Matrix.submatrix] using!
    h.submatrix (fun ij : (ι × κ) × (ι × κ) ↦
      ((ij.1.1, ij.2.1), (ij.1.2, ij.2.2)))

/-- Evaluation of the square of the Euclidean radius by fourth moments. -/
def momentRadius (M : FourthMoment ι) : ℝ := ∑ i, ∑ j, M i i j j

/-- The radius-four normalization factors exactly under tensor products. -/
theorem tensorMoment_radius (M : FourthMoment ι) (N : FourthMoment κ) :
    momentRadius (tensorMoment M N) = momentRadius M * momentRadius N := by
  classical
  simp only [momentRadius, tensorMoment, Fintype.sum_prod_type]
  calc
    _ = ∑ i, ∑ j, ∑ k, ∑ l, M i i j j * N k k l l := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by simp_rw [Finset.sum_mul, Finset.mul_sum]

/-- Evaluation of one linear fourth power by homogeneous fourth moments. -/
def rowFourthMoment (M : FourthMoment ι) (a : ι → ℝ) : ℝ :=
  ∑ v : Fin 4 → ι, M (v 0) (v 1) (v 2) (v 3) * ∏ s, a (v s)

/-- Both the fourth moments and the actual linear row tensorize. -/
theorem tensorMoment_rowFourth (M : FourthMoment ι) (N : FourthMoment κ)
    (a : ι → ℝ) (b : κ → ℝ) :
    rowFourthMoment (tensorMoment M N) (fun ik ↦ a ik.1 * b ik.2) =
      rowFourthMoment M a * rowFourthMoment N b := by
  classical
  let f : (Fin 4 → ι) → ℝ :=
    fun v ↦ M (v 0) (v 1) (v 2) (v 3) * ∏ s, a (v s)
  let g : (Fin 4 → κ) → ℝ :=
    fun v ↦ N (v 0) (v 1) (v 2) (v 3) * ∏ s, b (v s)
  calc
    _ = ∑ p : (Fin 4 → ι) × (Fin 4 → κ), f p.1 * g p.2 := by
      apply Fintype.sum_equiv
        (Equiv.arrowProdEquivProdArrow (Fin 4) (fun _ ↦ ι) (fun _ ↦ κ))
      intro v
      change
        M (v 0).1 (v 1).1 (v 2).1 (v 3).1 *
            N (v 0).2 (v 1).2 (v 2).2 (v 3).2 *
            (∏ s, a (v s).1 * b (v s).2) =
          (M (v 0).1 (v 1).1 (v 2).1 (v 3).1 * ∏ s, a (v s).1) *
            (N (v 0).2 (v 1).2 (v 2).2 (v 3).2 * ∏ s, b (v s).2)
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := by
      rw [Fintype.sum_prod_type]
      change (∑ v, ∑ w, f v * g w) = (∑ v, f v) * ∑ w, g w
      rw [Fintype.sum_mul_sum]

/-- Moment value of the sum of the actual row fourth powers of a matrix. -/
def matrixFourthMoment (M : FourthMoment ι) (A : α → ι → ℝ) : ℝ :=
  ∑ j, rowFourthMoment M (A j)

/-- The complete fourth-power objective value factors under tensorization. -/
theorem tensorMoment_matrixFourth (M : FourthMoment ι) (N : FourthMoment κ)
    (A : α → ι → ℝ) (B : β → κ → ℝ) :
    matrixFourthMoment (tensorMoment M N) (tensorMatrix A B) =
      matrixFourthMoment M A * matrixFourthMoment N B := by
  classical
  unfold matrixFourthMoment
  rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  exact tensorMoment_rowFourth M N (A j) (B k)

universe u

/-- Nested product coordinates for an iterated actual tensor product. -/
def TensorIndex (ι : Type u) : ℕ → Type u
  | 0 => PUnit
  | t + 1 => ι × TensorIndex ι t

instance tensorIndexFintype (ι : Type*) [Fintype ι] (t : ℕ) :
    Fintype (TensorIndex ι t) := by
  induction t with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ t ih =>
      letI := ih
      exact inferInstanceAs (Fintype (ι × TensorIndex ι t))

instance tensorIndexZeroUnique (ι : Type*) : Unique (TensorIndex ι 0) :=
  inferInstanceAs (Unique PUnit)

/-- The tensor input dimension is the actual cardinality power. -/
theorem tensorIndex_card (t : ℕ) :
    Fintype.card (TensorIndex ι t) = Fintype.card ι ^ t := by
  induction t with
  | zero => simpa only [pow_zero] using Fintype.card_unique (α := TensorIndex ι 0)
  | succ t ih =>
      calc
        Fintype.card (TensorIndex ι (t+1)) =
            Fintype.card (ι × TensorIndex ι t) := Fintype.card_congr (Equiv.refl _)
        _ = Fintype.card ι ^ (t+1) := by rw [Fintype.card_prod, ih, pow_succ]; ring

/-- Iterated Kronecker matrices, with the scalar identity at order zero. -/
def matrixPower (A : α → ι → ℝ) :
    (t : ℕ) → Matrix (TensorIndex α t) (TensorIndex ι t) ℝ
  | 0 => fun _ _ ↦ 1
  | t + 1 => tensorMatrix A (fun j i ↦ matrixPower A t j i)

/-- Iterated homogeneous fourth moments. -/
def momentPower (M : FourthMoment ι) :
    (t : ℕ) → FourthMoment (TensorIndex ι t)
  | 0 => fun _ _ _ _ ↦ 1
  | t + 1 => tensorMoment M (momentPower M t)

/-- Tensor domination iterates over all actual inputs in the growing space. -/
theorem matrixPower_fourthBound (A : α → ι → ℝ) (hA : FourthBound A) (t : ℕ) :
    FourthBound (matrixPower A t) := by
  classical
  induction t with
  | zero =>
      intro x
      simp only [matrixPower, Fintype.sum_unique, one_mul]
      nlinarith
  | succ t ih => exact tensorMatrix_fourthBound A (matrixPower A t) hA ih

omit [Fintype ι] in
/-- Full moment symmetry iterates in the four GLOBAL slots. -/
theorem momentPower_fullSymmetric (M : FourthMoment ι)
    (hM : FullSymmetricMoment M) (t : ℕ) :
    FullSymmetricMoment (momentPower M t) := by
  induction t with
  | zero => intro σ v; rfl
  | succ t ih => exact tensorMoment_fullSymmetric M (momentPower M t) hM ih

/-- Every iterated quadratic moment Gram matrix is genuinely PSD. -/
theorem momentPower_gram_posSemidef (M : FourthMoment ι)
    (hM : (momentGram M).PosSemidef) (t : ℕ) :
    (momentGram (momentPower M t)).PosSemidef := by
  classical
  induction t with
  | zero =>
      have heq : momentGram (momentPower M 0) = 1 := by
        ext ij kl
        have hsub : ij = kl := @Subsingleton.elim (PUnit × PUnit) inferInstance ij kl
        simp [momentGram, momentPower, Matrix.one_apply, hsub]
      rw [heq]
      exact Matrix.PosSemidef.one
  | succ t ih => exact tensorMoment_gram_posSemidef M (momentPower M t) hM ih

/-- The fourth-radius moment of a tensor power factors exactly. -/
theorem momentPower_radius (M : FourthMoment ι) (t : ℕ) :
    momentRadius (momentPower M t) = momentRadius M ^ t := by
  classical
  induction t with
  | zero => simp [momentRadius, momentPower]
  | succ t ih =>
      change momentRadius (tensorMoment M (momentPower M t)) = _
      rw [tensorMoment_radius, ih, pow_succ]
      ring

/-- The objective fourth moment amplifies to the exact cardinality power. -/
theorem momentPower_matrixFourth (M : FourthMoment ι) (A : α → ι → ℝ) (t : ℕ) :
    matrixFourthMoment (momentPower M t) (matrixPower A t) =
      matrixFourthMoment M A ^ t := by
  classical
  induction t with
  | zero => simp [matrixFourthMoment, rowFourthMoment, momentPower, matrixPower]
  | succ t ih =>
      change matrixFourthMoment (tensorMoment M (momentPower M t))
        (tensorMatrix A (fun j i ↦ matrixPower A t j i)) = _
      rw [tensorMoment_matrixFourth, ih, pow_succ]
      ring

end QuarticTensorAmplification
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
