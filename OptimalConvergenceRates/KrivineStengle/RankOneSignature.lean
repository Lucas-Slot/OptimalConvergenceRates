import OptimalConvergenceRates.KrivineStengle.MatrixSignature
import OptimalConvergenceRates.KrivineStengle.OrderedSignCalculus

noncomputable section

open Matrix QuadraticMap

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F]

private def tailDot {k : ℕ} (v : Fin (k + 1) → F) :
    (Fin k → F) →ₗ[F] F where
  toFun x := ∑ j, v j.succ * x j
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

private def linearProdShear {W : Type*} [AddCommGroup W] [Module F W]
    (L : W →ₗ[F] F) : (F × W) ≃ₗ[F] (F × W) where
  toFun z := (z.1 + L z.2, z.2)
  invFun z := (z.1 - L z.2, z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' x y := by ext <;> simp [add_assoc, add_left_comm, add_comm]
  map_smul' c x := by ext <;> simp [mul_add]

private def finZeroSplit (k : ℕ) :
    (Fin (k + 1) → F) ≃ₗ[F] F × (Fin k → F) :=
  LinearEquiv.piCongrLeft F (fun _ : Option (Fin k) ↦ F) (finSuccEquiv k) ≪≫ₗ
    LinearEquiv.piOptionEquivProd F

/-- A coordinate shear whose zero coordinate is the dot product with `v`. -/
def rankOneShear {k : ℕ} (v : Fin (k + 1) → F) :
    (Fin (k + 1) → F) ≃ₗ[F] (Fin (k + 1) → F) :=
  finZeroSplit k ≪≫ₗ linearProdShear (tailDot v) ≪≫ₗ (finZeroSplit k).symm

@[simp]
theorem rankOneShear_apply_zero {k : ℕ} (v : Fin (k + 1) → F)
    (hv : v 0 = 1) (x : Fin (k + 1) → F) :
    rankOneShear v x 0 = ∑ i, v i * x i := by
  rw [show (∑ i, v i * x i) = v 0 * x 0 + ∑ j : Fin k, v j.succ * x j.succ by
    rw [Fin.sum_univ_succ]]
  simp [rankOneShear, finZeroSplit, linearProdShear, tailDot, hv,
    LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft',
    Equiv.piCongrLeft',
    LinearEquiv.piOptionEquivProd, Equiv.piOptionEquivProd]

@[simp]
theorem rankOneShear_apply_succ {k : ℕ} (v : Fin (k + 1) → F)
    (x : Fin (k + 1) → F) (j : Fin k) :
    rankOneShear v x j.succ = x j.succ := by
  simp [rankOneShear, finZeroSplit, linearProdShear, tailDot,
    LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft',
    Equiv.piCongrLeft',
    LinearEquiv.piOptionEquivProd, Equiv.piOptionEquivProd]

variable [LinearOrder F] [IsStrictOrderedRing F]

/-- The symmetric rank-one matrix `c * v vᵀ`, with a normalized first
coordinate, has signature `sign(c)`. -/
theorem matrixSignature_rankOne_succ {k : ℕ} (c : F)
    (v : Fin (k + 1) → F) (hv : v 0 = 1) :
    matrixSignature (fun i j ↦ c * v i * v j) = orderedSign c := by
  let diagonal : Fin (k + 1) → F := fun i ↦ if i = 0 then c else 0
  let M : Matrix (Fin (k + 1)) (Fin (k + 1)) F := fun i j ↦ c * v i * v j
  change matrixSignature M = orderedSign c
  unfold matrixSignature
  calc
    signature (Matrix.toQuadraticForm' M) =
        signature (weightedSumSquares F diagonal) := by
      apply signature_congr (rankOneShear v)
      intro x
      simp only [weightedSumSquares_apply, smul_eq_mul]
      rw [Fin.sum_univ_succ, rankOneShear_apply_zero v hv]
      simp [diagonal]
      simp only [Matrix.toQuadraticForm', Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
        Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec]
      simp only [M]
      let s := ∑ i, v i * x i
      have hrow (i : Fin (k + 1)) :
          (∑ j, c * v i * v j * x j) = c * v i * s := by
        simp only [s]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      simp_rw [hrow]
      calc
        c * ((∑ i, v i * x i) * ∑ i, v i * x i) = c * s * s := by
          simp only [s]
          ring
        _ = (∑ i, x i * (c * v i)) * s := by
          congr 1
          simp only [s]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = ∑ i, x i * (c * v i * s) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = diagonalSignature diagonal := signature_weightedSumSquares diagonal
    _ = orderedSign c := by
      rw [diagonalSignature, Fin.sum_univ_succ]
      simp [diagonal]

end OptimalConvergenceRates.KrivineStengle

end
