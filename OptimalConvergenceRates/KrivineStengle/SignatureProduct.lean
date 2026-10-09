import OptimalConvergenceRates.KrivineStengle.SignatureInvariant
import Mathlib.LinearAlgebra.QuadraticForm.Prod

noncomputable section

open QuadraticMap

namespace OptimalConvergenceRates.KrivineStengle

universe u v w

variable {F : Type u} [Field F]

/-- Concatenate two coordinate vectors. -/
noncomputable def finFunProdEquiv {m n : ℕ} :
    ((Fin m → F) × (Fin n → F)) ≃ₗ[F] (Fin (m + n) → F) :=
  (LinearEquiv.sumPiEquivProdPi F (Fin m) (Fin n) (fun _ ↦ F)).symm.trans
    (LinearEquiv.piCongrLeft F (fun _ : Fin (m + n) ↦ F) finSumFinEquiv)

@[simp] theorem finFunProdEquiv_apply_castAdd {m n : ℕ}
    (x : (Fin m → F) × (Fin n → F)) (i : Fin m) :
    finFunProdEquiv (F := F) x (Fin.castAdd n i) = x.1 i := by
  change Equiv.piCongrLeft (fun _ : Fin (m + n) ↦ F) finSumFinEquiv
      (Equiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n ↦ F) |>.symm x)
      (finSumFinEquiv (Sum.inl i)) = x.1 i
  exact Equiv.piCongrLeft_sumInl _ _ _ _ _

@[simp] theorem finFunProdEquiv_apply_natAdd {m n : ℕ}
    (x : (Fin m → F) × (Fin n → F)) (j : Fin n) :
    finFunProdEquiv (F := F) x (Fin.natAdd m j) = x.2 j := by
  change Equiv.piCongrLeft (fun _ : Fin (m + n) ↦ F) finSumFinEquiv
      (Equiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n ↦ F) |>.symm x)
      (finSumFinEquiv (Sum.inr j)) = x.2 j
  exact Equiv.piCongrLeft_sumInr _ _ _ _ _

/-- Concatenating coordinate vectors carries the orthogonal product of diagonal
forms to the diagonal form with concatenated coefficients. -/
theorem weightedSumSquares_prod {m n : ℕ} (left : Fin m → F)
    (right : Fin n → F) (x : (Fin m → F) × (Fin n → F)) :
    weightedSumSquares F (Sum.elim left right ∘ finSumFinEquiv.symm)
        (finFunProdEquiv (F := F) x) =
      ((weightedSumSquares F left).prod (weightedSumSquares F right)) x := by
  rw [QuadraticMap.prod_apply]
  simp only [weightedSumSquares_apply, smul_eq_mul]
  let term : Fin (m + n) → F := fun i ↦
    (Sum.elim left right ∘ finSumFinEquiv.symm) i *
      (finFunProdEquiv (F := F) x i * finFunProdEquiv (F := F) x i)
  change (∑ i, term i) = _
  calc
    _ = ∑ s : Fin m ⊕ Fin n, term (finSumFinEquiv s) :=
      (Equiv.sum_comp finSumFinEquiv term).symm
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp [term]

variable [LinearOrder F] [IsStrictOrderedRing F]

/-- Signature is additive under orthogonal products of finite-dimensional
quadratic forms. -/
theorem signature_prod
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (QV : QuadraticForm F V) (QW : QuadraticForm F W) :
    signature (QV.prod QW) = signature QV + signature QW := by
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨left, ⟨eLeft⟩⟩ := QV.equivalent_weightedSumSquares
  obtain ⟨right, ⟨eRight⟩⟩ := QW.equivalent_weightedSumSquares
  let appended := Sum.elim left right ∘ finSumFinEquiv.symm
  let eProd := eLeft.prod eRight
  calc
    signature (QV.prod QW) =
        signature ((weightedSumSquares F left).prod
          (weightedSumSquares F right)) :=
      signature_congr eProd.toLinearEquiv eProd.map_app
    _ = signature (weightedSumSquares F appended) :=
      signature_congr (finFunProdEquiv (F := F)) (weightedSumSquares_prod left right)
    _ = diagonalSignature appended := signature_weightedSumSquares appended
    _ = diagonalSignature left + diagonalSignature right :=
      diagonalSignature_append left right
    _ = signature (weightedSumSquares F left) +
        signature (weightedSumSquares F right) := by
      rw [signature_weightedSumSquares, signature_weightedSumSquares]
    _ = signature QV + signature QW := by
      rw [signature_congr eLeft.toLinearEquiv eLeft.map_app,
        signature_congr eRight.toLinearEquiv eRight.map_app]

end OptimalConvergenceRates.KrivineStengle

end
