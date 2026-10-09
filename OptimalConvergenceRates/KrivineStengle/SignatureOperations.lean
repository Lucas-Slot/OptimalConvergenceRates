import OptimalConvergenceRates.KrivineStengle.SignatureProduct

noncomputable section

open QuadraticMap

namespace OptimalConvergenceRates.KrivineStengle

universe u v w

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {W : Type w} [AddCommGroup W] [Module F W] [FiniteDimensional F W]

theorem isPositiveOn_smul_pos (Q : QuadraticForm F V) (S : Submodule F V)
    {c : F} (hc : 0 < c) :
    IsPositiveOn (c • Q) S ↔ IsPositiveOn Q S := by
  constructor
  · intro h x hx
    have hcx := h x hx
    rcases (mul_pos_iff.mp (by simpa only [smul_apply, smul_eq_mul] using hcx)) with hpos | hneg
    · exact hpos.2
    · exact False.elim ((not_lt_of_ge hc.le) hneg.1)
  · intro h x hx
    simpa only [smul_apply, smul_eq_mul] using mul_pos hc (h x hx)

theorem positiveRanks_smul_pos (Q : QuadraticForm F V) {c : F} (hc : 0 < c) :
    positiveRanks (c • Q) = positiveRanks Q := by
  classical
  ext k
  simp only [positiveRanks, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hk, S, hS, hdim⟩
    exact ⟨hk, S, (isPositiveOn_smul_pos Q S hc).mp hS, hdim⟩
  · rintro ⟨hk, S, hS, hdim⟩
    exact ⟨hk, S, (isPositiveOn_smul_pos Q S hc).mpr hS, hdim⟩

theorem positiveIndex_smul_pos (Q : QuadraticForm F V) {c : F} (hc : 0 < c) :
    positiveIndex (c • Q) = positiveIndex Q := by
  apply le_antisymm
  · obtain ⟨S, hS, hdim⟩ :=
      exists_positiveSubspace_finrank_eq_positiveIndex (c • Q)
    rw [← hdim]
    exact finrank_le_positiveIndex Q S ((isPositiveOn_smul_pos Q S hc).mp hS)
  · obtain ⟨S, hS, hdim⟩ :=
      exists_positiveSubspace_finrank_eq_positiveIndex Q
    rw [← hdim]
    exact finrank_le_positiveIndex (c • Q) S ((isPositiveOn_smul_pos Q S hc).mpr hS)
theorem negativeIndex_smul_pos (Q : QuadraticForm F V) {c : F} (hc : 0 < c) :
    negativeIndex (c • Q) = negativeIndex Q := by
  rw [negativeIndex, negativeIndex]
  have hneg : -(c • Q) = c • (-Q) := by
    ext x
    simp
  rw [hneg, positiveIndex_smul_pos (-Q) hc]

theorem signature_smul_pos (Q : QuadraticForm F V) {c : F} (hc : 0 < c) :
    signature (c • Q) = signature Q := by
  simp only [signature, positiveIndex_smul_pos Q hc, negativeIndex_smul_pos Q hc]

theorem positiveIndex_zero :
    positiveIndex (0 : QuadraticForm F V) = 0 := by
  obtain ⟨S, hS, hdim⟩ :=
    exists_positiveSubspace_finrank_eq_positiveIndex (0 : QuadraticForm F V)
  have hSbot : S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    by_contra hx0
    have hx0' : (⟨x, hx⟩ : S) ≠ 0 := by
      intro h
      apply hx0
      exact congrArg Subtype.val h
    have := hS ⟨x, hx⟩ hx0'
    simp at this
  rw [hSbot] at hdim
  simpa using hdim.symm

theorem signature_zero : signature (0 : QuadraticForm F V) = 0 := by
  simp [signature, negativeIndex, positiveIndex_zero]

/-- A chosen linear splitting identifies a vector space with the target of a
surjection times its kernel. -/
noncomputable def linearEquivProdKerOfRightInverse
    (L : V →ₗ[F] W) (s : W →ₗ[F] V)
    (hs : L.comp s = LinearMap.id) : V ≃ₗ[F] W × LinearMap.ker L where
  toFun x :=
    (L x, ⟨x - s (L x), by
      change L (x - s (L x)) = 0
      rw [map_sub]
      have hright : L (s (L x)) = L x := LinearMap.congr_fun hs (L x)
      rw [hright, sub_self]⟩)
  invFun y := s y.1 + y.2.1
  left_inv x := by
    simp
  right_inv y := by
    apply Prod.ext
    · change L (s y.1 + y.2.1) = y.1
      rw [map_add]
      have hright : L (s y.1) = y.1 := LinearMap.congr_fun hs y.1
      rw [hright, y.2.2, add_zero]
    · apply Subtype.ext
      change s y.1 + y.2.1 - s (L (s y.1 + y.2.1)) = y.2.1
      have hright : L (s y.1) = y.1 := LinearMap.congr_fun hs y.1
      have hker : L y.2.1 = 0 := y.2.2
      simp only [map_add, hright, hker, add_zero]
      abel
  map_add' x y := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      change x + y - s (L (x + y)) = (x - s (L x)) + (y - s (L y))
      simp only [map_add]
      abel
  map_smul' c x := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      change c • x - s (L (c • x)) = c • (x - s (L x))
      simp only [map_smul, smul_sub]

theorem signature_comp_surjective (Q : QuadraticForm F W) (L : V →ₗ[F] W)
    (hL : Function.Surjective L) :
    signature (Q.comp L) = signature Q := by
  obtain ⟨s, hs⟩ := L.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hL)
  let e := linearEquivProdKerOfRightInverse L s hs
  have hform (x : V) : (Q.prod (0 : QuadraticForm F (LinearMap.ker L))) (e x) =
      (Q.comp L) x := by
    simp [e, linearEquivProdKerOfRightInverse]
  calc
    signature (Q.comp L) =
        signature (Q.prod (0 : QuadraticForm F (LinearMap.ker L))) :=
      signature_congr e hform
    _ = signature Q + signature (0 : QuadraticForm F (LinearMap.ker L)) :=
      signature_prod Q 0
    _ = signature Q := by rw [signature_zero, add_zero]

end OptimalConvergenceRates.KrivineStengle

end
