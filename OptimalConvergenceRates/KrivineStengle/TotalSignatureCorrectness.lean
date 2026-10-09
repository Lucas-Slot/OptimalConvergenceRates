/-
  OptimalConvergenceRates/KrivineStengle/TotalSignatureCorrectness.lean

  Semantic correctness and totality of the guarded matrix-signature formula.
-/
import OptimalConvergenceRates.KrivineStengle.TotalSignatureFormula

noncomputable section

open Matrix MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

theorem matrixSignature_zero {d : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] : matrixSignature (0 : Matrix (Fin d) (Fin d) F) = 0 := by
  have hdiag : (0 : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal (fun _ : Fin d ↦ (0 : F)) := by
    ext i j
    simp
  rw [hdiag, matrixSignature_diagonal]
  simp [diagonalSignature]

/-- The total formula realizes exactly the requested signature. Unlike the
leading-pivot formula, there is no side condition: the finite transvection
family supplies a nonzero pivot whenever the symmetric matrix is nonzero. -/
theorem realizes_totalMatrixSignatureFormula_iff
    {n d : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (M : Matrix (Fin d) (Fin d) (GuardedRational n)) (s : ℤ)
    (hvalid : GuardedMatrixValid coeff x M)
    (hsymm : (evalGuardedMatrix coeff x M).IsSymm) :
    (totalMatrixSignatureFormula d M s).Realizes coeff x ↔
      matrixSignature (evalGuardedMatrix coeff x M) = s := by
  induction d generalizing s with
  | zero =>
      rw [matrixSignature_fin_zero]
      by_cases hs : s = 0
      · simp [totalMatrixSignatureFormula, hs]
      · have hs' : (0 : ℤ) ≠ s := fun h ↦ hs h.symm
        simp [totalMatrixSignatureFormula, hs, hs']
  | succ k ih =>
      simp only [totalMatrixSignatureFormula, SignFormula.realizes_disj,
        SignFormula.realizes_conj]
      constructor
      · intro h
        rcases h with ⟨hzero, hstatus⟩ | hpivots
        · have hzero' :=
            (realizes_guardedMatrixZeroFormula_iff coeff x M).1 hzero
          have hsigzero : matrixSignature (evalGuardedMatrix coeff x M) = 0 := by
            rw [hzero'.2]
            exact matrixSignature_zero
          have hs : s = 0 := by
            by_cases hs : s = 0
            · exact hs
            · simp [hs] at hstatus
          simpa [hs] using hsigzero
        · rw [SignFormula.realizes_any] at hpivots
          obtain ⟨row, hrow, hrowRealizes⟩ := hpivots
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
          rw [SignFormula.realizes_any] at hrowRealizes
          obtain ⟨branch, hbranch, hbranchRealizes⟩ := hrowRealizes
          obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hbranch
          let N := guardedPivotMatrix (i, j) M
          change (guardedPivotSignatureBranch (totalMatrixSignatureFormula k)
            N s).Realizes coeff x at hbranchRealizes
          simp only [guardedPivotSignatureBranch, SignFormula.realizes_conj,
            SignFormula.realizes_disj] at hbranchRealizes
          have hvalidN : GuardedMatrixValid coeff x N :=
            guardedPivotMatrix_valid coeff x (i, j) hvalid
          have hsymmN : N.IsSymm := guardedPivotMatrix_isSymm (i, j) M
          have hpreserve :
              matrixSignature (evalGuardedMatrix coeff x N) =
                matrixSignature (evalGuardedMatrix coeff x M) := by
            dsimp [N]
            exact matrixSignature_eval_guardedPivotMatrix
              coeff x (i, j) hvalid hsymm
          rcases hbranchRealizes with
            ⟨_, (⟨hpos, hrec⟩ | ⟨hneg, hrec⟩)⟩
          · have hp : 0 < (N 0 0).eval coeff x :=
              (GuardedRational.realizes_positiveFormula_iff coeff x (N 0 0)).1 hpos
            have hpne : (N 0 0).eval coeff x ≠ 0 := ne_of_gt hp
            have hvalidS := guardedMatrixSchurComplement_valid coeff x hvalidN hpne
            have hsymmSraw := guardedMatrixSchurComplement_isSymm hsymmN
            have hsymmS := eval_guardedMatrix_isSymm coeff x hsymmSraw
            have hrec' := (ih (guardedMatrixSchurComplement N) (s - 1)
              hvalidS hsymmS).1 hrec
            have hsplit := matrixSignature_eval_eq_orderedSign_add_guardedSchur
              coeff x hvalidN hsymmN hpne
            rw [orderedSign_eq_one_iff.mpr hp, hrec'] at hsplit
            omega
          · have hnpos : 0 < ((N 0 0).neg).eval coeff x :=
              (GuardedRational.realizes_positiveFormula_iff coeff x
                ((N 0 0).neg)).1 hneg
            rw [GuardedRational.eval_neg] at hnpos
            have hp : (N 0 0).eval coeff x < 0 := neg_pos.mp hnpos
            have hpne : (N 0 0).eval coeff x ≠ 0 := ne_of_lt hp
            have hvalidS := guardedMatrixSchurComplement_valid coeff x hvalidN hpne
            have hsymmSraw := guardedMatrixSchurComplement_isSymm hsymmN
            have hsymmS := eval_guardedMatrix_isSymm coeff x hsymmSraw
            have hrec' := (ih (guardedMatrixSchurComplement N) (s + 1)
              hvalidS hsymmS).1 hrec
            have hsplit := matrixSignature_eval_eq_orderedSign_add_guardedSchur
              coeff x hvalidN hsymmN hpne
            rw [orderedSign_eq_neg_one_iff.mpr hp, hrec'] at hsplit
            omega
      · intro hsignature
        by_cases hzero : evalGuardedMatrix coeff x M = 0
        · apply Or.inl
          refine ⟨(realizes_guardedMatrixZeroFormula_iff coeff x M).2
            ⟨hvalid, hzero⟩, ?_⟩
          have hs : s = 0 := by
            have hz : matrixSignature (evalGuardedMatrix coeff x M) = 0 := by
              rw [hzero]
              exact matrixSignature_zero
            omega
          simp [hs]
        · apply Or.inr
          obtain ⟨⟨i, j⟩, hpivot⟩ :=
            exists_guardedPivotMatrix_eval_zero_zero_ne_zero
              coeff x hvalid hsymm hzero
          apply (SignFormula.realizes_any coeff x _).2
          refine ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
          apply (SignFormula.realizes_any coeff x _).2
          refine ⟨_, List.mem_ofFn.mpr ⟨j, rfl⟩, ?_⟩
          let N := guardedPivotMatrix (i, j) M
          change (guardedPivotSignatureBranch (totalMatrixSignatureFormula k)
            N s).Realizes coeff x
          simp only [guardedPivotSignatureBranch, SignFormula.realizes_conj,
            SignFormula.realizes_disj]
          have hvalidN : GuardedMatrixValid coeff x N :=
            guardedPivotMatrix_valid coeff x (i, j) hvalid
          have hsymmN : N.IsSymm := guardedPivotMatrix_isSymm (i, j) M
          have hguard : (N 0 0).guardFormula.Realizes coeff x :=
            (GuardedRational.realizes_guardFormula coeff x (N 0 0)).2
              (hvalidN 0 0)
          have hpreserve :
              matrixSignature (evalGuardedMatrix coeff x N) =
                matrixSignature (evalGuardedMatrix coeff x M) := by
            dsimp [N]
            exact matrixSignature_eval_guardedPivotMatrix
              coeff x (i, j) hvalid hsymm
          change (N 0 0).eval coeff x ≠ 0 at hpivot
          rcases lt_or_gt_of_ne hpivot.symm with hp | hp
          · refine ⟨hguard, Or.inl ⟨
              (GuardedRational.realizes_positiveFormula_iff coeff x (N 0 0)).2 hp,
              ?_⟩⟩
            have hvalidS := guardedMatrixSchurComplement_valid coeff x hvalidN
              (ne_of_gt hp)
            have hsymmSraw := guardedMatrixSchurComplement_isSymm hsymmN
            have hsymmS := eval_guardedMatrix_isSymm coeff x hsymmSraw
            apply (ih (guardedMatrixSchurComplement N) (s - 1)
              hvalidS hsymmS).2
            have hsplit := matrixSignature_eval_eq_orderedSign_add_guardedSchur
              coeff x hvalidN hsymmN (ne_of_gt hp)
            rw [orderedSign_eq_one_iff.mpr hp] at hsplit
            omega
          · refine ⟨hguard, Or.inr ⟨?_, ?_⟩⟩
            · apply (GuardedRational.realizes_positiveFormula_iff coeff x
                ((N 0 0).neg)).2
              rw [GuardedRational.eval_neg]
              exact neg_pos.mpr hp
            · have hvalidS := guardedMatrixSchurComplement_valid coeff x hvalidN
                (ne_of_lt hp)
              have hsymmSraw := guardedMatrixSchurComplement_isSymm hsymmN
              have hsymmS := eval_guardedMatrix_isSymm coeff x hsymmSraw
              apply (ih (guardedMatrixSchurComplement N) (s + 1)
                hvalidS hsymmS).2
              have hsplit := matrixSignature_eval_eq_orderedSign_add_guardedSchur
                coeff x hvalidN hsymmN (ne_of_lt hp)
              rw [orderedSign_eq_neg_one_iff.mpr hp] at hsplit
              omega

end OptimalConvergenceRates.KrivineStengle

end
