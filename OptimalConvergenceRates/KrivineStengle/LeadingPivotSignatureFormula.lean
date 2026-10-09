/-
  OptimalConvergenceRates/KrivineStengle/LeadingPivotSignatureFormula.lean

  A guarded sign formula for the branch on which recursive leading
  Schur-complement pivots are all nonzero.
-/
import OptimalConvergenceRates.KrivineStengle.GuardedSchurComplement

noncomputable section

open Matrix MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- The always-true polynomial sign formula. -/
def trueSignFormula (n : ℕ) : SignFormula n := .positive 1

/-- The always-false polynomial sign formula. -/
def falseSignFormula (n : ℕ) : SignFormula n := .eqZero 1

@[simp] theorem realizes_trueSignFormula {n : ℕ} {F : Type*}
    [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (x : Fin n → F) :
    (trueSignFormula n).Realizes coeff x := by
  simp [trueSignFormula]

@[simp] theorem not_realizes_falseSignFormula {n : ℕ} {F : Type*}
    [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (x : Fin n → F) :
    ¬(falseSignFormula n).Realizes coeff x := by
  simp [falseSignFormula]

/-- The semantic condition defining the recursive branch on which every
leading Schur-complement pivot is nonzero. -/
def LeadingPivotCondition {n : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F) :
    (d : ℕ) → Matrix (Fin d) (Fin d) (GuardedRational n) → Prop
  | 0, _ => True
  | k + 1, M =>
      (M 0 0).eval coeff x ≠ 0 ∧
        LeadingPivotCondition coeff x k (guardedMatrixSchurComplement M)

/-- On the branch where every leading pivot is nonzero, recursively split
off its sign and ask that the residual signature have the corresponding
integer value. Every division is accompanied by its polynomial guard. -/
def leadingPivotSignatureFormula {n : ℕ} :
    (d : ℕ) → Matrix (Fin d) (Fin d) (GuardedRational n) → ℤ → SignFormula n
  | 0, _, s => if s = 0 then trueSignFormula n else falseSignFormula n
  | k + 1, M, s =>
      .conj (M 0 0).guardFormula
        (.disj
          (.conj (M 0 0).positiveFormula
            (leadingPivotSignatureFormula k (guardedMatrixSchurComplement M) (s - 1)))
          (.conj ((M 0 0).neg).positiveFormula
            (leadingPivotSignatureFormula k (guardedMatrixSchurComplement M) (s + 1))))

theorem matrixSignature_fin_zero {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (M : Matrix (Fin 0) (Fin 0) F) :
    matrixSignature M = 0 := by
  have hM : M = Matrix.diagonal (fun _ : Fin 0 ↦ (0 : F)) := by
    ext i
    exact Fin.elim0 i
  rw [hM, matrixSignature_diagonal]
  simp [diagonalSignature]

end OptimalConvergenceRates.KrivineStengle

end

noncomputable section

open Matrix MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- Correctness of the recursive leading-pivot formula. The hypotheses say
that the input guarded matrix is already valid at the specialization and is
symbolically symmetric. The formula then records exactly the nonzero-pivot
branch condition and the resulting matrix signature. -/
theorem realizes_leadingPivotSignatureFormula_iff
    {n d : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (M : Matrix (Fin d) (Fin d) (GuardedRational n)) (s : ℤ)
    (hvalid : GuardedMatrixValid coeff x M) (hM : M.IsSymm) :
    (leadingPivotSignatureFormula d M s).Realizes coeff x ↔
      LeadingPivotCondition coeff x d M ∧
        matrixSignature (evalGuardedMatrix coeff x M) = s := by
  induction d generalizing s with
  | zero =>
      rw [matrixSignature_fin_zero]
      by_cases hs : s = 0
      · simp [leadingPivotSignatureFormula, LeadingPivotCondition, hs]
      · have hs' : (0 : ℤ) ≠ s := fun h ↦ hs h.symm
        simp [leadingPivotSignatureFormula, LeadingPivotCondition, hs, hs']
  | succ k ih =>
      simp only [leadingPivotSignatureFormula, SignFormula.realizes_conj,
        SignFormula.realizes_disj, LeadingPivotCondition]
      constructor
      · rintro ⟨_, (⟨hpos, hrec⟩ | ⟨hneg, hrec⟩)⟩
        · have hp : 0 < (M 0 0).eval coeff x :=
            (GuardedRational.realizes_positiveFormula_iff coeff x (M 0 0)).1 hpos
          have hpne : (M 0 0).eval coeff x ≠ 0 := ne_of_gt hp
          have hvalidS := guardedMatrixSchurComplement_valid coeff x hvalid hpne
          have hsymmS := guardedMatrixSchurComplement_isSymm hM
          have hrec' := (ih (guardedMatrixSchurComplement M) (s - 1)
            hvalidS hsymmS).1 hrec
          refine ⟨⟨hpne, hrec'.1⟩, ?_⟩
          have hsplit := matrixSignature_eval_eq_orderedSign_add_guardedSchur
            coeff x hvalid hM hpne
          rw [orderedSign_eq_one_iff.mpr hp, hrec'.2] at hsplit
          omega
        · have hnpos : 0 < ((M 0 0).neg).eval coeff x :=
            (GuardedRational.realizes_positiveFormula_iff coeff x
              ((M 0 0).neg)).1 hneg
          rw [GuardedRational.eval_neg] at hnpos
          have hp : (M 0 0).eval coeff x < 0 := neg_pos.mp hnpos
          have hpne : (M 0 0).eval coeff x ≠ 0 := ne_of_lt hp
          have hvalidS := guardedMatrixSchurComplement_valid coeff x hvalid hpne
          have hsymmS := guardedMatrixSchurComplement_isSymm hM
          have hrec' := (ih (guardedMatrixSchurComplement M) (s + 1)
            hvalidS hsymmS).1 hrec
          refine ⟨⟨hpne, hrec'.1⟩, ?_⟩
          have hsplit := matrixSignature_eval_eq_orderedSign_add_guardedSchur
            coeff x hvalid hM hpne
          rw [orderedSign_eq_neg_one_iff.mpr hp, hrec'.2] at hsplit
          omega
      · rintro ⟨⟨hpne, hcondition⟩, hsignature⟩
        have hguard : (M 0 0).guardFormula.Realizes coeff x :=
          (GuardedRational.realizes_guardFormula coeff x (M 0 0)).2 (hvalid 0 0)
        rcases lt_or_gt_of_ne hpne.symm with hp | hp
        · refine ⟨hguard, Or.inl ⟨
            (GuardedRational.realizes_positiveFormula_iff coeff x (M 0 0)).2 hp,
            ?_⟩⟩
          have hvalidS := guardedMatrixSchurComplement_valid coeff x hvalid
            (ne_of_gt hp)
          have hsymmS := guardedMatrixSchurComplement_isSymm hM
          apply (ih (guardedMatrixSchurComplement M) (s - 1)
            hvalidS hsymmS).2
          refine ⟨hcondition, ?_⟩
          have hsplit := matrixSignature_eval_eq_orderedSign_add_guardedSchur
            coeff x hvalid hM (ne_of_gt hp)
          rw [orderedSign_eq_one_iff.mpr hp] at hsplit
          omega
        · refine ⟨hguard, Or.inr ⟨?_, ?_⟩⟩
          · apply (GuardedRational.realizes_positiveFormula_iff coeff x
              ((M 0 0).neg)).2
            rw [GuardedRational.eval_neg]
            exact neg_pos.mpr hp
          · have hvalidS := guardedMatrixSchurComplement_valid coeff x hvalid
              (ne_of_lt hp)
            have hsymmS := guardedMatrixSchurComplement_isSymm hM
            apply (ih (guardedMatrixSchurComplement M) (s + 1)
              hvalidS hsymmS).2
            refine ⟨hcondition, ?_⟩
            have hsplit := matrixSignature_eval_eq_orderedSign_add_guardedSchur
              coeff x hvalid hM (ne_of_lt hp)
            rw [orderedSign_eq_neg_one_iff.mpr hp] at hsplit
            omega

end OptimalConvergenceRates.KrivineStengle

end
