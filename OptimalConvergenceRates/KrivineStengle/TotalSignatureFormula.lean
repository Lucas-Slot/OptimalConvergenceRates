/-
  OptimalConvergenceRates/KrivineStengle/TotalSignatureFormula.lean

  A total finite sign formula for the signature of a symmetric guarded
  rational matrix, including zero pivots and off-diagonal pivot creation.
-/
import OptimalConvergenceRates.KrivineStengle.SignaturePivot
import OptimalConvergenceRates.KrivineStengle.LeadingPivotSignatureFormula

noncomputable section

open Matrix MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

namespace SignFormula

/-- Finite disjunction. The empty disjunction is false. -/
def any {n : ℕ} : List (SignFormula n) → SignFormula n
  | [] => falseSignFormula n
  | formula :: formulas => .disj formula (any formulas)

@[simp] theorem realizes_any {n : ℕ} {F : Type*}
    [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (x : Fin n → F) (formulas : List (SignFormula n)) :
    (any formulas).Realizes coeff x ↔
      ∃ formula ∈ formulas, formula.Realizes coeff x := by
  induction formulas with
  | nil => simp [any]
  | cons formula formulas ih => simp [any, ih]

end SignFormula

/-- An entry is valid and specializes to zero. -/
def guardedZeroFormula {n : ℕ} (r : GuardedRational n) : SignFormula n :=
  .conj r.guardFormula r.eqZeroFormula

/-- Every entry of the guarded matrix is valid and specializes to zero. -/
def guardedMatrixZeroFormula {n d : ℕ}
    (M : Matrix (Fin d) (Fin d) (GuardedRational n)) : SignFormula n :=
  SignFormula.all (List.ofFn fun i : Fin d ↦
    SignFormula.all (List.ofFn fun j : Fin d ↦ guardedZeroFormula (M i j)))

theorem realizes_guardedZeroFormula_iff {n : ℕ} {F : Type*}
    [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (x : Fin n → F) (r : GuardedRational n) :
    (guardedZeroFormula r).Realizes coeff x ↔
      r.Valid coeff x ∧ r.eval coeff x = 0 := by
  rw [guardedZeroFormula, SignFormula.realizes_conj,
    GuardedRational.realizes_guardFormula,
    and_congr_right_iff]
  intro hr
  exact GuardedRational.realizes_eqZeroFormula_iff coeff x r hr

theorem realizes_guardedMatrixZeroFormula_iff {n d : ℕ}
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (M : Matrix (Fin d) (Fin d) (GuardedRational n)) :
    (guardedMatrixZeroFormula M).Realizes coeff x ↔
      GuardedMatrixValid coeff x M ∧ evalGuardedMatrix coeff x M = 0 := by
  constructor
  · intro h
    rw [guardedMatrixZeroFormula, SignFormula.realizes_all] at h
    have hentry (i j : Fin d) :
        (guardedZeroFormula (M i j)).Realizes coeff x := by
      have hi := h _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
      rw [SignFormula.realizes_all] at hi
      exact hi _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
    refine ⟨fun i j ↦ (realizes_guardedZeroFormula_iff coeff x (M i j)).1
      (hentry i j) |>.1, ?_⟩
    ext i j
    exact (realizes_guardedZeroFormula_iff coeff x (M i j)).1
      (hentry i j) |>.2
  · rintro ⟨hvalid, hzero⟩
    rw [guardedMatrixZeroFormula, SignFormula.realizes_all]
    intro row hrow
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
    rw [SignFormula.realizes_all]
    intro entry hentry
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hentry
    apply (realizes_guardedZeroFormula_iff coeff x (M i j)).2
    refine ⟨hvalid i j, ?_⟩
    have hz := congr_fun (congr_fun hzero i) j
    simpa [evalGuardedMatrix] using hz

/-- One nonzero pivot branch of the total signature decision formula. -/
def guardedPivotSignatureBranch {n k : ℕ}
    (recurse : Matrix (Fin k) (Fin k) (GuardedRational n) → ℤ → SignFormula n)
    (N : Matrix (Fin (k + 1)) (Fin (k + 1)) (GuardedRational n))
    (s : ℤ) : SignFormula n :=
  .conj (N 0 0).guardFormula
    (.disj
      (.conj (N 0 0).positiveFormula
        (recurse (guardedMatrixSchurComplement N) (s - 1)))
      (.conj ((N 0 0).neg).positiveFormula
        (recurse (guardedMatrixSchurComplement N) (s + 1))))

/-- Total guarded decision formula for matrix signature. At positive dimension
it accepts the zero matrix with signature zero, or chooses one of the finite
diagonal/transvection pivots and recurses on its Schur complement. -/
def totalMatrixSignatureFormula {n : ℕ} :
    (d : ℕ) → Matrix (Fin d) (Fin d) (GuardedRational n) → ℤ → SignFormula n
  | 0, _, s => if s = 0 then trueSignFormula n else falseSignFormula n
  | k + 1, M, s =>
      .disj
        (.conj (guardedMatrixZeroFormula M)
          (if s = 0 then trueSignFormula n else falseSignFormula n))
        (SignFormula.any (List.ofFn fun i : Fin (k + 1) ↦
          SignFormula.any (List.ofFn fun j : Fin (k + 1) ↦
            guardedPivotSignatureBranch (totalMatrixSignatureFormula k)
              (guardedPivotMatrix (i, j) M) s)))

end OptimalConvergenceRates.KrivineStengle

end
