/-
  OptimalConvergenceRates/KrivineStengle/LiteralClauseNormalization.lean

  Normalize sign-literal clauses to finite disjunctions of clauses using
  only equations and strict positivity atoms.
-/
import OptimalConvergenceRates.KrivineStengle.SignNormalForm

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- A conjunction represented by its equation atoms and strict positivity atoms. -/
structure StrictClauseData (n : ℕ) where
  equations : List (MvPolynomial (Fin n) ℝ)
  positives : List (MvPolynomial (Fin n) ℝ)

namespace StrictClauseData

def Realizes {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F)
    (clause : StrictClauseData n) : Prop :=
  (∀ p ∈ clause.equations, eval₂Hom coeff x p = 0) ∧
    (∀ p ∈ clause.positives, 0 < eval₂Hom coeff x p)

def append {n : ℕ} (left right : StrictClauseData n) : StrictClauseData n where
  equations := left.equations ++ right.equations
  positives := left.positives ++ right.positives

@[simp] theorem realizes_append
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F)
    (left right : StrictClauseData n) :
    (append left right).Realizes coeff x ↔
      left.Realizes coeff x ∧ right.Realizes coeff x := by
  simp only [Realizes, append, List.forall_mem_append]
  tauto

end StrictClauseData

/-- Strict-clause alternatives equivalent to one sign literal. -/
def literalStrictClauses {n : ℕ} : SignLiteral n → List (StrictClauseData n)
  | .eqZero p => [⟨[p], []⟩]
  | .positive p => [⟨[], [p]⟩]
  | .neZero p => [⟨[], [p]⟩, ⟨[], [-p]⟩]
  | .nonpositive p => [⟨[p], []⟩, ⟨[], [-p]⟩]

/-- Semantics of a finite disjunction of strict clauses. -/
def StrictDNFRealizes {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F)
    (clauses : List (StrictClauseData n)) : Prop :=
  ∃ clause ∈ clauses, clause.Realizes coeff x

theorem strictDNFRealizes_literalStrictClauses
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F)
    (literal : SignLiteral n) :
    StrictDNFRealizes coeff x (literalStrictClauses literal) ↔
      literal.Realizes coeff x := by
  cases literal with
  | eqZero p => simp [StrictDNFRealizes, literalStrictClauses,
      StrictClauseData.Realizes, SignLiteral.Realizes]
  | positive p => simp [StrictDNFRealizes, literalStrictClauses,
      StrictClauseData.Realizes, SignLiteral.Realizes]
  | neZero p =>
      constructor
      · rintro ⟨clause, hmem, hrealizes⟩
        simp only [literalStrictClauses, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · exact ne_of_gt (hrealizes.2 p (by simp))
        · have hneg := hrealizes.2 (-p) (by simp)
          have hpneg : eval₂Hom coeff x p < 0 := by simpa using hneg
          exact ne_of_lt hpneg
      · intro hne
        rcases lt_or_gt_of_ne hne with hneg | hpos
        · refine ⟨⟨[], [-p]⟩, by simp [literalStrictClauses], ?_⟩
          refine ⟨by simp, ?_⟩
          intro q hq
          simp only [List.mem_singleton] at hq
          subst q
          simpa using hneg
        · refine ⟨⟨[], [p]⟩, by simp [literalStrictClauses], ?_⟩
          exact ⟨by simp, by simpa using hpos⟩
  | nonpositive p =>
      constructor
      · rintro ⟨clause, hmem, hrealizes⟩
        simp only [literalStrictClauses, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · have hzero := hrealizes.1 p (by simp)
          simp [SignLiteral.Realizes, hzero]
        · have hneg := hrealizes.2 (-p) (by simp)
          have hpneg : eval₂Hom coeff x p < 0 := by simpa using hneg
          exact not_lt_of_ge hpneg.le
      · intro hnotpos
        have hle : eval₂Hom coeff x p ≤ 0 := le_of_not_gt hnotpos
        rcases hle.eq_or_lt with hzero | hneg
        · refine ⟨⟨[p], []⟩, by simp [literalStrictClauses], ?_⟩
          exact ⟨by simpa [hzero], by simp⟩
        · refine ⟨⟨[], [-p]⟩, by simp [literalStrictClauses], ?_⟩
          refine ⟨by simp, ?_⟩
          intro q hq
          simp only [List.mem_singleton] at hq
          subst q
          simpa using hneg

/-- Cartesian conjunction of two strict DNFs. -/
def strictDNFAnd {n : ℕ}
    (left right : List (StrictClauseData n)) : List (StrictClauseData n) :=
  left.flatMap fun leftClause ↦
    right.map fun rightClause ↦ leftClause.append rightClause

@[simp] theorem strictDNFRealizes_and
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F)
    (left right : List (StrictClauseData n)) :
    StrictDNFRealizes coeff x (strictDNFAnd left right) ↔
      StrictDNFRealizes coeff x left ∧ StrictDNFRealizes coeff x right := by
  constructor
  · rintro ⟨clause, hclause, hrealizes⟩
    obtain ⟨leftClause, hleft, hclause⟩ := List.mem_flatMap.mp hclause
    obtain ⟨rightClause, hright, rfl⟩ := List.mem_map.mp hclause
    rw [StrictClauseData.realizes_append] at hrealizes
    exact ⟨⟨leftClause, hleft, hrealizes.1⟩,
      ⟨rightClause, hright, hrealizes.2⟩⟩
  · rintro ⟨⟨leftClause, hleft, hleftRealizes⟩,
      ⟨rightClause, hright, hrightRealizes⟩⟩
    refine ⟨leftClause.append rightClause, ?_, ?_⟩
    · exact List.mem_flatMap.mpr ⟨leftClause, hleft,
        List.mem_map.mpr ⟨rightClause, hright, rfl⟩⟩
    · exact (StrictClauseData.realizes_append coeff x leftClause rightClause).2
        ⟨hleftRealizes, hrightRealizes⟩

/-- Distribute every literal alternative through a conjunctive clause. -/
def normalizeLiteralClause {n : ℕ} :
    List (SignLiteral n) → List (StrictClauseData n)
  | [] => [⟨[], []⟩]
  | literal :: literals =>
      strictDNFAnd (literalStrictClauses literal)
        (normalizeLiteralClause literals)

theorem strictDNFRealizes_normalizeLiteralClause
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F)
    (clause : List (SignLiteral n)) :
    StrictDNFRealizes coeff x (normalizeLiteralClause clause) ↔
      SignFormula.ClauseRealizes coeff x clause := by
  induction clause with
  | nil => simp [normalizeLiteralClause, StrictDNFRealizes,
      StrictClauseData.Realizes, SignFormula.ClauseRealizes]
  | cons literal literals ih =>
      rw [normalizeLiteralClause, strictDNFRealizes_and,
        strictDNFRealizes_literalStrictClauses, ih]
      simp [SignFormula.ClauseRealizes]

end OptimalConvergenceRates.KrivineStengle

end
