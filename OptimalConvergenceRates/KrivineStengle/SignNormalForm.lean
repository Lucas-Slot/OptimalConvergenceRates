/-
  OptimalConvergenceRates/KrivineStengle/SignNormalForm.lean

  Constructive disjunctive normal form for polynomial sign formulas.
-/
import OptimalConvergenceRates.KrivineStengle.SignFormula
import Mathlib.Tactic.Tauto

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- Literals needed after pushing negations through a sign formula. -/
inductive SignLiteral (n : ℕ) where
  | eqZero (p : MvPolynomial (Fin n) ℝ)
  | positive (p : MvPolynomial (Fin n) ℝ)
  | neZero (p : MvPolynomial (Fin n) ℝ)
  | nonpositive (p : MvPolynomial (Fin n) ℝ)

namespace SignLiteral

def Realizes {n : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (x : Fin n → F) : SignLiteral n → Prop
  | eqZero p => eval₂Hom coeff x p = 0
  | positive p => 0 < eval₂Hom coeff x p
  | neZero p => eval₂Hom coeff x p ≠ 0
  | nonpositive p => ¬0 < eval₂Hom coeff x p

end SignLiteral

namespace SignFormula

/-- Semantics of one conjunctive clause. -/
def ClauseRealizes {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F)
    (clause : List (SignLiteral n)) : Prop :=
  ∀ literal ∈ clause, literal.Realizes coeff x

/-- Semantics of a disjunction of conjunctive clauses. -/
def DNFRealizes {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F)
    (dnf : List (List (SignLiteral n))) : Prop :=
  ∃ clause ∈ dnf, ClauseRealizes coeff x clause

/-- Cartesian conjunction of two DNFs. -/
def dnfAnd {n : ℕ} (left right : List (List (SignLiteral n))) :
    List (List (SignLiteral n)) :=
  left.flatMap fun leftClause ↦ right.map fun rightClause ↦ leftClause ++ rightClause

@[simp] theorem dnfRealizes_append {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F) (left right) :
    DNFRealizes coeff x (left ++ right) ↔
      DNFRealizes coeff x left ∨ DNFRealizes coeff x right := by
  constructor
  · rintro ⟨clause, hmem, hclause⟩
    rcases List.mem_append.mp hmem with hleft | hright
    · exact Or.inl ⟨clause, hleft, hclause⟩
    · exact Or.inr ⟨clause, hright, hclause⟩
  · rintro (⟨clause, hleft, hclause⟩ | ⟨clause, hright, hclause⟩)
    · exact ⟨clause, List.mem_append.mpr (Or.inl hleft), hclause⟩
    · exact ⟨clause, List.mem_append.mpr (Or.inr hright), hclause⟩

@[simp] theorem dnfRealizes_and {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F) (left right) :
    DNFRealizes coeff x (dnfAnd left right) ↔
      DNFRealizes coeff x left ∧ DNFRealizes coeff x right := by
  constructor
  · rintro ⟨clause, hmem, hall⟩
    obtain ⟨leftClause, hleft, hmem⟩ := List.mem_flatMap.mp hmem
    obtain ⟨rightClause, hright, rfl⟩ := List.mem_map.mp hmem
    refine ⟨⟨leftClause, hleft, ?_⟩, ⟨rightClause, hright, ?_⟩⟩
    · intro literal hliteral
      exact hall literal (List.mem_append.mpr (Or.inl hliteral))
    · intro literal hliteral
      exact hall literal (List.mem_append.mpr (Or.inr hliteral))
  · rintro ⟨⟨leftClause, hleft, hallLeft⟩, ⟨rightClause, hright, hallRight⟩⟩
    refine ⟨leftClause ++ rightClause, ?_, ?_⟩
    · exact List.mem_flatMap.mpr
        ⟨leftClause, hleft, List.mem_map.mpr ⟨rightClause, hright, rfl⟩⟩
    · intro literal hliteral
      rcases List.mem_append.mp hliteral with hliteral | hliteral
      · exact hallLeft literal hliteral
      · exact hallRight literal hliteral

/-- `toDNF polarity formula` produces DNF for `formula` when `polarity = true`, and for its
negation when `polarity = false`. -/
def toDNF {n : ℕ} : Bool → SignFormula n → List (List (SignLiteral n))
  | true, .eqZero p => [[.eqZero p]]
  | false, .eqZero p => [[.neZero p]]
  | true, .positive p => [[.positive p]]
  | false, .positive p => [[.nonpositive p]]
  | true, .conj left right => dnfAnd (toDNF true left) (toDNF true right)
  | false, .conj left right => toDNF false left ++ toDNF false right
  | true, .disj left right => toDNF true left ++ toDNF true right
  | false, .disj left right => dnfAnd (toDNF false left) (toDNF false right)
  | polarity, .neg formula => toDNF (!polarity) formula

/-- Correctness of constructive DNF conversion, uniformly over every ordered field. -/
theorem dnfRealizes_toDNF {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F)
    (formula : SignFormula n) (polarity : Bool) :
    DNFRealizes coeff x (toDNF polarity formula) ↔
      if polarity then formula.Realizes coeff x else ¬formula.Realizes coeff x := by
  classical
  induction formula generalizing polarity with
  | eqZero p => cases polarity <;> simp [toDNF, DNFRealizes, ClauseRealizes, SignLiteral.Realizes]
  | positive p =>
      cases polarity <;> simp [toDNF, DNFRealizes, ClauseRealizes, SignLiteral.Realizes]
  | conj left right ihLeft ihRight =>
      cases polarity <;> simp [toDNF, ihLeft, ihRight]; tauto
  | disj left right ihLeft ihRight =>
      cases polarity <;> simp [toDNF, ihLeft, ihRight, not_or]
  | neg formula ih =>
      cases polarity <;> simp [toDNF, ih]

/-- The positive-polarity specialization used by elimination. -/
theorem dnfRealizes_toDNF_true {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F)
    (formula : SignFormula n) :
    DNFRealizes coeff x (toDNF true formula) ↔ formula.Realizes coeff x := by
  simpa using dnfRealizes_toDNF coeff x formula true

end SignFormula

end OptimalConvergenceRates.KrivineStengle

end
