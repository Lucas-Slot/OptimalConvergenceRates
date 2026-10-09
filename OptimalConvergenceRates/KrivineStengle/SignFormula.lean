/-
  OptimalConvergenceRates/KrivineStengle/SignFormula.lean

  A deliberately small language of polynomial sign formulas.
-/
import OptimalConvergenceRates.KrivineStengle.Defs
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Algebra.MvPolynomial.Eval

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- Quantifier-free formulas built from polynomial equations and strict positivity atoms. -/
inductive SignFormula (n : ℕ) where
  | eqZero (p : MvPolynomial (Fin n) ℝ)
  | positive (p : MvPolynomial (Fin n) ℝ)
  | conj (left right : SignFormula n)
  | disj (left right : SignFormula n)
  | neg (formula : SignFormula n)

namespace SignFormula

/-- Semantics in an ordered field under an explicit interpretation of real coefficients. -/
def Realizes {n : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (x : Fin n → F) : SignFormula n → Prop
  | eqZero p => eval₂Hom coeff x p = 0
  | positive p => 0 < eval₂Hom coeff x p
  | conj left right => left.Realizes coeff x ∧ right.Realizes coeff x
  | disj left right => left.Realizes coeff x ∨ right.Realizes coeff x
  | neg formula => ¬formula.Realizes coeff x

@[simp] theorem realizes_eqZero {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F) (p) :
    (eqZero p).Realizes coeff x ↔ eval₂Hom coeff x p = 0 := Iff.rfl

@[simp] theorem realizes_positive {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F) (p) :
    (positive p).Realizes coeff x ↔ 0 < eval₂Hom coeff x p := Iff.rfl

@[simp] theorem realizes_conj {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F) (a b) :
    (conj a b).Realizes coeff x ↔ a.Realizes coeff x ∧ b.Realizes coeff x := Iff.rfl

@[simp] theorem realizes_disj {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F) (a b) :
    (disj a b).Realizes coeff x ↔ a.Realizes coeff x ∨ b.Realizes coeff x := Iff.rfl

@[simp] theorem realizes_neg {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F) (a) :
    (neg a).Realizes coeff x ↔ ¬a.Realizes coeff x := Iff.rfl

/-- Ordered field embeddings preserve and reflect all quantifier-free sign formulas. -/
theorem realizes_map_iff {n : ℕ} {F E : Type*}
    [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    [Field E] [LinearOrder E] [IsStrictOrderedRing E]
    (i : F →+*o E) (coeff : ℝ →+* F) (x : Fin n → F) (formula : SignFormula n) :
    formula.Realizes (i.toRingHom.comp coeff) (fun j ↦ i (x j)) ↔
      formula.Realizes coeff x := by
  have hinj : Function.Injective i := i.toRingHom.injective
  have hstrict : StrictMono i := i.monotone'.strictMono_of_injective hinj
  have heval (p : MvPolynomial (Fin n) ℝ) :
      eval₂Hom (i.toRingHom.comp coeff) (fun j ↦ i (x j)) p =
        i (eval₂Hom coeff x p) := by
    symm
    exact map_eval₂Hom coeff x i.toRingHom p
  induction formula with
  | eqZero p =>
      rw [realizes_eqZero, realizes_eqZero, heval, ← map_zero i]
      exact hinj.eq_iff
  | positive p =>
      rw [realizes_positive, realizes_positive, heval, ← map_zero i,
        hstrict.lt_iff_lt]
  | conj a b iha ihb => simp only [realizes_conj, iha, ihb]
  | disj a b iha ihb => simp only [realizes_disj, iha, ihb]
  | neg a iha => simp only [realizes_neg, iha]

/-- Existential realizability of a sign formula in an interpreted ordered field. -/
def Satisfiable {n : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (formula : SignFormula n) : Prop :=
  ∃ x : Fin n → F, formula.Realizes coeff x

theorem satisfiable_map {n : ℕ} {F E : Type*}
    [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    [Field E] [LinearOrder E] [IsStrictOrderedRing E]
    (i : F →+*o E) (coeff : ℝ →+* F) {formula : SignFormula n}
    (h : formula.Satisfiable coeff) :
    formula.Satisfiable (i.toRingHom.comp coeff) := by
  obtain ⟨x, hx⟩ := h
  exact ⟨fun j ↦ i (x j), (realizes_map_iff i coeff x formula).2 hx⟩


/-- Finite conjunction. The empty conjunction is represented by the true atom \`0 < 1\`. -/
def all : List (SignFormula n) → SignFormula n
  | [] => positive 1
  | formula :: formulas => conj formula (all formulas)

@[simp] theorem realizes_all {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F) (formulas) :
    (all formulas).Realizes coeff x ↔
      ∀ formula ∈ formulas, formula.Realizes coeff x := by
  induction formulas with
  | nil => simp [all]
  | cons formula formulas ih => simp [all, ih]

/-- The sign atom saying that a polynomial is weakly nonnegative. -/
def nonnegative (p : MvPolynomial (Fin n) ℝ) : SignFormula n :=
  neg (positive (-p))

@[simp] theorem realizes_nonnegative {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F) (p) :
    (nonnegative p).Realizes coeff x ↔ 0 ≤ eval₂Hom coeff x p := by
  simp [nonnegative]

/-- The single finite sign formula expressing a counterexample to nonnegativity of \`p\` on
the basic closed set generated by \`g\`. -/
def counterexampleFormula {m n : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) : SignFormula n :=
  conj (all (List.ofFn fun i ↦ nonnegative (g i))) (positive (-p))

@[simp] theorem realizes_counterexampleFormula {m n : ℕ}
    (g : Fin m → MvPolynomial (Fin n) ℝ) (p : MvPolynomial (Fin n) ℝ)
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (x : Fin n → F) :
    (counterexampleFormula g p).Realizes coeff x ↔
      (∀ i, 0 ≤ eval₂Hom coeff x (g i)) ∧ eval₂Hom coeff x p < 0 := by
  simp [counterexampleFormula]

/-- Every homomorphism out of a multivariate polynomial ring is evaluation at the images of
the variables, with coefficients interpreted through its restriction to constants. -/
theorem eval₂Hom_comp_C_X {F : Type*} [CommRing F] (phi : MvPolynomial (Fin n) ℝ →+* F) :
    eval₂Hom (phi.comp C) (fun i ↦ phi (X i)) = phi := by
  ext <;> simp

theorem counterexampleFormula_realizes_of_hom {m n : ℕ}
    (g : Fin m → MvPolynomial (Fin n) ℝ) (p : MvPolynomial (Fin n) ℝ)
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (phi : MvPolynomial (Fin n) ℝ →+* F)
    (hg : ∀ i, 0 ≤ phi (g i)) (hp : phi p < 0) :
    (counterexampleFormula g p).Realizes (phi.comp C) (fun i ↦ phi (X i)) := by
  rw [realizes_counterexampleFormula]
  simpa only [RingHom.congr_fun (eval₂Hom_comp_C_X phi)] using And.intro hg hp

theorem hom_inequalities_of_counterexampleFormula_realizes {m n : ℕ}
    (g : Fin m → MvPolynomial (Fin n) ℝ) (p : MvPolynomial (Fin n) ℝ)
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (phi : MvPolynomial (Fin n) ℝ →+* F)
    (h : (counterexampleFormula g p).Realizes (phi.comp C) (fun i ↦ phi (X i))) :
    (∀ i, 0 ≤ phi (g i)) ∧ phi p < 0 := by
  rw [realizes_counterexampleFormula] at h
  simpa only [RingHom.congr_fun (eval₂Hom_comp_C_X phi)] using h

end SignFormula

end OptimalConvergenceRates.KrivineStengle

end
