/-
  OptimalConvergenceRates/KrivineStengle/GuardedRational.lean

  Guarded rational arithmetic and conversion of its tests to polynomial sign atoms.
-/
import OptimalConvergenceRates.KrivineStengle.SignNormalForm
import Mathlib.Tactic.FieldSimp

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- A symbolic rational expression in parameters, represented by numerator and denominator
polynomials. Nonvanishing of the denominator is always carried as a separate guard. -/
structure GuardedRational (n : ℕ) where
  num : MvPolynomial (Fin n) ℝ
  den : MvPolynomial (Fin n) ℝ

namespace GuardedRational

def eval {n : ℕ} {F : Type*} [Field F] (coeff : ℝ →+* F) (x : Fin n → F)
    (r : GuardedRational n) : F :=
  eval₂Hom coeff x r.num / eval₂Hom coeff x r.den

def Valid {n : ℕ} {F : Type*} [Field F] (coeff : ℝ →+* F) (x : Fin n → F)
    (r : GuardedRational n) : Prop :=
  eval₂Hom coeff x r.den ≠ 0

def ofPolynomial (p : MvPolynomial (Fin n) ℝ) : GuardedRational n := ⟨p, 1⟩

def zero : GuardedRational n := ofPolynomial 0

def one : GuardedRational n := ofPolynomial 1

def add (r s : GuardedRational n) : GuardedRational n :=
  ⟨r.num * s.den + s.num * r.den, r.den * s.den⟩

def mul (r s : GuardedRational n) : GuardedRational n :=
  ⟨r.num * s.num, r.den * s.den⟩

/-- Symbolic inversion. Its validity requires both the old denominator guard and a proof that
the old numerator is nonzero. -/
def inv (r : GuardedRational n) : GuardedRational n := ⟨r.den, r.num⟩

@[simp] theorem valid_ofPolynomial {n : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F) (p) :
    (ofPolynomial p).Valid coeff x := by
  simp [Valid, ofPolynomial]

@[simp] theorem eval_ofPolynomial {n : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F) (p) :
    (ofPolynomial p).eval coeff x = eval₂Hom coeff x p := by
  simp [eval, ofPolynomial]

theorem Valid.add {n : ℕ} {F : Type*} [Field F] (coeff : ℝ →+* F)
    (x : Fin n → F) {r s : GuardedRational n}
    (hr : r.Valid coeff x) (hs : s.Valid coeff x) :
    (r.add s).Valid coeff x := by
  change eval₂Hom coeff x (r.den * s.den) ≠ 0
  rw [map_mul]
  exact mul_ne_zero hr hs

theorem Valid.mul {n : ℕ} {F : Type*} [Field F] (coeff : ℝ →+* F)
    (x : Fin n → F) {r s : GuardedRational n}
    (hr : r.Valid coeff x) (hs : s.Valid coeff x) :
    (r.mul s).Valid coeff x := by
  change eval₂Hom coeff x (r.den * s.den) ≠ 0
  rw [map_mul]
  exact mul_ne_zero hr hs

theorem Valid.inv {n : ℕ} {F : Type*} [Field F] (coeff : ℝ →+* F)
    (x : Fin n → F) {r : GuardedRational n}
    (hnum : eval₂Hom coeff x r.num ≠ 0) :
    r.inv.Valid coeff x :=
  hnum

theorem eval_add {n : ℕ} {F : Type*} [Field F] (coeff : ℝ →+* F)
    (x : Fin n → F) {r s : GuardedRational n}
    (hr : r.Valid coeff x) (hs : s.Valid coeff x) :
    (r.add s).eval coeff x = r.eval coeff x + s.eval coeff x := by
  have hr0 : eval₂Hom coeff x r.den ≠ 0 := hr
  have hs0 : eval₂Hom coeff x s.den ≠ 0 := hs
  simp only [eval, add, map_add, map_mul]
  field_simp [hr0, hs0]

theorem eval_mul {n : ℕ} {F : Type*} [Field F] (coeff : ℝ →+* F)
    (x : Fin n → F) {r s : GuardedRational n}
    (hr : r.Valid coeff x) (hs : s.Valid coeff x) :
    (r.mul s).eval coeff x = r.eval coeff x * s.eval coeff x := by
  simp only [eval, mul, map_mul]
  field_simp

theorem eval_inv {n : ℕ} {F : Type*} [Field F] (coeff : ℝ →+* F)
    (x : Fin n → F) {r : GuardedRational n}
    (hr : r.Valid coeff x) (hnum : eval₂Hom coeff x r.num ≠ 0) :
    r.inv.eval coeff x = (r.eval coeff x)⁻¹ := by
  simp only [eval, inv]
  field_simp

/-- The polynomial guard saying that the denominator does not vanish. -/
def guardFormula (r : GuardedRational n) : SignFormula n :=
  .neg (.eqZero r.den)

/-- The polynomial atom equivalent to equality of the guarded rational expression to zero. -/
def eqZeroFormula (r : GuardedRational n) : SignFormula n :=
  .eqZero r.num

/-- The polynomial atom equivalent to strict positivity of the guarded rational expression. -/
def positiveFormula (r : GuardedRational n) : SignFormula n :=
  .positive (r.num * r.den)

@[simp] theorem realizes_guardFormula {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F)
    (r : GuardedRational n) :
    r.guardFormula.Realizes coeff x ↔ r.Valid coeff x := by
  rfl

theorem realizes_eqZeroFormula_iff {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F)
    (r : GuardedRational n) (hr : r.Valid coeff x) :
    r.eqZeroFormula.Realizes coeff x ↔ r.eval coeff x = 0 := by
  change eval₂Hom coeff x r.num = 0 ↔
    eval₂Hom coeff x r.num / eval₂Hom coeff x r.den = 0
  constructor
  · intro hnum
    rw [hnum, zero_div]
  · intro hdiv
    rcases div_eq_zero_iff.mp hdiv with hnum | hden
    · exact hnum
    · exact False.elim (hr hden)

theorem realizes_positiveFormula_iff {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F)
    (r : GuardedRational n) :
    r.positiveFormula.Realizes coeff x ↔ 0 < r.eval coeff x := by
  change 0 < eval₂Hom coeff x (r.num * r.den) ↔ 0 < r.eval coeff x
  simp only [map_mul, eval]
  exact mul_pos_iff.trans div_pos_iff.symm

end GuardedRational

end OptimalConvergenceRates.KrivineStengle

end
