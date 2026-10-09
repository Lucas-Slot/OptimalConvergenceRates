/-
  OptimalConvergenceRates/KrivineStengle/RealComplex.lean

  The quadratic extension obtained by adjoining a square root of `-1` to
  an ordered real-closed field, and its elementary square-root property.
-/
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Tactic.FieldSimp

noncomputable section

namespace OptimalConvergenceRates.KrivineStengle

universe u

/-- The algebra `R[i]`, represented by pairs with `i² = -1`. -/
abbrev RealComplex (R : Type u) [Ring R] := QuadraticAlgebra R (-1) 0

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Minus one is not a square in an ordered field.  This supplies the
irreducibility fact used by the quadratic-algebra field instance. -/
theorem sq_ne_neg_one (x : R) : x ^ 2 ≠ -1 := by
  nlinarith [sq_nonneg x]

instance realComplex_irreducibleFact :
    Fact (∀ x : R, x ^ 2 ≠ (-1 : R) + 0 * x) :=
  ⟨fun x ↦ by simpa using sq_ne_neg_one x⟩

instance : Field (RealComplex R) := inferInstance

@[simp] theorem realComplex_omega_sq :
    (QuadraticAlgebra.omega : RealComplex R) ^ 2 = -1 := by
  rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_mk]
  ext
  · simp only [QuadraticAlgebra.re_neg, QuadraticAlgebra.re_one]
  · simp only [QuadraticAlgebra.im_neg, QuadraticAlgebra.im_one, neg_zero]

variable [IsRealClosed R]

/-- Every element of `R[i]` is a square.  This is the elementary
quadratic-closure calculation used in the Galois proof that `R[i]` is
algebraically closed. -/
theorem realComplex_isSquare (z : RealComplex R) : IsSquare z := by
  rcases z with ⟨a, b⟩
  by_cases hb : b = 0
  · subst b
    by_cases ha : 0 ≤ a
    · obtain ⟨u, hu⟩ :=
        IsRealClosed.exists_eq_pow_of_nonneg ha (by decide : (2 : ℕ) ≠ 0)
      refine ⟨(⟨u, 0⟩ : RealComplex R), ?_⟩
      ext
      · simpa [pow_two] using hu
      · simp
    · have hna : 0 ≤ -a := neg_nonneg.mpr (le_of_not_ge ha)
      obtain ⟨u, hu⟩ :=
        IsRealClosed.exists_eq_pow_of_nonneg hna (by decide : (2 : ℕ) ≠ 0)
      refine ⟨(⟨0, u⟩ : RealComplex R), ?_⟩
      ext
      · simp only [QuadraticAlgebra.re_mul]
        nlinarith [hu]
      · simp
  · have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
    have hspos : 0 < a ^ 2 + b ^ 2 := by positivity
    obtain ⟨r₀, hr₀⟩ := IsRealClosed.exists_eq_pow_of_nonneg hspos.le
      (by decide : (2 : ℕ) ≠ 0)
    let r : R := |r₀|
    have hr2 : r ^ 2 = a ^ 2 + b ^ 2 := by
      dsimp [r]
      rw [sq_abs]
      exact hr₀.symm
    have hr₀0 : r₀ ≠ 0 := by
      intro h
      subst r₀
      simp at hr₀
      nlinarith
    have hrpos : 0 < r := by simpa [r] using (abs_pos.mpr hr₀0)
    have har : a < r := by
      nlinarith [sq_nonneg (a + r)]
    have hhalf : 0 < (r + a) / 2 := by nlinarith
    obtain ⟨u, hu⟩ := IsRealClosed.exists_eq_pow_of_nonneg hhalf.le
      (by decide : (2 : ℕ) ≠ 0)
    have hu0 : u ≠ 0 := by
      intro h
      subst u
      simp at hu
      nlinarith
    let v : R := b / (2 * u)
    have htwo_uv : 2 * u * v = b := by
      dsimp [v]
      field_simp [hu0]
    have hv2 : v ^ 2 = (r - a) / 2 := by
      dsimp [v]
      field_simp [hu0]
      nlinarith [hr2]
    refine ⟨(⟨u, v⟩ : RealComplex R), ?_⟩
    ext
    · simp only [QuadraticAlgebra.re_mul]
      nlinarith
    · simp only [QuadraticAlgebra.im_mul]
      nlinarith [htwo_uv]

end OptimalConvergenceRates.KrivineStengle

end
