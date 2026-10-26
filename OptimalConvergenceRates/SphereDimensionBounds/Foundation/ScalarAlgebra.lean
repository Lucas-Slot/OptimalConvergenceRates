import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
/-!
# Scalar algebra for the sphere SOS project

These statements isolate polynomial identities and finite real inequalities
used in the sphere lower-bound construction.
-/

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

/-- The four-variable Choi--Lam quartic, over any commutative ring. -/
def choiLam {R : Type*} [CommRing R] (a b c d : R) : R :=
  a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 + d ^ 4 - 4 * a * b * c * d

/-- The complement of the Choi--Lam form in the squared norm is SOS.

The identity is stated over an arbitrary commutative ring, so it also applies
directly to multivariate polynomial rings.
-/
theorem choiLam_upper_sos_identity {R : Type*} [CommRing R] (a b c d : R) :
    (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 - choiLam a b c d =
      (a * b + c * d) ^ 2 + (b * c + a * d) ^ 2 +
        a ^ 4 + b ^ 4 + c ^ 4 + a ^ 2 * c ^ 2 + a ^ 2 * d ^ 2 +
          2 * b ^ 2 * d ^ 2 + c ^ 2 * d ^ 2 := by
  unfold choiLam
  ring

/-- Adding the squared norm gives an explicit order-two SOS certificate. -/
theorem choiLam_feasible_sos_identity {R : Type*} [CommRing R] (a b c d : R) :
    choiLam a b c d + (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 =
      (a * b - c * d) ^ 2 + (b * c - a * d) ^ 2 +
        a ^ 4 + b ^ 4 + c ^ 4 + 2 * d ^ 4 +
          2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 3 * a ^ 2 * c ^ 2 +
            a ^ 2 * d ^ 2 + 2 * b ^ 2 * d ^ 2 + c ^ 2 * d ^ 2 := by
  unfold choiLam
  ring

/-- Global nonnegativity of the Choi--Lam quartic.

The proof is the four-term arithmetic--geometric mean argument written using
three nonnegative squared expressions and absolute values.
-/
theorem choiLam_nonneg (a b c d : ℝ) : 0 ≤ choiLam a b c d := by
  have h₁ := mul_nonneg (sq_nonneg (|a| - |c|)) (sq_nonneg b)
  have h₂ := sq_nonneg (|a| * |c| - d ^ 2)
  have h₃ := mul_nonneg (mul_nonneg (abs_nonneg a) (abs_nonneg c))
    (sq_nonneg (|b| - |d|))
  have hprod : a * b * c * d ≤ |a| * |b| * |c| * |d| := by
    simpa only [abs_mul] using (le_abs_self (a * b * c * d))
  simp only [sub_sq, mul_pow, sq_abs] at h₁ h₂ h₃
  unfold choiLam
  nlinarith

theorem choiLam_le_norm_fourth (a b c d : ℝ) :
    choiLam a b c d ≤ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 := by
  have h : 0 ≤ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 - choiLam a b c d := by
    rw [choiLam_upper_sos_identity]
    positivity
  linarith

/-- The scalar normalization estimate also covers embeddings in larger spheres. -/
theorem choiLam_le_one (a b c d : ℝ)
    (hnorm : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≤ 1) :
    choiLam a b c d ≤ 1 := by
  have hnorm₀ : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by positivity
  calc
    choiLam a b c d ≤ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 :=
      choiLam_le_norm_fourth a b c d
    _ ≤ 1 := by nlinarith

theorem choiLam_at_first_basis : choiLam (1 : ℝ) 0 0 0 = 0 := by
  norm_num [choiLam]

theorem choiLam_at_fourth_basis : choiLam (0 : ℝ) 0 0 1 = 1 := by
  norm_num [choiLam]

/-- The rounding margin used to establish nonnegativity of the Boolean quartic. -/
theorem rounding_margin (A B m : ℝ) (hB : 0 ≤ B) (hround : m ≤ 2 * A + 6 * B) :
    m / 4 ≤ A + 6 * B - m / 4 := by
  linarith

/-- The one-clause rounding estimate from a bound on three scalar errors. -/
theorem rounding_clause_bound (u v e₁ e₂ e₃ : ℝ)
    (herr : |u - v| ≤ e₁ + e₂ + e₃) :
    u ^ 2 ≤ 2 * v ^ 2 + 6 * (e₁ ^ 2 + e₂ ^ 2 + e₃ ^ 2) := by
  have hsq := pow_le_pow_left₀ (abs_nonneg (u - v)) herr 2
  rw [sq_abs] at hsq
  have hsum : (e₁ + e₂ + e₃) ^ 2 ≤ 3 * (e₁ ^ 2 + e₂ ^ 2 + e₃ ^ 2) := by
    nlinarith [sq_nonneg (e₁ - e₂), sq_nonneg (e₁ - e₃), sq_nonneg (e₂ - e₃)]
  nlinarith [sq_nonneg (u - 2 * v)]

/-- Exact evaluation of the negative term after occurrence normalization and `/7`. -/
theorem boolean_gap_arithmetic (m : ℝ) (hm : m ≠ 0) :
    (-(m / 4) * (1 / (16 * m ^ 2))) / 7 = -(1 / (448 * m)) := by
  field_simp [hm]; ring

/-- Converting density `m = 8N` to the note's constant `gamma = 1/3584`. -/
theorem boolean_gap_density_arithmetic (N : ℝ) (hN : N ≠ 0) :
    -(1 / (448 * (8 * N))) = -((1 / 3584) / N) := by
  field_simp [hN]; ring

/-- A positive radius and nonnegative angular factor give the fourth-power bound. -/
theorem fourth_power_half_bound (s τ : ℝ) (hτ : 0 ≤ τ) (hs : τ / 2 ≤ s) :
    τ ^ 4 ≤ 16 * s ^ 4 := by
  have hhalf : (0 : ℝ) ≤ τ / 2 := by linarith
  have hpow := pow_le_pow_left₀ hhalf hs 4
  nlinarith

/-- The final scalar absorption step in the uniform sphere-transfer argument.

The usual application has `delta > 0` and `A ≥ 0`. Those extra hypotheses are
unnecessary here: if `delta ≤ 0`, nonnegativity of `epsilon` already suffices.
-/
theorem transfer_scalar_bound (A delta epsilon s τ : ℝ)
    (hA : A ≤ 1) (hAdelta : A ≤ delta / 32) (hepsilon : 0 ≤ epsilon)
    (hcert : delta * s ^ 4 - A * τ ^ 4 ≤ (1 + A) * epsilon)
    (hs : τ / 2 ≤ s) (hτ : 0 ≤ τ) :
    delta * τ ^ 4 / 64 ≤ epsilon := by
  have hτfour : 0 ≤ τ ^ 4 := by positivity
  by_cases hdelta : 0 ≤ delta
  · have hpower := fourth_power_half_bound s τ hτ hs
    have hscaled := mul_le_mul_of_nonneg_left hpower hdelta
    have herror := mul_le_mul_of_nonneg_right hAdelta hτfour
    have hcoeff := mul_le_mul_of_nonneg_right hA hepsilon
    nlinarith
  · have hdeltanonpos : delta ≤ 0 := le_of_lt (lt_of_not_ge hdelta)
    have hproduct := mul_nonpos_of_nonpos_of_nonneg hdeltanonpos hτfour
    nlinarith

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
