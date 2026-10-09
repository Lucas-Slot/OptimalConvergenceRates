import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.OrderConventions
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Elementary inversion of quartic error bounds

This file contains the numerical calculation shared by the cube and CQC
inverse-degree statements.
-/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence

/-- The order obtained by taking the fourth root of `A / epsilon`, while also
respecting a pre-existing minimum order. -/
def quarticInverseOrder (r₀ : ℕ) (A epsilon : ℝ) : ℕ :=
  max r₀ (Nat.ceil ((A / epsilon) ^ ((1 : ℝ) / 4)))

theorem quarticInverseOrder_ge (r₀ : ℕ) (A epsilon : ℝ) :
    r₀ ≤ quarticInverseOrder r₀ A epsilon :=
  Nat.le_max_left _ _

/-- The chosen inverse order makes an `A / r^4` error no larger than the
requested positive perturbation. -/
theorem quarticScale_le_epsilon
    {r₀ : ℕ} (hr₀ : 0 < r₀) {A epsilon : ℝ}
    (hA : 0 ≤ A) (hepsilon : 0 < epsilon) :
    A / (quarticInverseOrder r₀ A epsilon : ℝ) ^ 4 ≤ epsilon := by
  by_cases hAzero : A = 0
  · simpa [hAzero] using hepsilon.le
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
  let x : ℝ := (A / epsilon) ^ ((1 : ℝ) / 4)
  let r : ℕ := quarticInverseOrder r₀ A epsilon
  have hxpos : 0 < x := by
    dsimp [x]
    exact Real.rpow_pos_of_pos (div_pos hApos hepsilon) _
  have hxr : x ≤ (r : ℝ) := by
    dsimp [r, quarticInverseOrder]
    exact (Nat.le_ceil x).trans (by exact_mod_cast Nat.le_max_right r₀ (Nat.ceil x))
  have hx4 : x ^ 4 = A / epsilon := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hA hepsilon.le)]
    norm_num
  have hpow : A / epsilon ≤ (r : ℝ) ^ 4 := by
    rw [← hx4]
    exact pow_le_pow_left₀ hxpos.le hxr 4
  have hrpos : 0 < (r : ℝ) := by
    exact_mod_cast hr₀.trans_le (quarticInverseOrder_ge r₀ A epsilon)
  have hscaled : A ≤ (r : ℝ) ^ 4 * epsilon :=
    (div_le_iff₀ hepsilon).mp hpow
  rw [div_le_iff₀ (pow_pos hrpos 4)]
  simpa [mul_comm] using hscaled

/-- The explicit inverse order is bounded by the threshold plus the fourth
root, up to the unavoidable ceiling error. -/
theorem quarticInverseOrder_lt (r₀ : ℕ) {A epsilon : ℝ}
    (hA : 0 ≤ A) (hepsilon : 0 < epsilon) :
    (quarticInverseOrder r₀ A epsilon : ℝ) <
      (r₀ : ℝ) + (A / epsilon) ^ ((1 : ℝ) / 4) + 1 := by
  let x : ℝ := (A / epsilon) ^ ((1 : ℝ) / 4)
  have hx : 0 ≤ x := Real.rpow_nonneg (div_nonneg hA hepsilon.le) _
  have hceil : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
  have hmax : quarticInverseOrder r₀ A epsilon ≤ r₀ + Nat.ceil x := by
    change max r₀ (Nat.ceil x) ≤ r₀ + Nat.ceil x
    omega
  calc
    (quarticInverseOrder r₀ A epsilon : ℝ) ≤
        (r₀ + Nat.ceil x : ℕ) := by exact_mod_cast hmax
    _ = (r₀ : ℝ) + Nat.ceil x := by push_cast; ring
    _ < (r₀ : ℝ) + (x + 1) := by gcongr
    _ = (r₀ : ℝ) + (A / epsilon) ^ ((1 : ℝ) / 4) + 1 := by
      dsimp [x]
      ring

end OptimalConvergenceRates.QuarticConvergence

end
