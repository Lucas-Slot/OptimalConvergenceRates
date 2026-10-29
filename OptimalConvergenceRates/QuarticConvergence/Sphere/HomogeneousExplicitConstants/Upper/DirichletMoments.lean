import Mathlib.Analysis.Real.Pi.Bounds
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.DirichletBounds

/-!
# Actual one-dimensional angular moments of the quotient Dirichlet kernel

These integrals are on `[0,π]` with angular density `sin θ^(n-2)`.
No identification with a spherical measure or SOS repair operator is asserted.
-/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants

open MeasureTheory Set
open scoped Interval

def angularDirichletMass (n k : ℕ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi, angularDirichletWeight n k θ

def angularDirichletMoment (n k j : ℕ) : ℝ :=
  (∫ θ in (0 : ℝ)..Real.pi, θ ^ j * angularDirichletWeight n k θ) /
    angularDirichletMass n k

def angularDirichletMassLower (n k : ℕ) : ℝ :=
  ((2 / Real.pi) ^ (n - 2) / ((n : ℝ) - 1)) * (k : ℝ) ^ (n + 7)

theorem angularDirichletMass_lower (n k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k) :
    angularDirichletMassLower n k ≤ angularDirichletMass n k := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have ha0 : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  have haPi : 1 / (k : ℝ) ≤ Real.pi := by
    have ha1 := (div_le_one hkpos).2 hkR
    linarith [Real.pi_gt_three]
  let C : ℝ := (k : ℝ) ^ (2 * (n + 3)) * (2 / Real.pi) ^ (n - 2)
  have hcap : (∫ θ in (0 : ℝ)..(1 / (k : ℝ)), C * θ ^ (n - 2)) ≤
      ∫ θ in (0 : ℝ)..(1 / (k : ℝ)), angularDirichletWeight n k θ := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo ha0
      ((continuous_const.mul (continuous_pow _)).intervalIntegrable _ _)
      (angularDirichletWeight_intervalIntegrable n k _ _)
    intro θ hθ
    exact angularDirichletWeight_lower n k hk hθ.1 hθ.2.le
  have hcapEval : (∫ θ in (0 : ℝ)..(1 / (k : ℝ)), C * θ ^ (n - 2)) =
      angularDirichletMassLower n k := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    rw [show n - 2 + 1 = n - 1 by omega]
    rw [zero_pow (by omega : n - 1 ≠ 0), sub_zero]
    dsimp [C, angularDirichletMassLower]
    rw [show 2 * (n + 3) = (n + 7) + (n - 1) by omega, pow_add]
    simp only [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_ofNat, div_pow, one_pow]
    rw [show (n : ℝ) - 2 + 1 = (n : ℝ) - 1 by ring]
    have hnsubne : (n : ℝ) - 1 ≠ 0 := by linarith
    field_simp [hkpos.ne', Real.pi_ne_zero, hnsubne]
  have hsubset : (∫ θ in (0 : ℝ)..(1 / (k : ℝ)), angularDirichletWeight n k θ) ≤
      angularDirichletMass n k := by
    apply intervalIntegral.integral_mono_interval le_rfl ha0 haPi
      ?_ (angularDirichletWeight_intervalIntegrable n k 0 Real.pi)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with θ hθ
    exact angularDirichletWeight_nonneg n k ⟨hθ.1.le, hθ.2⟩
  exact hcapEval ▸ hcap.trans hsubset

theorem angularDirichletMass_pos (n k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k) :
    0 < angularDirichletMass n k := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnsub : 0 < (n : ℝ) - 1 := by linarith
  have hkpos : (0 : ℝ) < k := by linarith
  have hlower : 0 < angularDirichletMassLower n k := by
    unfold angularDirichletMassLower
    positivity
  exact hlower.trans_le (angularDirichletMass_lower n k hn hk)

/-- A finite-interval inverse-power tail estimate with its endpoint term retained. -/
theorem integral_inverse_pow (m : ℕ) (hm : 0 < m) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ θ in a..b, 1 / θ ^ (m + 1)) = (1 / a ^ m - 1 / b ^ m) / (m : ℝ) := by
  have hzero : (0 : ℝ) ∉ [[a, b]] := by
    rw [uIcc_of_le hab]
    intro h
    linarith [h.1]
  have hexp : (-(m : ℤ) - 1 : ℤ) ≠ -1 := by omega
  have hfun : (fun θ : ℝ ↦ 1 / θ ^ (m + 1)) = fun θ ↦ θ ^ (-(m : ℤ) - 1) := by
    funext θ
    rw [show (-(m : ℤ) - 1 : ℤ) = -((m + 1 : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast, one_div]
  rw [hfun, integral_zpow (Or.inr ⟨hexp, hzero⟩)]
  rw [show (-(m : ℤ) - 1 + 1 : ℤ) = -(m : ℤ) by omega]
  simp only [zpow_neg, zpow_natCast, Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one,
    one_div]
  rw [show -(m : ℝ) - 1 + 1 = -(m : ℝ) by ring]
  ring

theorem integral_inverse_pow_le (m : ℕ) (hm : 0 < m) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ θ in a..b, 1 / θ ^ (m + 1)) ≤ 1 / ((m : ℝ) * a ^ m) := by
  rw [integral_inverse_pow m hm ha hab]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hb : 0 < b := ha.trans_le hab
  calc
    (1 / a ^ m - 1 / b ^ m) / (m : ℝ) ≤ (1 / a ^ m) / (m : ℝ) := by
      exact div_le_div_of_nonneg_right (sub_le_self _ (by positivity)) hmR.le
    _ = 1 / ((m : ℝ) * a ^ m) := by ring

theorem angularDirichletMoment_inner_le (n k j : ℕ) {a : ℝ}
    (ha : 0 ≤ a) (haPi : a ≤ Real.pi) :
    (∫ θ in (0 : ℝ)..a, θ ^ j * angularDirichletWeight n k θ) ≤
      a ^ j * angularDirichletMass n k := by
  have hinner : (∫ θ in (0 : ℝ)..a, θ ^ j * angularDirichletWeight n k θ) ≤
      ∫ θ in (0 : ℝ)..a, a ^ j * angularDirichletWeight n k θ := by
    apply intervalIntegral.integral_mono_on ha
      (angularDirichletMoment_intervalIntegrable n k j _ _)
      ((angularDirichletWeight_intervalIntegrable n k _ _).const_mul _)
    intro θ hθ
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hθ.1 hθ.2 j)
      (angularDirichletWeight_nonneg n k ⟨hθ.1, hθ.2.trans haPi⟩)
  rw [intervalIntegral.integral_const_mul] at hinner
  have hmass : (∫ θ in (0 : ℝ)..a, angularDirichletWeight n k θ) ≤
      angularDirichletMass n k := by
    apply intervalIntegral.integral_mono_interval le_rfl ha haPi
      ?_ (angularDirichletWeight_intervalIntegrable n k 0 Real.pi)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with θ hθ
    exact angularDirichletWeight_nonneg n k ⟨hθ.1.le, hθ.2⟩
  exact hinner.trans (mul_le_mul_of_nonneg_left hmass (pow_nonneg ha j))

theorem angularDirichletMoment_le_large_radius (n k j : ℕ) {a : ℝ}
    (haPi : Real.pi ≤ a) :
    (∫ θ in (0 : ℝ)..Real.pi, θ ^ j * angularDirichletWeight n k θ) ≤
      a ^ j * angularDirichletMass n k := by
  unfold angularDirichletMass
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on Real.pi_pos.le
    (angularDirichletMoment_intervalIntegrable n k j _ _)
    ((angularDirichletWeight_intervalIntegrable n k _ _).const_mul _)
  intro θ hθ
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hθ.1 (hθ.2.trans haPi) j)
    (angularDirichletWeight_nonneg n k hθ)

/-- The actual kernel integral split at any positive radius, given a scalar
inverse-power envelope on its tail. -/
theorem angularDirichletMoment_split_le (n k j m : ℕ) (hm : 0 < m) {a B : ℝ}
    (ha : 0 < a) (haPi : a ≤ Real.pi) (hB : 0 ≤ B)
    (htail : ∀ θ ∈ Icc a Real.pi,
      θ ^ j * angularDirichletWeight n k θ ≤ B * (1 / θ ^ (m + 1))) :
    (∫ θ in (0 : ℝ)..Real.pi, θ ^ j * angularDirichletWeight n k θ) ≤
      a ^ j * angularDirichletMass n k + B / ((m : ℝ) * a ^ m) := by
  have hinv : IntervalIntegrable (fun θ : ℝ ↦ 1 / θ ^ (m + 1)) volume a Real.pi := by
    have hc : ContinuousOn (fun θ : ℝ ↦ 1 / θ ^ (m + 1)) (Icc a Real.pi) :=
      continuousOn_const.div (continuousOn_id.pow _)
        (fun θ hθ ↦ pow_ne_zero _ (ne_of_gt (ha.trans_le hθ.1)))
    apply hc.intervalIntegrable_of_Icc haPi
  have htailInt : (∫ θ in a..Real.pi, θ ^ j * angularDirichletWeight n k θ) ≤
      B / ((m : ℝ) * a ^ m) := by
    calc
      _ ≤ ∫ θ in a..Real.pi, B * (1 / θ ^ (m + 1)) :=
        intervalIntegral.integral_mono_on haPi
          (angularDirichletMoment_intervalIntegrable n k j _ _) (hinv.const_mul B) htail
      _ = B * ∫ θ in a..Real.pi, 1 / θ ^ (m + 1) := intervalIntegral.integral_const_mul _ _
      _ ≤ B * (1 / ((m : ℝ) * a ^ m)) :=
        mul_le_mul_of_nonneg_left (integral_inverse_pow_le m hm ha haPi) hB
      _ = _ := by ring
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (angularDirichletMoment_intervalIntegrable n k j 0 a)
    (angularDirichletMoment_intervalIntegrable n k j a Real.pi)]
  exact add_le_add (angularDirichletMoment_inner_le n k j ha.le haPi) htailInt

theorem angularDirichletMoment_pointwise_tail (n k j m : ℕ)
    (hexp : j + (n - 2) + (m + 1) = 2 * (n + 3)) {θ : ℝ}
    (hθ0 : 0 < θ) (hθpi : θ ≤ Real.pi) :
    θ ^ j * angularDirichletWeight n k θ ≤
      Real.pi ^ (2 * (n + 3)) * (1 / θ ^ (m + 1)) := by
  have hD := quotientDirichlet_abs_upper k hθ0 hθpi
  have hsin := Real.sin_le hθ0.le
  have hsin0 := Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le hθpi
  have hweight : angularDirichletWeight n k θ ≤
      (Real.pi / θ) ^ (2 * (n + 3)) * θ ^ (n - 2) :=
    mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hD _)
      (pow_le_pow_left₀ hsin0 hsin _) (by positivity) (by positivity)
  have hid : θ ^ j * ((Real.pi / θ) ^ (2 * (n + 3)) * θ ^ (n - 2)) =
      Real.pi ^ (2 * (n + 3)) * (1 / θ ^ (m + 1)) := by
    rw [div_pow, ← hexp]
    simp only [pow_add]
    field_simp
  exact (mul_le_mul_of_nonneg_left hweight (pow_nonneg hθ0.le j)).trans_eq hid

/-- Actual normalized moment bound from exponent bookkeeping and one scalar
identity matching the raw tail to the proved normalization lower bound. -/
theorem angularDirichletMoment_le_of_tail_identity
    (n k j m : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k) (hm : 0 < m)
    (hexp : j + (n - 2) + (m + 1) = 2 * (n + 3)) (C : ℝ) (hC : 0 ≤ C)
    (hid : Real.pi ^ (2 * (n + 3)) / ((m : ℝ) * (32 / (k : ℝ)) ^ m) =
      C * angularDirichletMassLower n k / (k : ℝ) ^ j) :
    angularDirichletMoment n k j ≤ ((32 : ℝ) ^ j + C) / (k : ℝ) ^ j := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  let a : ℝ := 32 / (k : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htail0 : 0 ≤ Real.pi ^ (2 * (n + 3)) / ((m : ℝ) * a ^ m) := by positivity
  have hraw : (∫ θ in (0 : ℝ)..Real.pi, θ ^ j * angularDirichletWeight n k θ) ≤
      a ^ j * angularDirichletMass n k +
        Real.pi ^ (2 * (n + 3)) / ((m : ℝ) * a ^ m) := by
    by_cases haPi : a ≤ Real.pi
    · apply angularDirichletMoment_split_le n k j m hm ha haPi (by positivity)
      intro θ hθ
      exact angularDirichletMoment_pointwise_tail n k j m hexp (ha.trans_le hθ.1) hθ.2
    · exact (angularDirichletMoment_le_large_radius n k j (le_of_not_ge haPi)).trans
        (le_add_of_nonneg_right htail0)
  have htail : Real.pi ^ (2 * (n + 3)) / ((m : ℝ) * a ^ m) ≤
      C * angularDirichletMass n k / (k : ℝ) ^ j := by
    rw [hid]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (angularDirichletMass_lower n k hn hk) hC)
      (by positivity)
  unfold angularDirichletMoment
  apply (div_le_iff₀ (angularDirichletMass_pos n k hn hk)).2
  calc
    _ ≤ a ^ j * angularDirichletMass n k + C * angularDirichletMass n k / (k : ℝ) ^ j :=
      hraw.trans (add_le_add le_rfl htail)
    _ = (((32 : ℝ) ^ j + C) / (k : ℝ) ^ j) * angularDirichletMass n k := by
      dsimp [a]
      rw [div_pow]
      ring

theorem angularDirichlet_second_tail_identity (n k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k) :
    Real.pi ^ (2 * (n + 3)) / (((n + 5 : ℕ) : ℝ) * (32 / (k : ℝ)) ^ (n + 5)) =
      dirichletSecondTailConstant n * angularDirichletMassLower n k / (k : ℝ) ^ 2 := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hnsub : (n : ℝ) - 1 ≠ 0 := by linarith
  have hnplus : (n : ℝ) + 5 ≠ 0 := by positivity
  unfold dirichletSecondTailConstant angularDirichletMassLower
  rw [show n + 7 = (n + 5) + 2 by omega, pow_add]
  simp only [Nat.cast_add, Nat.cast_ofNat, div_pow]
  field_simp [hkpos.ne', Real.pi_ne_zero, hnsub, hnplus]
  ring

theorem angularDirichlet_fourth_tail_identity (n k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k) :
    Real.pi ^ (2 * (n + 3)) / (((n + 3 : ℕ) : ℝ) * (32 / (k : ℝ)) ^ (n + 3)) =
      dirichletFourthTailConstant n * angularDirichletMassLower n k / (k : ℝ) ^ 4 := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hnsub : (n : ℝ) - 1 ≠ 0 := by linarith
  have hnplus : (n : ℝ) + 3 ≠ 0 := by positivity
  unfold dirichletFourthTailConstant angularDirichletMassLower
  rw [show n + 7 = (n + 3) + 4 by omega, pow_add]
  simp only [Nat.cast_add, Nat.cast_ofNat, div_pow]
  field_simp [hkpos.ne', Real.pi_ne_zero, hnsub, hnplus]
  ring

/-- Uniform second angular moment for the actual quotient kernel. -/
theorem angularDirichlet_second_moment_le (n k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k) :
    angularDirichletMoment n k 2 ≤ 1025 / (k : ℝ) ^ 2 := by
  have h := angularDirichletMoment_le_of_tail_identity n k 2 (n + 5) hn hk (by omega)
    (by omega) (dirichletSecondTailConstant n) (dirichlet_second_tail_constant_nonneg n hn)
    (angularDirichlet_second_tail_identity n k hn hk)
  exact h.trans (div_le_div_of_nonneg_right (dirichlet_second_moment_constant_le n hn) (by
    positivity))

/-- Uniform fourth angular moment for the actual quotient kernel. -/
theorem angularDirichlet_fourth_moment_le (n k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k) :
    angularDirichletMoment n k 4 ≤ 1048577 / (k : ℝ) ^ 4 := by
  have h := angularDirichletMoment_le_of_tail_identity n k 4 (n + 3) hn hk (by omega)
    (by omega) (dirichletFourthTailConstant n) (dirichlet_fourth_tail_constant_nonneg n hn)
    (angularDirichlet_fourth_tail_identity n k hn hk)
  exact h.trans (div_le_div_of_nonneg_right (dirichlet_fourth_moment_constant_le n hn) (by
    positivity))

end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
