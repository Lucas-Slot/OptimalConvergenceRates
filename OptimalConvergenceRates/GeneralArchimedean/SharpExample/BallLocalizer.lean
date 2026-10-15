/-
  The bounded-degree ball localizer for the truncated signed-moment
  obstruction.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.LocalizingPositivity

noncomputable section

open Finset MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

theorem sharpShiftedMomentScale_two_zero_sq
    {η : ℝ} (hη : 0 < η) (i j : ℕ) :
    sharpShiftedMomentScale η 2 0 i j ^ 2 =
      η ^ 2 * Real.exp (32 * (i : ℝ) + 16) *
        sharpShiftedMomentScale η 0 0 i j ^ 2 := by
  have hsqrt : Real.sqrt η ^ (2 + 0) = η := by
    norm_num [Real.sq_sqrt hη.le]
  have hscale : sharpShiftedMomentScale η 2 0 i j =
      η * Real.exp (16 * (i : ℝ) + 8) *
        sharpShiftedMomentScale η 0 0 i j := by
    unfold sharpShiftedMomentScale
    rw [hsqrt]
    simp only [add_zero, pow_zero, mul_one]
    have hexp :
        Real.exp (2 * ((((2 * i + 2 : ℕ) : ℝ) ^ 2) +
            (((2 * j : ℕ) : ℝ) ^ 2))) =
          Real.exp (16 * (i : ℝ) + 8) *
            Real.exp (2 * ((((2 * i : ℕ) : ℝ) ^ 2) +
              (((2 * j : ℕ) : ℝ) ^ 2))) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  rw [hscale]
  have hexp : Real.exp (16 * (i : ℝ) + 8) ^ 2 =
      Real.exp (32 * (i : ℝ) + 16) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    (η * Real.exp (16 * (i : ℝ) + 8) *
        sharpShiftedMomentScale η 0 0 i j) ^ 2 =
      η ^ 2 * Real.exp (16 * (i : ℝ) + 8) ^ 2 *
        sharpShiftedMomentScale η 0 0 i j ^ 2 := by ring
    _ = _ := by rw [hexp]

theorem sharpShiftedMomentScale_zero_two_sq
    {η : ℝ} (hη : 0 < η) (i j : ℕ) :
    sharpShiftedMomentScale η 0 2 i j ^ 2 =
      η ^ 2 * Real.exp (32 * (j : ℝ) + 16) *
        sharpShiftedMomentScale η 0 0 i j ^ 2 := by
  have hsqrt : Real.sqrt η ^ (0 + 2) = η := by
    norm_num [Real.sq_sqrt hη.le]
  have hscale : sharpShiftedMomentScale η 0 2 i j =
      η * Real.exp (16 * (j : ℝ) + 8) *
        sharpShiftedMomentScale η 0 0 i j := by
    unfold sharpShiftedMomentScale
    rw [hsqrt]
    simp only [add_zero, pow_zero, mul_one]
    have hexp :
        Real.exp (2 * ((((2 * i : ℕ) : ℝ) ^ 2) +
            (((2 * j + 2 : ℕ) : ℝ) ^ 2))) =
          Real.exp (16 * (j : ℝ) + 8) *
            Real.exp (2 * ((((2 * i : ℕ) : ℝ) ^ 2) +
              (((2 * j : ℕ) : ℝ) ^ 2))) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  rw [hscale]
  have hexp : Real.exp (16 * (j : ℝ) + 8) ^ 2 =
      Real.exp (32 * (j : ℝ) + 16) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    (η * Real.exp (16 * (j : ℝ) + 8) *
        sharpShiftedMomentScale η 0 0 i j) ^ 2 =
      η ^ 2 * Real.exp (16 * (j : ℝ) + 8) ^ 2 *
        sharpShiftedMomentScale η 0 0 i j ^ 2 := by ring
    _ = _ := by rw [hexp]

theorem support_coordinate_le_totalDegree
    (q : MvPolynomial (Fin 2) ℝ) {α : Fin 2 →₀ ℕ}
    (hα : α ∈ q.support) (k : Fin 2) : α k ≤ q.totalDegree := by
  exact (Finsupp.le_degree k α).trans (MvPolynomial.le_totalDegree hα)

/-- Positivity of the ball localizer under the explicit bounded-degree
smallness condition used in the moment obstruction. -/
theorem sharpMomentFunctional_ball_sq_nonneg
    {η ρ : ℝ} {D : ℕ} (hη : 0 < η) (hρ : (1 : ℝ) / 2 ≤ ρ)
    (hsmall : η ^ 2 * Real.exp (32 * (D : ℝ) + 16) ≤ (1 : ℝ) / 12)
    (q : MvPolynomial (Fin 2) ℝ) (hdeg : q.totalDegree ≤ D) :
    0 ≤ sharpMomentFunctional η
      ((C ρ - obstructionA ^ 2 - obstructionB ^ 2) * q ^ 2) := by
  let D0 := ∑ α ∈ q.support,
    (q.coeff α * sharpShiftedMomentScale η 0 0 (α 0) (α 1)) ^ 2
  let Da := ∑ α ∈ q.support,
    (q.coeff α * sharpShiftedMomentScale η 2 0 (α 0) (α 1)) ^ 2
  let Db := ∑ α ∈ q.support,
    (q.coeff α * sharpShiftedMomentScale η 0 2 (α 0) (α 1)) ^ 2
  have hDa : Da ≤ (1 / 12 : ℝ) * D0 := by
    dsimp [Da, D0]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro α hα
    have hi : α 0 ≤ D := (support_coordinate_le_totalDegree q hα 0).trans hdeg
    have hiR : ((α 0 : ℕ) : ℝ) ≤ D := by exact_mod_cast hi
    have harg : 32 * ((α 0 : ℕ) : ℝ) + 16 ≤ 32 * (D : ℝ) + 16 := by
      nlinarith
    have hexp := Real.exp_le_exp.mpr harg
    have hratio :
        η ^ 2 * Real.exp (32 * ((α 0 : ℕ) : ℝ) + 16) ≤ (1 : ℝ) / 12 :=
      (mul_le_mul_of_nonneg_left hexp (sq_nonneg η)).trans hsmall
    simp only [mul_pow]
    rw [sharpShiftedMomentScale_two_zero_sq hη]
    have hc : 0 ≤ q.coeff α ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hratio
      (sq_nonneg (q.coeff α * sharpShiftedMomentScale η 0 0 (α 0) (α 1)))]
  have hDb : Db ≤ (1 / 12 : ℝ) * D0 := by
    dsimp [Db, D0]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro α hα
    have hj : α 1 ≤ D := (support_coordinate_le_totalDegree q hα 1).trans hdeg
    have hjR : ((α 1 : ℕ) : ℝ) ≤ D := by exact_mod_cast hj
    have harg : 32 * ((α 1 : ℕ) : ℝ) + 16 ≤ 32 * (D : ℝ) + 16 := by
      nlinarith
    have hexp := Real.exp_le_exp.mpr harg
    have hratio :
        η ^ 2 * Real.exp (32 * ((α 1 : ℕ) : ℝ) + 16) ≤ (1 : ℝ) / 12 :=
      (mul_le_mul_of_nonneg_left hexp (sq_nonneg η)).trans hsmall
    simp only [mul_pow]
    rw [sharpShiftedMomentScale_zero_two_sq hη]
    nlinarith [mul_le_mul_of_nonneg_left hratio
      (sq_nonneg (q.coeff α * sharpShiftedMomentScale η 0 0 (α 0) (α 1)))]
  have h0 := (sharpShiftedMomentFunctional_sq_bounds hη 0 0 q).1
  have ha := (sharpShiftedMomentFunctional_sq_bounds hη 2 0 q).2
  have hb := (sharpShiftedMomentFunctional_sq_bounds hη 0 2 q).2
  simp only [Nat.zero_mul, Nat.mul_zero, pow_zero, one_mul] at h0 ha hb
  change (1 / 2 : ℝ) * D0 ≤ sharpMomentFunctional η
    (monomial (bivarExponent 0 0) 1 * q ^ 2) at h0
  change sharpMomentFunctional η
    (monomial (bivarExponent 2 0) 1 * q ^ 2) ≤ (3 / 2 : ℝ) * Da at ha
  change sharpMomentFunctional η
    (monomial (bivarExponent 0 2) 1 * q ^ 2) ≤ (3 / 2 : ℝ) * Db at hb
  have hD0 : 0 ≤ D0 := by dsimp [D0]; positivity
  have hcompare :
      sharpMomentFunctional η
          (monomial (bivarExponent 2 0) 1 * q ^ 2) +
        sharpMomentFunctional η
          (monomial (bivarExponent 0 2) 1 * q ^ 2) ≤
        ρ * sharpMomentFunctional η
          (monomial (bivarExponent 0 0) 1 * q ^ 2) := by
    have hr := mul_le_mul_of_nonneg_left h0 (by linarith : 0 ≤ ρ)
    nlinarith
  have hzero : monomial (bivarExponent 0 0) (1 : ℝ) =
      (1 : MvPolynomial (Fin 2) ℝ) := by simp [bivarExponent]
  have ha2 : monomial (bivarExponent 2 0) (1 : ℝ) = obstructionA ^ 2 := by
    rw [show bivarExponent 2 0 = Finsupp.single (0 : Fin 2) 2 by
      ext k
      fin_cases k <;> simp [bivarExponent]]
    change monomial (Finsupp.single (0 : Fin 2) 2) 1 =
      monomial (Finsupp.single (0 : Fin 2) 1) 1 ^ 2
    have he : Finsupp.single (0 : Fin 2) 1 + Finsupp.single (0 : Fin 2) 1 =
        Finsupp.single (0 : Fin 2) 2 := by
      ext k
      fin_cases k <;> simp
    rw [pow_two, monomial_mul_monomial, he]
    norm_num
  have hb2 : monomial (bivarExponent 0 2) (1 : ℝ) = obstructionB ^ 2 := by
    rw [show bivarExponent 0 2 = Finsupp.single (1 : Fin 2) 2 by
      ext k
      fin_cases k <;> simp [bivarExponent]]
    change monomial (Finsupp.single (1 : Fin 2) 2) 1 =
      monomial (Finsupp.single (1 : Fin 2) 1) 1 ^ 2
    have he : Finsupp.single (1 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 =
        Finsupp.single (1 : Fin 2) 2 := by
      ext k
      fin_cases k <;> simp
    rw [pow_two, monomial_mul_monomial, he]
    norm_num
  rw [hzero, one_mul, ha2, hb2] at hcompare
  have hρq : sharpMomentFunctional η (C ρ * q ^ 2) =
      ρ * sharpMomentFunctional η (q ^ 2) := by
    rw [← MvPolynomial.smul_eq_C_mul, map_smul]
    rfl
  rw [show (C ρ - obstructionA ^ 2 - obstructionB ^ 2) * q ^ 2 =
      C ρ * q ^ 2 - obstructionA ^ 2 * q ^ 2 - obstructionB ^ 2 * q ^ 2 by ring,
    map_sub, map_sub, hρq]
  linarith

end OptimalConvergenceRates.GeneralArchimedean

end
