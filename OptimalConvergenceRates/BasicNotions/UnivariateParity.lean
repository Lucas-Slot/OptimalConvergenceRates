/-
  Reusable even/odd decompositions for real univariate polynomials.

  This isolates the parity machinery previously developed inside the
  problem-specific lower-bound folders and exposes the square-variable
  contractions needed by the GeneralArchimedean argument.
-/
import OptimalConvergenceRates.BasicNotions.SOS
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Inductions

noncomputable section

namespace OptimalConvergenceRates
namespace UnivariateParity

/-- Contracting exponents by two cannot increase natural degree. -/
theorem contract_two_natDegree_le (P : Polynomial ℝ) :
    (Polynomial.contract 2 P).natDegree ≤ P.natDegree := by
  by_cases hP : P = 0
  · subst P
    rw [show (0 : Polynomial ℝ) = Polynomial.C 0 by simp]
    rw [Polynomial.contract_C]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [Polynomial.coeff_contract (by norm_num : (2 : ℕ) ≠ 0)]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_lt_of_le hn (by omega : n ≤ n * 2))

/-- Projection onto the even powers. -/
noncomputable def evenPart (P : Polynomial ℝ) : Polynomial ℝ :=
  (2 : ℝ)⁻¹ • (P + P.comp (-Polynomial.X))

/-- Projection onto the odd powers. -/
noncomputable def oddPart (P : Polynomial ℝ) : Polynomial ℝ :=
  (2 : ℝ)⁻¹ • (P - P.comp (-Polynomial.X))

theorem evenPart_eval (P : Polynomial ℝ) (t : ℝ) :
    (evenPart P).eval t = (P.eval t + P.eval (-t)) / 2 := by
  dsimp [evenPart]
  simp [Polynomial.eval_add, Polynomial.eval_comp]
  ring

theorem oddPart_eval (P : Polynomial ℝ) (t : ℝ) :
    (oddPart P).eval t = (P.eval t - P.eval (-t)) / 2 := by
  dsimp [oddPart]
  simp [Polynomial.eval_sub, Polynomial.eval_comp]
  ring

theorem evenPart_add_oddPart (P : Polynomial ℝ) :
    evenPart P + oddPart P = P := by
  dsimp [evenPart, oddPart]
  ext n
  simp [Polynomial.coeff_add, Polynomial.coeff_sub]
  ring

theorem coeff_comp_neg_X (P : Polynomial ℝ) (n : ℕ) :
    (P.comp (-Polynomial.X)).coeff n = P.coeff n * (-1 : ℝ) ^ n := by
  rw [show (-Polynomial.X : Polynomial ℝ) =
      Polynomial.C (-1 : ℝ) * Polynomial.X by simp]
  exact Polynomial.comp_C_mul_X_coeff

theorem evenPart_odd_coeff_eq_zero
    (P : Polynomial ℝ) {n : ℕ} (hn : ¬ 2 ∣ n) :
    (evenPart P).coeff n = 0 := by
  have hnodd : Odd n := Nat.not_even_iff_odd.mp <| by
    rw [even_iff_two_dvd]
    exact hn
  have hpow : (-1 : ℝ) ^ n = -1 :=
    (neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℝ) ≠ 1)).mpr hnodd
  dsimp [evenPart]
  rw [Polynomial.coeff_smul, Polynomial.coeff_add, coeff_comp_neg_X, hpow]
  simp

theorem oddPart_even_coeff_eq_zero
    (P : Polynomial ℝ) {n : ℕ} (hn : 2 ∣ n) :
    (oddPart P).coeff n = 0 := by
  have hneven : Even n := even_iff_two_dvd.mpr hn
  have hpow : (-1 : ℝ) ^ n = 1 := hneven.neg_one_pow
  dsimp [oddPart]
  rw [Polynomial.coeff_smul, Polynomial.coeff_sub, coeff_comp_neg_X, hpow]
  simp

theorem evenPart_even_coeff
    (P : Polynomial ℝ) {n : ℕ} (hn : 2 ∣ n) :
    (evenPart P).coeff n = P.coeff n := by
  have hneven : Even n := even_iff_two_dvd.mpr hn
  have hpow : (-1 : ℝ) ^ n = 1 := hneven.neg_one_pow
  dsimp [evenPart]
  rw [Polynomial.coeff_smul, Polynomial.coeff_add, coeff_comp_neg_X, hpow]
  simp
  ring

theorem oddPart_odd_coeff
    (P : Polynomial ℝ) {n : ℕ} (hn : ¬ 2 ∣ n) :
    (oddPart P).coeff n = P.coeff n := by
  have hnodd : Odd n := Nat.not_even_iff_odd.mp <| by
    rw [even_iff_two_dvd]
    exact hn
  have hpow : (-1 : ℝ) ^ n = -1 :=
    (neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℝ) ≠ 1)).mpr hnodd
  dsimp [oddPart]
  rw [Polynomial.coeff_smul, Polynomial.coeff_sub, coeff_comp_neg_X, hpow]
  simp
  ring


theorem evenPart_expand_contract (P : Polynomial ℝ) :
    Polynomial.expand ℝ 2 (Polynomial.contract 2 (evenPart P)) = evenPart P := by
  ext n
  rw [Polynomial.coeff_expand (by norm_num : 0 < (2 : ℕ))]
  by_cases hn : 2 ∣ n
  · rw [ite_eq_left hn, Polynomial.coeff_contract (by norm_num : (2 : ℕ) ≠ 0),
      Nat.div_mul_cancel hn]
  · rw [ite_eq_right hn]
    exact (evenPart_odd_coeff_eq_zero P hn).symm

/-- The odd part has zero constant coefficient. -/
@[simp]
theorem oddPart_coeff_zero (P : Polynomial ℝ) :
    (oddPart P).coeff 0 = 0 :=
  oddPart_even_coeff_eq_zero P (by simp)

/-- Removing one factor of X from the odd part leaves only even powers. -/
theorem divX_oddPart_odd_coeff_eq_zero
    (P : Polynomial ℝ) {n : ℕ} (hn : ¬ 2 ∣ n) :
    (Polynomial.divX (oddPart P)).coeff n = 0 := by
  rw [Polynomial.coeff_divX]
  apply oddPart_even_coeff_eq_zero
  omega

theorem divX_oddPart_expand_contract (P : Polynomial ℝ) :
    Polynomial.expand ℝ 2
        (Polynomial.contract 2 (Polynomial.divX (oddPart P))) =
      Polynomial.divX (oddPart P) := by
  ext n
  rw [Polynomial.coeff_expand (by norm_num : 0 < (2 : ℕ))]
  by_cases hn : 2 ∣ n
  · rw [ite_eq_left hn, Polynomial.coeff_contract (by norm_num : (2 : ℕ) ≠ 0),
      Nat.div_mul_cancel hn]
  · rw [ite_eq_right hn]
    exact (divX_oddPart_odd_coeff_eq_zero P hn).symm

theorem X_mul_divX_oddPart (P : Polynomial ℝ) :
    Polynomial.X * Polynomial.divX (oddPart P) = oddPart P := by
  simpa using Polynomial.X_mul_divX_add (oddPart P)

/-- Even powers re-indexed as a polynomial in the squared variable. -/
noncomputable def evenContract (P : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.contract 2 (evenPart P)

/-- Odd powers after removing one X, re-indexed in the squared variable. -/
noncomputable def oddContract (P : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.contract 2 (Polynomial.divX (oddPart P))

theorem evenContract_eval_sq (P : Polynomial ℝ) (t : ℝ) :
    (evenContract P).eval (t ^ 2) = (evenPart P).eval t := by
  have h := congrArg (fun Q : Polynomial ℝ => Q.eval t) (evenPart_expand_contract P)
  simpa [evenContract] using h

theorem oddContract_eval_sq (P : Polynomial ℝ) (t : ℝ) :
    t * (oddContract P).eval (t ^ 2) = (oddPart P).eval t := by
  have hcontract := congrArg (fun Q : Polynomial ℝ => Q.eval t)
    (divX_oddPart_expand_contract P)
  have hmul := congrArg (fun Q : Polynomial ℝ => Q.eval t) (X_mul_divX_oddPart P)
  simp only [Polynomial.eval_mul, Polynomial.eval_X] at hmul
  have hcontract' : (Polynomial.divX (oddPart P)).eval t =
      (oddContract P).eval (t ^ 2) := by
    simpa [oddContract] using hcontract.symm
  rw [hcontract'] at hmul
  exact hmul

/-- Canonical decomposition P(t) = P0(t^2) + t V0(t^2). -/
theorem eval_evenContract_add_oddContract (P : Polynomial ℝ) (t : ℝ) :
    P.eval t =
      (evenContract P).eval (t ^ 2) + t * (oddContract P).eval (t ^ 2) := by
  have hparts := congrArg (fun Q : Polynomial ℝ => Q.eval t) (evenPart_add_oddPart P)
  simp only [Polynomial.eval_add] at hparts
  rw [evenContract_eval_sq, oddContract_eval_sq]
  exact hparts.symm

theorem evenPart_natDegree_le (P : Polynomial ℝ) :
    (evenPart P).natDegree ≤ P.natDegree := by
  dsimp [evenPart]
  calc
    ((2 : ℝ)⁻¹ • (P + P.comp (-Polynomial.X))).natDegree
        ≤ (P + P.comp (-Polynomial.X)).natDegree := Polynomial.natDegree_smul_le _ _
    _ ≤ max P.natDegree (P.comp (-Polynomial.X)).natDegree :=
      Polynomial.natDegree_add_le _ _
    _ ≤ P.natDegree := by
      apply max_le
      · exact le_rfl
      · calc
          (P.comp (-Polynomial.X)).natDegree
              ≤ P.natDegree * (-Polynomial.X : Polynomial ℝ).natDegree :=
            Polynomial.natDegree_comp_le
          _ ≤ P.natDegree * 1 := by
            exact Nat.mul_le_mul_left _ <|
              Polynomial.natDegree_neg_le_of_le Polynomial.natDegree_X_le
          _ = P.natDegree := by omega

theorem oddPart_natDegree_le (P : Polynomial ℝ) :
    (oddPart P).natDegree ≤ P.natDegree := by
  dsimp [oddPart]
  calc
    ((2 : ℝ)⁻¹ • (P - P.comp (-Polynomial.X))).natDegree
        ≤ (P - P.comp (-Polynomial.X)).natDegree := Polynomial.natDegree_smul_le _ _
    _ ≤ max P.natDegree (P.comp (-Polynomial.X)).natDegree :=
      Polynomial.natDegree_sub_le _ _
    _ ≤ P.natDegree := by
      apply max_le
      · exact le_rfl
      · calc
          (P.comp (-Polynomial.X)).natDegree
              ≤ P.natDegree * (-Polynomial.X : Polynomial ℝ).natDegree :=
            Polynomial.natDegree_comp_le
          _ ≤ P.natDegree * 1 := by
            exact Nat.mul_le_mul_left _ <|
              Polynomial.natDegree_neg_le_of_le Polynomial.natDegree_X_le
          _ = P.natDegree := by omega

theorem evenContract_natDegree_le (P : Polynomial ℝ) :
    (evenContract P).natDegree ≤ P.natDegree :=
  (contract_two_natDegree_le (evenPart P)).trans (evenPart_natDegree_le P)

theorem oddContract_natDegree_le (P : Polynomial ℝ) :
    (oddContract P).natDegree ≤ P.natDegree :=
  (contract_two_natDegree_le (Polynomial.divX (oddPart P))).trans <|
    Polynomial.natDegree_divX_le.trans (oddPart_natDegree_le P)

/-- The polynomial obtained by multiplying the parity decomposition by its
sign-conjugate. -/
noncomputable def conjugateProduct (P : Polynomial ℝ) : Polynomial ℝ :=
  evenContract P ^ 2 - Polynomial.X * oddContract P ^ 2

theorem conjugateProduct_eval_sq (P : Polynomial ℝ) (t : ℝ) :
    (conjugateProduct P).eval (t ^ 2) = P.eval t * P.eval (-t) := by
  have hpos := eval_evenContract_add_oddContract P t
  have hneg := eval_evenContract_add_oddContract P (-t)
  simp only [neg_sq] at hneg
  simp only [conjugateProduct, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_mul, Polynomial.eval_X]
  rw [hpos, hneg]
  ring

end UnivariateParity
end OptimalConvergenceRates

end
