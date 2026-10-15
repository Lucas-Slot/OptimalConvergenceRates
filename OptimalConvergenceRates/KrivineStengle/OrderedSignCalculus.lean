/-
  OptimalConvergenceRates/KrivineStengle/OrderedSignCalculus.lean

  Multiplicative and finite-product identities for the three-valued
  ordered sign.  These are the combinatorial core of strict root counting.
-/
import OptimalConvergenceRates.KrivineStengle.Signature

noncomputable section

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

@[simp] theorem orderedSign_one : orderedSign (1 : F) = 1 := by
  simp [orderedSign]

@[simp] theorem orderedSign_eq_zero_iff {a : F} : orderedSign a = 0 ↔ a = 0 := by
  rcases lt_trichotomy 0 a with ha | rfl | ha
  · simp [orderedSign, ha, ne_of_gt ha]
  · simp
  · simp [orderedSign, ha, not_lt_of_ge ha.le, ne_of_lt ha]

/-- Ordered sign is multiplicative. -/
theorem orderedSign_mul (a b : F) :
    orderedSign (a * b) = orderedSign a * orderedSign b := by
  rcases lt_trichotomy 0 a with ha | rfl | ha <;>
    rcases lt_trichotomy 0 b with hb | rfl | hb
  · have hab := mul_pos ha hb
    simp [orderedSign, ha, hb, hab]
  · simp
  · have hab : a * b < 0 := mul_neg_of_pos_of_neg ha hb
    simp [orderedSign, ha, hb, hab, not_lt_of_ge hb.le,
      not_lt_of_ge hab.le]
  · simp
  · simp
  · simp
  · have hab : a * b < 0 := mul_neg_of_neg_of_pos ha hb
    simp [orderedSign, ha, hb, hab, not_lt_of_ge ha.le,
      not_lt_of_ge hab.le]
  · simp
  · have hab : 0 < a * b := mul_pos_of_neg_of_neg ha hb
    simp [orderedSign, ha, hb, hab, not_lt_of_ge ha.le,
      not_lt_of_ge hb.le]

/-- A nonzero square has ordered sign one. -/
theorem orderedSign_sq (a : F) :
    orderedSign (a ^ 2) = if a = 0 then 0 else 1 := by
  by_cases ha : a = 0
  · simp [ha]
  · have hsq : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    simp [orderedSign, ha, hsq]

/-- Ordered sign commutes with a finite product. -/
theorem orderedSign_prod {I : Type*} (s : Finset I) (a : I → F) :
    orderedSign (∏ i ∈ s, a i) = ∏ i ∈ s, orderedSign (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, orderedSign_mul, ih]

/-- Summing the first and second powers of a sign selects strict positivity. -/
theorem sum_orderedSign_pow_one_two (a : F) :
    (∑ j : Fin 2, orderedSign (a ^ (j.1 + 1))) =
      if 0 < a then 2 else 0 := by
  rw [Fin.sum_univ_two]
  norm_num only [Fin.val_zero, Fin.val_one, pow_one]
  rw [orderedSign_sq]
  by_cases ha : a = 0
  · simp [ha]
  · by_cases hpos : 0 < a
    · rw [ite_eq_right ha, orderedSign_eq_one_iff.mpr hpos, ite_eq_left hpos]
      norm_num
    · have hneg : a < 0 := lt_of_le_of_ne (le_of_not_gt hpos) ha
      rw [ite_eq_right ha, orderedSign_eq_neg_one_iff.mpr hneg, ite_eq_right hpos]
      norm_num

/-- The `{1,2}` exponent sum is `2^s` exactly when all entries are
strictly positive, and is zero otherwise. -/
theorem sum_orderedSign_products_pow_one_two {s : ℕ} (a : Fin s → F) :
    (∑ exponent : Fin s → Fin 2,
        orderedSign (∏ i, a i ^ (exponent i).1.succ)) =
      if ∀ i, 0 < a i then (2 : ℤ) ^ s else 0 := by
  classical
  calc
    (∑ exponent : Fin s → Fin 2,
        orderedSign (∏ i, a i ^ (exponent i).1.succ)) =
        ∑ exponent : Fin s → Fin 2,
          ∏ i, orderedSign (a i ^ (exponent i).1.succ) := by
            apply Finset.sum_congr rfl
            intro exponent _
            simpa using orderedSign_prod (Finset.univ : Finset (Fin s))
              (fun i ↦ a i ^ (exponent i).1.succ)
    _ = ∏ i : Fin s, ∑ j : Fin 2, orderedSign (a i ^ j.1.succ) := by
      rw [Fintype.prod_sum]
    _ = ∏ i : Fin s, if 0 < a i then 2 else 0 := by
      apply Finset.prod_congr rfl
      intro i _
      exact sum_orderedSign_pow_one_two (a i)
    _ = if ∀ i, 0 < a i then (2 : ℤ) ^ s else 0 := by
      by_cases h : ∀ i, 0 < a i
      · simp [h]
      · simp only [h, ite_false]
        push Not at h
        obtain ⟨i, hi⟩ := h
        exact Finset.prod_eq_zero (Finset.mem_univ i)
          (ite_eq_right (not_lt_of_ge hi))

end OptimalConvergenceRates.KrivineStengle

end
