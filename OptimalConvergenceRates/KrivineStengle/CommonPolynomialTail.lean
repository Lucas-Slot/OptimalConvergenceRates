/-
  OptimalConvergenceRates/KrivineStengle/CommonPolynomialTail.lean

  Common positive tails for finite polynomial families.
-/
import OptimalConvergenceRates.KrivineStengle.PolynomialTailSigns

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-- For a nonzero polynomial, eventual positivity at positive infinity is
equivalent to positivity of its leading coefficient. -/
theorem exists_forall_gt_eval_pos_iff_leadingCoeff_pos {p : R[X]}
    (hp0 : p ≠ 0) :
    (∃ B : R, ∀ x, B < x → 0 < p.eval x) ↔
      0 < p.leadingCoeff := by
  constructor
  · rintro ⟨B, hB⟩
    rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hp0) with hlead | hlead
    · have hnegLead : 0 < (-p).leadingCoeff := by simpa using hlead
      obtain ⟨C, hC⟩ := exists_forall_gt_eval_pos_of_leadingCoeff_pos hnegLead
      let x := max B C + 1
      have hBx : B < x := lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
      have hCx : C < x := lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
      have hp := hB x hBx
      have hnp := hC x hCx
      simp only [eval_neg] at hnp
      linarith
    · exact hlead
  · exact exists_forall_gt_eval_pos_of_leadingCoeff_pos

/-- A finite family whose members all have positive leading coefficient
has one common positive tail. -/
theorem exists_common_positive_tail
    (fs : List R[X])
    (hfs : ∀ p ∈ fs, p ≠ 0 ∧ 0 < p.leadingCoeff) :
    ∃ B : R, ∀ x, B < x → ∀ p ∈ fs, 0 < p.eval x := by
  induction fs with
  | nil => exact ⟨0, by simp⟩
  | cons p fs ih =>
      have hp := hfs p (by simp)
      have hrest : ∀ q ∈ fs, q ≠ 0 ∧ 0 < q.leadingCoeff := by
        intro q hq
        exact hfs q (by simp [hq])
      obtain ⟨Bp, hBp⟩ := exists_forall_gt_eval_pos_of_leadingCoeff_pos hp.2
      obtain ⟨Br, hBr⟩ := ih hrest
      refine ⟨max Bp Br, ?_⟩
      intro x hx q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hBp x (lt_of_le_of_lt (le_max_left _ _) hx)
      · exact hBr x (lt_of_le_of_lt (le_max_right _ _) hx) q hq

/-- Exact finite-family positive-tail criterion. -/
theorem exists_common_positive_tail_iff (fs : List R[X]) :
    (∃ B : R, ∀ x, B < x → ∀ p ∈ fs, 0 < p.eval x) ↔
      ∀ p ∈ fs, p ≠ 0 ∧ 0 < p.leadingCoeff := by
  constructor
  · rintro ⟨B, hB⟩ p hp
    have hp0 : p ≠ 0 := by
      intro hpzero
      have hcontra := hB (B + 1) (lt_add_one B) p hp
      simp [hpzero] at hcontra
    refine ⟨hp0, (exists_forall_gt_eval_pos_iff_leadingCoeff_pos hp0).1 ?_⟩
    exact ⟨B, fun x hx ↦ hB x hx p hp⟩
  · exact exists_common_positive_tail fs

end OptimalConvergenceRates.KrivineStengle

end
