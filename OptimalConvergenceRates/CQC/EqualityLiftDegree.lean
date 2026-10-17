import OptimalConvergenceRates.CQC.EqualityEmbedding
import OptimalConvergenceRates.CQC.LiftDegree

/-!
# Degree bounds for the equality-aware fixed lift
-/

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

theorem totalDegree_equalitySlackValueSum_le
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    (equalitySlackValueSum g).totalDegree ≤ 1 := by
  unfold equalitySlackValueSum
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e _
  simp

theorem totalDegree_descendedEqualitySlackObjective_le
    {e d : ℕ} (hm : 0 < m) (he : 2 ≤ e)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (M : ℝ)
    (hg : ∀ i, (g i).totalDegree ≤ e)
    (hp : p.totalDegree ≤ d) :
    (descendedEqualitySlackObjective g p M).totalDegree ≤
      d + 4 * m * (e - 1) := by
  have hselected :
      ∀ i, (selectedGenerator g i).totalDegree ≤ e :=
    fun i ↦ hg (selectedRawIndex g i)
  have hcore :=
    totalDegree_descendedSlackObjective_le
      (selectedConstraintCount_pos (g := g) hm) he
      (selectedGenerator g) p M hselected hp
  have hcount := selectedConstraintCount_le g
  have hfactor :
      4 * selectedConstraintCount g * (e - 1) ≤
        4 * m * (e - 1) :=
    Nat.mul_le_mul_right (e - 1) (Nat.mul_le_mul_left 4 hcount)
  have hcore' :
      (descendedSlackObjective (selectedGenerator g) p M).totalDegree ≤
        d + 4 * m * (e - 1) :=
    hcore.trans (Nat.add_le_add_left hfactor d)
  have hextra :
      (C M * equalitySlackValueSum g).totalDegree ≤ 1 := by
    calc
      (C M * equalitySlackValueSum g).totalDegree ≤
          (C M).totalDegree + (equalitySlackValueSum g).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + 1 := Nat.add_le_add (by simp)
        (totalDegree_equalitySlackValueSum_le g)
      _ = 1 := by omega
  have htarget : 1 ≤ d + 4 * m * (e - 1) := by
    have hm1 : 1 ≤ m := hm
    have he1 : 1 ≤ e - 1 := by omega
    have hprod : 1 ≤ 4 * m * (e - 1) := by
      exact one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by norm_num) hm1) he1
    omega
  unfold descendedEqualitySlackObjective
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le hcore' (hextra.trans htarget))

theorem totalDegree_embedded_descendedEqualitySlackObjective_le
    {e d : ℕ} (hm : 0 < m) (he : 2 ≤ e)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (M : ℝ)
    (hg : ∀ i, (g i).totalDegree ≤ e)
    (hp : p.totalDegree ≤ d) :
    (embedSelectedPolynomial g
      (descendedEqualitySlackObjective g p M)).totalDegree ≤
        d + 4 * m * (e - 1) :=
  (totalDegree_embedSelectedPolynomial_le g _).trans
    (totalDegree_descendedEqualitySlackObjective_le hm he g p M hg hp)

theorem totalDegree_unitBoxLiftPolynomial_equality_le
    {e d : ℕ} (hm : 0 < m) (he : 2 ≤ e)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (M R : ℝ)
    (hg : ∀ i, (g i).totalDegree ≤ e)
    (hp : p.totalDegree ≤ d) :
    (unitBoxLiftPolynomial R
      (embedSelectedPolynomial g
        (descendedEqualitySlackObjective g p M))).totalDegree ≤
          d + 4 * m * (e - 1) := by
  calc
    (unitBoxLiftPolynomial R
      (embedSelectedPolynomial g
        (descendedEqualitySlackObjective g p M))).totalDegree ≤
        1 * (embedSelectedPolynomial g
          (descendedEqualitySlackObjective g p M)).totalDegree := by
      exact QuarticConvergence.totalDegree_aeval_le_mul_general
        (unitToSlackValueMap R) (unitToSlackValueMap_totalDegree_le_one R) _
    _ ≤ 1 * (d + 4 * m * (e - 1)) :=
      Nat.mul_le_mul_left 1
        (totalDegree_embedded_descendedEqualitySlackObjective_le
          hm he g p M hg hp)
    _ = d + 4 * m * (e - 1) := by omega

end CQCInternal
end OptimalConvergenceRates

end
