/-
  OptimalConvergenceRates/MarkovInequality/ChebyshevExtrema.lean

  Chebyshev extremal nodes, derivative roots, and differential identities for Markov inequalities.
-/
import OptimalConvergenceRates.Chebyshev.ChebyshevGrowth
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

open Polynomial Finset
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates

/-!
## Chebyshev specialization support
-/

/-- Chebyshev extremal nodes, ordered increasingly from  to . -/
noncomputable def chebyshevExtremalNode (d : ℕ) : Fin (d + 1) → ℝ :=
  fun i => Polynomial.Chebyshev.node d (d - i.val)

/-- The reversed Mathlib Chebyshev nodes are strictly increasing. -/
theorem chebyshevExtremalNode_strictMono (d : ℕ) :
    StrictMono (chebyshevExtremalNode d) := by
  intro i j hij
  unfold chebyshevExtremalNode
  have hsub_lt : d - j.val < d - i.val := by omega
  have hle : d - i.val ≤ d := Nat.sub_le _ _
  exact Polynomial.Chebyshev.node_lt hle hsub_lt

/-- The leftmost Chebyshev extremal node is minus one. -/
theorem chebyshevExtremalNode_left {d : ℕ} (hd : d ≠ 0) :
    chebyshevExtremalNode d 0 = -1 := by
  unfold chebyshevExtremalNode
  simp only [Fin.val_zero, tsub_zero]
  exact Polynomial.Chebyshev.node_eq_neg_one hd

/-- The rightmost Chebyshev extremal node is one. -/
theorem chebyshevExtremalNode_right (d : ℕ) :
    chebyshevExtremalNode d ⟨d, by omega⟩ = 1 := by
  unfold chebyshevExtremalNode
  simp [Polynomial.Chebyshev.node_eq_one]

/-- Chebyshev has absolute value one at every extremal node. -/
theorem chebyshevT_eval_extremalNode_abs (d : ℕ) (i : Fin (d + 1)) :
    |(chebyshevT d).eval (chebyshevExtremalNode d i)| = 1 := by
  unfold chebyshevExtremalNode
  rw [chebyshevT_eq_T_nat]
  have hle : d - i.val ≤ d := Nat.sub_le _ _
  rw [Polynomial.Chebyshev.eval_T_real_node (Finset.mem_Iic.mpr hle)]
  rw [abs_pow, abs_neg, abs_one, one_pow]

/-- Adjacent Chebyshev extremal values have opposite signs. -/
theorem chebyshevT_extremalNode_adjacent_mul_neg (d : ℕ) (i : Fin d) :
    (chebyshevT d).eval (chebyshevExtremalNode d ⟨i.val, by omega⟩) *
      (chebyshevT d).eval (chebyshevExtremalNode d ⟨i.val + 1, by omega⟩) < 0 := by
  unfold chebyshevExtremalNode
  rw [chebyshevT_eq_T_nat]
  have hle1 : d - i.val ≤ d := Nat.sub_le _ _
  have hle2 : d - (i.val + 1) ≤ d := Nat.sub_le _ _
  rw [Polynomial.Chebyshev.eval_T_real_node (Finset.mem_Iic.mpr hle1)]
  rw [Polynomial.Chebyshev.eval_T_real_node (Finset.mem_Iic.mpr hle2)]
  have hsucc : d - i.val = d - (i.val + 1) + 1 := by omega
  rw [hsucc, pow_succ]
  norm_num

/-- Roots of the derivative of a Chebyshev polynomial in cosine form. -/
theorem chebyshevT_derivative_eq_zero_iff_exists_cos
    {d : ℕ} (hd : 1 ≤ d) (x : ℝ) :
    (Polynomial.derivative (chebyshevT d)).eval x = 0 ↔
      ∃ k : ℕ, k < d - 1 ∧ x = Real.cos ((k + 1) * Real.pi / d) := by
  rw [chebyshevT_eq_T_nat, Polynomial.Chebyshev.T_derivative_eq_U]
  simp only [Polynomial.eval_mul, Polynomial.eval_intCast]
  rw [mul_eq_zero_iff_left]
  · have hcast : (↑d - 1 : ℤ) = ↑(d - 1 : ℕ) := by omega
    have hden : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by
      norm_num [Nat.cast_sub hd]
    constructor
    · intro hx
      have hne : Polynomial.Chebyshev.U ℝ (↑d - 1 : ℤ) ≠ 0 := by
        rw [hcast]
        exact Polynomial.degree_ne_bot.mp (by rw [Polynomial.Chebyshev.degree_U_natCast]; simp)
      have hxmem : x ∈ (Polynomial.Chebyshev.U ℝ (↑d - 1 : ℤ)).roots :=
        (Polynomial.mem_roots hne).mpr hx
      rw [hcast, Polynomial.Chebyshev.roots_U_real, Finset.mem_val] at hxmem
      obtain ⟨k, hk, hxk⟩ := Finset.mem_image.mp hxmem
      refine ⟨k, Finset.mem_range.mp hk, ?_⟩
      rw [← hxk, hden]
    · rintro ⟨k, hk, rfl⟩
      rw [hcast]
      have hxmem : Real.cos ((k + 1) * Real.pi / ↑d) ∈
          (Polynomial.Chebyshev.U ℝ (d - 1 : ℕ)).roots := by
        rw [Polynomial.Chebyshev.roots_U_real, Finset.mem_val]
        rw [← hden]
        exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
      exact (Polynomial.mem_roots (Polynomial.degree_ne_bot.mp (by
        rw [Polynomial.Chebyshev.degree_U_natCast]; simp))).mp hxmem
  · exact_mod_cast (Nat.ne_zero_of_lt hd)

/-- Roots of the derivative of  are exactly the interior extremal nodes. -/
theorem chebyshevT_derivative_eq_zero_iff_exists_extremalNode
    {d : ℕ} (hd : 2 ≤ d) (x : ℝ) :
    (Polynomial.derivative (chebyshevT d)).eval x = 0 ↔
      ∃ i : Fin (d - 1), x = chebyshevExtremalNode d ⟨i.val + 1, by omega⟩ := by
  rw [chebyshevT_derivative_eq_zero_iff_exists_cos (Nat.one_le_of_lt hd) x]
  constructor
  · rintro ⟨k, hk, hx⟩
    let i : Fin (d - 1) := ⟨d - (k + 1) - 1, by omega⟩
    refine ⟨i, ?_⟩
    rw [hx]
    unfold chebyshevExtremalNode Polynomial.Chebyshev.node
    change Real.cos ((↑k + 1) * Real.pi / ↑d) =
      Real.cos (↑(d - (i.val + 1)) * Real.pi / ↑d)
    have hi : i.val + 1 = d - (k + 1) := by
      dsimp [i]
      omega
    have hidx : d - (i.val + 1) = k + 1 := by omega
    rw [hidx]
    norm_num
  · rintro ⟨i, hx⟩
    let k : ℕ := d - (i.val + 1) - 1
    refine ⟨k, by dsimp [k]; omega, ?_⟩
    rw [hx]
    unfold chebyshevExtremalNode Polynomial.Chebyshev.node
    change Real.cos (↑(d - (i.val + 1)) * Real.pi / ↑d) =
      Real.cos ((↑k + 1) * Real.pi / ↑d)
    have hk1 : k + 1 = d - (i.val + 1) := by
      dsimp [k]
      omega
    rw [← hk1]
    norm_num

/-- Chebyshev's differential equation in the repository's  notation. -/
theorem chebyshevT_differential_identity (d : ℕ) :
    (Polynomial.X ^ 2 - 1) * Polynomial.derivative (Polynomial.derivative (chebyshevT d)) +
      Polynomial.X * Polynomial.derivative (chebyshevT d) =
        (((d : ℤ) ^ 2 : Polynomial ℝ) * chebyshevT d) := by
  rw [chebyshevT_eq_T_nat]
  have h := Polynomial.Chebyshev.one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T
    (R := ℝ) (d : ℤ)
  rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply] at h
  set T := Polynomial.Chebyshev.T ℝ (↑d : ℤ)
  set D := Polynomial.derivative T
  set DD := Polynomial.derivative D
  change (Polynomial.X ^ 2 - 1) * DD + Polynomial.X * D =
    (((d : ℤ) ^ 2 : Polynomial ℝ) * T)
  change (1 - Polynomial.X ^ 2) * DD =
    Polynomial.X * D - (((d : ℤ) ^ 2 : Polynomial ℝ) * T) at h
  calc (Polynomial.X ^ 2 - 1) * DD + Polynomial.X * D
      = -((1 - Polynomial.X ^ 2) * DD) + Polynomial.X * D := by ring
    _ = -(Polynomial.X * D - (((d : ℤ) ^ 2 : Polynomial ℝ) * T)) +
        Polynomial.X * D := by rw [h]
    _ = (((d : ℤ) ^ 2 : Polynomial ℝ) * T) := by ring

/-- The auxiliary polynomial from the comparison lemma is bounded by  for . -/
theorem chebyshevT_differential_eval_abs_le
    (d : ℕ) (x : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    |(((Polynomial.X ^ 2 - 1) * Polynomial.derivative (Polynomial.derivative (chebyshevT d)) +
      Polynomial.X * Polynomial.derivative (chebyshevT d)).eval x)| ≤ (d : ℝ) ^ 2 := by
  rw [chebyshevT_differential_identity d, Polynomial.eval_mul]
  have hconst : Polynomial.eval x (((d : ℤ) ^ 2 : Polynomial ℝ)) = (d : ℝ) ^ 2 := by
    norm_num
  rw [hconst]
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (d : ℝ) ^ 2)]
  calc (d : ℝ) ^ 2 * |(chebyshevT d).eval x|
      ≤ (d : ℝ) ^ 2 * 1 := by
          exact mul_le_mul_of_nonneg_left (chebyshevT_abs_le_one d x hx1 hx2) (by positivity)
    _ = (d : ℝ) ^ 2 := by ring


end OptimalConvergenceRates
