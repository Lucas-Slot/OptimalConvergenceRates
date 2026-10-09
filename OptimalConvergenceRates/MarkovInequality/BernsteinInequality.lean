/-
  OptimalConvergenceRates/MarkovInequality/BernsteinInequality.lean

  Bernstein-type first-derivative bound at the center of [-1,1].
-/
import OptimalConvergenceRates.MarkovInequality.ChebyshevExtrema
import OptimalConvergenceRates.MarkovInequality.PolynomialDerivativeLemmas
import OptimalConvergenceRates.MarkovInequality.MarkovFirstDerivativeProof

open Polynomial Finset
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates

private noncomputable def markovAuxR (q : Polynomial ℝ) : Polynomial ℝ :=
  (Polynomial.X ^ 2 - 1) * Polynomial.derivative (Polynomial.derivative q) +
    Polynomial.X * Polynomial.derivative q

private theorem chebyshevT_eval_zero_of_nat_odd (d : ℕ) (hodd : Odd d) :
    (chebyshevT d).eval 0 = 0 := by
  rw [chebyshevT_eq_T_nat]
  exact Polynomial.Chebyshev.T_eval_zero_of_odd (R := ℝ) (n := (d : ℤ))
    ((Int.odd_coe_nat d).mpr hodd)

private theorem chebyshevT_derivative_eval_zero_abs_le_nat (d : ℕ) :
    |Polynomial.eval 0 (Polynomial.derivative (chebyshevT d))| ≤ (d : ℝ) := by
  rw [chebyshevT_eq_T_nat, Polynomial.Chebyshev.T_derivative_eq_U]
  simp only [Polynomial.eval_mul, Polynomial.eval_intCast]
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
  have hU : |Polynomial.eval 0 (Polynomial.Chebyshev.U ℝ (↑d - 1))| ≤ 1 := by
    by_cases hEven : Even ((d : ℤ) - 1)
    · rw [Polynomial.Chebyshev.U_eval_zero_of_even (R := ℝ) hEven]
      rw [← Int.cast_abs, Int.abs_negOnePow, Int.cast_one]
    · have hOdd : Odd ((d : ℤ) - 1) := Int.not_even_iff_odd.mp hEven
      rw [Polynomial.Chebyshev.U_eval_zero_of_odd (R := ℝ) hOdd]
      norm_num
  calc (d : ℝ) * |Polynomial.eval 0 (Polynomial.Chebyshev.U ℝ (↑d - 1))|
      ≤ (d : ℝ) * 1 := mul_le_mul_of_nonneg_left hU (Nat.cast_nonneg d)
    _ = (d : ℝ) := by ring

private theorem chebyshevT_markovAuxR_eval_zero_of_odd (d : ℕ) (hodd : Odd d) :
    (markovAuxR (chebyshevT d)).eval 0 = 0 := by
  unfold markovAuxR
  have hdiff := congrArg (fun q : Polynomial ℝ => q.eval 0) (chebyshevT_differential_identity d)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_one, zero_pow two_ne_zero, zero_mul, add_zero] at hdiff
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_one, zero_pow two_ne_zero, zero_mul, add_zero]
  rw [hdiff]
  rw [chebyshevT_eval_zero_of_nat_odd d hodd, mul_zero]

private theorem univariate_bernstein_first_derivative_zero_normalized_odd
    {n : ℕ} (hn : 2 ≤ n) (hnodd : Odd n)
    (p : Polynomial ℝ) (hdeg : p.natDegree ≤ n)
    (hp : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → |p.eval x| ≤ 1) :
    |(Polynomial.derivative p).eval 0| ≤ (n : ℝ) := by
  have hp_nodes : ∀ i : Fin (n + 1),
      |p.eval (chebyshevExtremalNode n i)| ≤
        |(chebyshevT n).eval (chebyshevExtremalNode n i)| := by
    intro i
    have hmem : chebyshevExtremalNode n i ∈ Set.Icc (-1 : ℝ) 1 := by
      unfold chebyshevExtremalNode
      exact Polynomial.Chebyshev.node_mem_Icc
    rw [chebyshevT_eval_extremalNode_abs]
    exact hp _ hmem.1 hmem.2
  have hcomp := duffin_schaeffer_first_derivative_comparison hn p (chebyshevT n)
    (chebyshevExtremalNode n)
    (chebyshevExtremalNode_strictMono n)
    (chebyshevExtremalNode_left (by omega))
    (chebyshevExtremalNode_right n)
    hdeg
    (natDegree_chebyshevT n)
    (chebyshevT_derivative_eq_zero_iff_exists_extremalNode hn)
    (chebyshevT_extremalNode_adjacent_mul_neg n)
    hp_nodes 0 (by norm_num) (by norm_num)
  have hmax : max |(Polynomial.derivative (chebyshevT n)).eval 0|
      |(markovAuxR (chebyshevT n)).eval 0| ≤ (n : ℝ) := by
    rw [chebyshevT_markovAuxR_eval_zero_of_odd n hnodd, abs_zero, max_le_iff]
    exact ⟨chebyshevT_derivative_eval_zero_abs_le_nat n, Nat.cast_nonneg n⟩
  exact hcomp.trans hmax

/-- Bernstein inequality at the center of `[-1, 1]`, with an explicit coarse
constant.  The proof uses Duffin-Schaeffer comparison against an odd Chebyshev
polynomial.  If `d` is even, comparison with `T_{d+1}` gives `(d+1)`, which is
absorbed into `2*d` for positive `d`. -/
theorem univariate_bernstein_first_derivative_zero_bound
    (p : Polynomial ℝ) (d : ℕ) (hdeg : p.natDegree ≤ d)
    (M : ℝ) (hM : 0 ≤ M)
    (hp : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → |p.eval x| ≤ M) :
    |(Polynomial.derivative p).eval 0| ≤ 2 * (d : ℝ) * M := by
  rcases d with _ | d
  · have hp0 : p.natDegree = 0 := Nat.le_zero.mp hdeg
    rw [Polynomial.derivative_of_natDegree_zero hp0, Polynomial.eval_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg 0)) hM
  · rcases d with _ | d
    · have h := markov_first_derivative_bound_degree_one p M hM hdeg hp 0
      have hscale : (1 : ℝ) ^ 2 * M ≤ 2 * (1 : ℝ) * M := by nlinarith [hM]
      simpa using h.trans hscale
    · by_cases hM0 : M = 0
      · have hp_zero : p = 0 := by
          apply Polynomial.eq_zero_of_infinite_isRoot
          apply (Set.Ioo_infinite (by norm_num : (-1 : ℝ) < 1)).mono
          intro t ht
          have htIcc := Set.mem_Icc_of_Ioo ht
          have hb := hp t htIcc.1 htIcc.2
          rw [hM0] at hb
          exact abs_nonpos_iff.mp hb
        subst hp_zero
        simp [hM0]
      · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
        set q : Polynomial ℝ := Polynomial.C M⁻¹ * p with hq
        have hqdeg_succ : q.natDegree ≤ d + 2 := by
          calc q.natDegree ≤ p.natDegree := by
                rw [hq]
                exact Polynomial.natDegree_C_mul_le M⁻¹ p
            _ ≤ d + 2 := hdeg
        have hqbound : ∀ y : ℝ, -1 ≤ y → y ≤ 1 → |q.eval y| ≤ 1 := by
          intro y hy1 hy2
          rw [hq, Polynomial.eval_mul, Polynomial.eval_C, abs_mul,
            abs_of_nonneg (inv_nonneg.mpr hM)]
          rw [inv_mul_le_iff₀ hMpos]
          simpa using hp y hy1 hy2
        have hderiv : Polynomial.derivative q = Polynomial.C M⁻¹ * Polynomial.derivative p := by
          rw [hq, Polynomial.derivative_mul]
          simp
        have htarget : |(Polynomial.derivative q).eval 0| ≤ 2 * ((d + 2 : ℕ) : ℝ) := by
          by_cases hodd : Odd (d + 2)
          · have hn : 2 ≤ d + 2 := by omega
            have h := univariate_bernstein_first_derivative_zero_normalized_odd
              hn hodd q hqdeg_succ hqbound
            have hle : ((d + 2 : ℕ) : ℝ) ≤ 2 * ((d + 2 : ℕ) : ℝ) := by
              calc
                ((d + 2 : ℕ) : ℝ) = 1 * ((d + 2 : ℕ) : ℝ) := by ring
                _ ≤ 2 * ((d + 2 : ℕ) : ℝ) := by
                  exact mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2)
                    (Nat.cast_nonneg (d + 2))
            exact h.trans hle
          · have hodd2 : Odd (d + 3) := by
              rcases Nat.not_odd_iff_even.mp hodd with ⟨m, hm⟩
              rw [show d + 3 = d + 2 + 1 by omega, hm]
              exact ⟨m, by omega⟩
            have hn : 2 ≤ d + 3 := by omega
            have hdeg2 : q.natDegree ≤ d + 3 := le_trans hqdeg_succ (by omega)
            have h := univariate_bernstein_first_derivative_zero_normalized_odd
              hn hodd2 q hdeg2 hqbound
            have hle : ((d + 3 : ℕ) : ℝ) ≤ 2 * ((d + 2 : ℕ) : ℝ) := by
              have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
              calc
                ((d + 3 : ℕ) : ℝ) = (d : ℝ) + 3 := by norm_num
                _ ≤ (d : ℝ) + 4 := by norm_num
                _ ≤ (d : ℝ) + (d : ℝ) + 4 := by linarith
                _ = 2 * ((d + 2 : ℕ) : ℝ) := by norm_num; ring
            exact h.trans hle
        rw [hderiv, Polynomial.eval_mul, Polynomial.eval_C, abs_mul,
          abs_of_nonneg (inv_nonneg.mpr hM)] at htarget
        calc |(Polynomial.derivative p).eval 0|
            = M * (M⁻¹ * |(Polynomial.derivative p).eval 0|) := by
                rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hMpos), one_mul]
          _ ≤ M * (2 * ((d + 2 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left htarget hM
          _ = 2 * ((d + 1 + 1 : ℕ) : ℝ) * M := by norm_num; ring

end OptimalConvergenceRates

end
