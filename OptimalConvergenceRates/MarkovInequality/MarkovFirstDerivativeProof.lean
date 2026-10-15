/-
  OptimalConvergenceRates/MarkovInequality/MarkovFirstDerivativeProof.lean

  Duffin-Schaeffer proof of the sharp first-derivative Markov inequality on [-1,1].
-/
import OptimalConvergenceRates.MarkovInequality.PolynomialDerivativeLemmas
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

open Polynomial Finset
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates

/-!
## Target statement with an arbitrary bound

The exported sup-norm theorem has `M = polySupNormUni p`. The proof first establishes
an arbitrary nonnegative bound `M` on `[-1,1]`, then specializes to the sup norm.
-/

/-- Degree-zero case of the first-derivative Markov inequality with an arbitrary bound. -/
theorem markov_first_derivative_bound_degree_zero
    (p : Polynomial ℝ) (M : ℝ) (hM : 0 ≤ M) (hdeg : p.natDegree ≤ 0)
    (x : ℝ) :
    |(Polynomial.derivative p).eval x| ≤ (0 : ℝ) ^ 2 * M := by
  have hp0 : p.natDegree = 0 := Nat.le_zero.mp hdeg
  rw [Polynomial.derivative_of_natDegree_zero hp0, Polynomial.eval_zero, abs_zero]
  positivity

private theorem derivative_eq_C_coeff_one_of_natDegree_le_one
    (p : Polynomial ℝ) (hdeg : p.natDegree ≤ 1) :
    Polynomial.derivative p = Polynomial.C (p.coeff 1) := by
  ext n
  rw [Polynomial.coeff_derivative]
  cases n with
  | zero => simp
  | succ n =>
      have hcoeff : p.coeff (Nat.succ n + 1) = 0 := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero] at hdeg
        exact hdeg (Nat.succ n + 1) (by omega)
      simp [hcoeff]

private theorem eq_C_add_C_mul_X_of_natDegree_le_one
    (p : Polynomial ℝ) (hdeg : p.natDegree ≤ 1) :
    p = Polynomial.C (p.coeff 0) + Polynomial.C (p.coeff 1) * Polynomial.X := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero => simp
      | succ n =>
          have hcoeff : p.coeff (Nat.succ (Nat.succ n)) = 0 := by
            rw [Polynomial.natDegree_le_iff_coeff_eq_zero] at hdeg
            exact hdeg (Nat.succ (Nat.succ n)) (by omega)
          simp [hcoeff]

/-- Degree-one case of the first-derivative Markov inequality with an arbitrary bound. -/
theorem markov_first_derivative_bound_degree_one
    (p : Polynomial ℝ) (M : ℝ) (_hM : 0 ≤ M) (hdeg : p.natDegree ≤ 1)
    (hp : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → |p.eval x| ≤ M)
    (x : ℝ) :
    |(Polynomial.derivative p).eval x| ≤ (1 : ℝ) ^ 2 * M := by
  set a := p.coeff 1 with ha
  set b := p.coeff 0 with hb
  have hp_lin := eq_C_add_C_mul_X_of_natDegree_le_one p hdeg
  have hderiv := derivative_eq_C_coeff_one_of_natDegree_le_one p hdeg
  have hp1 := hp 1 (by norm_num) (by norm_num)
  have hpm1 := hp (-1) (by norm_num) (by norm_num)
  rw [hp_lin] at hp1 hpm1
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    at hp1 hpm1
  rw [← ha, ← hb] at hp1 hpm1
  have hp1' : |b + a| ≤ M := by simpa using hp1
  have hpm1' : |b - a| ≤ M := by simpa [sub_eq_add_neg] using hpm1
  have habs : |a| ≤ M := by
    have htri : |(b + a) - (b - a)| ≤ |b + a| + |b - a| := abs_sub _ _
    have hdouble : |(b + a) - (b - a)| = 2 * |a| := by
      rw [show (b + a) - (b - a) = 2 * a by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hdouble] at htri
    nlinarith
  rw [hderiv]
  simp only [Polynomial.eval_C, one_pow, one_mul]
  simpa [ha] using habs

/-!
## Abstract comparison theorem specialized later to `q = T_d`

The comparison is stated with abstract hypotheses before its Chebyshev specialization.
-/

private noncomputable def markovAuxA (q : Polynomial ℝ) : Polynomial ℝ :=
  (Polynomial.X - 1) * Polynomial.derivative q

private noncomputable def markovAuxB (q : Polynomial ℝ) : Polynomial ℝ :=
  (Polynomial.X + 1) * Polynomial.derivative q

private noncomputable def markovAuxR (q : Polynomial ℝ) : Polynomial ℝ :=
  (Polynomial.X ^ 2 - 1) * Polynomial.derivative (Polynomial.derivative q) +
    Polynomial.X * Polynomial.derivative q

private theorem continuous_nonneg_on_Icc_of_nonneg_on_Ioo
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : Continuous f)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 ≤ f x) :
    ∀ x ∈ Set.Icc a b, 0 ≤ f x := by
  intro x hx
  have hxcl : x ∈ closure (Set.Ioo a b) := by
    rw [closure_Ioo (ne_of_lt hab)]
    exact hx
  have hmaps : Set.MapsTo f (Set.Ioo a b) (Set.Ici 0) := by
    intro y hy
    exact hpos y hy
  have hmaps_cl := hmaps.closure hf
  have hximage : f x ∈ closure (Set.Ici (0 : ℝ)) := hmaps_cl hxcl
  simpa [isClosed_Ici.closure_eq] using hximage

private theorem pairwise_nonneg_of_adjacent_mul_pos_nat
    (r : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N)
    (hadj : ∀ k : ℕ, k + 1 ≤ N → 0 < r k * r (k + 1)) :
    ∀ i j : ℕ, i ≤ N → j ≤ N → 0 ≤ r i * r j := by
  have hsame_pos : ∀ k : ℕ, k ≤ N → 0 < r 0 → 0 < r k := by
    intro k hk h0
    induction k with
    | zero => exact h0
    | succ k ih =>
        have hkN : k ≤ N := by omega
        have hkpos := ih hkN
        have hadj_k := hadj k (by omega)
        rw [mul_comm] at hadj_k
        exact pos_of_mul_pos_left hadj_k (le_of_lt hkpos)
  have hsame_neg : ∀ k : ℕ, k ≤ N → r 0 < 0 → r k < 0 := by
    intro k hk h0
    induction k with
    | zero => exact h0
    | succ k ih =>
        have hkN : k ≤ N := by omega
        have hkneg := ih hkN
        have hadj_k := hadj k (by omega)
        rw [mul_comm] at hadj_k
        exact neg_of_mul_pos_left hadj_k (le_of_lt hkneg)
  intro i j hi hj
  have h00 : 0 < r 0 * r 1 := hadj 0 (by omega)
  have h0ne : r 0 ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at h00
    exact not_lt_of_ge le_rfl h00
  rcases lt_or_gt_of_ne h0ne with h0neg | h0pos
  · exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt (hsame_neg i hi h0neg))
      (le_of_lt (hsame_neg j hj h0neg))
  · exact mul_nonneg (le_of_lt (hsame_pos i hi h0pos)) (le_of_lt (hsame_pos j hj h0pos))

private theorem pairwise_nonneg_of_adjacent_mul_pos_fin
    {n : ℕ} (hn : 1 ≤ n) (r : Fin (n + 1) → ℝ)
    (hadj : ∀ i : Fin n, 0 < r ⟨i.val, by omega⟩ * r ⟨i.val + 1, by omega⟩) :
    ∀ i j : Fin (n + 1), 0 ≤ r i * r j := by
  intro i j
  have hpair := pairwise_nonneg_of_adjacent_mul_pos_nat
    (fun k => if hk : k ≤ n then r ⟨k, by omega⟩ else 0) hn ?_ i.val j.val (by omega) (by omega)
  · have hi_le : i.val ≤ n := by omega
    have hj_le : j.val ≤ n := by omega
    simpa [hi_le, hj_le] using hpair
  · intro k hk
    have hk0 : k ≤ n := by omega
    have hk1 : k + 1 ≤ n := by omega
    let ik : Fin n := ⟨k, by omega⟩
    simpa [hk0, hk1, ik] using hadj ik

private theorem lagrangeDenom_adjacent_mul_neg
    {n : ℕ} (_hn : 1 ≤ n) (τ : Fin (n + 1) → ℝ) (hτ_strict : StrictMono τ)
    (i : Fin n) :
    lagrangeDenom τ ⟨i.val, by omega⟩ * lagrangeDenom τ ⟨i.val + 1, by omega⟩ < 0 := by
  classical
  let ii : Fin (n + 1) := ⟨i.val, by omega⟩
  let jj : Fin (n + 1) := ⟨i.val + 1, by omega⟩
  let S : Finset (Fin (n + 1)) := (Finset.univ.erase ii).erase jj
  have hii_ne_jj : ii ≠ jj := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [ii, jj] at hval
    omega
  have hS_eq : (Finset.univ.erase jj).erase ii = S := by
    ext k
    simp [S, and_comm]
  have hj_mem : jj ∈ Finset.univ.erase ii := by
    simp [hii_ne_jj.symm]
  have hi_mem : ii ∈ Finset.univ.erase jj := by
    simp [hii_ne_jj]
  have hleft : lagrangeDenom τ ii = (Finset.prod S (fun k => τ ii - τ k)) * (τ ii - τ jj) := by
    unfold lagrangeDenom S
    rw [← Finset.prod_erase_mul (s := Finset.univ.erase ii) (f := fun k => τ ii - τ k) hj_mem]
  have hright : lagrangeDenom τ jj = (Finset.prod S (fun k => τ jj - τ k)) * (τ jj - τ ii) := by
    unfold lagrangeDenom
    rw [← Finset.prod_erase_mul (s := Finset.univ.erase jj) (f := fun k => τ jj - τ k) hi_mem]
    rw [hS_eq]
  have hpaired_pos : 0 < (Finset.prod S (fun k => (τ ii - τ k) * (τ jj - τ k))) := by
    apply Finset.prod_pos
    intro k hk
    have hk_mem := Finset.mem_erase.mp hk
    have hk_ne_jj : k ≠ jj := hk_mem.1
    have hk_ne_ii : k ≠ ii := (Finset.mem_erase.mp hk_mem.2).1
    have hlt_or_gt : k.val < ii.val ∨ jj.val < k.val := by
      have hkne_i : k.val ≠ i.val := by
        intro hval
        exact hk_ne_ii (Fin.ext (by dsimp [ii]; exact hval))
      have hkne_j : k.val ≠ i.val + 1 := by
        intro hval
        exact hk_ne_jj (Fin.ext (by dsimp [jj]; exact hval))
      dsimp [ii, jj]
      omega
    rcases hlt_or_gt with hlt | hgt
    · have hklt_i : τ k < τ ii := hτ_strict (by exact_mod_cast hlt)
      have hklt_j : τ k < τ jj := hτ_strict (by
        change k.val < jj.val
        have hii_val : ii.val = i.val := rfl
        have hjj_val : jj.val = i.val + 1 := rfl
        omega)
      exact mul_pos (sub_pos.mpr hklt_i) (sub_pos.mpr hklt_j)
    · have hilt_k : τ ii < τ k := hτ_strict (by
        change ii.val < k.val
        have hii_val : ii.val = i.val := rfl
        have hjj_val : jj.val = i.val + 1 := rfl
        omega)
      have hjlt_k : τ jj < τ k := hτ_strict (by
        change jj.val < k.val
        exact hgt)
      exact mul_pos_of_neg_of_neg (sub_neg.mpr hilt_k) (sub_neg.mpr hjlt_k)
  have hcommon_pos :
      0 < (Finset.prod S (fun k => τ ii - τ k)) *
        (Finset.prod S (fun k => τ jj - τ k)) := by
    rw [← Finset.prod_mul_distrib]
    exact hpaired_pos
  have hadj_neg : (τ ii - τ jj) * (τ jj - τ ii) < 0 := by
    have hij_lt : τ ii < τ jj := hτ_strict (by
      dsimp [ii, jj]
      exact_mod_cast Nat.lt_succ_self i.val)
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hij_lt) (sub_pos.mpr hij_lt)
  rw [hleft, hright]
  nlinarith [mul_neg_of_pos_of_neg hcommon_pos hadj_neg]

private theorem div_adjacent_mul_pos_of_mul_neg
    {a b c d : ℝ} (hab : a * b < 0) (hcd : c * d < 0) :
    0 < (a / c) * (b / d) := by
  have hcd_ne : c * d ≠ 0 := ne_of_lt hcd
  have hcinv : c ≠ 0 := left_ne_zero_of_mul hcd_ne
  have hdinv : d ≠ 0 := right_ne_zero_of_mul hcd_ne
  have hden_inv_neg : (c * d)⁻¹ < 0 := (inv_lt_zero.mpr hcd)
  have hprod : 0 < (a * b) * (c * d)⁻¹ := mul_pos_of_neg_of_neg hab hden_inv_neg
  convert hprod using 1
  field_simp [hcinv, hdinv]

private theorem ratio_pairwise_nonneg_of_adjacent_mul_neg
    {n : ℕ} (hn : 1 ≤ n) (f g : Fin (n + 1) → ℝ)
    (hf : ∀ i : Fin n, f ⟨i.val, by omega⟩ * f ⟨i.val + 1, by omega⟩ < 0)
    (hg : ∀ i : Fin n, g ⟨i.val, by omega⟩ * g ⟨i.val + 1, by omega⟩ < 0) :
    ∀ i j : Fin (n + 1), 0 ≤ (f i / g i) * (f j / g j) := by
  apply pairwise_nonneg_of_adjacent_mul_pos_fin hn
  intro i
  exact div_adjacent_mul_pos_of_mul_neg (hf i) (hg i)

private theorem common_sign_of_pairwise_mul_nonneg
    {ι : Type*} [Nonempty ι] (f : ι → ℝ)
    (hpair : ∀ i j : ι, 0 ≤ f i * f j) :
    (∀ i : ι, 0 ≤ f i) ∨ (∀ i : ι, f i ≤ 0) := by
  classical
  by_cases hnonneg : ∀ i : ι, 0 ≤ f i
  · exact Or.inl hnonneg
  · push Not at hnonneg
    rcases hnonneg with ⟨i0, hi0⟩
    refine Or.inr ?_
    intro j
    by_contra hjpos_not
    have hjpos : 0 < f j := lt_of_not_ge hjpos_not
    have hprod_pos : f i0 * f j < 0 := mul_neg_of_neg_of_pos hi0 hjpos
    exact not_lt_of_ge (hpair i0 j) hprod_pos

private def lagrangeQDerivativeTermsCommonSign
    {n : ℕ} (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ) (x : ℝ) : Prop :=
  (∀ i : Fin (n + 1),
      0 ≤ q.eval (τ i) * (Polynomial.derivative (lagrangeBasis τ i)).eval x) ∨
    (∀ i : Fin (n + 1),
      q.eval (τ i) * (Polynomial.derivative (lagrangeBasis τ i)).eval x ≤ 0)

private theorem lagrange_term_pairwise_nonneg_of_product_derivative_pairwise
    {n : ℕ} (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ) (x : ℝ)
    (hcoeff : ∀ i j : Fin (n + 1),
      0 ≤ (q.eval (τ i) / lagrangeDenom τ i) * (q.eval (τ j) / lagrangeDenom τ j))
    (hprod : ∀ i j : Fin (n + 1),
      0 ≤ lagrangeProductDerivativeEval τ i x * lagrangeProductDerivativeEval τ j x) :
    ∀ i j : Fin (n + 1),
      0 ≤ (q.eval (τ i) * (Polynomial.derivative (lagrangeBasis τ i)).eval x) *
        (q.eval (τ j) * (Polynomial.derivative (lagrangeBasis τ j)).eval x) := by
  intro i j
  rw [lagrangeBasis_derivative_eval_eq_inv_mul_prod_derivative τ i x,
    lagrangeBasis_derivative_eval_eq_inv_mul_prod_derivative τ j x]
  change 0 ≤
    (q.eval (τ i) * ((lagrangeDenom τ i)⁻¹ * lagrangeProductDerivativeEval τ i x)) *
      (q.eval (τ j) * ((lagrangeDenom τ j)⁻¹ * lagrangeProductDerivativeEval τ j x))
  have hmain : 0 ≤ ((q.eval (τ i) / lagrangeDenom τ i) *
      (q.eval (τ j) / lagrangeDenom τ j)) *
      (lagrangeProductDerivativeEval τ i x * lagrangeProductDerivativeEval τ j x) :=
    mul_nonneg (hcoeff i j) (hprod i j)
  convert hmain using 1; ring

private theorem q_div_lagrangeDenom_pairwise_nonneg
    {n : ℕ} (hn : 1 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ)
    (hq_alt : ∀ i : Fin n,
      q.eval (τ ⟨i.val, by omega⟩) * q.eval (τ ⟨i.val + 1, by omega⟩) < 0) :
    ∀ i j : Fin (n + 1),
      0 ≤ (q.eval (τ i) / lagrangeDenom τ i) * (q.eval (τ j) / lagrangeDenom τ j) := by
  exact ratio_pairwise_nonneg_of_adjacent_mul_neg hn
    (fun i : Fin (n + 1) => q.eval (τ i))
    (fun i : Fin (n + 1) => lagrangeDenom τ i)
    hq_alt
    (fun i => lagrangeDenom_adjacent_mul_neg hn τ hτ_strict i)

private theorem lagrangeQDerivativeTermsCommonSign_of_pairwise_mul_nonneg
    {n : ℕ} (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ) (x : ℝ)
    (hpair : ∀ i j : Fin (n + 1),
      0 ≤ (q.eval (τ i) * (Polynomial.derivative (lagrangeBasis τ i)).eval x) *
        (q.eval (τ j) * (Polynomial.derivative (lagrangeBasis τ j)).eval x)) :
    lagrangeQDerivativeTermsCommonSign q τ x := by
  exact common_sign_of_pairwise_mul_nonneg
    (fun i : Fin (n + 1) =>
      q.eval (τ i) * (Polynomial.derivative (lagrangeBasis τ i)).eval x) hpair

private theorem lagrangeQDerivativeTermsCommonSign.comm
    {n : ℕ} {q : Polynomial ℝ} {τ : Fin (n + 1) → ℝ} {x : ℝ}
    (h : lagrangeQDerivativeTermsCommonSign q τ x) :
    (∀ i : Fin (n + 1),
        0 ≤ q.eval (τ i) * (Polynomial.derivative (lagrangeBasis τ i)).eval x) ∨
      (∀ i : Fin (n + 1),
        q.eval (τ i) * (Polynomial.derivative (lagrangeBasis τ i)).eval x ≤ 0) := h

private theorem derivative_eval_le_of_lagrange_common_sign
    {n : ℕ} (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ) (hτ_strict : StrictMono τ)
    (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree = n)
    (hp_nodes : ∀ i : Fin (n + 1), |p.eval (τ i)| ≤ |q.eval (τ i)|)
    (x : ℝ)
    (hterms : (∀ i : Fin (n + 1),
        0 ≤ q.eval (τ i) * (Polynomial.derivative (lagrangeBasis τ i)).eval x) ∨
      (∀ i : Fin (n + 1),
        q.eval (τ i) * (Polynomial.derivative (lagrangeBasis τ i)).eval x ≤ 0)) :
    |(Polynomial.derivative p).eval x| ≤ |(Polynomial.derivative q).eval x| := by
  rcases hterms with hnonneg | hnonpos
  · exact derivative_eval_le_of_lagrange_common_nonneg p q τ hτ_strict hpdeg hqdeg
      hp_nodes x hnonneg
  · exact derivative_eval_le_of_lagrange_common_nonpos p q τ hτ_strict hpdeg hqdeg
      hp_nodes x hnonpos

private theorem comparison_of_lagrange_common_sign
    {n : ℕ} (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ) (hτ_strict : StrictMono τ)
    (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree = n)
    (hp_nodes : ∀ i : Fin (n + 1), |p.eval (τ i)| ≤ |q.eval (τ i)|)
    (x : ℝ) (hterms : lagrangeQDerivativeTermsCommonSign q τ x) :
    |(Polynomial.derivative p).eval x| ≤
      max |(Polynomial.derivative q).eval x| |(markovAuxR q).eval x| := by
  exact (derivative_eval_le_of_lagrange_common_sign p q τ hτ_strict hpdeg hqdeg hp_nodes x
    hterms.comm).trans (le_max_left _ _)

private theorem markovAuxR_eq_X_add_one_mul_derivative_A_sub_derivative
    (q : Polynomial ℝ) :
    markovAuxR q = (Polynomial.X + 1) * Polynomial.derivative (markovAuxA q) -
      Polynomial.derivative q := by
  unfold markovAuxR markovAuxA
  simp [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X]
  ring

private theorem markovAuxR_eq_X_sub_one_mul_derivative_B_add_derivative
    (q : Polynomial ℝ) :
    markovAuxR q = (Polynomial.X - 1) * Polynomial.derivative (markovAuxB q) +
      Polynomial.derivative q := by
  unfold markovAuxR markovAuxB
  simp [Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.derivative_X]
  ring

private theorem markovAuxA_eval_derivative_zero_of_derivative_zero
    (q : Polynomial ℝ) {x : ℝ} (hx : (Polynomial.derivative (markovAuxA q)).eval x = 0) :
    (markovAuxR q).eval x = - (Polynomial.derivative q).eval x := by
  rw [markovAuxR_eq_X_add_one_mul_derivative_A_sub_derivative, Polynomial.eval_sub,
    Polynomial.eval_mul, hx, mul_zero, zero_sub]

private theorem markovAuxB_eval_derivative_zero_of_derivative_zero
    (q : Polynomial ℝ) {x : ℝ} (hx : (Polynomial.derivative (markovAuxB q)).eval x = 0) :
    (markovAuxR q).eval x = (Polynomial.derivative q).eval x := by
  rw [markovAuxR_eq_X_sub_one_mul_derivative_B_add_derivative, Polynomial.eval_add,
    Polynomial.eval_mul, hx, mul_zero, zero_add]

private theorem markovAuxR_eval_neg_one (q : Polynomial ℝ) :
    (markovAuxR q).eval (-1) = - (Polynomial.derivative q).eval (-1) := by
  rw [markovAuxR_eq_X_add_one_mul_derivative_A_sub_derivative, Polynomial.eval_sub,
    Polynomial.eval_mul]
  norm_num

private theorem markovAuxR_eval_one (q : Polynomial ℝ) :
    (markovAuxR q).eval 1 = (Polynomial.derivative q).eval 1 := by
  rw [markovAuxR_eq_X_sub_one_mul_derivative_B_add_derivative, Polynomial.eval_add,
    Polynomial.eval_mul]
  norm_num

private theorem polynomial_derivative_zero_between_of_eval_eq
    (P : Polynomial ℝ) {a b : ℝ} (hab : a < b) (hP : P.eval a = P.eval b) :
    ∃ c ∈ Set.Ioo a b, (Polynomial.derivative P).eval c = 0 := by
  obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope
    (fun x => P.eval x) (fun x => (Polynomial.derivative P).eval x) hab
    P.continuous.continuousOn
    (fun x _ => P.hasDerivAt x)
  refine ⟨c, hc_mem, ?_⟩
  rw [hP, sub_self, zero_div] at hc_eq
  exact hc_eq

private theorem markovAuxA_eval_one (q : Polynomial ℝ) :
    (markovAuxA q).eval 1 = 0 := by
  unfold markovAuxA
  simp

private theorem markovAuxB_eval_neg_one (q : Polynomial ℝ) :
    (markovAuxB q).eval (-1) = 0 := by
  unfold markovAuxB
  simp

private theorem markovAuxA_eval_eq_zero_of_derivative_q_eq_zero
    (q : Polynomial ℝ) {x : ℝ} (hx : (Polynomial.derivative q).eval x = 0) :
    (markovAuxA q).eval x = 0 := by
  unfold markovAuxA
  rw [Polynomial.eval_mul, hx, mul_zero]

private theorem markovAuxB_eval_eq_zero_of_derivative_q_eq_zero
    (q : Polynomial ℝ) {x : ℝ} (hx : (Polynomial.derivative q).eval x = 0) :
    (markovAuxB q).eval x = 0 := by
  unfold markovAuxB
  rw [Polynomial.eval_mul, hx, mul_zero]

private theorem exists_markovAuxA_derivative_zero_between_nodes
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ)
    (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin (n - 1)) :
    ∃ η ∈ Set.Ioo (τ ⟨j.val + 1, by omega⟩) (τ ⟨j.val + 2, by omega⟩),
      (Polynomial.derivative (markovAuxA q)).eval η = 0 := by
  have hleft : (markovAuxA q).eval (τ ⟨j.val + 1, by omega⟩) = 0 := by
    apply markovAuxA_eval_eq_zero_of_derivative_q_eq_zero
    exact (hqcrit _).mpr ⟨j, rfl⟩
  have hright : (markovAuxA q).eval (τ ⟨j.val + 2, by omega⟩) = 0 := by
    by_cases hlast : j.val + 2 = n
    · have hfin : (⟨j.val + 2, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := by
        ext
        exact hlast
      rw [hfin, hτ_right]
      exact markovAuxA_eval_one q
    · apply markovAuxA_eval_eq_zero_of_derivative_q_eq_zero
      let k : Fin (n - 1) := ⟨j.val + 1, by omega⟩
      have hnode : τ ⟨j.val + 2, by omega⟩ = τ ⟨k.val + 1, by omega⟩ := by
        rfl
      rw [hnode]
      exact (hqcrit _).mpr ⟨k, rfl⟩
  exact polynomial_derivative_zero_between_of_eval_eq (markovAuxA q)
    (hτ_strict (by
      change j.val + 1 < j.val + 2
      omega))
    (hleft.trans hright.symm)

private theorem derivative_natDegree_lt_of_natDegree_le
    {n : ℕ} (hn : 1 ≤ n) (p : Polynomial ℝ) (hpdeg : p.natDegree ≤ n) :
    (Polynomial.derivative p).natDegree < n := by
  calc (Polynomial.derivative p).natDegree ≤ p.natDegree - 1 := Polynomial.natDegree_derivative_le p
    _ < n := by omega

private theorem derivative_natDegree_eq_pred_of_natDegree_eq
    {n : ℕ} (hn : 1 ≤ n) (q : Polynomial ℝ) (hqdeg : q.natDegree = n) :
    (Polynomial.derivative q).natDegree = n - 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · calc (Polynomial.derivative q).natDegree ≤ q.natDegree - 1 :=
        Polynomial.natDegree_derivative_le q
      _ = n - 1 := by rw [hqdeg]
  · rw [Polynomial.coeff_derivative]
    have hidx : n - 1 + 1 = n := by omega
    rw [hidx]
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      rw [Nat.cast_sub hn]
      ring
    rw [hcast]
    have hqne : q ≠ 0 := by
      intro hq0
      rw [hq0, Polynomial.natDegree_zero] at hqdeg
      omega
    have hqcoeff : q.coeff n ≠ 0 := by
      rw [← hqdeg, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hqne
    exact mul_ne_zero hqcoeff (by exact_mod_cast (by omega : n ≠ 0))

private theorem markovAuxR_natDegree_le
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (hqdeg : q.natDegree = n) :
    (markovAuxR q).natDegree ≤ n := by
  unfold markovAuxR
  have hd1 : (Polynomial.derivative q).natDegree ≤ n - 1 := by
    calc
      (Polynomial.derivative q).natDegree ≤ q.natDegree - 1 :=
        Polynomial.natDegree_derivative_le q
      _ = n - 1 := by rw [hqdeg]
  have hd2 : (Polynomial.derivative (Polynomial.derivative q)).natDegree ≤ n - 2 := by
    calc (Polynomial.derivative (Polynomial.derivative q)).natDegree
        ≤ (Polynomial.derivative q).natDegree - 1 := Polynomial.natDegree_derivative_le _
      _ ≤ n - 2 := by omega
  have hleft :
      ((Polynomial.X ^ 2 - 1) * Polynomial.derivative (Polynomial.derivative q)).natDegree ≤ n := by
    calc ((Polynomial.X ^ 2 - 1) * Polynomial.derivative (Polynomial.derivative q)).natDegree
        ≤ (Polynomial.X ^ 2 - 1 : Polynomial ℝ).natDegree +
            (Polynomial.derivative (Polynomial.derivative q)).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ 2 + (n - 2) := by
          gcongr
          exact le_of_eq (by simpa using
            (Polynomial.natDegree_X_pow_sub_C (n := 2) (r := (1 : ℝ))))
      _ = n := by omega
  have hright : (Polynomial.X * Polynomial.derivative q).natDegree ≤ n := by
    calc (Polynomial.X * Polynomial.derivative q).natDegree
        ≤ Polynomial.X.natDegree + (Polynomial.derivative q).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ 1 + (n - 1) := by
          gcongr
          exact le_of_eq (Polynomial.natDegree_X : (Polynomial.X : Polynomial ℝ).natDegree = 1)
      _ = n := by omega
  exact (Polynomial.natDegree_add_le _ _).trans (max_le hleft hright)

private theorem markovAuxR_coeff_natDegree
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (hqdeg : q.natDegree = n) :
    (markovAuxR q).coeff n = (n : ℝ) ^ 2 * q.coeff n := by
  unfold markovAuxR
  set D := Polynomial.derivative q
  set DD := Polynomial.derivative D
  have hDD_coeff : DD.coeff (n - 2) = q.coeff n * (n : ℝ) * (n - 1 : ℝ) := by
    dsimp [DD, D]
    rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative]
    have h1 : n - 2 + 1 = n - 1 := by omega
    have h2 : n - 1 + 1 = n := by omega
    rw [h1, h2]
    have hcast1 : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      norm_num [Nat.cast_sub (by omega : 1 ≤ n)]
    have hcast2 : ((n - 2 : ℕ) : ℝ) + 1 = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 2 ≤ n)]
      ring
    rw [hcast1, hcast2]
  have hDD_le : DD.natDegree ≤ n - 2 := by
    dsimp [DD, D]
    calc (Polynomial.derivative (Polynomial.derivative q)).natDegree
        ≤ (Polynomial.derivative q).natDegree - 1 := Polynomial.natDegree_derivative_le _
      _ ≤ (q.natDegree - 1) - 1 := by
          exact Nat.sub_le_sub_right (Polynomial.natDegree_derivative_le q) 1
      _ = n - 2 := by rw [hqdeg]; omega
  have hleft : ((Polynomial.X ^ 2 - 1) * DD).coeff n = DD.coeff (n - 2) := by
    have hpoly : (Polynomial.X ^ 2 - 1) * DD = Polynomial.X ^ 2 * DD - DD := by ring
    rw [hpoly, Polynomial.coeff_sub]
    have hshift : (Polynomial.X ^ 2 * DD).coeff n = DD.coeff (n - 2) := by
      rw [Polynomial.coeff_X_pow_mul']
      simp [show 2 ≤ n by omega]
    have hzero : DD.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hDD_le (by omega))
    rw [hshift, hzero, sub_zero]
  have hright : (Polynomial.X * D).coeff n = D.coeff (n - 1) := by
    have hpoly : Polynomial.X * D = Polynomial.X ^ 1 * D := by ring
    rw [hpoly]
    rw [Polynomial.coeff_X_pow_mul']
    simp [show 1 ≤ n by omega]
  have hD_coeff : D.coeff (n - 1) = q.coeff n * (n : ℝ) := by
    dsimp [D]
    rw [Polynomial.coeff_derivative]
    have h : n - 1 + 1 = n := by omega
    rw [h]
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      ring
    rw [hcast]
  rw [Polynomial.coeff_add, hleft, hright, hDD_coeff, hD_coeff]
  ring

private theorem markovAuxR_natDegree_eq
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (hqdeg : q.natDegree = n) :
    (markovAuxR q).natDegree = n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact markovAuxR_natDegree_le hn q hqdeg
  · rw [markovAuxR_coeff_natDegree hn q hqdeg]
    have hqne : q ≠ 0 := by
      intro hq0
      rw [hq0, Polynomial.natDegree_zero] at hqdeg
      omega
    have hqcoeff : q.coeff n ≠ 0 := by
      rw [← hqdeg, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hqne
    exact mul_ne_zero (pow_ne_zero 2 (by exact_mod_cast (by omega : n ≠ 0))) hqcoeff

private theorem markovAuxR_add_C_mul_derivative_natDegree_eq
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (a : ℝ)
    (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree = n) :
    (markovAuxR q + Polynomial.C a * Polynomial.derivative p).natDegree = n := by
  have hterm_lt :
      (Polynomial.C a * Polynomial.derivative p).natDegree < (markovAuxR q).natDegree := by
    rw [markovAuxR_natDegree_eq hn q hqdeg]
    calc (Polynomial.C a * Polynomial.derivative p).natDegree
        ≤ (Polynomial.derivative p).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ < n := derivative_natDegree_lt_of_natDegree_le (Nat.one_le_of_lt hn) p hpdeg
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hterm_lt]
  exact markovAuxR_natDegree_eq hn q hqdeg

private theorem one_div_sub_right_sub_one_div_sub_left_neg
    {a b x : ℝ} (ha : a < x) (hb : x < b) :
    1 / (x - b) - 1 / (x - a) < 0 := by
  have hxb_ne : x - b ≠ 0 := by linarith
  have hxa_ne : x - a ≠ 0 := by linarith
  field_simp [hxb_ne, hxa_ne]
  apply div_neg_of_pos_of_neg
  · linarith
  · nlinarith

private theorem one_div_sub_strictAnti_on_component
    {c x y : ℝ} (hxy : x < y)
    (hsame : (x < c ∧ y < c) ∨ (c < x ∧ c < y)) :
    1 / (y - c) < 1 / (x - c) := by
  have hx_ne : x - c ≠ 0 := by
    rcases hsame with h | h <;> linarith
  have hy_ne : y - c ≠ 0 := by
    rcases hsame with h | h <;> linarith
  have hprod : 0 < (x - c) * (y - c) := by
    rcases hsame with h | h <;> nlinarith
  have hdiff : 0 < 1 / (x - c) - 1 / (y - c) := by
    field_simp [hx_ne, hy_ne]
    exact div_pos (by linarith) hprod
  linarith

private theorem sum_one_div_sub_strictAnti_on_components
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (ρ : ι → ℝ) {x y : ℝ}
    (hxy : x < y)
    (hsep : ∀ i ∈ s, (x < ρ i ∧ y < ρ i) ∨ (ρ i < x ∧ ρ i < y)) :
    (∑ i ∈ s, 1 / (y - ρ i)) < ∑ i ∈ s, 1 / (x - ρ i) := by
  apply Finset.sum_lt_sum_of_nonempty hs
  intro i hi
  exact one_div_sub_strictAnti_on_component hxy (hsep i hi)

private theorem node_separated_of_mem_adjacent_interval
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ_strict : StrictMono τ)
    (j : Fin n) {x y : ℝ}
    (hx : x ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩))
    (hy : y ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩))
    (k : Fin (n + 1)) :
    (x < τ k ∧ y < τ k) ∨ (τ k < x ∧ τ k < y) := by
  by_cases hk : k.val ≤ j.val
  · right
    have hkle : τ k ≤ τ ⟨j.val, by omega⟩ := by
      by_cases heq : k.val = j.val
      · have hidx : k = ⟨j.val, by omega⟩ := by
          ext
          exact heq
        rw [hidx]
      · have hlt : k.val < j.val := lt_of_le_of_ne hk heq
        exact le_of_lt (hτ_strict (by exact (Fin.mk_lt_mk).2 hlt))
    exact ⟨lt_of_le_of_lt hkle hx.1, lt_of_le_of_lt hkle hy.1⟩
  · left
    have hjk : j.val + 1 ≤ k.val := by omega
    have hle : τ ⟨j.val + 1, by omega⟩ ≤ τ k := by
      by_cases heq : k.val = j.val + 1
      · have hidx : k = ⟨j.val + 1, by omega⟩ := by
          ext
          exact heq
        rw [hidx]
      · have hlt : j.val + 1 < k.val := lt_of_le_of_ne hjk (Ne.symm heq)
        exact le_of_lt (hτ_strict (by exact (Fin.mk_lt_mk).2 hlt))
    exact ⟨lt_of_lt_of_le hx.2 hle, lt_of_lt_of_le hy.2 hle⟩

private theorem ne_node_of_mem_adjacent_interval
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ_strict : StrictMono τ)
    (j : Fin n) {x : ℝ}
    (hx : x ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩))
    (k : Fin (n + 1)) : x ≠ τ k := by
  have hsep := node_separated_of_mem_adjacent_interval τ hτ_strict j hx hx k
  rcases hsep with ⟨hlt, _⟩ | ⟨hlt, _⟩
  · exact ne_of_lt hlt
  · exact ne_of_gt hlt

private noncomputable def lagrangeLogDerivativeSum
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.univ.erase i, 1 / (x - τ k)

private theorem lagrangeLogDerivativeSum_sub
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) (x : ℝ) :
    lagrangeLogDerivativeSum τ i x - lagrangeLogDerivativeSum τ j x =
      1 / (x - τ j) - 1 / (x - τ i) := by
  classical
  unfold lagrangeLogDerivativeSum
  let f : Fin (n + 1) → ℝ := fun k => 1 / (x - τ k)
  have hi := Finset.sum_erase_add (Finset.univ : Finset (Fin (n + 1))) f
    (Finset.mem_univ i)
  have hj := Finset.sum_erase_add (Finset.univ : Finset (Fin (n + 1))) f
    (Finset.mem_univ j)
  change (∑ k ∈ Finset.univ.erase i, f k) - (∑ k ∈ Finset.univ.erase j, f k) =
    f j - f i
  linarith

private theorem lagrangeProductDerivativeEval_eq_eval_mul_sum_of_mem_adjacent_interval
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ_strict : StrictMono τ)
    (j : Fin n) {x : ℝ}
    (hx : x ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩))
    (i : Fin (n + 1)) :
    lagrangeProductDerivativeEval τ i x =
      ((Finset.univ.erase i).prod (fun k => Polynomial.X - Polynomial.C (τ k))).eval x *
        (∑ k ∈ Finset.univ.erase i, 1 / (x - τ k)) := by
  unfold lagrangeProductDerivativeEval
  rw [lagrangeProductDerivativeEval_eq_eval_mul_sum τ i]
  intro k _
  exact ne_node_of_mem_adjacent_interval τ hτ_strict j hx k

private theorem lagrangeProductDerivativeEval_eq_eval_mul_logDerivativeSum
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ_strict : StrictMono τ)
    (j : Fin n) {x : ℝ}
    (hx : x ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩))
    (i : Fin (n + 1)) :
    lagrangeProductDerivativeEval τ i x =
      ((Finset.univ.erase i).prod (fun k => Polynomial.X - Polynomial.C (τ k))).eval x *
        lagrangeLogDerivativeSum τ i x := by
  rw [lagrangeProductDerivativeEval_eq_eval_mul_sum_of_mem_adjacent_interval τ hτ_strict j hx i]
  rfl

private noncomputable def lagrangeProductEval
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (x : ℝ) : ℝ :=
  ((Finset.univ.erase i).prod (fun k => Polynomial.X - Polynomial.C (τ k))).eval x

private theorem lagrangeProductEval_eq_prod
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (x : ℝ) :
    lagrangeProductEval τ i x = (Finset.univ.erase i).prod (fun k => x - τ k) := by
  unfold lagrangeProductEval
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro k _
  simp

private noncomputable def lagrangeFullProductEval
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (x : ℝ) : ℝ :=
  (Finset.univ : Finset (Fin (n + 1))).prod (fun k => x - τ k)

private theorem lagrangeProductEval_mul_sub_eq_fullProduct
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (x : ℝ) :
    lagrangeProductEval τ i x * (x - τ i) = lagrangeFullProductEval τ x := by
  rw [lagrangeProductEval_eq_prod]
  unfold lagrangeFullProductEval
  exact Finset.prod_erase_mul (s := (Finset.univ : Finset (Fin (n + 1))))
    (f := fun k => x - τ k) (a := i) (Finset.mem_univ i)

private theorem lagrangeProductEval_pair_mul_nonneg_of_sub_mul_pos
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) {x : ℝ}
    (hden : 0 < (x - τ i) * (x - τ j)) :
    0 ≤ lagrangeProductEval τ i x * lagrangeProductEval τ j x := by
  let Pi := lagrangeProductEval τ i x
  let Pj := lagrangeProductEval τ j x
  let di := x - τ i
  let dj := x - τ j
  let F := lagrangeFullProductEval τ x
  have h1 : Pi * di = F := lagrangeProductEval_mul_sub_eq_fullProduct τ i x
  have h2 : Pj * dj = F := lagrangeProductEval_mul_sub_eq_fullProduct τ j x
  change 0 ≤ Pi * Pj
  apply nonneg_of_mul_nonneg_left (a := Pi * Pj) (b := di * dj) ?_ hden
  have heq : (Pi * Pj) * (di * dj) = (Pi * di) * (Pj * dj) := by ring
  rw [heq, h1, h2]
  nlinarith [sq_nonneg F]

private theorem lagrangeProductEval_pair_mul_nonpos_of_sub_mul_neg
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) {x : ℝ}
    (hden : (x - τ i) * (x - τ j) < 0) :
    lagrangeProductEval τ i x * lagrangeProductEval τ j x ≤ 0 := by
  let Pi := lagrangeProductEval τ i x
  let Pj := lagrangeProductEval τ j x
  let di := x - τ i
  let dj := x - τ j
  let F := lagrangeFullProductEval τ x
  have h1 : Pi * di = F := lagrangeProductEval_mul_sub_eq_fullProduct τ i x
  have h2 : Pj * dj = F := lagrangeProductEval_mul_sub_eq_fullProduct τ j x
  change Pi * Pj ≤ 0
  apply nonpos_of_mul_nonneg_left (a := Pi * Pj) (b := di * dj) ?_ hden
  have heq : (Pi * Pj) * (di * dj) = (Pi * di) * (Pj * dj) := by ring
  rw [heq, h1, h2]
  nlinarith [sq_nonneg F]

private theorem lagrangeProductDerivative_pairwise_nonneg_of_eval_log_pairwise
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ_strict : StrictMono τ)
    (c : Fin n) {x : ℝ}
    (hx : x ∈ Set.Ioo (τ ⟨c.val, by omega⟩) (τ ⟨c.val + 1, by omega⟩))
    (hpair : ∀ i j : Fin (n + 1),
      0 ≤ (lagrangeProductEval τ i x * lagrangeProductEval τ j x) *
        (lagrangeLogDerivativeSum τ i x * lagrangeLogDerivativeSum τ j x)) :
    ∀ i j : Fin (n + 1),
      0 ≤ lagrangeProductDerivativeEval τ i x * lagrangeProductDerivativeEval τ j x := by
  intro i j
  rw [lagrangeProductDerivativeEval_eq_eval_mul_logDerivativeSum τ hτ_strict c hx i,
    lagrangeProductDerivativeEval_eq_eval_mul_logDerivativeSum τ hτ_strict c hx j]
  change 0 ≤ (lagrangeProductEval τ i x * lagrangeLogDerivativeSum τ i x) *
    (lagrangeProductEval τ j x * lagrangeLogDerivativeSum τ j x)
  convert hpair i j using 1; ring

private theorem lagrangeLogDerivativeSum_zero_eq_A_nodes
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (x : ℝ) :
    lagrangeLogDerivativeSum τ 0 x =
      ∑ k : Fin n, 1 / (x - τ ⟨k.val + 1, by omega⟩) := by
  classical
  unfold lagrangeLogDerivativeSum
  let f : Fin (n + 1) → ℝ := fun k => 1 / (x - τ k)
  have herase := Finset.sum_erase_add (Finset.univ : Finset (Fin (n + 1))) f
    (Finset.mem_univ (0 : Fin (n + 1)))
  have htotal := Fin.sum_univ_succ f
  change (∑ k ∈ Finset.univ.erase (0 : Fin (n + 1)), f k) + f 0 = ∑ k, f k at herase
  rw [htotal] at herase
  change (∑ k ∈ Finset.univ.erase (0 : Fin (n + 1)), f k) = ∑ k : Fin n, f k.succ
  linarith

private theorem lagrangeLogDerivativeSum_last_eq_B_nodes
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (x : ℝ) :
    lagrangeLogDerivativeSum τ ⟨n, by omega⟩ x =
      ∑ k : Fin n, 1 / (x - τ ⟨k.val, by omega⟩) := by
  classical
  unfold lagrangeLogDerivativeSum
  let f : Fin (n + 1) → ℝ := fun k => 1 / (x - τ k)
  have herase := Finset.sum_erase_add (Finset.univ : Finset (Fin (n + 1))) f
    (Finset.mem_univ (Fin.last n))
  have htotal := Fin.sum_univ_castSucc f
  change (∑ k ∈ Finset.univ.erase (Fin.last n), f k) + f (Fin.last n) = ∑ k, f k
    at herase
  rw [htotal] at herase
  change (∑ k ∈ Finset.univ.erase (Fin.last n), f k) = ∑ k : Fin n, f k.castSucc
  linarith

private theorem sum_fin_eq_last_add_sum_cast_pred
    {n : ℕ} (hn : 1 ≤ n) (g : Fin n → ℝ) :
    (∑ k : Fin n, g k) = g ⟨n - 1, by omega⟩ +
      ∑ k : Fin (n - 1), g ⟨k.val, by omega⟩ := by
  let hN : n = n - 1 + 1 := by omega
  let e : Fin n ≃ Fin (n - 1 + 1) := (Fin.castOrderIso hN).toEquiv
  have hsum := Fintype.sum_equiv e g (fun i : Fin (n - 1 + 1) => g (e.symm i))
    (by intro x; simp [e])
  rw [hsum]
  rw [Fin.sum_univ_castSucc]
  have hlast : g (e.symm (Fin.last (n - 1))) = g ⟨n - 1, by omega⟩ := by
    congr 1
  have hcast : (∑ i : Fin (n - 1), g (e.symm i.castSucc)) =
      ∑ k : Fin (n - 1), g ⟨k.val, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro k _
    congr 1
  rw [hlast, hcast]
  ring

private theorem lagrangeLogDerivativeSum_zero_eq_A_endpoint_add_interior
    {n : ℕ} (hn : 1 ≤ n) (τ : Fin (n + 1) → ℝ) (x : ℝ) :
    lagrangeLogDerivativeSum τ 0 x =
      1 / (x - τ ⟨n, by omega⟩) +
        ∑ k : Fin (n - 1), 1 / (x - τ ⟨k.val + 1, by omega⟩) := by
  rw [lagrangeLogDerivativeSum_zero_eq_A_nodes]
  rw [sum_fin_eq_last_add_sum_cast_pred hn]
  simp only [one_div, add_left_inj, inv_inj, sub_right_inj]
  have hnat : n - 1 + 1 = n := Nat.sub_add_cancel hn
  exact congrArg τ (Fin.ext (by simp [hnat]))

private theorem sum_fin_eq_zero_add_sum_succ_pred
    {n : ℕ} (hn : 1 ≤ n) (g : Fin n → ℝ) :
    (∑ k : Fin n, g k) = g ⟨0, by omega⟩ +
      ∑ k : Fin (n - 1), g ⟨k.val + 1, by omega⟩ := by
  let hN : n = n - 1 + 1 := by omega
  let e : Fin n ≃ Fin (n - 1 + 1) := (Fin.castOrderIso hN).toEquiv
  have hsum := Fintype.sum_equiv e g (fun i : Fin (n - 1 + 1) => g (e.symm i))
    (by intro x; simp [e])
  rw [hsum]
  rw [Fin.sum_univ_succ]
  have hzero : g (e.symm 0) = g ⟨0, by omega⟩ := by
    congr 1
  have hsucc : (∑ i : Fin (n - 1), g (e.symm i.succ)) =
      ∑ k : Fin (n - 1), g ⟨k.val + 1, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro k _
    congr 1
  rw [hzero, hsucc]

private theorem lagrangeLogDerivativeSum_last_eq_B_endpoint_add_interior
    {n : ℕ} (hn : 1 ≤ n) (τ : Fin (n + 1) → ℝ) (x : ℝ) :
    lagrangeLogDerivativeSum τ ⟨n, by omega⟩ x =
      1 / (x - τ 0) +
        ∑ k : Fin (n - 1), 1 / (x - τ ⟨k.val + 1, by omega⟩) := by
  rw [lagrangeLogDerivativeSum_last_eq_B_nodes]
  rw [sum_fin_eq_zero_add_sum_succ_pred hn]
  simp

private theorem lagrangeLogDerivativeSum_zero_neg_of_mem_first_interval
    {n : ℕ} (hn : 1 ≤ n) (τ : Fin (n + 1) → ℝ) (hτ_strict : StrictMono τ)
    {x : ℝ} (hx : x ∈ Set.Ioo (τ 0) (τ ⟨1, by omega⟩)) :
    lagrangeLogDerivativeSum τ 0 x < 0 := by
  rw [lagrangeLogDerivativeSum_zero_eq_A_nodes]
  apply Finset.sum_neg
  · intro k _
    apply div_neg_of_pos_of_neg zero_lt_one
    have hnode : τ ⟨1, by omega⟩ ≤ τ ⟨k.val + 1, by omega⟩ := by
      by_cases hk : k.val = 0
      · have hval : (⟨k.val + 1, by omega⟩ : Fin (n + 1)).val =
            (⟨1, by omega⟩ : Fin (n + 1)).val := by
          simp [hk]
        exact le_of_eq (congrArg τ (Fin.ext hval.symm))
      · exact le_of_lt (hτ_strict (by
          change (1 : ℕ) < k.val + 1
          omega))
    nlinarith [hx.2, hnode]
  · exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩

private theorem lagrangeLogDerivativeSum_last_pos_of_mem_last_interval
    {n : ℕ} (hn : 1 ≤ n) (τ : Fin (n + 1) → ℝ) (hτ_strict : StrictMono τ)
    {x : ℝ} (hx : x ∈ Set.Ioo (τ ⟨n - 1, by omega⟩) (τ ⟨n, by omega⟩)) :
    0 < lagrangeLogDerivativeSum τ ⟨n, by omega⟩ x := by
  rw [lagrangeLogDerivativeSum_last_eq_B_nodes]
  apply Finset.sum_pos
  · intro k _
    apply div_pos zero_lt_one
    have hnode : τ ⟨k.val, by omega⟩ ≤ τ ⟨n - 1, by omega⟩ := by
      by_cases hk : k.val = n - 1
      · have hval : (⟨k.val, by omega⟩ : Fin (n + 1)).val =
            (⟨n - 1, by omega⟩ : Fin (n + 1)).val := by
          simp [hk]
        exact le_of_eq (congrArg τ (Fin.ext hval))
      · exact le_of_lt (hτ_strict (by
          change k.val < n - 1
          omega))
    nlinarith [hx.1, hnode]
  · exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩

private theorem sum_one_div_sub_interior_nodes_strictAnti_on_adjacent_interval
    {n : ℕ} (hn : 2 ≤ n) (τ : Fin (n + 1) → ℝ) (hτ_strict : StrictMono τ)
    (j : Fin n) {x y : ℝ} (hxy : x < y)
    (hx : x ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩))
    (hy : y ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩)) :
    (∑ k : Fin (n - 1), 1 / (y - τ ⟨k.val + 1, by omega⟩)) <
      ∑ k : Fin (n - 1), 1 / (x - τ ⟨k.val + 1, by omega⟩) := by
  classical
  have hs : (Finset.univ : Finset (Fin (n - 1))).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  exact sum_one_div_sub_strictAnti_on_components (Finset.univ : Finset (Fin (n - 1))) hs
    (fun k : Fin (n - 1) => τ ⟨k.val + 1, by omega⟩) hxy
    (by
      intro k _
      exact node_separated_of_mem_adjacent_interval τ hτ_strict j hx hy
        ⟨k.val + 1, by omega⟩)

private theorem sum_one_div_sub_B_nodes_strictAnti_on_adjacent_interval
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ_strict : StrictMono τ)
    (j : Fin n) {x y : ℝ} (hxy : x < y)
    (hx : x ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩))
    (hy : y ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩)) :
    (∑ k : Fin n, 1 / (y - τ ⟨k.val, by omega⟩)) <
      ∑ k : Fin n, 1 / (x - τ ⟨k.val, by omega⟩) := by
  classical
  have hs : (Finset.univ : Finset (Fin n)).Nonempty := ⟨j, Finset.mem_univ j⟩
  exact sum_one_div_sub_strictAnti_on_components (Finset.univ : Finset (Fin n)) hs
    (fun k : Fin n => τ ⟨k.val, by omega⟩) hxy
    (by
      intro k _
      exact node_separated_of_mem_adjacent_interval τ hτ_strict j hx hy ⟨k.val, by omega⟩)

private theorem sum_one_div_sub_A_nodes_strictAnti_on_adjacent_interval
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ_strict : StrictMono τ)
    (j : Fin n) {x y : ℝ} (hxy : x < y)
    (hx : x ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩))
    (hy : y ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩)) :
    (∑ k : Fin n, 1 / (y - τ ⟨k.val + 1, by omega⟩)) <
      ∑ k : Fin n, 1 / (x - τ ⟨k.val + 1, by omega⟩) := by
  classical
  have hs : (Finset.univ : Finset (Fin n)).Nonempty := ⟨j, Finset.mem_univ j⟩
  exact sum_one_div_sub_strictAnti_on_components (Finset.univ : Finset (Fin n)) hs
    (fun k : Fin n => τ ⟨k.val + 1, by omega⟩) hxy
    (by
      intro k _
      exact node_separated_of_mem_adjacent_interval τ hτ_strict j hx hy
        ⟨k.val + 1, by omega⟩)

private theorem add_mul_nonneg_of_nonneg_of_abs_le_abs
    {u v a : ℝ} (hv : 0 ≤ v) (huv : |u| ≤ |v|) (ha : |a| ≤ 1) :
    0 ≤ v + a * u := by
  have hau : |a * u| ≤ v := by
    calc |a * u| = |a| * |u| := abs_mul a u
      _ ≤ 1 * |u| := mul_le_mul_of_nonneg_right ha (abs_nonneg u)
      _ ≤ |v| := by simpa using huv
      _ = v := abs_of_nonneg hv
  have hbounds := abs_le.mp hau
  linarith

private theorem add_mul_nonpos_of_nonpos_of_abs_le_abs
    {u v a : ℝ} (hv : v ≤ 0) (huv : |u| ≤ |v|) (ha : |a| ≤ 1) :
    v + a * u ≤ 0 := by
  have hau : |a * u| ≤ -v := by
    calc |a * u| = |a| * |u| := abs_mul a u
      _ ≤ 1 * |u| := mul_le_mul_of_nonneg_right ha (abs_nonneg u)
      _ ≤ |v| := by simpa using huv
      _ = -v := abs_of_nonpos hv
  have hbounds := abs_le.mp hau
  linarith

private theorem perturb_endpoint_mul_nonpos_of_abs_bounds
    {u₁ u₂ v₁ v₂ a : ℝ} (h₁ : |u₁| ≤ |v₁|) (h₂ : |u₂| ≤ |v₂|)
    (ha : |a| ≤ 1) (hv : v₁ * v₂ ≤ 0) :
    (v₁ + a * u₁) * (v₂ + a * u₂) ≤ 0 := by
  by_cases hv₁0 : v₁ = 0
  · have hu₁ : u₁ = 0 := by
      rw [hv₁0, abs_zero] at h₁
      exact abs_nonpos_iff.mp h₁
    simp [hv₁0, hu₁]
  by_cases hv₂0 : v₂ = 0
  · have hu₂ : u₂ = 0 := by
      rw [hv₂0, abs_zero] at h₂
      exact abs_nonpos_iff.mp h₂
    simp [hv₂0, hu₂]
  by_cases hv₁pos : 0 < v₁
  · have hv₂neg : v₂ < 0 := by
      rw [lt_iff_not_ge]
      intro hv₂nonneg
      have hv₂pos : 0 < v₂ := lt_of_le_of_ne hv₂nonneg (Ne.symm hv₂0)
      exact not_le_of_gt (mul_pos hv₁pos hv₂pos) hv
    have hleft : 0 ≤ v₁ + a * u₁ :=
      add_mul_nonneg_of_nonneg_of_abs_le_abs (le_of_lt hv₁pos) h₁ ha
    have hright : v₂ + a * u₂ ≤ 0 :=
      add_mul_nonpos_of_nonpos_of_abs_le_abs (le_of_lt hv₂neg) h₂ ha
    exact mul_nonpos_of_nonneg_of_nonpos hleft hright
  · have hv₁neg : v₁ < 0 := lt_of_le_of_ne (by linarith) hv₁0
    have hv₂pos : 0 < v₂ := by
      rw [lt_iff_not_ge]
      intro hv₂nonpos
      have hv₂neg : v₂ < 0 := lt_of_le_of_ne hv₂nonpos hv₂0
      exact not_le_of_gt (mul_pos_of_neg_of_neg hv₁neg hv₂neg) hv
    have hleft : v₁ + a * u₁ ≤ 0 :=
      add_mul_nonpos_of_nonpos_of_abs_le_abs (le_of_lt hv₁neg) h₁ ha
    have hright : 0 ≤ v₂ + a * u₂ :=
      add_mul_nonneg_of_nonneg_of_abs_le_abs (le_of_lt hv₂pos) h₂ ha
    exact mul_nonpos_of_nonpos_of_nonneg hleft hright

private theorem exists_coeff_abs_le_one_add_mul_eq_zero
    {u v : ℝ} (hvu : |v| ≤ |u|) :
    ∃ a : ℝ, |a| ≤ 1 ∧ v + a * u = 0 := by
  by_cases hu : u = 0
  · have hv : v = 0 := by
      rw [hu, abs_zero] at hvu
      exact abs_nonpos_iff.mp hvu
    exact ⟨0, by norm_num, by simp [hv, hu]⟩
  · refine ⟨-v / u, ?_, ?_⟩
    · rw [abs_div, abs_neg]
      exact div_le_one_of_le₀ hvu (abs_nonneg u)
    · field_simp [hu]
      ring

private theorem polynomial_exists_root_Icc_of_eval_mul_nonpos
    (P : Polynomial ℝ) {a b : ℝ} (hab : a ≤ b)
    (hprod : P.eval a * P.eval b ≤ 0) :
    ∃ c ∈ Set.Icc a b, P.eval c = 0 := by
  by_cases ha : P.eval a = 0
  · exact ⟨a, ⟨le_rfl, hab⟩, ha⟩
  by_cases hb : P.eval b = 0
  · exact ⟨b, ⟨hab, le_rfl⟩, hb⟩
  by_cases hapos : 0 < P.eval a
  · have hbneg : P.eval b < 0 := by
      rw [lt_iff_not_ge]
      intro hb_nonneg
      have hbpos : 0 < P.eval b := lt_of_le_of_ne hb_nonneg (Ne.symm hb)
      exact not_le_of_gt (mul_pos hapos hbpos) hprod
    obtain ⟨c, hc_mem, hc_eq⟩ := intermediate_value_Icc' hab P.continuous.continuousOn
      (Set.mem_Icc.mpr ⟨le_of_lt hbneg, le_of_lt hapos⟩)
    exact ⟨c, hc_mem, hc_eq⟩
  · have haneg : P.eval a < 0 := lt_of_le_of_ne (by linarith) ha
    have hbpos : 0 < P.eval b := by
      rw [lt_iff_not_ge]
      intro hb_nonpos
      have hbneg : P.eval b < 0 := lt_of_le_of_ne hb_nonpos hb
      exact not_le_of_gt (mul_pos_of_neg_of_neg haneg hbneg) hprod
    obtain ⟨c, hc_mem, hc_eq⟩ := intermediate_value_Icc hab P.continuous.continuousOn
      (Set.mem_Icc.mpr ⟨le_of_lt haneg, le_of_lt hbpos⟩)
    exact ⟨c, hc_mem, hc_eq⟩

private theorem exists_coeff_abs_le_one_markovAuxR_perturb_eval_eq_zero
    (p q : Polynomial ℝ) {x : ℝ}
    (habs : |(markovAuxR q).eval x| ≤ |(Polynomial.derivative p).eval x|) :
    ∃ a : ℝ, |a| ≤ 1 ∧
      (markovAuxR q + Polynomial.C a * Polynomial.derivative p).eval x = 0 := by
  obtain ⟨a, ha, heq⟩ := exists_coeff_abs_le_one_add_mul_eq_zero habs
  refine ⟨a, ha, ?_⟩
  simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] using heq

private theorem derivative_le_markovAuxR_of_no_perturb_root
    (p q : Polynomial ℝ) {x : ℝ}
    (hno : ∀ a : ℝ, |a| ≤ 1 →
      (markovAuxR q + Polynomial.C a * Polynomial.derivative p).eval x ≠ 0) :
    |(Polynomial.derivative p).eval x| ≤ |(markovAuxR q).eval x| := by
  by_contra hnot
  have hle : |(markovAuxR q).eval x| ≤ |(Polynomial.derivative p).eval x| :=
    le_of_lt (lt_of_not_ge hnot)
  obtain ⟨a, ha, hzero⟩ := exists_coeff_abs_le_one_markovAuxR_perturb_eval_eq_zero p q hle
  exact hno a ha hzero

private theorem comparison_of_no_perturb_root
    (p q : Polynomial ℝ) {x : ℝ}
    (hno : ∀ a : ℝ, |a| ≤ 1 →
      (markovAuxR q + Polynomial.C a * Polynomial.derivative p).eval x ≠ 0) :
    |(Polynomial.derivative p).eval x| ≤
      max |(Polynomial.derivative q).eval x| |(markovAuxR q).eval x| := by
  exact (derivative_le_markovAuxR_of_no_perturb_root p q hno).trans (le_max_right _ _)

private theorem exists_root_markovAuxR_perturb_Icc
    (p q : Polynomial ℝ) {a s t : ℝ} (hst : s ≤ t)
    (hs_bound : |(Polynomial.derivative p).eval s| ≤ |(markovAuxR q).eval s|)
    (ht_bound : |(Polynomial.derivative p).eval t| ≤ |(markovAuxR q).eval t|)
    (hrprod : (markovAuxR q).eval s * (markovAuxR q).eval t ≤ 0)
    (ha : |a| ≤ 1) :
    ∃ c ∈ Set.Icc s t,
      (markovAuxR q + Polynomial.C a * Polynomial.derivative p).eval c = 0 := by
  apply polynomial_exists_root_Icc_of_eval_mul_nonpos
  · exact hst
  · simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] using
      perturb_endpoint_mul_nonpos_of_abs_bounds hs_bound ht_bound ha hrprod

private theorem polynomial_eval_mul_pos_of_no_root_between
    (P : Polynomial ℝ) {a b : ℝ} (hab : a ≤ b)
    (ha : P.eval a ≠ 0) (hb : P.eval b ≠ 0)
    (hno : ∀ x ∈ Set.Ioo a b, P.eval x ≠ 0) :
    0 < P.eval a * P.eval b := by
  by_contra hnot
  have hprod : P.eval a * P.eval b ≤ 0 := le_of_not_gt hnot
  obtain ⟨c, hc_mem, hc_zero⟩ := polynomial_exists_root_Icc_of_eval_mul_nonpos P hab hprod
  have hca : c ≠ a := by
    intro h
    rw [h] at hc_zero
    exact ha hc_zero
  have hcb : c ≠ b := by
    intro h
    rw [h] at hc_zero
    exact hb hc_zero
  have hc_ioo : c ∈ Set.Ioo a b := by
    exact ⟨lt_of_le_of_ne hc_mem.1 (Ne.symm hca), lt_of_le_of_ne hc_mem.2 hcb⟩
  exact hno c hc_ioo hc_zero

private theorem not_extra_root_of_natDegree_eq_of_fin_roots
    {n : ℕ} (hn : 0 < n) (P : Polynomial ℝ) (ρ : Fin n → ℝ)
    (hρ : Function.Injective ρ) (hdeg : P.natDegree = n)
    (hroots : ∀ i : Fin n, P.eval (ρ i) = 0)
    {x : ℝ} (hxnot : ∀ i : Fin n, x ≠ ρ i) (hxroot : P.eval x = 0) : False := by
  have hPne : P ≠ 0 := by
    intro hP0
    rw [hP0, Polynomial.natDegree_zero] at hdeg
    omega
  have hmem_roots : ∀ y ∈ insert x (Finset.image ρ Finset.univ), y ∈ P.roots.toFinset := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_image] at hy
    rcases hy with rfl | ⟨i, _, rfl⟩
    · exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hPne).mpr hxroot)
    · exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hPne).mpr (hroots i))
  have hcard_subset := Finset.card_le_card hmem_roots
  have hx_not_mem : x ∉ Finset.image ρ Finset.univ := by
    intro hxmem
    rcases Finset.mem_image.mp hxmem with ⟨i, _, hi⟩
    exact hxnot i hi.symm
  have hcard_lower : n + 1 ≤ P.roots.toFinset.card := by
    calc n + 1 = (insert x (Finset.image ρ Finset.univ)).card := by
          rw [Finset.card_insert_of_notMem hx_not_mem, Finset.card_image_of_injective _ hρ,
            Finset.card_univ, Fintype.card_fin]
      _ ≤ P.roots.toFinset.card := hcard_subset
  have hcard_upper : P.roots.toFinset.card ≤ n := by
    calc P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ = n := hdeg
  omega

private theorem not_extra_root_of_markovAuxR_perturb_of_fin_roots
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (a : ℝ) (ρ : Fin n → ℝ)
    (hρ : Function.Injective ρ) (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree = n)
    (hroots : ∀ i : Fin n,
      (markovAuxR q + Polynomial.C a * Polynomial.derivative p).eval (ρ i) = 0)
    {x : ℝ} (hxnot : ∀ i : Fin n, x ≠ ρ i)
    (hxroot : (markovAuxR q + Polynomial.C a * Polynomial.derivative p).eval x = 0) : False := by
  exact not_extra_root_of_natDegree_eq_of_fin_roots (by omega : 0 < n)
    (markovAuxR q + Polynomial.C a * Polynomial.derivative p) ρ hρ
    (markovAuxR_add_C_mul_derivative_natDegree_eq hn p q a hpdeg hqdeg)
    hroots hxnot hxroot

private theorem derivative_q_splits
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩) :
    (Polynomial.derivative q).Splits := by
  rw [Polynomial.splits_iff_card_roots]
  have hdeg := derivative_natDegree_eq_pred_of_natDegree_eq (by omega : 1 ≤ n) q hqdeg
  have hDne : Polynomial.derivative q ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hdeg
    omega
  have hmem_roots : ∀ i : Fin (n - 1),
      τ ⟨i.val + 1, by omega⟩ ∈ (Polynomial.derivative q).roots.toFinset := by
    intro i
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hDne).mpr ((hqcrit _).mpr ⟨i, rfl⟩))
  have hcard_lower : n - 1 ≤ (Polynomial.derivative q).roots.card := by
    have hsubset : Finset.image (fun i : Fin (n - 1) => τ ⟨i.val + 1, by omega⟩) Finset.univ ⊆
        (Polynomial.derivative q).roots.toFinset := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      exact hmem_roots i
    have hinj : Function.Injective (fun i : Fin (n - 1) => τ ⟨i.val + 1, by omega⟩) := by
      intro i j hij
      have hfin : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) = ⟨j.val + 1, by omega⟩ :=
        hτ_strict.injective hij
      ext
      exact Nat.succ.inj (congrArg Fin.val hfin)
    calc n - 1 = (Finset.image (fun i : Fin (n - 1) => τ ⟨i.val + 1, by omega⟩)
          Finset.univ).card := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      _ ≤ (Polynomial.derivative q).roots.toFinset.card := by
        exact Finset.card_le_card hsubset
      _ ≤ (Polynomial.derivative q).roots.card := Multiset.toFinset_card_le _
  exact le_antisymm (Polynomial.card_roots' (Polynomial.derivative q)) (by
    simpa [hdeg] using hcard_lower)

private theorem derivative_q_roots_nodup
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩) :
    (Polynomial.derivative q).roots.Nodup := by
  rw [← Multiset.toFinset_card_eq_card_iff_nodup]
  have hdeg := derivative_natDegree_eq_pred_of_natDegree_eq (by omega : 1 ≤ n) q hqdeg
  have hDne : Polynomial.derivative q ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hdeg
    omega
  have hsubset : Finset.image (fun i : Fin (n - 1) => τ ⟨i.val + 1, by omega⟩) Finset.univ ⊆
      (Polynomial.derivative q).roots.toFinset := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hDne).mpr ((hqcrit _).mpr ⟨i, rfl⟩))
  have hinj : Function.Injective (fun i : Fin (n - 1) => τ ⟨i.val + 1, by omega⟩) := by
    intro i j hij
    have hfin : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) = ⟨j.val + 1, by omega⟩ :=
      hτ_strict.injective hij
    ext
    exact Nat.succ.inj (congrArg Fin.val hfin)
  have hcard_lower : n - 1 ≤ (Polynomial.derivative q).roots.toFinset.card := by
    calc n - 1 = (Finset.image (fun i : Fin (n - 1) => τ ⟨i.val + 1, by omega⟩)
          Finset.univ).card := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      _ ≤ (Polynomial.derivative q).roots.toFinset.card := Finset.card_le_card hsubset
  have hcard_upper : (Polynomial.derivative q).roots.card ≤ n - 1 := by
    simpa [hdeg] using Polynomial.card_roots' (Polynomial.derivative q)
  exact le_antisymm (Multiset.toFinset_card_le _) (le_trans hcard_upper hcard_lower)

private theorem derivative_q_roots_toFinset_eq
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (_hτ_strict : StrictMono τ) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩) :
    (Polynomial.derivative q).roots.toFinset =
      Finset.image (fun i : Fin (n - 1) => τ ⟨i.val + 1, by omega⟩) Finset.univ := by
  apply Finset.Subset.antisymm
  · intro x hx
    have hDne : Polynomial.derivative q ≠ 0 := by
      have hdeg := derivative_natDegree_eq_pred_of_natDegree_eq (by omega : 1 ≤ n) q hqdeg
      intro hzero
      rw [hzero, Polynomial.natDegree_zero] at hdeg
      omega
    have hxroot : (Polynomial.derivative q).eval x = 0 :=
      (Polynomial.mem_roots hDne).mp (Multiset.mem_toFinset.mp hx)
    obtain ⟨i, hi⟩ := (hqcrit x).mp hxroot
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    have hDne : Polynomial.derivative q ≠ 0 := by
      have hdeg := derivative_natDegree_eq_pred_of_natDegree_eq (by omega : 1 ≤ n) q hqdeg
      intro hzero
      rw [hzero, Polynomial.natDegree_zero] at hdeg
      omega
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hDne).mpr ((hqcrit _).mpr ⟨i, rfl⟩))

private theorem markovAuxA_roots_eq
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (hqdeg : q.natDegree = n) :
    (markovAuxA q).roots = ({1} : Multiset ℝ) + (Polynomial.derivative q).roots := by
  unfold markovAuxA
  have hDdeg := derivative_natDegree_eq_pred_of_natDegree_eq (by omega : 1 ≤ n) q hqdeg
  have hDne : Polynomial.derivative q ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hDdeg
    omega
  have hlin : (Polynomial.X - (1 : Polynomial ℝ)) ≠ 0 := by
    simpa using Polynomial.X_sub_C_ne_zero (r := (1 : ℝ))
  have hprod : (Polynomial.X - (1 : Polynomial ℝ)) * Polynomial.derivative q ≠ 0 :=
    mul_ne_zero hlin hDne
  rw [Polynomial.roots_mul hprod]
  have hlin_roots : (Polynomial.X - (1 : Polynomial ℝ)).roots = ({1} : Multiset ℝ) := by
    simpa using Polynomial.roots_X_sub_C (R := ℝ) 1
  rw [hlin_roots]

private theorem markovAuxB_roots_eq
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (hqdeg : q.natDegree = n) :
    (markovAuxB q).roots = ({-1} : Multiset ℝ) + (Polynomial.derivative q).roots := by
  unfold markovAuxB
  have hDdeg := derivative_natDegree_eq_pred_of_natDegree_eq (by omega : 1 ≤ n) q hqdeg
  have hDne : Polynomial.derivative q ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hDdeg
    omega
  have hlin : (Polynomial.X + (1 : Polynomial ℝ)) ≠ 0 := by
    simpa [sub_eq_add_neg] using Polynomial.X_sub_C_ne_zero (r := (-1 : ℝ))
  have hprod : (Polynomial.X + (1 : Polynomial ℝ)) * Polynomial.derivative q ≠ 0 :=
    mul_ne_zero hlin hDne
  rw [Polynomial.roots_mul hprod]
  have hlin_roots : (Polynomial.X + (1 : Polynomial ℝ)).roots = ({-1} : Multiset ℝ) := by
    simpa using Polynomial.roots_X_add_C (R := ℝ) 1
  rw [hlin_roots]

private theorem derivative_q_roots_eq_node_multiset
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩) :
    (Polynomial.derivative q).roots =
      (Finset.image (fun i : Fin (n - 1) => τ ⟨i.val + 1, by omega⟩) Finset.univ).val := by
  calc (Polynomial.derivative q).roots
      = (Polynomial.derivative q).roots.toFinset.val := by
          rw [Multiset.toFinset_val]
          exact (Multiset.dedup_eq_self.mpr
            (derivative_q_roots_nodup hn q τ hτ_strict hqdeg hqcrit)).symm
    _ = (Finset.image (fun i : Fin (n - 1) => τ ⟨i.val + 1, by omega⟩) Finset.univ).val := by
          rw [derivative_q_roots_toFinset_eq hn q τ hτ_strict hqdeg hqcrit]

private theorem derivative_q_roots_sum_eq_interior_node_sum
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (g : ℝ → ℝ) :
    (((Polynomial.derivative q).roots.map g).sum) =
      ∑ i : Fin (n - 1), g (τ ⟨i.val + 1, by omega⟩) := by
  rw [derivative_q_roots_eq_node_multiset hn q τ hτ_strict hqdeg hqcrit]
  change (Finset.image (fun i : Fin (n - 1) => τ ⟨i.val + 1, by omega⟩) Finset.univ).sum g =
    Finset.univ.sum (fun i : Fin (n - 1) => g (τ ⟨i.val + 1, by omega⟩))
  rw [Finset.sum_image]
  intro i _ j _ hij
  have hfin : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) = ⟨j.val + 1, by omega⟩ :=
    hτ_strict.injective hij
  ext
  exact Nat.succ.inj (congrArg Fin.val hfin)

private theorem markovAuxA_splits
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩) :
    (markovAuxA q).Splits := by
  unfold markovAuxA
  simpa using (Polynomial.Splits.X_sub_C (R := ℝ) 1).mul
    (derivative_q_splits hn q τ hτ_strict hqdeg hqcrit)

private theorem markovAuxB_splits
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩) :
    (markovAuxB q).Splits := by
  unfold markovAuxB
  simpa [sub_eq_add_neg] using (Polynomial.Splits.X_sub_C (R := ℝ) (-1)).mul
    (derivative_q_splits hn q τ hτ_strict hqdeg hqcrit)

private theorem markovAuxA_derivative_div_eval_eq_roots_sum
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    {x : ℝ} (hx : (markovAuxA q).eval x ≠ 0) :
    (Polynomial.derivative (markovAuxA q)).eval x / (markovAuxA q).eval x =
      ((markovAuxA q).roots.map fun z => 1 / (x - z)).sum :=
  (markovAuxA_splits hn q τ hτ_strict hqdeg hqcrit).eval_derivative_div_eval_of_ne_zero hx

private theorem markovAuxB_derivative_div_eval_eq_roots_sum
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    {x : ℝ} (hx : (markovAuxB q).eval x ≠ 0) :
    (Polynomial.derivative (markovAuxB q)).eval x / (markovAuxB q).eval x =
      ((markovAuxB q).roots.map fun z => 1 / (x - z)).sum :=
  (markovAuxB_splits hn q τ hτ_strict hqdeg hqcrit).eval_derivative_div_eval_of_ne_zero hx

private theorem markovAuxA_derivative_div_eval_eq_node_sum
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    {x : ℝ} (hx : (markovAuxA q).eval x ≠ 0) :
    (Polynomial.derivative (markovAuxA q)).eval x / (markovAuxA q).eval x =
      1 / (x - τ ⟨n, by omega⟩) +
        ∑ i : Fin (n - 1), 1 / (x - τ ⟨i.val + 1, by omega⟩) := by
  rw [markovAuxA_derivative_div_eval_eq_roots_sum hn q τ hτ_strict hqdeg hqcrit hx,
    markovAuxA_roots_eq hn q hqdeg]
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_singleton, Multiset.sum_singleton]
  rw [derivative_q_roots_sum_eq_interior_node_sum hn q τ hτ_strict hqdeg hqcrit]
  rw [hτ_right]

private theorem markovAuxB_derivative_div_eval_eq_node_sum
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_left : τ 0 = -1) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    {x : ℝ} (hx : (markovAuxB q).eval x ≠ 0) :
    (Polynomial.derivative (markovAuxB q)).eval x / (markovAuxB q).eval x =
      1 / (x - τ 0) + ∑ i : Fin (n - 1), 1 / (x - τ ⟨i.val + 1, by omega⟩) := by
  rw [markovAuxB_derivative_div_eval_eq_roots_sum hn q τ hτ_strict hqdeg hqcrit hx,
    markovAuxB_roots_eq hn q hqdeg]
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_singleton, Multiset.sum_singleton]
  rw [derivative_q_roots_sum_eq_interior_node_sum hn q τ hτ_strict hqdeg hqcrit]
  rw [hτ_left]

private theorem markovAux_log_derivative_difference_eq_endpoints
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_left : τ 0 = -1)
    (hτ_right : τ ⟨n, by omega⟩ = 1) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    {x : ℝ} (hxA : (markovAuxA q).eval x ≠ 0) (hxB : (markovAuxB q).eval x ≠ 0) :
    (Polynomial.derivative (markovAuxA q)).eval x / (markovAuxA q).eval x -
      (Polynomial.derivative (markovAuxB q)).eval x / (markovAuxB q).eval x =
      1 / (x - τ ⟨n, by omega⟩) - 1 / (x - τ 0) := by
  rw [markovAuxA_derivative_div_eval_eq_node_sum hn q τ hτ_strict hτ_right hqdeg
      hqcrit hxA,
    markovAuxB_derivative_div_eval_eq_node_sum hn q τ hτ_strict hτ_left hqdeg hqcrit hxB]
  ring

private theorem derivative_q_ne_zero_at_left_endpoint
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩) :
    (Polynomial.derivative q).eval (τ 0) ≠ 0 := by
  intro hzero
  obtain ⟨i, hi⟩ := (hqcrit (τ 0)).mp hzero
  have hlt : τ 0 < τ ⟨i.val + 1, by omega⟩ := hτ_strict (by
    change 0 < i.val + 1
    omega)
  rw [← hi] at hlt
  exact (lt_irrefl _) hlt

private theorem derivative_q_ne_zero_at_right_endpoint
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩) :
    (Polynomial.derivative q).eval (τ ⟨n, by omega⟩) ≠ 0 := by
  intro hzero
  obtain ⟨i, hi⟩ := (hqcrit (τ ⟨n, by omega⟩)).mp hzero
  have hlt : τ ⟨i.val + 1, by omega⟩ < τ ⟨n, by omega⟩ := hτ_strict (by
    change i.val + 1 < n
    omega)
  rw [← hi] at hlt
  exact (lt_irrefl _) hlt

private theorem derivative_q_ne_zero_between_adjacent_nodes
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin n) {x : ℝ}
    (hx : x ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩)) :
    (Polynomial.derivative q).eval x ≠ 0 := by
  intro hxzero
  obtain ⟨i, hi⟩ := (hqcrit x).mp hxzero
  have hleft_lt : τ ⟨j.val, by omega⟩ < τ ⟨i.val + 1, by omega⟩ := by
    rw [← hi]
    exact hx.1
  have hright_lt : τ ⟨i.val + 1, by omega⟩ < τ ⟨j.val + 1, by omega⟩ := by
    rw [← hi]
    exact hx.2
  have hleft_index : j.val < i.val + 1 := by
    exact (hτ_strict.lt_iff_lt).mp hleft_lt
  have hright_index : i.val + 1 < j.val + 1 := by
    exact (hτ_strict.lt_iff_lt).mp hright_lt
  omega

private theorem markovAuxA_eval_ne_zero_of_mem_adjacent_interval
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin n) {x : ℝ}
    (hx : x ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩)) :
    (markovAuxA q).eval x ≠ 0 := by
  unfold markovAuxA
  rw [Polynomial.eval_mul]
  apply mul_ne_zero
  · simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
    have hright_node : τ ⟨j.val + 1, by omega⟩ ≤ τ ⟨n, by omega⟩ := by
      by_cases hlast : j.val + 1 = n
      · have hval : (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val =
            (⟨n, by omega⟩ : Fin (n + 1)).val := by
          simp [hlast]
        exact le_of_eq (congrArg τ (Fin.ext hval))
      · exact le_of_lt (hτ_strict (by
          change j.val + 1 < n
          omega))
    have hxlt1 : x < 1 := by
      rw [← hτ_right]
      exact lt_of_lt_of_le hx.2 hright_node
    linarith
  · exact derivative_q_ne_zero_between_adjacent_nodes hn q τ hτ_strict hqcrit j hx

private theorem markovAuxB_eval_ne_zero_of_mem_adjacent_interval
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin n) {x : ℝ}
    (hx : x ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩)) :
    (markovAuxB q).eval x ≠ 0 := by
  unfold markovAuxB
  rw [Polynomial.eval_mul]
  apply mul_ne_zero
  · simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    have hleft_node : τ 0 ≤ τ ⟨j.val, by omega⟩ := by
      by_cases hfirst : j.val = 0
      · have hval : (⟨j.val, by omega⟩ : Fin (n + 1)).val =
            (0 : Fin (n + 1)).val := by
          simp [hfirst]
        exact le_of_eq (congrArg τ (Fin.ext hval.symm))
      · exact le_of_lt (hτ_strict (by
          change (0 : Fin (n + 1)) < ⟨j.val, by omega⟩
          exact_mod_cast (show 0 < j.val by omega)))
    have hneglt : -1 < x := by
      rw [← hτ_left]
      exact lt_of_le_of_lt hleft_node hx.1
    linarith
  · exact derivative_q_ne_zero_between_adjacent_nodes hn q τ hτ_strict hqcrit j hx

private theorem markovAuxA_eval_ne_zero_of_mem_not_last_interval
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin n) (hjlast : j.val + 1 < n) {x : ℝ}
    (hx : x ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩)) :
    (markovAuxA q).eval x ≠ 0 := by
  unfold markovAuxA
  rw [Polynomial.eval_mul]
  apply mul_ne_zero
  · simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
    have hxlt1 : x < 1 := by
      have hnode_lt : τ ⟨j.val + 1, by omega⟩ < τ ⟨n, by omega⟩ :=
        hτ_strict (by simpa using hjlast)
      rw [hτ_right] at hnode_lt
      exact lt_trans hx.2 hnode_lt
    linarith
  · exact derivative_q_ne_zero_between_adjacent_nodes hn q τ hτ_strict hqcrit j hx

private theorem markovAuxB_eval_ne_zero_of_mem_not_first_interval
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin n) (hjfirst : 0 < j.val) {x : ℝ}
    (hx : x ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩)) :
    (markovAuxB q).eval x ≠ 0 := by
  unfold markovAuxB
  rw [Polynomial.eval_mul]
  apply mul_ne_zero
  · simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    have hneglt : -1 < x := by
      have hnode_lt : τ 0 < τ ⟨j.val, by omega⟩ := hτ_strict (by exact (Fin.mk_lt_mk).2 hjfirst)
      rw [hτ_left] at hnode_lt
      exact lt_trans hnode_lt hx.1
    linarith
  · exact derivative_q_ne_zero_between_adjacent_nodes hn q τ hτ_strict hqcrit j hx

private theorem markovAux_log_derivative_difference_neg_on_middle_interval
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_left : τ 0 = -1)
    (hτ_right : τ ⟨n, by omega⟩ = 1) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin n) (hjfirst : 0 < j.val) (hjlast : j.val + 1 < n) {x : ℝ}
    (hx : x ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩)) :
    (Polynomial.derivative (markovAuxA q)).eval x / (markovAuxA q).eval x -
      (Polynomial.derivative (markovAuxB q)).eval x / (markovAuxB q).eval x < 0 := by
  rw [markovAux_log_derivative_difference_eq_endpoints hn q τ hτ_strict hτ_left hτ_right
    hqdeg hqcrit
    (markovAuxA_eval_ne_zero_of_mem_not_last_interval hn q τ hτ_strict hτ_right hqcrit
      j hjlast hx)
    (markovAuxB_eval_ne_zero_of_mem_not_first_interval hn q τ hτ_strict hτ_left hqcrit
      j hjfirst hx)]
  have hleft_node : τ 0 < τ ⟨j.val, by omega⟩ :=
    hτ_strict (show (0 : Fin (n + 1)) < ⟨j.val, by omega⟩ by
      exact_mod_cast hjfirst)
  have hright_node : τ ⟨j.val + 1, by omega⟩ < τ ⟨n, by omega⟩ :=
    hτ_strict (show (⟨j.val + 1, by omega⟩ : Fin (n + 1)) < ⟨n, by omega⟩ by
      exact_mod_cast hjlast)
  exact one_div_sub_right_sub_one_div_sub_left_neg
    (lt_trans hleft_node hx.1)
    (lt_trans hx.2 hright_node)


private theorem markovAuxB_log_derivative_strictAnti_on_middle_interval
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_left : τ 0 = -1) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin n) (hjfirst : 0 < j.val) {x y : ℝ} (hxy : x < y)
    (hx : x ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩))
    (hy : y ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩)) :
    (Polynomial.derivative (markovAuxB q)).eval y / (markovAuxB q).eval y <
      (Polynomial.derivative (markovAuxB q)).eval x / (markovAuxB q).eval x := by
  rw [markovAuxB_derivative_div_eval_eq_node_sum hn q τ hτ_strict hτ_left hqdeg hqcrit
      (markovAuxB_eval_ne_zero_of_mem_not_first_interval hn q τ hτ_strict hτ_left hqcrit
        j hjfirst hy),
    markovAuxB_derivative_div_eval_eq_node_sum hn q τ hτ_strict hτ_left hqdeg hqcrit
      (markovAuxB_eval_ne_zero_of_mem_not_first_interval hn q τ hτ_strict hτ_left hqcrit
        j hjfirst hx)]
  have hleft_node : τ 0 < τ ⟨j.val, by omega⟩ :=
    hτ_strict (show (0 : Fin (n + 1)) < ⟨j.val, by omega⟩ by
      exact_mod_cast hjfirst)
  have hendpoint : 1 / (y - τ 0) < 1 / (x - τ 0) :=
    one_div_sub_strictAnti_on_component hxy (Or.inr ⟨lt_trans hleft_node hx.1,
      lt_trans hleft_node hy.1⟩)
  have hinterior := sum_one_div_sub_interior_nodes_strictAnti_on_adjacent_interval hn τ
    hτ_strict j hxy hx hy
  linarith

private theorem markovAuxB_log_derivative_pos_at_A_critical_middle
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_left : τ 0 = -1)
    (hτ_right : τ ⟨n, by omega⟩ = 1) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin n) (hjfirst : 0 < j.val) (hjlast : j.val + 1 < n) {η : ℝ}
    (hηmem : η ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩))
    (hηcrit : (Polynomial.derivative (markovAuxA q)).eval η = 0) :
    0 < (Polynomial.derivative (markovAuxB q)).eval η / (markovAuxB q).eval η := by
  have hneg := markovAux_log_derivative_difference_neg_on_middle_interval hn q τ hτ_strict
    hτ_left hτ_right hqdeg hqcrit j hjfirst hjlast hηmem
  rw [hηcrit, zero_div, zero_sub] at hneg
  linarith

private theorem derivative_q_eval_mul_pos_left_endpoint_of_mem_first_interval
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    {x : ℝ} (hx : x ∈ Set.Ioo (τ 0) (τ ⟨1, by omega⟩)) :
    0 < (Polynomial.derivative q).eval (τ 0) * (Polynomial.derivative q).eval x := by
  have hleft := derivative_q_ne_zero_at_left_endpoint hn q τ hτ_strict hqcrit
  have hxne := derivative_q_ne_zero_between_adjacent_nodes hn q τ hτ_strict hqcrit
    (⟨0, by omega⟩ : Fin n) hx
  apply polynomial_eval_mul_pos_of_no_root_between (Polynomial.derivative q) (le_of_lt hx.1)
    hleft hxne
  intro y hy
  apply derivative_q_ne_zero_between_adjacent_nodes hn q τ hτ_strict hqcrit
    (⟨0, by omega⟩ : Fin n)
  exact ⟨hy.1, lt_trans hy.2 hx.2⟩

private theorem derivative_q_eval_mul_pos_right_endpoint_of_mem_last_interval
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    {x : ℝ} (hx : x ∈ Set.Ioo (τ ⟨n - 1, by omega⟩) (τ ⟨n, by omega⟩)) :
    0 < (Polynomial.derivative q).eval x *
      (Polynomial.derivative q).eval (τ ⟨n, by omega⟩) := by
  have hlast : (⟨n - 1 + 1, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := by
    ext
    exact Nat.sub_add_cancel (by omega : 1 ≤ n)
  have hxne := derivative_q_ne_zero_between_adjacent_nodes hn q τ hτ_strict hqcrit
    (⟨n - 1, by omega⟩ : Fin n) (by
      change x ∈ Set.Ioo (τ ⟨n - 1, by omega⟩) (τ ⟨n - 1 + 1, by omega⟩)
      rw [hlast]
      exact hx)
  have hright := derivative_q_ne_zero_at_right_endpoint hn q τ hτ_strict hqcrit
  apply polynomial_eval_mul_pos_of_no_root_between (Polynomial.derivative q) (le_of_lt hx.2)
    hxne hright
  intro y hy
  apply derivative_q_ne_zero_between_adjacent_nodes hn q τ hτ_strict hqcrit
    (⟨n - 1, by omega⟩ : Fin n)
  change y ∈ Set.Ioo (τ ⟨n - 1, by omega⟩) (τ ⟨n - 1 + 1, by omega⟩)
  rw [hlast]
  exact ⟨lt_trans hx.1 hy.1, hy.2⟩

private theorem derivative_q_eval_mul_pos_of_mem_same_adjacent_interval
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin n) {a b : ℝ}
    (ha : a ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩))
    (hb : b ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩)) :
    0 < (Polynomial.derivative q).eval a * (Polynomial.derivative q).eval b := by
  have hane := derivative_q_ne_zero_between_adjacent_nodes hn q τ hτ_strict hqcrit j ha
  have hbne := derivative_q_ne_zero_between_adjacent_nodes hn q τ hτ_strict hqcrit j hb
  by_cases hab : a ≤ b
  · apply polynomial_eval_mul_pos_of_no_root_between (Polynomial.derivative q) hab hane hbne
    intro x hx
    apply derivative_q_ne_zero_between_adjacent_nodes hn q τ hτ_strict hqcrit j
    exact ⟨lt_trans ha.1 hx.1, lt_trans hx.2 hb.2⟩
  · have hba : b ≤ a := le_of_not_ge hab
    have h := polynomial_eval_mul_pos_of_no_root_between (Polynomial.derivative q) hba hbne hane
      (by
        intro x hx
        apply derivative_q_ne_zero_between_adjacent_nodes hn q τ hτ_strict hqcrit j
        exact ⟨lt_trans hb.1 hx.1, lt_trans hx.2 ha.2⟩)
    simpa [mul_comm] using h

private theorem markovAuxR_eval_mul_neg_left_endpoint_of_B_derivative_zero
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    {ξ : ℝ} (hξmem : ξ ∈ Set.Ioo (τ 0) (τ ⟨1, by omega⟩))
    (hξzero : (Polynomial.derivative (markovAuxB q)).eval ξ = 0) :
    (markovAuxR q).eval (τ 0) * (markovAuxR q).eval ξ < 0 := by
  have hsame := derivative_q_eval_mul_pos_left_endpoint_of_mem_first_interval hn q τ hτ_strict
    hqcrit hξmem
  rw [hτ_left] at hsame
  rw [hτ_left, markovAuxR_eval_neg_one,
    markovAuxB_eval_derivative_zero_of_derivative_zero q hξzero]
  nlinarith

private theorem markovAuxR_eval_mul_neg_right_endpoint_of_A_derivative_zero
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    {η : ℝ} (hηmem : η ∈ Set.Ioo (τ ⟨n - 1, by omega⟩) (τ ⟨n, by omega⟩))
    (hηzero : (Polynomial.derivative (markovAuxA q)).eval η = 0) :
    (markovAuxR q).eval η * (markovAuxR q).eval (τ ⟨n, by omega⟩) < 0 := by
  have hsame := derivative_q_eval_mul_pos_right_endpoint_of_mem_last_interval hn q τ hτ_strict
    hqcrit hηmem
  rw [hτ_right] at hsame
  rw [markovAuxA_eval_derivative_zero_of_derivative_zero q hηzero,
    hτ_right, markovAuxR_eval_one]
  nlinarith

private theorem markovAuxR_eval_mul_neg_of_aux_derivative_zeros_in_same_adjacent_interval
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin n) {η ξ : ℝ}
    (hηmem : η ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩))
    (hξmem : ξ ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩))
    (hηzero : (Polynomial.derivative (markovAuxA q)).eval η = 0)
    (hξzero : (Polynomial.derivative (markovAuxB q)).eval ξ = 0) :
    (markovAuxR q).eval η * (markovAuxR q).eval ξ < 0 := by
  have hsame := derivative_q_eval_mul_pos_of_mem_same_adjacent_interval hn q τ hτ_strict
    hqcrit j hηmem hξmem
  rw [markovAuxA_eval_derivative_zero_of_derivative_zero q hηzero,
    markovAuxB_eval_derivative_zero_of_derivative_zero q hξzero]
  nlinarith

private theorem exists_markovAuxB_derivative_zero_between_nodes
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ)
    (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin (n - 1)) :
    ∃ ξ ∈ Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩),
      (Polynomial.derivative (markovAuxB q)).eval ξ = 0 := by
  have hleft : (markovAuxB q).eval (τ ⟨j.val, by omega⟩) = 0 := by
    by_cases hzero : j.val = 0
    · have hfin : (⟨j.val, by omega⟩ : Fin (n + 1)) = 0 := by
        ext
        exact hzero
      rw [hfin, hτ_left]
      exact markovAuxB_eval_neg_one q
    · apply markovAuxB_eval_eq_zero_of_derivative_q_eq_zero
      let k : Fin (n - 1) := ⟨j.val - 1, by omega⟩
      have hnode : τ ⟨j.val, by omega⟩ = τ ⟨k.val + 1, by omega⟩ := by
        congr
        dsimp [k]
        omega
      rw [hnode]
      exact (hqcrit _).mpr ⟨k, rfl⟩
  have hright : (markovAuxB q).eval (τ ⟨j.val + 1, by omega⟩) = 0 := by
    apply markovAuxB_eval_eq_zero_of_derivative_q_eq_zero
    exact (hqcrit _).mpr ⟨j, rfl⟩
  exact polynomial_derivative_zero_between_of_eval_eq (markovAuxB q)
    (hτ_strict (by
      change j.val < j.val + 1
      omega))
    (hleft.trans hright.symm)

private noncomputable def markovEtaInterior
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin (n - 1)) : ℝ :=
  Classical.choose (exists_markovAuxA_derivative_zero_between_nodes hn q τ hτ_strict hτ_right
    hqcrit j)

private theorem markovEtaInterior_mem
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin (n - 1)) :
    markovEtaInterior hn q τ hτ_strict hτ_right hqcrit j ∈
      Set.Ioo (τ ⟨j.val + 1, by omega⟩) (τ ⟨j.val + 2, by omega⟩) :=
  (Classical.choose_spec (exists_markovAuxA_derivative_zero_between_nodes hn q τ hτ_strict
    hτ_right hqcrit j)).1

private theorem markovEtaInterior_derivative_zero
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin (n - 1)) :
    (Polynomial.derivative (markovAuxA q)).eval
      (markovEtaInterior hn q τ hτ_strict hτ_right hqcrit j) = 0 :=
  (Classical.choose_spec (exists_markovAuxA_derivative_zero_between_nodes hn q τ hτ_strict
    hτ_right hqcrit j)).2

private noncomputable def markovXiInterior
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin (n - 1)) : ℝ :=
  Classical.choose (exists_markovAuxB_derivative_zero_between_nodes hn q τ hτ_strict hτ_left
    hqcrit j)

private theorem markovXiInterior_mem
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin (n - 1)) :
    markovXiInterior hn q τ hτ_strict hτ_left hqcrit j ∈
      Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩) :=
  (Classical.choose_spec (exists_markovAuxB_derivative_zero_between_nodes hn q τ hτ_strict
    hτ_left hqcrit j)).1

private theorem markovXiInterior_derivative_zero
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin (n - 1)) :
    (Polynomial.derivative (markovAuxB q)).eval
      (markovXiInterior hn q τ hτ_strict hτ_left hqcrit j) = 0 :=
  (Classical.choose_spec (exists_markovAuxB_derivative_zero_between_nodes hn q τ hτ_strict
    hτ_left hqcrit j)).2

private theorem markovEtaInterior_lt_markovXiInterior_middle
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin (n - 2)) :
    markovEtaInterior hn q τ hτ_strict hτ_right hqcrit ⟨j.val, by omega⟩ <
      markovXiInterior hn q τ hτ_strict hτ_left hqcrit ⟨j.val + 1, by omega⟩ := by
  let ηi : Fin (n - 1) := ⟨j.val, by omega⟩
  let ξi : Fin (n - 1) := ⟨j.val + 1, by omega⟩
  let ci : Fin n := ⟨j.val + 1, by omega⟩
  have hηmem : markovEtaInterior hn q τ hτ_strict hτ_right hqcrit ηi ∈
      Set.Ioo (τ ⟨ci.val, by omega⟩) (τ ⟨ci.val + 1, by omega⟩) := by
    have hmem := markovEtaInterior_mem hn q τ hτ_strict hτ_right hqcrit ηi
    have hleft_idx : (⟨ηi.val + 1, by omega⟩ : Fin (n + 1)) = ⟨ci.val, by omega⟩ := by
      ext
      dsimp [ηi, ci]
    have hright_idx : (⟨ηi.val + 2, by omega⟩ : Fin (n + 1)) =
        ⟨ci.val + 1, by omega⟩ := by
      ext
      dsimp [ηi, ci]
    simpa [hleft_idx, hright_idx] using hmem
  have hξmem : markovXiInterior hn q τ hτ_strict hτ_left hqcrit ξi ∈
      Set.Ioo (τ ⟨ci.val, by omega⟩) (τ ⟨ci.val + 1, by omega⟩) := by
    have hmem := markovXiInterior_mem hn q τ hτ_strict hτ_left hqcrit ξi
    have hleft_idx : (⟨ξi.val, by omega⟩ : Fin (n + 1)) = ⟨ci.val, by omega⟩ := by
      ext
      dsimp [ξi, ci]
    have hright_idx : (⟨ξi.val + 1, by omega⟩ : Fin (n + 1)) =
        ⟨ci.val + 1, by omega⟩ := by
      ext
      dsimp [ξi, ci]
    simpa [hleft_idx, hright_idx] using hmem
  have hci_first : 0 < ci.val := by
    dsimp [ci]
    omega
  have hci_last : ci.val + 1 < n := by
    dsimp [ci]
    omega
  have hηpos : 0 < (Polynomial.derivative (markovAuxB q)).eval
        (markovEtaInterior hn q τ hτ_strict hτ_right hqcrit ηi) /
      (markovAuxB q).eval (markovEtaInterior hn q τ hτ_strict hτ_right hqcrit ηi) :=
    markovAuxB_log_derivative_pos_at_A_critical_middle hn q τ hτ_strict hτ_left hτ_right
      hqdeg hqcrit ci hci_first hci_last hηmem
      (markovEtaInterior_derivative_zero hn q τ hτ_strict hτ_right hqcrit ηi)
  have hξzero : (Polynomial.derivative (markovAuxB q)).eval
        (markovXiInterior hn q τ hτ_strict hτ_left hqcrit ξi) /
      (markovAuxB q).eval (markovXiInterior hn q τ hτ_strict hτ_left hqcrit ξi) = 0 := by
    rw [markovXiInterior_derivative_zero hn q τ hτ_strict hτ_left hqcrit ξi, zero_div]
  by_contra hnot
  have hle : markovXiInterior hn q τ hτ_strict hτ_left hqcrit ξi ≤
      markovEtaInterior hn q τ hτ_strict hτ_right hqcrit ηi := le_of_not_gt hnot
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hmono := markovAuxB_log_derivative_strictAnti_on_middle_interval hn q τ hτ_strict
      hτ_left hqdeg hqcrit ci hci_first hlt hξmem hηmem
    rw [hξzero] at hmono
    linarith
  · rw [← heq, hξzero] at hηpos
    linarith


private noncomputable def markovCLeft
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (k : Fin n) : ℝ :=
  if hk : k.val = 0 then τ 0
  else markovEtaInterior hn q τ hτ_strict hτ_right hqcrit ⟨k.val - 1, by omega⟩

private theorem markovCLeft_zero
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩) :
    markovCLeft hn q τ hτ_strict hτ_right hqcrit ⟨0, by omega⟩ = τ 0 := by
  simp [markovCLeft]

private theorem markovCLeft_succ
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin (n - 1)) :
    markovCLeft hn q τ hτ_strict hτ_right hqcrit ⟨j.val + 1, by omega⟩ =
      markovEtaInterior hn q τ hτ_strict hτ_right hqcrit j := by
  simp [markovCLeft]

private noncomputable def markovCRight
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (k : Fin n) : ℝ :=
  if hk : k.val + 1 = n then τ ⟨n, by omega⟩
  else markovXiInterior hn q τ hτ_strict hτ_left hqcrit ⟨k.val, by omega⟩

private theorem markovCRight_last
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩) :
    markovCRight hn q τ hτ_strict hτ_left hqcrit ⟨n - 1, by omega⟩ =
      τ ⟨n, by omega⟩ := by
  simp [markovCRight, Nat.sub_add_cancel (by omega : 1 ≤ n)]

private theorem markovCRight_of_fin_pred
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin (n - 1)) :
    markovCRight hn q τ hτ_strict hτ_left hqcrit ⟨j.val, by omega⟩ =
      markovXiInterior hn q τ hτ_strict hτ_left hqcrit j := by
  have hnot : ¬j.val + 1 = n := by omega
  simp [markovCRight, hnot]

private theorem markovCLeft_succ_mem
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin (n - 1)) :
    markovCLeft hn q τ hτ_strict hτ_right hqcrit ⟨j.val + 1, by omega⟩ ∈
      Set.Ioo (τ ⟨j.val + 1, by omega⟩) (τ ⟨j.val + 2, by omega⟩) := by
  rw [markovCLeft_succ]
  exact markovEtaInterior_mem hn q τ hτ_strict hτ_right hqcrit j

private theorem lagrangeLogDerivativeSum_zero_at_markovCLeft_of_pos
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (c : Fin n) (hc : 0 < c.val) :
    lagrangeLogDerivativeSum τ 0
      (markovCLeft hn q τ hτ_strict hτ_right hqcrit c) = 0 := by
  let j : Fin (n - 1) := ⟨c.val - 1, by omega⟩
  have hcidx : c = ⟨j.val + 1, by omega⟩ := by
    ext
    dsimp [j]
    omega
  have hmem : markovCLeft hn q τ hτ_strict hτ_right hqcrit c ∈
      Set.Ioo (τ ⟨c.val, by omega⟩) (τ ⟨c.val + 1, by omega⟩) := by
    have h := markovCLeft_succ_mem hn q τ hτ_strict hτ_right hqcrit j
    have hleft : (⟨j.val + 1, by omega⟩ : Fin (n + 1)) = ⟨c.val, by omega⟩ := by
      ext
      dsimp [j]
      omega
    have hright : (⟨j.val + 2, by omega⟩ : Fin (n + 1)) = ⟨c.val + 1, by omega⟩ := by
      ext
      dsimp [j]
      omega
    simpa [hcidx, hleft, hright] using h
  have hAne := markovAuxA_eval_ne_zero_of_mem_adjacent_interval hn q τ hτ_strict hτ_right
    hqcrit c hmem
  have hlog := markovAuxA_derivative_div_eval_eq_node_sum hn q τ hτ_strict hτ_right
    hqdeg hqcrit hAne
  have hderiv : (Polynomial.derivative (markovAuxA q)).eval
      (markovCLeft hn q τ hτ_strict hτ_right hqcrit c) = 0 := by
    rw [hcidx, markovCLeft_succ]
    exact markovEtaInterior_derivative_zero hn q τ hτ_strict hτ_right hqcrit j
  rw [hderiv, zero_div] at hlog
  rw [lagrangeLogDerivativeSum_zero_eq_A_endpoint_add_interior (Nat.one_le_of_lt hn)]
  exact hlog.symm

private theorem markovCLeft_succ_derivative_zero
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin (n - 1)) :
    (Polynomial.derivative (markovAuxA q)).eval
      (markovCLeft hn q τ hτ_strict hτ_right hqcrit ⟨j.val + 1, by omega⟩) = 0 := by
  rw [markovCLeft_succ]
  exact markovEtaInterior_derivative_zero hn q τ hτ_strict hτ_right hqcrit j

private theorem markovCRight_pred_mem
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin (n - 1)) :
    markovCRight hn q τ hτ_strict hτ_left hqcrit ⟨j.val, by omega⟩ ∈
      Set.Ioo (τ ⟨j.val, by omega⟩) (τ ⟨j.val + 1, by omega⟩) := by
  rw [markovCRight_of_fin_pred]
  exact markovXiInterior_mem hn q τ hτ_strict hτ_left hqcrit j

private theorem markovCRight_pred_derivative_zero
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin (n - 1)) :
    (Polynomial.derivative (markovAuxB q)).eval
      (markovCRight hn q τ hτ_strict hτ_left hqcrit ⟨j.val, by omega⟩) = 0 := by
  rw [markovCRight_of_fin_pred]
  exact markovXiInterior_derivative_zero hn q τ hτ_strict hτ_left hqcrit j

private theorem lagrangeLogDerivativeSum_last_at_markovCRight_of_not_last
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_left : τ 0 = -1) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (c : Fin n) (hc : c.val + 1 < n) :
    lagrangeLogDerivativeSum τ ⟨n, by omega⟩
      (markovCRight hn q τ hτ_strict hτ_left hqcrit c) = 0 := by
  let j : Fin (n - 1) := ⟨c.val, by omega⟩
  have hcidx : c = ⟨j.val, by omega⟩ := by
    ext
    rfl
  have hmem : markovCRight hn q τ hτ_strict hτ_left hqcrit c ∈
      Set.Ioo (τ ⟨c.val, by omega⟩) (τ ⟨c.val + 1, by omega⟩) := by
    have h := markovCRight_pred_mem hn q τ hτ_strict hτ_left hqcrit j
    have hleft : (⟨j.val, by omega⟩ : Fin (n + 1)) = ⟨c.val, by omega⟩ := by
      ext
      rfl
    have hright : (⟨j.val + 1, by omega⟩ : Fin (n + 1)) = ⟨c.val + 1, by omega⟩ := by
      ext
      rfl
    simpa [hcidx, hleft, hright] using h
  have hBne := markovAuxB_eval_ne_zero_of_mem_adjacent_interval hn q τ hτ_strict hτ_left
    hqcrit c hmem
  have hlog := markovAuxB_derivative_div_eval_eq_node_sum hn q τ hτ_strict hτ_left
    hqdeg hqcrit hBne
  have hderiv : (Polynomial.derivative (markovAuxB q)).eval
      (markovCRight hn q τ hτ_strict hτ_left hqcrit c) = 0 := by
    rw [hcidx]
    exact markovCRight_pred_derivative_zero hn q τ hτ_strict hτ_left hqcrit j
  rw [hderiv, zero_div] at hlog
  rw [lagrangeLogDerivativeSum_last_eq_B_endpoint_add_interior (Nat.one_le_of_lt hn)]
  exact hlog.symm

private theorem markovC_order_first
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩) :
    markovCLeft hn q τ hτ_strict hτ_right hqcrit ⟨0, by omega⟩ ≤
      markovCRight hn q τ hτ_strict hτ_left hqcrit ⟨0, by omega⟩ := by
  have hmem := markovCRight_pred_mem hn q τ hτ_strict hτ_left hqcrit ⟨0, by omega⟩
  rw [markovCLeft_zero]
  exact le_of_lt hmem.1

private theorem markovC_order_last
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩) :
    markovCLeft hn q τ hτ_strict hτ_right hqcrit ⟨n - 1, by omega⟩ ≤
      markovCRight hn q τ hτ_strict hτ_left hqcrit ⟨n - 1, by omega⟩ := by
  let j : Fin (n - 1) := ⟨n - 2, by omega⟩
  have hleft :
      markovCLeft hn q τ hτ_strict hτ_right hqcrit ⟨n - 1, by omega⟩ =
        markovEtaInterior hn q τ hτ_strict hτ_right hqcrit j := by
    have hidx : (⟨n - 1, by omega⟩ : Fin n) = ⟨j.val + 1, by omega⟩ := by
      ext
      dsimp [j]
      omega
    rw [hidx, markovCLeft_succ]
  have hright :
      markovCRight hn q τ hτ_strict hτ_left hqcrit ⟨n - 1, by omega⟩ = τ ⟨n, by omega⟩ := by
    rw [markovCRight_last]
  rw [hleft, hright]
  have hmem := markovEtaInterior_mem hn q τ hτ_strict hτ_right hqcrit j
  have hright_idx : (⟨j.val + 2, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := by
    ext
    dsimp [j]
    omega
  simpa [hright_idx] using le_of_lt hmem.2

private theorem markovCLeft_left_le
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (i : Fin n) :
    τ ⟨i.val, by omega⟩ ≤ markovCLeft hn q τ hτ_strict hτ_right hqcrit i := by
  by_cases hi0 : i.val = 0
  · have hidx : i = ⟨0, by omega⟩ := by
      ext
      exact hi0
    rw [hidx, markovCLeft_zero]
    change τ 0 ≤ τ 0
    exact le_rfl
  · let j : Fin (n - 1) := ⟨i.val - 1, by omega⟩
    have hidx : i = ⟨j.val + 1, by omega⟩ := by
      ext
      dsimp [j]
      omega
    have hmem := markovCLeft_succ_mem hn q τ hτ_strict hτ_right hqcrit j
    rw [hidx, markovCLeft_succ]
    exact le_of_lt hmem.1

private theorem markovCLeft_left_lt_of_pos
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (i : Fin n) (hi : 0 < i.val) :
    τ ⟨i.val, by omega⟩ < markovCLeft hn q τ hτ_strict hτ_right hqcrit i := by
  let j : Fin (n - 1) := ⟨i.val - 1, by omega⟩
  have hidx : i = ⟨j.val + 1, by omega⟩ := by
    ext
    dsimp [j]
    omega
  have hmem := markovCLeft_succ_mem hn q τ hτ_strict hτ_right hqcrit j
  rw [hidx, markovCLeft_succ]
  exact hmem.1

private theorem markovCRight_right_le
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (i : Fin n) :
    markovCRight hn q τ hτ_strict hτ_left hqcrit i ≤ τ ⟨i.val + 1, by omega⟩ := by
  by_cases hilast : i.val + 1 = n
  · have hidx : i = ⟨n - 1, by omega⟩ := by
      ext
      have hval : i.val = n - 1 := by omega
      exact hval
    rw [hidx, markovCRight_last]
    have hright_idx :
        (⟨(⟨n - 1, by omega⟩ : Fin n).val + 1, by omega⟩ : Fin (n + 1)) =
          ⟨n, by omega⟩ := by
      ext
      dsimp
      omega
    rw [hright_idx]
  · let j : Fin (n - 1) := ⟨i.val, by omega⟩
    have hmem := markovCRight_pred_mem hn q τ hτ_strict hτ_left hqcrit j
    change markovCRight hn q τ hτ_strict hτ_left hqcrit ⟨j.val, by omega⟩ ≤
      τ ⟨j.val + 1, by omega⟩
    exact le_of_lt hmem.2

private theorem markovCRight_right_lt_of_not_last
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (i : Fin n) (hi : i.val + 1 < n) :
    markovCRight hn q τ hτ_strict hτ_left hqcrit i < τ ⟨i.val + 1, by omega⟩ := by
  let j : Fin (n - 1) := ⟨i.val, by omega⟩
  have hmem := markovCRight_pred_mem hn q τ hτ_strict hτ_left hqcrit j
  change markovCRight hn q τ hτ_strict hτ_left hqcrit ⟨j.val, by omega⟩ <
    τ ⟨j.val + 1, by omega⟩
  exact hmem.2

private theorem markovC_order_middle
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin (n - 2)) :
    markovCLeft hn q τ hτ_strict hτ_right hqcrit ⟨j.val + 1, by omega⟩ ≤
      markovCRight hn q τ hτ_strict hτ_left hqcrit ⟨j.val + 1, by omega⟩ := by
  let ηi : Fin (n - 1) := ⟨j.val, by omega⟩
  let ξi : Fin (n - 1) := ⟨j.val + 1, by omega⟩
  have hleft :
      markovCLeft hn q τ hτ_strict hτ_right hqcrit ⟨j.val + 1, by omega⟩ =
        markovEtaInterior hn q τ hτ_strict hτ_right hqcrit ηi := by
    change markovCLeft hn q τ hτ_strict hτ_right hqcrit ⟨ηi.val + 1, by omega⟩ =
      markovEtaInterior hn q τ hτ_strict hτ_right hqcrit ηi
    rw [markovCLeft_succ]
  have hright :
      markovCRight hn q τ hτ_strict hτ_left hqcrit ⟨j.val + 1, by omega⟩ =
        markovXiInterior hn q τ hτ_strict hτ_left hqcrit ξi := by
    change markovCRight hn q τ hτ_strict hτ_left hqcrit ⟨ξi.val, by omega⟩ =
      markovXiInterior hn q τ hτ_strict hτ_left hqcrit ξi
    rw [markovCRight_of_fin_pred]
  rw [hleft, hright]
  exact le_of_lt (markovEtaInterior_lt_markovXiInterior_middle hn q τ hτ_strict hτ_right
    hτ_left hqdeg hqcrit j)

private theorem markovC_order
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (i : Fin n) :
    markovCLeft hn q τ hτ_strict hτ_right hqcrit i ≤
      markovCRight hn q τ hτ_strict hτ_left hqcrit i := by
  by_cases hi0 : i.val = 0
  · have hidx : i = ⟨0, by omega⟩ := by
      ext
      exact hi0
    rw [hidx]
    exact markovC_order_first hn q τ hτ_strict hτ_right hτ_left hqcrit
  · by_cases hilast : i.val = n - 1
    · have hidx : i = ⟨n - 1, by omega⟩ := by
        ext
        exact hilast
      rw [hidx]
      exact markovC_order_last hn q τ hτ_strict hτ_right hτ_left hqcrit
    · let j : Fin (n - 2) := ⟨i.val - 1, by omega⟩
      have hidx : i = ⟨j.val + 1, by omega⟩ := by
        ext
        dsimp [j]
        omega
      rw [hidx]
      exact markovC_order_middle hn q τ hτ_strict hτ_right hτ_left hqdeg hqcrit j

private theorem markovC_mem_node_interval
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (i : Fin n) {x : ℝ}
    (hx : x ∈ Set.Icc (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)
      (markovCRight hn q τ hτ_strict hτ_left hqcrit i)) :
    x ∈ Set.Icc (τ ⟨i.val, by omega⟩) (τ ⟨i.val + 1, by omega⟩) := by
  exact ⟨le_trans (markovCLeft_left_le hn q τ hτ_strict hτ_right hqcrit i) hx.1,
    le_trans hx.2 (markovCRight_right_le hn q τ hτ_strict hτ_left hqcrit i)⟩

private theorem markovC_mem_node_interval_strict_of_interior
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (i : Fin n) {x : ℝ}
    (hx : x ∈ Set.Icc (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)
      (markovCRight hn q τ hτ_strict hτ_left hqcrit i))
    (hleft : i.val = 0 → x ≠ τ 0)
    (hright : i.val + 1 = n → x ≠ τ ⟨n, by omega⟩) :
    x ∈ Set.Ioo (τ ⟨i.val, by omega⟩) (τ ⟨i.val + 1, by omega⟩) := by
  have hmem := markovC_mem_node_interval hn q τ hτ_strict hτ_right hτ_left hqcrit i hx
  constructor
  · refine lt_of_le_of_ne hmem.1 ?_
    intro h
    by_cases hi0 : i.val = 0
    · apply hleft hi0
      have hidx : (⟨i.val, by omega⟩ : Fin (n + 1)) = 0 := by
        ext
        exact hi0
      rw [← h, hidx]
    · have hstrict := markovCLeft_left_lt_of_pos hn q τ hτ_strict hτ_right hqcrit i (by omega)
      have hle := hx.1
      rw [h] at hstrict
      exact not_lt_of_ge hle hstrict
  · refine lt_of_le_of_ne hmem.2 ?_
    intro h
    by_cases hilast : i.val + 1 = n
    · apply hright hilast
      have hidx : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := by
        ext
        exact hilast
      rw [h, hidx]
    · have hstrict := markovCRight_right_lt_of_not_last hn q τ hτ_strict hτ_left hqcrit i
        (by omega)
      have hle := hx.2
      rw [← h] at hstrict
      exact not_lt_of_ge hle hstrict

private theorem markovC_Ioo_mem_node_interval
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (i : Fin n) {x : ℝ}
    (hx : x ∈ Set.Ioo (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)
      (markovCRight hn q τ hτ_strict hτ_left hqcrit i)) :
    x ∈ Set.Ioo (τ ⟨i.val, by omega⟩) (τ ⟨i.val + 1, by omega⟩) := by
  apply markovC_mem_node_interval_strict_of_interior hn q τ hτ_strict hτ_right hτ_left
    hqcrit i ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  · intro hi0 hxeq
    have hCleft : markovCLeft hn q τ hτ_strict hτ_right hqcrit i = τ 0 := by
      have hidx : i = ⟨0, by omega⟩ := by
        ext
        exact hi0
      rw [hidx, markovCLeft_zero]
    rw [hCleft, hxeq] at hx
    exact lt_irrefl _ hx.1
  · intro hilast hxeq
    have hCright : markovCRight hn q τ hτ_strict hτ_left hqcrit i = τ ⟨n, by omega⟩ := by
      unfold markovCRight
      simp [hilast]
    rw [hxeq, hCright] at hx
    exact lt_irrefl _ hx.2

private theorem lagrangeLogDerivativeSum_zero_neg_on_markovC_Ioo
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (c : Fin n) {y : ℝ}
    (hy : y ∈ Set.Ioo (markovCLeft hn q τ hτ_strict hτ_right hqcrit c)
      (markovCRight hn q τ hτ_strict hτ_left hqcrit c)) :
    lagrangeLogDerivativeSum τ 0 y < 0 := by
  have hynode := markovC_Ioo_mem_node_interval hn q τ hτ_strict hτ_right hτ_left
    hqcrit c hy
  by_cases hc0 : c.val = 0
  · have hcidx : c = ⟨0, by omega⟩ := by
      ext
      exact hc0
    rw [hcidx] at hynode
    simpa using lagrangeLogDerivativeSum_zero_neg_of_mem_first_interval (Nat.one_le_of_lt hn)
      τ hτ_strict hynode
  · have hcpos : 0 < c.val := by omega
    let j : Fin (n - 1) := ⟨c.val - 1, by omega⟩
    have hcleft_mem : markovCLeft hn q τ hτ_strict hτ_right hqcrit c ∈
        Set.Ioo (τ ⟨c.val, by omega⟩) (τ ⟨c.val + 1, by omega⟩) := by
      have hcidx : c = ⟨j.val + 1, by omega⟩ := by
        ext
        dsimp [j]
        omega
      have h := markovCLeft_succ_mem hn q τ hτ_strict hτ_right hqcrit j
      have hleft : (⟨j.val + 1, by omega⟩ : Fin (n + 1)) = ⟨c.val, by omega⟩ := by
        ext
        dsimp [j]
        omega
      have hright : (⟨j.val + 2, by omega⟩ : Fin (n + 1)) = ⟨c.val + 1, by omega⟩ := by
        ext
        dsimp [j]
        omega
      simpa [hcidx, hleft, hright] using h
    have hmono := sum_one_div_sub_A_nodes_strictAnti_on_adjacent_interval τ hτ_strict c
      hy.1 hcleft_mem hynode
    rw [← lagrangeLogDerivativeSum_zero_eq_A_nodes] at hmono
    have hrhs := lagrangeLogDerivativeSum_zero_eq_A_nodes τ
      (markovCLeft hn q τ hτ_strict hτ_right hqcrit c)
    rw [← hrhs] at hmono
    have hzero := lagrangeLogDerivativeSum_zero_at_markovCLeft_of_pos hn q τ hτ_strict
      hτ_right hqdeg hqcrit c hcpos
    rw [hzero] at hmono
    exact hmono

private theorem lagrangeLogDerivativeSum_last_pos_on_markovC_Ioo
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (c : Fin n) {y : ℝ}
    (hy : y ∈ Set.Ioo (markovCLeft hn q τ hτ_strict hτ_right hqcrit c)
      (markovCRight hn q τ hτ_strict hτ_left hqcrit c)) :
    0 < lagrangeLogDerivativeSum τ ⟨n, by omega⟩ y := by
  have hynode := markovC_Ioo_mem_node_interval hn q τ hτ_strict hτ_right hτ_left
    hqcrit c hy
  by_cases hclast : c.val + 1 = n
  · have hcidx : c = ⟨n - 1, by omega⟩ := by
      ext
      have hval : c.val = n - 1 := by omega
      exact hval
    have hynode_last : y ∈ Set.Ioo (τ ⟨n - 1, by omega⟩) (τ ⟨n, by omega⟩) := by
      have hleft : (⟨(⟨n - 1, by omega⟩ : Fin n).val, by omega⟩ : Fin (n + 1)) =
          ⟨n - 1, by omega⟩ := by
        ext
        rfl
      have hright : (⟨(⟨n - 1, by omega⟩ : Fin n).val + 1, by omega⟩ : Fin (n + 1)) =
          ⟨n, by omega⟩ := by
        ext
        simp [Nat.sub_add_cancel (Nat.one_le_of_lt hn)]
      simpa [hcidx, hleft, hright] using hynode
    simpa using lagrangeLogDerivativeSum_last_pos_of_mem_last_interval (Nat.one_le_of_lt hn)
      τ hτ_strict hynode_last
  · have hcnotlast : c.val + 1 < n := by omega
    let j : Fin (n - 1) := ⟨c.val, by omega⟩
    have hcright_mem : markovCRight hn q τ hτ_strict hτ_left hqcrit c ∈
        Set.Ioo (τ ⟨c.val, by omega⟩) (τ ⟨c.val + 1, by omega⟩) := by
      have hcidx : c = ⟨j.val, by omega⟩ := by
        ext
        rfl
      have h := markovCRight_pred_mem hn q τ hτ_strict hτ_left hqcrit j
      have hleft : (⟨j.val, by omega⟩ : Fin (n + 1)) = ⟨c.val, by omega⟩ := by
        ext
        rfl
      have hright : (⟨j.val + 1, by omega⟩ : Fin (n + 1)) = ⟨c.val + 1, by omega⟩ := by
        ext
        rfl
      simpa [hcidx, hleft, hright] using h
    have hmono := sum_one_div_sub_B_nodes_strictAnti_on_adjacent_interval τ hτ_strict c
      hy.2 hynode hcright_mem
    rw [← lagrangeLogDerivativeSum_last_eq_B_nodes] at hmono
    have hrhs := lagrangeLogDerivativeSum_last_eq_B_nodes τ y
    rw [← hrhs] at hmono
    have hzero := lagrangeLogDerivativeSum_last_at_markovCRight_of_not_last hn q τ
      hτ_strict hτ_left hqdeg hqcrit c hcnotlast
    rw [hzero] at hmono
    exact hmono

private theorem lagrangeLogDerivativeSum_neg_on_markovC_Ioo_of_le
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (c : Fin n) {y : ℝ}
    (hy : y ∈ Set.Ioo (markovCLeft hn q τ hτ_strict hτ_right hqcrit c)
      (markovCRight hn q τ hτ_strict hτ_left hqcrit c))
    (i : Fin (n + 1)) (hi : i.val ≤ c.val) :
    lagrangeLogDerivativeSum τ i y < 0 := by
  have hF0 := lagrangeLogDerivativeSum_zero_neg_on_markovC_Ioo hn q τ hτ_strict
    hτ_right hτ_left hqdeg hqcrit c hy
  by_cases hi0 : i.val = 0
  · have hidx : i = 0 := by
      ext
      exact hi0
    simpa [hidx] using hF0
  · have hnode_i_le_c : τ i ≤ τ ⟨c.val, by omega⟩ := by
      by_cases hic : i.val = c.val
      · have hidx : i = ⟨c.val, by omega⟩ := by
          ext
          exact hic
        rw [hidx]
      · exact le_of_lt (hτ_strict (by
          change i.val < c.val
          omega))
    have h0i : τ 0 < τ i := hτ_strict (by
      change (0 : Fin (n + 1)) < i
      exact_mod_cast (show 0 < i.val by omega))
    have hynode := markovC_Ioo_mem_node_interval hn q τ hτ_strict hτ_right hτ_left
      hqcrit c hy
    have hpos_i : 0 < y - τ i := by
      nlinarith [hynode.1, hnode_i_le_c]
    have hden_lt : y - τ i < y - τ 0 := by
      linarith
    have hrec : 1 / (y - τ 0) < 1 / (y - τ i) :=
      one_div_lt_one_div_of_lt hpos_i hden_lt
    have hdiff := lagrangeLogDerivativeSum_sub τ i 0 y
    have hcomp : 1 / (y - τ 0) - 1 / (y - τ i) < 0 := by linarith
    linarith

private theorem lagrangeLogDerivativeSum_pos_on_markovC_Ioo_of_succ_le
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (c : Fin n) {y : ℝ}
    (hy : y ∈ Set.Ioo (markovCLeft hn q τ hτ_strict hτ_right hqcrit c)
      (markovCRight hn q τ hτ_strict hτ_left hqcrit c))
    (i : Fin (n + 1)) (hi : c.val + 1 ≤ i.val) :
    0 < lagrangeLogDerivativeSum τ i y := by
  have hFn := lagrangeLogDerivativeSum_last_pos_on_markovC_Ioo hn q τ hτ_strict
    hτ_right hτ_left hqdeg hqcrit c hy
  by_cases hin : i.val = n
  · have hidx : i = ⟨n, by omega⟩ := by
      ext
      exact hin
    simpa [hidx] using hFn
  · have hinlt : i.val < n := by omega
    have hnode_c1_le_i : τ ⟨c.val + 1, by omega⟩ ≤ τ i := by
      by_cases hci : c.val + 1 = i.val
      · have hidx : i = ⟨c.val + 1, by omega⟩ := by
          ext
          exact hci.symm
        rw [hidx]
      · exact le_of_lt (hτ_strict (by
          change c.val + 1 < i.val
          omega))
    have hin_node_lt : τ i < τ ⟨n, by omega⟩ := hτ_strict (by
      change i.val < n
      exact hinlt)
    have hynode := markovC_Ioo_mem_node_interval hn q τ hτ_strict hτ_right hτ_left
      hqcrit c hy
    have hneg_i : y - τ i < 0 := by
      nlinarith [hynode.2, hnode_c1_le_i]
    have hden_lt : y - τ ⟨n, by omega⟩ < y - τ i := by
      linarith
    have hrec : 1 / (y - τ i) < 1 / (y - τ ⟨n, by omega⟩) :=
      one_div_lt_one_div_of_neg_of_lt hneg_i hden_lt
    have hdiff := lagrangeLogDerivativeSum_sub τ i ⟨n, by omega⟩ y
    have hcomp : 0 < 1 / (y - τ ⟨n, by omega⟩) - 1 / (y - τ i) := by
      linarith
    linarith

private theorem lagrangeProductDerivative_pairwise_nonneg_on_markovC_Ioo
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (c : Fin n) {y : ℝ}
    (hy : y ∈ Set.Ioo (markovCLeft hn q τ hτ_strict hτ_right hqcrit c)
      (markovCRight hn q τ hτ_strict hτ_left hqcrit c)) :
    ∀ i j : Fin (n + 1),
      0 ≤ lagrangeProductDerivativeEval τ i y * lagrangeProductDerivativeEval τ j y := by
  have hynode := markovC_Ioo_mem_node_interval hn q τ hτ_strict hτ_right hτ_left
    hqcrit c hy
  apply lagrangeProductDerivative_pairwise_nonneg_of_eval_log_pairwise τ hτ_strict c hynode
  intro i j
  have hleft_pos : ∀ k : Fin (n + 1), k.val ≤ c.val → 0 < y - τ k := by
    intro k hk
    have hnode_le : τ k ≤ τ ⟨c.val, by omega⟩ := by
      by_cases hkc : k.val = c.val
      · have hidx : k = ⟨c.val, by omega⟩ := by
          ext
          exact hkc
        rw [hidx]
      · exact le_of_lt (hτ_strict (by
          change k.val < c.val
          omega))
    nlinarith [hynode.1, hnode_le]
  have hright_neg : ∀ k : Fin (n + 1), c.val + 1 ≤ k.val → y - τ k < 0 := by
    intro k hk
    have hnode_le : τ ⟨c.val + 1, by omega⟩ ≤ τ k := by
      by_cases hkc : c.val + 1 = k.val
      · have hidx : k = ⟨c.val + 1, by omega⟩ := by
          ext
          exact hkc.symm
        rw [hidx]
      · exact le_of_lt (hτ_strict (by
          change c.val + 1 < k.val
          omega))
    nlinarith [hynode.2, hnode_le]
  by_cases hi_left : i.val ≤ c.val
  · by_cases hj_left : j.val ≤ c.val
    · have hprod : 0 ≤ lagrangeProductEval τ i y * lagrangeProductEval τ j y := by
        apply lagrangeProductEval_pair_mul_nonneg_of_sub_mul_pos
        nlinarith [hleft_pos i hi_left, hleft_pos j hj_left]
      have hlog_i := lagrangeLogDerivativeSum_neg_on_markovC_Ioo_of_le hn q τ hτ_strict
        hτ_right hτ_left hqdeg hqcrit c hy i hi_left
      have hlog_j := lagrangeLogDerivativeSum_neg_on_markovC_Ioo_of_le hn q τ hτ_strict
        hτ_right hτ_left hqdeg hqcrit c hy j hj_left
      have hlog : 0 ≤ lagrangeLogDerivativeSum τ i y * lagrangeLogDerivativeSum τ j y := by
        nlinarith
      exact mul_nonneg hprod hlog
    · have hj_right : c.val + 1 ≤ j.val := by omega
      have hprod : lagrangeProductEval τ i y * lagrangeProductEval τ j y ≤ 0 := by
        apply lagrangeProductEval_pair_mul_nonpos_of_sub_mul_neg
        nlinarith [hleft_pos i hi_left, hright_neg j hj_right]
      have hlog_i := lagrangeLogDerivativeSum_neg_on_markovC_Ioo_of_le hn q τ hτ_strict
        hτ_right hτ_left hqdeg hqcrit c hy i hi_left
      have hlog_j := lagrangeLogDerivativeSum_pos_on_markovC_Ioo_of_succ_le hn q τ
        hτ_strict hτ_right hτ_left hqdeg hqcrit c hy j hj_right
      have hlog : lagrangeLogDerivativeSum τ i y * lagrangeLogDerivativeSum τ j y ≤ 0 := by
        nlinarith
      exact mul_nonneg_of_nonpos_of_nonpos hprod hlog
  · have hi_right : c.val + 1 ≤ i.val := by omega
    by_cases hj_left : j.val ≤ c.val
    · have hprod : lagrangeProductEval τ i y * lagrangeProductEval τ j y ≤ 0 := by
        apply lagrangeProductEval_pair_mul_nonpos_of_sub_mul_neg
        nlinarith [hright_neg i hi_right, hleft_pos j hj_left]
      have hlog_i := lagrangeLogDerivativeSum_pos_on_markovC_Ioo_of_succ_le hn q τ
        hτ_strict hτ_right hτ_left hqdeg hqcrit c hy i hi_right
      have hlog_j := lagrangeLogDerivativeSum_neg_on_markovC_Ioo_of_le hn q τ hτ_strict
        hτ_right hτ_left hqdeg hqcrit c hy j hj_left
      have hlog : lagrangeLogDerivativeSum τ i y * lagrangeLogDerivativeSum τ j y ≤ 0 := by
        nlinarith
      exact mul_nonneg_of_nonpos_of_nonpos hprod hlog
    · have hj_right : c.val + 1 ≤ j.val := by omega
      have hprod : 0 ≤ lagrangeProductEval τ i y * lagrangeProductEval τ j y := by
        apply lagrangeProductEval_pair_mul_nonneg_of_sub_mul_pos
        nlinarith [hright_neg i hi_right, hright_neg j hj_right]
      have hlog_i := lagrangeLogDerivativeSum_pos_on_markovC_Ioo_of_succ_le hn q τ
        hτ_strict hτ_right hτ_left hqdeg hqcrit c hy i hi_right
      have hlog_j := lagrangeLogDerivativeSum_pos_on_markovC_Ioo_of_succ_le hn q τ
        hτ_strict hτ_right hτ_left hqdeg hqcrit c hy j hj_right
      have hlog : 0 ≤ lagrangeLogDerivativeSum τ i y * lagrangeLogDerivativeSum τ j y := by
        nlinarith
      exact mul_nonneg hprod hlog

private theorem markovC_intervals_separated
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (i j : Fin n) (hij : i.val < j.val) :
    markovCRight hn q τ hτ_strict hτ_left hqcrit i <
      markovCLeft hn q τ hτ_strict hτ_right hqcrit j := by
  by_cases hadj : i.val + 1 = j.val
  · have hright_lt := markovCRight_right_lt_of_not_last hn q τ hτ_strict hτ_left hqcrit i
      (by omega)
    have hleft_lt := markovCLeft_left_lt_of_pos hn q τ hτ_strict hτ_right hqcrit j
      (by omega)
    have hidx : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) = ⟨j.val, by omega⟩ := by
      ext
      omega
    rw [hidx] at hright_lt
    exact lt_trans hright_lt hleft_lt
  · have hright_le := markovCRight_right_le hn q τ hτ_strict hτ_left hqcrit i
    have hleft_le := markovCLeft_left_le hn q τ hτ_strict hτ_right hqcrit j
    have hnode_lt : τ ⟨i.val + 1, by omega⟩ < τ ⟨j.val, by omega⟩ := by
      apply hτ_strict
      change i.val + 1 < j.val
      omega
    exact lt_of_le_of_lt hright_le (lt_of_lt_of_le hnode_lt hleft_le)

private theorem markovC_R_mul_neg_first
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩) :
    (markovAuxR q).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit ⟨0, by omega⟩) *
      (markovAuxR q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit ⟨0, by omega⟩) < 0 := by
  let j : Fin (n - 1) := ⟨0, by omega⟩
  have hleft :
      markovCLeft hn q τ hτ_strict hτ_right hqcrit ⟨0, by omega⟩ = τ 0 := by
    rw [markovCLeft_zero]
  have hright :
      markovCRight hn q τ hτ_strict hτ_left hqcrit ⟨0, by omega⟩ =
        markovXiInterior hn q τ hτ_strict hτ_left hqcrit j := by
    change markovCRight hn q τ hτ_strict hτ_left hqcrit ⟨j.val, by omega⟩ =
      markovXiInterior hn q τ hτ_strict hτ_left hqcrit j
    rw [markovCRight_of_fin_pred]
  rw [hleft, hright]
  exact markovAuxR_eval_mul_neg_left_endpoint_of_B_derivative_zero hn q τ hτ_strict hτ_left
    hqcrit (markovXiInterior_mem hn q τ hτ_strict hτ_left hqcrit j)
    (markovXiInterior_derivative_zero hn q τ hτ_strict hτ_left hqcrit j)

private theorem markovC_R_mul_neg_last
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩) :
    (markovAuxR q).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit ⟨n - 1, by omega⟩) *
      (markovAuxR q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit ⟨n - 1, by omega⟩) < 0 := by
  let j : Fin (n - 1) := ⟨n - 2, by omega⟩
  have hleft :
      markovCLeft hn q τ hτ_strict hτ_right hqcrit ⟨n - 1, by omega⟩ =
        markovEtaInterior hn q τ hτ_strict hτ_right hqcrit j := by
    have hidx : (⟨n - 1, by omega⟩ : Fin n) = ⟨j.val + 1, by omega⟩ := by
      ext
      dsimp [j]
      omega
    rw [hidx, markovCLeft_succ]
  have hright :
      markovCRight hn q τ hτ_strict hτ_left hqcrit ⟨n - 1, by omega⟩ =
        τ ⟨n, by omega⟩ := by
    rw [markovCRight_last]
  rw [hleft, hright]
  exact markovAuxR_eval_mul_neg_right_endpoint_of_A_derivative_zero hn q τ hτ_strict hτ_right
    hqcrit (by
      have hmem := markovEtaInterior_mem hn q τ hτ_strict hτ_right hqcrit j
      have hleft_idx : (⟨j.val + 1, by omega⟩ : Fin (n + 1)) = ⟨n - 1, by omega⟩ := by
        ext
        dsimp [j]
        omega
      have hright_idx : (⟨j.val + 2, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := by
        ext
        dsimp [j]
        omega
      simpa [hleft_idx, hright_idx] using hmem)
    (markovEtaInterior_derivative_zero hn q τ hτ_strict hτ_right hqcrit j)


private theorem markovC_R_mul_neg_middle
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (j : Fin (n - 2)) :
    (markovAuxR q).eval
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit ⟨j.val + 1, by omega⟩) *
      (markovAuxR q).eval
        (markovCRight hn q τ hτ_strict hτ_left hqcrit ⟨j.val + 1, by omega⟩) < 0 := by
  let ηi : Fin (n - 1) := ⟨j.val, by omega⟩
  let ξi : Fin (n - 1) := ⟨j.val + 1, by omega⟩
  let ci : Fin n := ⟨j.val + 1, by omega⟩
  have hleft :
      markovCLeft hn q τ hτ_strict hτ_right hqcrit ⟨j.val + 1, by omega⟩ =
        markovEtaInterior hn q τ hτ_strict hτ_right hqcrit ηi := by
    change markovCLeft hn q τ hτ_strict hτ_right hqcrit ⟨ηi.val + 1, by omega⟩ =
      markovEtaInterior hn q τ hτ_strict hτ_right hqcrit ηi
    rw [markovCLeft_succ]
  have hright :
      markovCRight hn q τ hτ_strict hτ_left hqcrit ⟨j.val + 1, by omega⟩ =
        markovXiInterior hn q τ hτ_strict hτ_left hqcrit ξi := by
    change markovCRight hn q τ hτ_strict hτ_left hqcrit ⟨ξi.val, by omega⟩ =
      markovXiInterior hn q τ hτ_strict hτ_left hqcrit ξi
    rw [markovCRight_of_fin_pred]
  rw [hleft, hright]
  exact markovAuxR_eval_mul_neg_of_aux_derivative_zeros_in_same_adjacent_interval hn q τ
    hτ_strict hqcrit ci
    (by
      have hmem := markovEtaInterior_mem hn q τ hτ_strict hτ_right hqcrit ηi
      have hleft_idx : (⟨ηi.val + 1, by omega⟩ : Fin (n + 1)) =
          ⟨ci.val, by omega⟩ := by
        ext
        dsimp [ηi, ci]
      have hright_idx : (⟨ηi.val + 2, by omega⟩ : Fin (n + 1)) =
          ⟨ci.val + 1, by omega⟩ := by
        ext
        dsimp [ηi, ci]
      simpa [hleft_idx, hright_idx] using hmem)
    (by
      have hmem := markovXiInterior_mem hn q τ hτ_strict hτ_left hqcrit ξi
      have hleft_idx : (⟨ξi.val, by omega⟩ : Fin (n + 1)) = ⟨ci.val, by omega⟩ := by
        ext
        dsimp [ξi, ci]
      have hright_idx : (⟨ξi.val + 1, by omega⟩ : Fin (n + 1)) =
          ⟨ci.val + 1, by omega⟩ := by
        ext
        dsimp [ξi, ci]
      simpa [hleft_idx, hright_idx] using hmem)
    (markovEtaInterior_derivative_zero hn q τ hτ_strict hτ_right hqcrit ηi)
    (markovXiInterior_derivative_zero hn q τ hτ_strict hτ_left hqcrit ξi)

private theorem markovC_R_mul_neg
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (i : Fin n) :
    (markovAuxR q).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit i) *
      (markovAuxR q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit i) < 0 := by
  by_cases hi0 : i.val = 0
  · have hidx : i = ⟨0, by omega⟩ := by
      ext
      exact hi0
    rw [hidx]
    exact markovC_R_mul_neg_first hn q τ hτ_strict hτ_right hτ_left hqcrit
  · by_cases hilast : i.val = n - 1
    · have hidx : i = ⟨n - 1, by omega⟩ := by
        ext
        exact hilast
      rw [hidx]
      exact markovC_R_mul_neg_last hn q τ hτ_strict hτ_right hτ_left hqcrit
    · let j : Fin (n - 2) := ⟨i.val - 1, by omega⟩
      have hidx : i = ⟨j.val + 1, by omega⟩ := by
        ext
        dsimp [j]
        omega
      rw [hidx]
      exact markovC_R_mul_neg_middle hn q τ hτ_strict hτ_right hτ_left hqcrit j

private theorem markovCLeft_abs_R_eq_abs_derivative_q
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (i : Fin n) :
    |(markovAuxR q).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)| =
      |(Polynomial.derivative q).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)| := by
  by_cases hi0 : i.val = 0
  · have hidx : i = ⟨0, by omega⟩ := by
      ext
      exact hi0
    rw [hidx, markovCLeft_zero, hτ_left, markovAuxR_eval_neg_one, abs_neg]
  · let j : Fin (n - 1) := ⟨i.val - 1, by omega⟩
    have hidx : i = ⟨j.val + 1, by omega⟩ := by
      ext
      dsimp [j]
      omega
    have hzero := markovCLeft_succ_derivative_zero hn q τ hτ_strict hτ_right hqcrit j
    rw [hidx, markovAuxA_eval_derivative_zero_of_derivative_zero q hzero, abs_neg]

private theorem markovCRight_abs_R_eq_abs_derivative_q
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (i : Fin n) :
    |(markovAuxR q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit i)| =
      |(Polynomial.derivative q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit i)| := by
  by_cases hilast : i.val + 1 = n
  · have hidx : i = ⟨n - 1, by omega⟩ := by
      have hval : i.val = n - 1 := by omega
      ext
      exact hval
    rw [hidx, markovCRight_last, hτ_right, markovAuxR_eval_one]
  · let j : Fin (n - 1) := ⟨i.val, by omega⟩
    have hidx : i = ⟨j.val, by omega⟩ := by
      ext
      rfl
    have hzero := markovCRight_pred_derivative_zero hn q τ hτ_strict hτ_left hqcrit j
    rw [hidx, markovAuxB_eval_derivative_zero_of_derivative_zero q hzero]

private theorem markovCLeft_derivative_q_bound_of_common_sign
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (hp_nodes : ∀ i : Fin (n + 1), |p.eval (τ i)| ≤ |q.eval (τ i)|)
    (i : Fin n)
    (hterms : (∀ k : Fin (n + 1),
        0 ≤ q.eval (τ k) *
          (Polynomial.derivative (lagrangeBasis τ k)).eval
            (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)) ∨
      (∀ k : Fin (n + 1),
        q.eval (τ k) *
          (Polynomial.derivative (lagrangeBasis τ k)).eval
            (markovCLeft hn q τ hτ_strict hτ_right hqcrit i) ≤ 0)) :
    |(Polynomial.derivative p).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)| ≤
      |(Polynomial.derivative q).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)| := by
  exact derivative_eval_le_of_lagrange_common_sign p q τ hτ_strict hpdeg hqdeg hp_nodes
    (markovCLeft hn q τ hτ_strict hτ_right hqcrit i) hterms

private theorem markovCRight_derivative_q_bound_of_common_sign
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_left : τ 0 = -1)
    (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (hp_nodes : ∀ i : Fin (n + 1), |p.eval (τ i)| ≤ |q.eval (τ i)|)
    (i : Fin n)
    (hterms : (∀ k : Fin (n + 1),
        0 ≤ q.eval (τ k) *
          (Polynomial.derivative (lagrangeBasis τ k)).eval
            (markovCRight hn q τ hτ_strict hτ_left hqcrit i)) ∨
      (∀ k : Fin (n + 1),
        q.eval (τ k) *
          (Polynomial.derivative (lagrangeBasis τ k)).eval
            (markovCRight hn q τ hτ_strict hτ_left hqcrit i) ≤ 0)) :
    |(Polynomial.derivative p).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit i)| ≤
      |(Polynomial.derivative q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit i)| := by
  exact derivative_eval_le_of_lagrange_common_sign p q τ hτ_strict hpdeg hqdeg hp_nodes
    (markovCRight hn q τ hτ_strict hτ_left hqcrit i) hterms

private theorem markovCLeft_derivative_bound_of_q_bound
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (i : Fin n)
    (hbound : |(Polynomial.derivative p).eval
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)| ≤
      |(Polynomial.derivative q).eval
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)|) :
    |(Polynomial.derivative p).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)| ≤
      |(markovAuxR q).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)| := by
  rwa [markovCLeft_abs_R_eq_abs_derivative_q hn q τ hτ_strict hτ_right hτ_left hqcrit i]

private theorem markovCRight_derivative_bound_of_q_bound
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (i : Fin n)
    (hbound : |(Polynomial.derivative p).eval
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i)| ≤
      |(Polynomial.derivative q).eval
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i)|) :
    |(Polynomial.derivative p).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit i)| ≤
      |(markovAuxR q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit i)| := by
  rwa [markovCRight_abs_R_eq_abs_derivative_q hn q τ hτ_strict hτ_right hτ_left hqcrit i]

private theorem markovC_R_mul_nonpos
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (i : Fin n) :
    (markovAuxR q).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit i) *
      (markovAuxR q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit i) ≤ 0 :=
  le_of_lt (markovC_R_mul_neg hn q τ hτ_strict hτ_right hτ_left hqcrit i)

private theorem exists_root_markovAuxR_perturb_markovC
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (a : ℝ) (ha : |a| ≤ 1) (i : Fin n)
    (horder : markovCLeft hn q τ hτ_strict hτ_right hqcrit i ≤
      markovCRight hn q τ hτ_strict hτ_left hqcrit i)
    (hleft_bound : |(Polynomial.derivative p).eval
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)| ≤
      |(markovAuxR q).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)|)
    (hright_bound : |(Polynomial.derivative p).eval
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i)| ≤
      |(markovAuxR q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit i)|) :
    ∃ c ∈ Set.Icc (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i),
      (markovAuxR q + Polynomial.C a * Polynomial.derivative p).eval c = 0 :=
  exists_root_markovAuxR_perturb_Icc p q horder hleft_bound hright_bound
    (markovC_R_mul_nonpos hn q τ hτ_strict hτ_right hτ_left hqcrit i) ha

private noncomputable def markovPerturbRoot
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (a : ℝ) (ha : |a| ≤ 1)
    (horder : ∀ i : Fin n, markovCLeft hn q τ hτ_strict hτ_right hqcrit i ≤
      markovCRight hn q τ hτ_strict hτ_left hqcrit i)
    (hleft_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)| ≤
      |(markovAuxR q).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)|)
    (hright_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i)| ≤
      |(markovAuxR q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit i)|)
    (i : Fin n) : ℝ :=
  Classical.choose (exists_root_markovAuxR_perturb_markovC hn p q τ hτ_strict hτ_right
    hτ_left hqcrit a ha i (horder i) (hleft_bound i) (hright_bound i))

private theorem markovPerturbRoot_mem
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (a : ℝ) (ha : |a| ≤ 1)
    (horder : ∀ i : Fin n, markovCLeft hn q τ hτ_strict hτ_right hqcrit i ≤
      markovCRight hn q τ hτ_strict hτ_left hqcrit i)
    (hleft_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)| ≤
      |(markovAuxR q).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)|)
    (hright_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i)| ≤
      |(markovAuxR q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit i)|)
    (i : Fin n) :
    markovPerturbRoot hn p q τ hτ_strict hτ_right hτ_left hqcrit a ha horder
        hleft_bound hright_bound i ∈
      Set.Icc (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i) :=
  (Classical.choose_spec (exists_root_markovAuxR_perturb_markovC hn p q τ hτ_strict
    hτ_right hτ_left hqcrit a ha i (horder i) (hleft_bound i) (hright_bound i))).1

private theorem markovPerturbRoot_zero
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (a : ℝ) (ha : |a| ≤ 1)
    (horder : ∀ i : Fin n, markovCLeft hn q τ hτ_strict hτ_right hqcrit i ≤
      markovCRight hn q τ hτ_strict hτ_left hqcrit i)
    (hleft_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)| ≤
      |(markovAuxR q).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)|)
    (hright_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i)| ≤
      |(markovAuxR q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit i)|)
    (i : Fin n) :
    (markovAuxR q + Polynomial.C a * Polynomial.derivative p).eval
      (markovPerturbRoot hn p q τ hτ_strict hτ_right hτ_left hqcrit a ha horder
        hleft_bound hright_bound i) = 0 :=
  (Classical.choose_spec (exists_root_markovAuxR_perturb_markovC hn p q τ hτ_strict
    hτ_right hτ_left hqcrit a ha i (horder i) (hleft_bound i) (hright_bound i))).2

private noncomputable def markovPerturbRootOfQBounds
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (a : ℝ) (ha : |a| ≤ 1)
    (hleft_q_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)| ≤
      |(Polynomial.derivative q).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)|)
    (hright_q_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i)| ≤
      |(Polynomial.derivative q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit i)|)
    (i : Fin n) : ℝ :=
  markovPerturbRoot hn p q τ hτ_strict hτ_right hτ_left hqcrit a ha
    (markovC_order hn q τ hτ_strict hτ_right hτ_left hqdeg hqcrit)
    (fun i => markovCLeft_derivative_bound_of_q_bound hn p q τ hτ_strict hτ_right hτ_left
      hqcrit i (hleft_q_bound i))
    (fun i => markovCRight_derivative_bound_of_q_bound hn p q τ hτ_strict hτ_right hτ_left
      hqcrit i (hright_q_bound i)) i

private theorem markovPerturbRootOfQBounds_mem
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (a : ℝ) (ha : |a| ≤ 1)
    (hleft_q_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)| ≤
      |(Polynomial.derivative q).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)|)
    (hright_q_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i)| ≤
      |(Polynomial.derivative q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit i)|)
    (i : Fin n) :
    markovPerturbRootOfQBounds hn p q τ hτ_strict hτ_right hτ_left hqdeg hqcrit a ha
        hleft_q_bound hright_q_bound i ∈
      Set.Icc (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i) :=
  markovPerturbRoot_mem hn p q τ hτ_strict hτ_right hτ_left hqcrit a ha
    (markovC_order hn q τ hτ_strict hτ_right hτ_left hqdeg hqcrit)
    (fun i => markovCLeft_derivative_bound_of_q_bound hn p q τ hτ_strict hτ_right hτ_left
      hqcrit i (hleft_q_bound i))
    (fun i => markovCRight_derivative_bound_of_q_bound hn p q τ hτ_strict hτ_right hτ_left
      hqcrit i (hright_q_bound i)) i

private theorem markovPerturbRootOfQBounds_zero
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (a : ℝ) (ha : |a| ≤ 1)
    (hleft_q_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)| ≤
      |(Polynomial.derivative q).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)|)
    (hright_q_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i)| ≤
      |(Polynomial.derivative q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit i)|)
    (i : Fin n) :
    (markovAuxR q + Polynomial.C a * Polynomial.derivative p).eval
      (markovPerturbRootOfQBounds hn p q τ hτ_strict hτ_right hτ_left hqdeg hqcrit a ha
        hleft_q_bound hright_q_bound i) = 0 :=
  markovPerturbRoot_zero hn p q τ hτ_strict hτ_right hτ_left hqcrit a ha
    (markovC_order hn q τ hτ_strict hτ_right hτ_left hqdeg hqcrit)
    (fun i => markovCLeft_derivative_bound_of_q_bound hn p q τ hτ_strict hτ_right hτ_left
      hqcrit i (hleft_q_bound i))
    (fun i => markovCRight_derivative_bound_of_q_bound hn p q τ hτ_strict hτ_right hτ_left
      hqcrit i (hright_q_bound i)) i


private theorem injective_of_mem_ordered_Icc
    {n : ℕ} {L R ρ : Fin n → ℝ}
    (hmem : ∀ i : Fin n, ρ i ∈ Set.Icc (L i) (R i))
    (hsep : ∀ i j : Fin n, i.val < j.val → R i < L j) :
    Function.Injective ρ := by
  intro i j hij
  by_contra hne
  have hval_ne : i.val ≠ j.val := by
    intro hval
    exact hne (Fin.ext hval)
  rcases lt_or_gt_of_ne hval_ne with hlt | hgt
  · have hltρ : ρ i < ρ j := lt_of_le_of_lt (hmem i).2 (lt_of_lt_of_le (hsep i j hlt) (hmem j).1)
    rw [hij] at hltρ
    exact lt_irrefl _ hltρ
  · have hltρ : ρ j < ρ i := lt_of_le_of_lt (hmem j).2 (lt_of_lt_of_le (hsep j i hgt) (hmem i).1)
    rw [hij] at hltρ
    exact lt_irrefl _ hltρ

private theorem markovPerturbRootOfQBounds_injective
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (a : ℝ) (ha : |a| ≤ 1)
    (hleft_q_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)| ≤
      |(Polynomial.derivative q).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)|)
    (hright_q_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i)| ≤
      |(Polynomial.derivative q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit i)|) :
    Function.Injective
      (markovPerturbRootOfQBounds hn p q τ hτ_strict hτ_right hτ_left hqdeg hqcrit a ha
        hleft_q_bound hright_q_bound) := by
  exact injective_of_mem_ordered_Icc
    (markovPerturbRootOfQBounds_mem hn p q τ hτ_strict hτ_right hτ_left hqdeg hqcrit a
      ha hleft_q_bound hright_q_bound)
    (markovC_intervals_separated hn q τ hτ_strict hτ_right hτ_left hqcrit)

private theorem comparison_of_not_mem_markovPerturbRoots
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (hleft_q_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)| ≤
      |(Polynomial.derivative q).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)|)
    (hright_q_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i)| ≤
      |(Polynomial.derivative q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit i)|)
    {x : ℝ}
    (hroot_inj : ∀ (a : ℝ) (ha : |a| ≤ 1), Function.Injective
      (markovPerturbRootOfQBounds hn p q τ hτ_strict hτ_right hτ_left hqdeg hqcrit a
        ha hleft_q_bound hright_q_bound))
    (hxnot : ∀ (a : ℝ) (ha : |a| ≤ 1) (i : Fin n), x ≠
      markovPerturbRootOfQBounds hn p q τ hτ_strict hτ_right hτ_left hqdeg hqcrit a ha
        hleft_q_bound hright_q_bound i) :
    |(Polynomial.derivative p).eval x| ≤
      max |(Polynomial.derivative q).eval x| |(markovAuxR q).eval x| := by
  apply comparison_of_no_perturb_root p q
  intro a ha hxroot
  exact not_extra_root_of_markovAuxR_perturb_of_fin_roots hn p q a
    (markovPerturbRootOfQBounds hn p q τ hτ_strict hτ_right hτ_left hqdeg hqcrit a ha
      hleft_q_bound hright_q_bound)
    (hroot_inj a ha) hpdeg hqdeg
    (fun i => markovPerturbRootOfQBounds_zero hn p q τ hτ_strict hτ_right hτ_left hqdeg
      hqcrit a ha hleft_q_bound hright_q_bound i)
    (fun i => hxnot a ha i) hxroot

private theorem markovC_endpoint_q_bounds_of_common_sign
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (hp_nodes : ∀ i : Fin (n + 1), |p.eval (τ i)| ≤ |q.eval (τ i)|)
    (hleft_terms : ∀ i : Fin n,
      (∀ k : Fin (n + 1),
          0 ≤ q.eval (τ k) *
            (Polynomial.derivative (lagrangeBasis τ k)).eval
              (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)) ∨
        (∀ k : Fin (n + 1),
          q.eval (τ k) *
            (Polynomial.derivative (lagrangeBasis τ k)).eval
              (markovCLeft hn q τ hτ_strict hτ_right hqcrit i) ≤ 0))
    (hright_terms : ∀ i : Fin n,
      (∀ k : Fin (n + 1),
          0 ≤ q.eval (τ k) *
            (Polynomial.derivative (lagrangeBasis τ k)).eval
              (markovCRight hn q τ hτ_strict hτ_left hqcrit i)) ∨
        (∀ k : Fin (n + 1),
          q.eval (τ k) *
            (Polynomial.derivative (lagrangeBasis τ k)).eval
              (markovCRight hn q τ hτ_strict hτ_left hqcrit i) ≤ 0)) :
    (∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)| ≤
      |(Polynomial.derivative q).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)|) ∧
    (∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i)| ≤
      |(Polynomial.derivative q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit i)|) := by
  constructor
  · intro i
    exact markovCLeft_derivative_q_bound_of_common_sign hn p q τ hτ_strict hτ_right hpdeg
      hqdeg hqcrit hp_nodes i (hleft_terms i)
  · intro i
    exact markovCRight_derivative_q_bound_of_common_sign hn p q τ hτ_strict hτ_left hpdeg
      hqdeg hqcrit hp_nodes i (hright_terms i)

private theorem not_mem_markovPerturbRoots_of_not_mem_markovC
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (hleft_q_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)| ≤
      |(Polynomial.derivative q).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)|)
    (hright_q_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i)| ≤
      |(Polynomial.derivative q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit i)|)
    {x : ℝ}
    (hxnotC : ∀ i : Fin n, x ∉ Set.Icc
      (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)
      (markovCRight hn q τ hτ_strict hτ_left hqcrit i)) :
    ∀ (a : ℝ) (ha : |a| ≤ 1) (i : Fin n), x ≠
      markovPerturbRootOfQBounds hn p q τ hτ_strict hτ_right hτ_left hqdeg hqcrit a ha
        hleft_q_bound hright_q_bound i := by
  intro a ha i hxeq
  have hmem := markovPerturbRootOfQBounds_mem hn p q τ hτ_strict hτ_right hτ_left hqdeg
    hqcrit a ha hleft_q_bound hright_q_bound i
  exact hxnotC i (by simpa [hxeq] using hmem)

private theorem comparison_of_not_mem_markovPerturbRoots_of_q_bounds
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (hleft_q_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)| ≤
      |(Polynomial.derivative q).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)|)
    (hright_q_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i)| ≤
      |(Polynomial.derivative q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit i)|)
    {x : ℝ}
    (hxnot : ∀ (a : ℝ) (ha : |a| ≤ 1) (i : Fin n), x ≠
      markovPerturbRootOfQBounds hn p q τ hτ_strict hτ_right hτ_left hqdeg hqcrit a ha
        hleft_q_bound hright_q_bound i) :
    |(Polynomial.derivative p).eval x| ≤
      max |(Polynomial.derivative q).eval x| |(markovAuxR q).eval x| := by
  exact comparison_of_not_mem_markovPerturbRoots hn p q τ hτ_strict hτ_right hτ_left hpdeg
    hqdeg hqcrit hleft_q_bound hright_q_bound
    (fun a ha => markovPerturbRootOfQBounds_injective hn p q τ hτ_strict hτ_right hτ_left
      hqdeg hqcrit a ha hleft_q_bound hright_q_bound)
    hxnot

private theorem comparison_of_common_sign_at
    {n : ℕ} (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree = n)
    (hp_nodes : ∀ i : Fin (n + 1), |p.eval (τ i)| ≤ |q.eval (τ i)|)
    {x : ℝ} (hterms : lagrangeQDerivativeTermsCommonSign q τ x) :
    |(Polynomial.derivative p).eval x| ≤
      max |(Polynomial.derivative q).eval x| |(markovAuxR q).eval x| := by
  exact comparison_of_lagrange_common_sign p q τ hτ_strict hpdeg hqdeg hp_nodes x hterms

private theorem comparison_of_mem_markovC_of_common_sign
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (hp_nodes : ∀ i : Fin (n + 1), |p.eval (τ i)| ≤ |q.eval (τ i)|)
    {x : ℝ} (i : Fin n)
    (_hxC : x ∈ Set.Icc (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)
      (markovCRight hn q τ hτ_strict hτ_left hqcrit i))
    (hterms : lagrangeQDerivativeTermsCommonSign q τ x) :
    |(Polynomial.derivative p).eval x| ≤
      max |(Polynomial.derivative q).eval x| |(markovAuxR q).eval x| := by
  exact comparison_of_common_sign_at p q τ hτ_strict hpdeg hqdeg hp_nodes hterms

private theorem comparison_of_not_mem_markovC_of_q_bounds
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (hleft_q_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)| ≤
      |(Polynomial.derivative q).eval (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)|)
    (hright_q_bound : ∀ i : Fin n, |(Polynomial.derivative p).eval
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i)| ≤
      |(Polynomial.derivative q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit i)|)
    {x : ℝ}
    (hxnotC : ∀ i : Fin n, x ∉ Set.Icc
      (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)
      (markovCRight hn q τ hτ_strict hτ_left hqcrit i)) :
    |(Polynomial.derivative p).eval x| ≤
      max |(Polynomial.derivative q).eval x| |(markovAuxR q).eval x| := by
  exact comparison_of_not_mem_markovPerturbRoots_of_q_bounds hn p q τ hτ_strict hτ_right
    hτ_left hpdeg hqdeg hqcrit hleft_q_bound hright_q_bound
    (not_mem_markovPerturbRoots_of_not_mem_markovC hn p q τ hτ_strict hτ_right hτ_left
      hqdeg hqcrit hleft_q_bound hright_q_bound hxnotC)

private theorem markovC_mem_or_not_mem_all
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (x : ℝ) :
    (∃ i : Fin n, x ∈ Set.Icc
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i)) ∨
      (∀ i : Fin n, x ∉ Set.Icc
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i)) := by
  classical
  by_cases h : ∃ i : Fin n, x ∈ Set.Icc
      (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)
      (markovCRight hn q τ hτ_strict hτ_left hqcrit i)
  · exact Or.inl h
  · exact Or.inr (by intro i hi; exact h ⟨i, hi⟩)

private theorem duffin_schaeffer_comparison_from_common_sign_partition
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (hp_nodes : ∀ i : Fin (n + 1), |p.eval (τ i)| ≤ |q.eval (τ i)|)
    {x : ℝ}
    (hleft_terms : ∀ i : Fin n,
      lagrangeQDerivativeTermsCommonSign q τ
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit i))
    (hright_terms : ∀ i : Fin n,
      lagrangeQDerivativeTermsCommonSign q τ
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i))
    (hCsign : ∀ i : Fin n,
      x ∈ Set.Icc (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i) →
      lagrangeQDerivativeTermsCommonSign q τ x)
    (hpartition : (∃ i : Fin n, x ∈ Set.Icc
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i)) ∨
      (∀ i : Fin n, x ∉ Set.Icc
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i))) :
    |(Polynomial.derivative p).eval x| ≤
      max |(Polynomial.derivative q).eval x| |(markovAuxR q).eval x| := by
  rcases hpartition with ⟨i, hxC⟩ | hxnotC
  · exact comparison_of_mem_markovC_of_common_sign hn p q τ hτ_strict hτ_right hτ_left hpdeg
      hqdeg hqcrit hp_nodes i hxC (hCsign i hxC)
  · have hbounds := markovC_endpoint_q_bounds_of_common_sign hn p q τ hτ_strict hτ_right
      hτ_left hpdeg hqdeg hqcrit hp_nodes
      (fun i => (hleft_terms i).comm) (fun i => (hright_terms i).comm)
    exact comparison_of_not_mem_markovC_of_q_bounds hn p q τ hτ_strict hτ_right hτ_left hpdeg
      hqdeg hqcrit hbounds.1 hbounds.2 hxnotC

private theorem duffin_schaeffer_comparison_from_common_sign
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (hp_nodes : ∀ i : Fin (n + 1), |p.eval (τ i)| ≤ |q.eval (τ i)|)
    (x : ℝ)
    (hleft_terms : ∀ i : Fin n,
      lagrangeQDerivativeTermsCommonSign q τ
        (markovCLeft hn q τ hτ_strict hτ_right hqcrit i))
    (hright_terms : ∀ i : Fin n,
      lagrangeQDerivativeTermsCommonSign q τ
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i))
    (hCsign : ∀ i : Fin n,
      x ∈ Set.Icc (markovCLeft hn q τ hτ_strict hτ_right hqcrit i)
        (markovCRight hn q τ hτ_strict hτ_left hqcrit i) →
      lagrangeQDerivativeTermsCommonSign q τ x) :
    |(Polynomial.derivative p).eval x| ≤
      max |(Polynomial.derivative q).eval x| |(markovAuxR q).eval x| := by
  exact duffin_schaeffer_comparison_from_common_sign_partition hn p q τ hτ_strict hτ_right
    hτ_left hpdeg hqdeg hqcrit hp_nodes hleft_terms hright_terms hCsign
    (markovC_mem_or_not_mem_all hn q τ hτ_strict hτ_right hτ_left hqcrit x)

private theorem duffin_schaeffer_comparison_from_pairwise_term_products
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (hp_nodes : ∀ i : Fin (n + 1), |p.eval (τ i)| ≤ |q.eval (τ i)|)
    (x : ℝ)
    (hleft_pair : ∀ c : Fin n, ∀ i j : Fin (n + 1),
      0 ≤ (q.eval (τ i) * (Polynomial.derivative (lagrangeBasis τ i)).eval
          (markovCLeft hn q τ hτ_strict hτ_right hqcrit c)) *
        (q.eval (τ j) * (Polynomial.derivative (lagrangeBasis τ j)).eval
          (markovCLeft hn q τ hτ_strict hτ_right hqcrit c)))
    (hright_pair : ∀ c : Fin n, ∀ i j : Fin (n + 1),
      0 ≤ (q.eval (τ i) * (Polynomial.derivative (lagrangeBasis τ i)).eval
          (markovCRight hn q τ hτ_strict hτ_left hqcrit c)) *
        (q.eval (τ j) * (Polynomial.derivative (lagrangeBasis τ j)).eval
          (markovCRight hn q τ hτ_strict hτ_left hqcrit c)))
    (hCpair : ∀ c : Fin n,
      x ∈ Set.Icc (markovCLeft hn q τ hτ_strict hτ_right hqcrit c)
        (markovCRight hn q τ hτ_strict hτ_left hqcrit c) →
      ∀ i j : Fin (n + 1),
        0 ≤ (q.eval (τ i) * (Polynomial.derivative (lagrangeBasis τ i)).eval x) *
          (q.eval (τ j) * (Polynomial.derivative (lagrangeBasis τ j)).eval x)) :
    |(Polynomial.derivative p).eval x| ≤
      max |(Polynomial.derivative q).eval x| |(markovAuxR q).eval x| := by
  apply duffin_schaeffer_comparison_from_common_sign hn p q τ hτ_strict hτ_right hτ_left
    hpdeg hqdeg hqcrit hp_nodes x
  · intro c
    exact lagrangeQDerivativeTermsCommonSign_of_pairwise_mul_nonneg q τ
      (markovCLeft hn q τ hτ_strict hτ_right hqcrit c) (hleft_pair c)
  · intro c
    exact lagrangeQDerivativeTermsCommonSign_of_pairwise_mul_nonneg q τ
      (markovCRight hn q τ hτ_strict hτ_left hqcrit c) (hright_pair c)
  · intro c hxC
    exact lagrangeQDerivativeTermsCommonSign_of_pairwise_mul_nonneg q τ x (hCpair c hxC)

private theorem lagrangeProductDerivative_pairwise_nonneg_on_Icc_of_Ioo
    {n : ℕ} (hn : 2 ≤ n) (q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (c : Fin n)
    (hopen : ∀ x ∈ Set.Ioo (markovCLeft hn q τ hτ_strict hτ_right hqcrit c)
        (markovCRight hn q τ hτ_strict hτ_left hqcrit c),
      ∀ i j : Fin (n + 1),
        0 ≤ lagrangeProductDerivativeEval τ i x * lagrangeProductDerivativeEval τ j x) :
    ∀ x ∈ Set.Icc (markovCLeft hn q τ hτ_strict hτ_right hqcrit c)
        (markovCRight hn q τ hτ_strict hτ_left hqcrit c),
      ∀ i j : Fin (n + 1),
        0 ≤ lagrangeProductDerivativeEval τ i x * lagrangeProductDerivativeEval τ j x := by
  intro x hx i j
  have horder := markovC_order hn q τ hτ_strict hτ_right hτ_left hqdeg hqcrit c
  have hne : markovCLeft hn q τ hτ_strict hτ_right hqcrit c ≠
      markovCRight hn q τ hτ_strict hτ_left hqcrit c := by
    intro hEq
    have hneg := markovC_R_mul_neg hn q τ hτ_strict hτ_right hτ_left hqcrit c
    rw [hEq] at hneg
    have hsquare : 0 ≤ (markovAuxR q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit c) *
        (markovAuxR q).eval (markovCRight hn q τ hτ_strict hτ_left hqcrit c) := by
      nlinarith [sq_nonneg ((markovAuxR q).eval
        (markovCRight hn q τ hτ_strict hτ_left hqcrit c))]
    exact not_lt_of_ge hsquare hneg
  have hlt : markovCLeft hn q τ hτ_strict hτ_right hqcrit c <
      markovCRight hn q τ hτ_strict hτ_left hqcrit c := lt_of_le_of_ne horder hne
  have hi_cont : Continuous fun y : ℝ => lagrangeProductDerivativeEval τ i y := by
    unfold lagrangeProductDerivativeEval
    exact Polynomial.continuous _
  have hj_cont : Continuous fun y : ℝ => lagrangeProductDerivativeEval τ j y := by
    unfold lagrangeProductDerivativeEval
    exact Polynomial.continuous _
  have hcont : Continuous fun y : ℝ =>
      lagrangeProductDerivativeEval τ i y * lagrangeProductDerivativeEval τ j y :=
    hi_cont.mul hj_cont
  exact continuous_nonneg_on_Icc_of_nonneg_on_Ioo hlt hcont
    (fun y hy => hopen y hy i j) x hx

private theorem duffin_schaeffer_comparison_from_product_derivative_signs
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (hq_alt : ∀ i : Fin n,
      q.eval (τ ⟨i.val, by omega⟩) * q.eval (τ ⟨i.val + 1, by omega⟩) < 0)
    (hp_nodes : ∀ i : Fin (n + 1), |p.eval (τ i)| ≤ |q.eval (τ i)|)
    (x : ℝ)
    (hleft_prod : ∀ c : Fin n, ∀ i j : Fin (n + 1),
      0 ≤ lagrangeProductDerivativeEval τ i
          (markovCLeft hn q τ hτ_strict hτ_right hqcrit c) *
        lagrangeProductDerivativeEval τ j
          (markovCLeft hn q τ hτ_strict hτ_right hqcrit c))
    (hright_prod : ∀ c : Fin n, ∀ i j : Fin (n + 1),
      0 ≤ lagrangeProductDerivativeEval τ i
          (markovCRight hn q τ hτ_strict hτ_left hqcrit c) *
        lagrangeProductDerivativeEval τ j
          (markovCRight hn q τ hτ_strict hτ_left hqcrit c))
    (hCprod : ∀ c : Fin n,
      x ∈ Set.Icc (markovCLeft hn q τ hτ_strict hτ_right hqcrit c)
        (markovCRight hn q τ hτ_strict hτ_left hqcrit c) →
      ∀ i j : Fin (n + 1),
        0 ≤ lagrangeProductDerivativeEval τ i x * lagrangeProductDerivativeEval τ j x) :
    |(Polynomial.derivative p).eval x| ≤
      max |(Polynomial.derivative q).eval x| |(markovAuxR q).eval x| := by
  have hcoeff := q_div_lagrangeDenom_pairwise_nonneg (Nat.one_le_of_lt hn) q τ hτ_strict hq_alt
  apply duffin_schaeffer_comparison_from_pairwise_term_products hn p q τ hτ_strict hτ_right
    hτ_left hpdeg hqdeg hqcrit hp_nodes x
  · intro c
    exact lagrange_term_pairwise_nonneg_of_product_derivative_pairwise q τ
      (markovCLeft hn q τ hτ_strict hτ_right hqcrit c) hcoeff (hleft_prod c)
  · intro c
    exact lagrange_term_pairwise_nonneg_of_product_derivative_pairwise q τ
      (markovCRight hn q τ hτ_strict hτ_left hqcrit c) hcoeff (hright_prod c)
  · intro c hxC
    exact lagrange_term_pairwise_nonneg_of_product_derivative_pairwise q τ x hcoeff (hCprod c hxC)

private theorem duffin_schaeffer_comparison_from_markovC_Ioo_product_derivative_signs
    {n : ℕ} (hn : 2 ≤ n) (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ) (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hτ_left : τ 0 = -1) (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (hq_alt : ∀ i : Fin n,
      q.eval (τ ⟨i.val, by omega⟩) * q.eval (τ ⟨i.val + 1, by omega⟩) < 0)
    (hp_nodes : ∀ i : Fin (n + 1), |p.eval (τ i)| ≤ |q.eval (τ i)|)
    (x : ℝ)
    (hC_open : ∀ c : Fin n, ∀ y ∈
      Set.Ioo (markovCLeft hn q τ hτ_strict hτ_right hqcrit c)
        (markovCRight hn q τ hτ_strict hτ_left hqcrit c),
      ∀ i j : Fin (n + 1),
        0 ≤ lagrangeProductDerivativeEval τ i y * lagrangeProductDerivativeEval τ j y) :
    |(Polynomial.derivative p).eval x| ≤
      max |(Polynomial.derivative q).eval x| |(markovAuxR q).eval x| := by
  let hclosed := fun c =>
    lagrangeProductDerivative_pairwise_nonneg_on_Icc_of_Ioo hn q τ hτ_strict hτ_right
      hτ_left hqdeg hqcrit c (hC_open c)
  exact duffin_schaeffer_comparison_from_product_derivative_signs hn p q τ hτ_strict hτ_right
    hτ_left hpdeg hqdeg hqcrit hq_alt hp_nodes x
    (fun c => hclosed c (markovCLeft hn q τ hτ_strict hτ_right hqcrit c)
      ⟨le_rfl, markovC_order hn q τ hτ_strict hτ_right hτ_left hqdeg hqcrit c⟩)
    (fun c => hclosed c (markovCRight hn q τ hτ_strict hτ_left hqcrit c)
      ⟨markovC_order hn q τ hτ_strict hτ_right hτ_left hqdeg hqcrit c, le_rfl⟩)
    (fun c hxC => hclosed c x hxC)

/-- Abstract Duffin-Schaeffer first-derivative comparison lemma.

The concrete Chebyshev specialization instantiates `q` with `chebyshevT n`; the
polynomial `r` below then becomes `n^2 * T_n` by the Chebyshev differential equation.
-/
theorem duffin_schaeffer_first_derivative_comparison
    {n : ℕ} (hn : 2 ≤ n)
    (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ)
    (hτ_strict : StrictMono τ)
    (hτ_left : τ 0 = -1)
    (hτ_right : τ ⟨n, by omega⟩ = 1)
    (hpdeg : p.natDegree ≤ n)
    (hqdeg : q.natDegree = n)
    (hqcrit : ∀ x : ℝ,
      (Polynomial.derivative q).eval x = 0 ↔
        ∃ i : Fin (n - 1), x = τ ⟨i.val + 1, by omega⟩)
    (hq_alt : ∀ i : Fin n,
      q.eval (τ ⟨i.val, by omega⟩) * q.eval (τ ⟨i.val + 1, by omega⟩) < 0)
    (hp_nodes : ∀ i : Fin (n + 1), |p.eval (τ i)| ≤ |q.eval (τ i)|)
    (x : ℝ) (_hx1 : -1 ≤ x) (_hx2 : x ≤ 1) :
    |(Polynomial.derivative p).eval x| ≤
      max |(Polynomial.derivative q).eval x| |(markovAuxR q).eval x| := by
  exact duffin_schaeffer_comparison_from_markovC_Ioo_product_derivative_signs hn p q τ
    hτ_strict hτ_right hτ_left hpdeg hqdeg hqcrit hq_alt hp_nodes x
    (fun c y hy => lagrangeProductDerivative_pairwise_nonneg_on_markovC_Ioo hn q τ
      hτ_strict hτ_right hτ_left hqdeg hqcrit c hy)

/-- Normalized first-derivative Markov inequality.

The proof handles degrees zero and one directly, then applies the Duffin-Schaeffer
comparison argument in degree at least two. -/
theorem univariate_markov_first_derivative_inside_normalized
    (p : Polynomial ℝ) (d : ℕ) (hdeg : p.natDegree ≤ d)
    (hp : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → |p.eval x| ≤ 1)
    (x : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    |(Polynomial.derivative p).eval x| ≤ (d : ℝ) ^ 2 := by
  rcases d with _ | d
  · simpa using markov_first_derivative_bound_degree_zero p 1 (by norm_num) hdeg x
  · rcases d with _ | d
    · simpa using markov_first_derivative_bound_degree_one p 1 (by norm_num) hdeg hp x
    · have hd : 2 ≤ d + 2 := by omega
      have hp_nodes : ∀ i : Fin (d + 2 + 1),
          |p.eval (chebyshevExtremalNode (d + 2) i)| ≤
            |(chebyshevT (d + 2)).eval (chebyshevExtremalNode (d + 2) i)| := by
        intro i
        have hmem : chebyshevExtremalNode (d + 2) i ∈ Set.Icc (-1 : ℝ) 1 := by
          unfold chebyshevExtremalNode
          exact Polynomial.Chebyshev.node_mem_Icc
        rw [chebyshevT_eval_extremalNode_abs]
        exact hp _ hmem.1 hmem.2
      have hcomp := duffin_schaeffer_first_derivative_comparison hd p (chebyshevT (d + 2))
        (chebyshevExtremalNode (d + 2))
        (chebyshevExtremalNode_strictMono (d + 2))
        (chebyshevExtremalNode_left (by omega))
        (chebyshevExtremalNode_right (d + 2))
        hdeg
        (natDegree_chebyshevT (d + 2))
        (chebyshevT_derivative_eq_zero_iff_exists_extremalNode hd)
        (chebyshevT_extremalNode_adjacent_mul_neg (d + 2))
        hp_nodes x hx1 hx2
      exact hcomp.trans (max_le (chebyshevT_deriv_bound_k1 (d + 2) x hx1 hx2)
        (chebyshevT_differential_eval_abs_le (d + 2) x hx1 hx2))

/-- Bounded-form first-derivative Markov inequality.

This reduces the arbitrary bound on the interval to the normalized statement by scaling. -/
theorem univariate_markov_first_derivative_inside_bound
    (p : Polynomial ℝ) (d : ℕ) (hdeg : p.natDegree ≤ d)
    (M : ℝ) (hM : 0 ≤ M)
    (hp : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → |p.eval x| ≤ M)
    (x : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    |(Polynomial.derivative p).eval x| ≤ (d : ℝ) ^ 2 * M := by
  by_cases hM0 : M = 0
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
    have hqdeg : q.natDegree ≤ d := by
      calc q.natDegree ≤ p.natDegree := by
            rw [hq]
            exact Polynomial.natDegree_C_mul_le M⁻¹ p
        _ ≤ d := hdeg
    have hqbound : ∀ y : ℝ, -1 ≤ y → y ≤ 1 → |q.eval y| ≤ 1 := by
      intro y hy1 hy2
      rw [hq, Polynomial.eval_mul, Polynomial.eval_C, abs_mul,
        abs_of_nonneg (inv_nonneg.mpr hM)]
      rw [inv_mul_le_iff₀ hMpos]
      simpa using hp y hy1 hy2
    have hnorm := univariate_markov_first_derivative_inside_normalized q d hqdeg hqbound
      x hx1 hx2
    have hderiv : Polynomial.derivative q = Polynomial.C M⁻¹ * Polynomial.derivative p := by
      rw [hq, Polynomial.derivative_mul]
      simp
    rw [hderiv, Polynomial.eval_mul, Polynomial.eval_C] at hnorm
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hM)] at hnorm
    calc |(Polynomial.derivative p).eval x|
        = M * (M⁻¹ * |(Polynomial.derivative p).eval x|) := by
            rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hMpos), one_mul]
      _ ≤ M * ((d : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hnorm hM
      _ = (d : ℝ) ^ 2 * M := by ring

/-- Sup-norm version of the first-derivative Markov inequality.

This specializes `univariate_markov_first_derivative_inside_bound` to the polynomial sup norm. -/
theorem univariate_markov_first_derivative_inside_proof
    (p : Polynomial ℝ) (d : ℕ) (hdeg : p.natDegree ≤ d)
    (x : ℝ) (hx : |x| ≤ 1) :
    |(Polynomial.derivative p).eval x| ≤ d ^ 2 * polySupNormUni p := by
  have hx' := abs_le.mp hx
  exact univariate_markov_first_derivative_inside_bound p d hdeg (polySupNormUni p)
    (polySupNormUni_nonneg p)
    (fun y hy1 hy2 => polySupNormUni_eval_le p y hy1 hy2)
    x hx'.1 hx'.2

end OptimalConvergenceRates

end
