/-
  OptimalConvergenceRates/MarkovInequality/PolynomialDerivativeLemmas.lean

  Lagrange interpolation and derivative-comparison lemmas for the Duffin-Schaeffer proof.
-/
import OptimalConvergenceRates.MarkovInequality.ChebyshevExtrema
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue

open Polynomial Finset
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates

/-!
## Lagrange interpolation infrastructure

A product-based Lagrange basis avoids polynomial division and simple-root
bookkeeping in the interpolation step.
-/

noncomputable def lagrangeDenom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (i : ι) : ℝ :=
  (Finset.univ.erase i).prod (fun j => τ i - τ j)

/-- Lagrange basis polynomial for a finite set of nodes. -/
noncomputable def lagrangeBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (i : ι) : Polynomial ℝ :=
  Polynomial.C ((lagrangeDenom τ i)⁻¹) *
    (Finset.univ.erase i).prod (fun j => Polynomial.X - Polynomial.C (τ j))

/-- Distinctness hypothesis for finite interpolation nodes. -/
def DistinctNodes {ι : Type*} (τ : ι → ℝ) : Prop :=
  Function.Injective τ

theorem lagrangeDenom_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ : ι → ℝ} (hτ : DistinctNodes τ) (i : ι) :
    lagrangeDenom τ i ≠ 0 := by
  unfold lagrangeDenom
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  exact sub_ne_zero.mpr (fun h => hji (hτ h.symm))

/-- The Lagrange basis vanishes at every other node. -/
theorem lagrangeBasis_eval_ne {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ : ι → ℝ} (_hτ : DistinctNodes τ) {i j : ι} (hij : i ≠ j) :
    (lagrangeBasis τ i).eval (τ j) = 0 := by
  unfold lagrangeBasis
  rw [Polynomial.eval_mul]
  apply mul_eq_zero_of_right
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero
  · exact Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  · simp

/-- The Lagrange basis is one at its own node. -/
theorem lagrangeBasis_eval_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ : ι → ℝ} (hτ : DistinctNodes τ) (i : ι) :
    (lagrangeBasis τ i).eval (τ i) = 1 := by
  unfold lagrangeBasis
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  have hprod_ne : lagrangeDenom τ i ≠ 0 := by
    unfold lagrangeDenom
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    exact sub_ne_zero.mpr (fun h => hji (hτ h.symm))
  have hprod_eval :
      (Finset.univ.erase i).prod (fun j => (Polynomial.X - Polynomial.C (τ j)).eval (τ i)) =
        lagrangeDenom τ i := by
    apply Finset.prod_congr rfl
    intro j hj
    simp
  rw [hprod_eval, inv_mul_cancel₀ hprod_ne]

theorem lagrangeBasis_derivative_eval_eq_inv_mul_prod_derivative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (i : ι) (x : ℝ) :
    (Polynomial.derivative (lagrangeBasis τ i)).eval x =
      (lagrangeDenom τ i)⁻¹ *
        (Polynomial.derivative
          ((Finset.univ.erase i).prod (fun j => Polynomial.X - Polynomial.C (τ j)))).eval x := by
  unfold lagrangeBasis
  rw [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.eval_mul, Polynomial.eval_C]

theorem lagrangeProduct_splits {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (i : ι) :
    ((Finset.univ.erase i).prod (fun j => Polynomial.X - Polynomial.C (τ j))).Splits := by
  exact Polynomial.Splits.prod (fun j _ => Polynomial.Splits.X_sub_C (R := ℝ) (τ j))

theorem lagrangeProduct_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (i : ι) :
    (Finset.univ.erase i).prod (fun j => Polynomial.X - Polynomial.C (τ j)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact Polynomial.X_sub_C_ne_zero (r := τ j)

theorem lagrangeProduct_eval_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (i : ι) {x : ℝ}
    (hx : ∀ j : ι, j ≠ i → x ≠ τ j) :
    ((Finset.univ.erase i).prod (fun j => Polynomial.X - Polynomial.C (τ j))).eval x ≠ 0 := by
  rw [Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact sub_ne_zero.mpr (hx j (Finset.mem_erase.mp hj).1)

theorem lagrangeProduct_roots
    {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ℝ) (i : ι) :
    ((Finset.univ.erase i).prod (fun j => Polynomial.X - Polynomial.C (τ j))).roots =
      ((Finset.univ.erase i).val.map τ) := by
  rw [Polynomial.roots_prod (fun j => Polynomial.X - Polynomial.C (τ j))
    (Finset.univ.erase i) (lagrangeProduct_ne_zero τ i)]
  simp [Polynomial.roots_X_sub_C]

theorem lagrangeProduct_derivative_div_eval_eq_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ℝ) (i : ι) {x : ℝ}
    (hx : ∀ j : ι, j ≠ i → x ≠ τ j) :
    (Polynomial.derivative
        ((Finset.univ.erase i).prod (fun j => Polynomial.X - Polynomial.C (τ j)))).eval x /
      ((Finset.univ.erase i).prod (fun j => Polynomial.X - Polynomial.C (τ j))).eval x =
        ∑ j ∈ Finset.univ.erase i, 1 / (x - τ j) := by
  rw [(lagrangeProduct_splits τ i).eval_derivative_div_eval_of_ne_zero
    (lagrangeProduct_eval_ne_zero τ i hx)]
  rw [lagrangeProduct_roots τ i]
  simp [Finset.sum_eq_multiset_sum]

theorem derivative_prod_linear_factors
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (τ : ι → ℝ) :
    Polynomial.derivative (s.prod (fun j => Polynomial.X - Polynomial.C (τ j))) =
      s.sum (fun j => (s.erase j).prod (fun k => Polynomial.X - Polynomial.C (τ k))) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.prod_insert ha, Polynomial.derivative_mul, Polynomial.derivative_X_sub_C, ih]
    rw [Finset.sum_insert ha]
    simp only [Finset.erase_insert ha, one_mul]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have haj : a ≠ j := by
      intro h
      exact ha (h ▸ hj)
    have herase : (insert a s).erase j = insert a (s.erase j) := by
      ext k
      simp
      aesop
    rw [herase, Finset.prod_insert]
    simp [ha]

noncomputable def lagrangeProductDerivativeEval
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (x : ℝ) : ℝ :=
  (Polynomial.derivative
    ((Finset.univ.erase i).prod (fun j => Polynomial.X - Polynomial.C (τ j)))).eval x

theorem lagrangeProductDerivativeEval_eq_sum_products
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (x : ℝ) :
    lagrangeProductDerivativeEval τ i x =
      ∑ j ∈ Finset.univ.erase i,
        ((Finset.univ.erase i).erase j).prod (fun k => x - τ k) := by
  unfold lagrangeProductDerivativeEval
  rw [derivative_prod_linear_factors]
  rw [Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro k hk
  simp

theorem lagrangeProductDerivativeEval_eq_eval_mul_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ℝ) (i : ι) {x : ℝ}
    (hx : ∀ j : ι, j ≠ i → x ≠ τ j) :
    (Polynomial.derivative
        ((Finset.univ.erase i).prod (fun j => Polynomial.X - Polynomial.C (τ j)))).eval x =
      ((Finset.univ.erase i).prod (fun j => Polynomial.X - Polynomial.C (τ j))).eval x *
        (∑ j ∈ Finset.univ.erase i, 1 / (x - τ j)) := by
  have hne := lagrangeProduct_eval_ne_zero τ i hx
  have h := lagrangeProduct_derivative_div_eval_eq_sum τ i hx
  field_simp [hne] at h
  exact h

theorem lagrangeBasis_natDegree_lt_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (i : ι) :
    (lagrangeBasis τ i).natDegree < Fintype.card ι := by
  unfold lagrangeBasis
  calc
    (Polynomial.C (((Finset.univ.erase i).prod (fun j => τ i - τ j))⁻¹) *
          (Finset.univ.erase i).prod (fun j => Polynomial.X - Polynomial.C (τ j))).natDegree
        ≤ ((Finset.univ.erase i).prod (fun j => Polynomial.X - Polynomial.C (τ j))).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
    _ ≤ (Finset.univ.erase i).sum (fun j => (Polynomial.X - Polynomial.C (τ j)).natDegree) := by
          exact Polynomial.natDegree_prod_le (Finset.univ.erase i)
            (fun j => Polynomial.X - Polynomial.C (τ j))
    _ ≤ (Finset.univ.erase i).sum (fun _ => 1) := by
          apply Finset.sum_le_sum
          intro j hj
          calc (Polynomial.X - Polynomial.C (τ j)).natDegree
              ≤ max Polynomial.X.natDegree (Polynomial.C (τ j)).natDegree :=
                Polynomial.natDegree_sub_le _ _
            _ ≤ 1 := by simp [Polynomial.natDegree_X]
    _ = (Finset.univ.erase i).card := by simp
    _ < Fintype.card ι := by
          have hcard := Finset.card_erase_add_one (s := (Finset.univ : Finset ι))
            (a := i) (Finset.mem_univ i)
          rw [Finset.card_univ] at hcard
          omega

/-- Lagrange interpolation formula for polynomials of degree below the number of nodes. -/
theorem lagrange_interpolation_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ : ι → ℝ} (hτ : DistinctNodes τ)
    (p : Polynomial ℝ) (hpdeg : p.natDegree < Fintype.card ι) :
    p = Finset.univ.sum (fun i : ι => Polynomial.C (p.eval (τ i)) * lagrangeBasis τ i) := by
  let S : Polynomial ℝ :=
    Finset.univ.sum (fun i : ι => Polynomial.C (p.eval (τ i)) * lagrangeBasis τ i)
  have hcard_pos : 0 < Fintype.card ι := lt_of_le_of_lt (Nat.zero_le _) hpdeg
  have hterm_deg : ∀ i : ι,
      (Polynomial.C (p.eval (τ i)) * lagrangeBasis τ i).natDegree ≤ Fintype.card ι - 1 := by
    intro i
    have hb := lagrangeBasis_natDegree_lt_card τ i
    have hmul := Polynomial.natDegree_C_mul_le (p.eval (τ i)) (lagrangeBasis τ i)
    omega
  have hSdeg_le : S.natDegree ≤ Fintype.card ι - 1 := by
    dsimp [S]
    simpa using Polynomial.natDegree_sum_le_of_forall_le Finset.univ
      (fun i : ι => Polynomial.C (p.eval (τ i)) * lagrangeBasis τ i)
      (by intro i hi; exact hterm_deg i)
  have hSdeg : S.natDegree < Fintype.card ι := by omega
  have h_eval_S : ∀ j : ι, S.eval (τ j) = p.eval (τ j) := by
    intro j
    dsimp [S]
    rw [Polynomial.eval_finset_sum]
    trans (Polynomial.C (p.eval (τ j)) * lagrangeBasis τ j).eval (τ j)
    · apply Finset.sum_eq_single j
      · intro i hi hij
        rw [Polynomial.eval_mul, lagrangeBasis_eval_ne hτ hij, mul_zero]
      · intro hj
        exact False.elim (hj (Finset.mem_univ j))
    · rw [Polynomial.eval_mul, Polynomial.eval_C, lagrangeBasis_eval_self hτ, mul_one]
  by_contra hp_ne
  have hsub_ne : p - S ≠ 0 := sub_ne_zero.mpr hp_ne
  have hsub_deg : (p - S).natDegree < Fintype.card ι := by
    calc (p - S).natDegree ≤ max p.natDegree S.natDegree := Polynomial.natDegree_sub_le _ _
      _ < Fintype.card ι := max_lt hpdeg hSdeg
  have hroots_mem : ∀ i : ι, τ i ∈ (p - S).roots := by
    intro i
    rw [Polynomial.mem_roots hsub_ne]
    change (p - S).eval (τ i) = 0
    rw [Polynomial.eval_sub, h_eval_S i, sub_self]
  have hcard_lower : Fintype.card ι ≤ (p - S).roots.card := by
    have hcard := Finset.card_le_card
      (Finset.image_subset_iff.mpr (fun i _ => Multiset.mem_toFinset.mpr (hroots_mem i)) :
        Finset.image τ Finset.univ ⊆ (p - S).roots.toFinset)
    rw [Finset.card_image_of_injective _ hτ, Finset.card_univ] at hcard
    exact le_trans hcard (Multiset.toFinset_card_le (p - S).roots)
  have hcard_upper := Polynomial.card_roots' (p - S)
  omega

theorem distinctNodes_of_strictMono {ι : Type*} [LinearOrder ι] {τ : ι → ℝ}
    (hτ : StrictMono τ) : DistinctNodes τ :=
  hτ.injective

theorem natDegree_lt_card_fin_succ_of_le {n : ℕ} {p : Polynomial ℝ}
    (hpdeg : p.natDegree ≤ n) : p.natDegree < Fintype.card (Fin (n + 1)) := by
  simp [Fintype.card_fin]
  omega

theorem derivative_lagrange_interpolation_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ : ι → ℝ} (hτ : DistinctNodes τ)
    (p : Polynomial ℝ) (hpdeg : p.natDegree < Fintype.card ι) :
    Polynomial.derivative p =
      Finset.univ.sum (fun i : ι =>
        Polynomial.C (p.eval (τ i)) * Polynomial.derivative (lagrangeBasis τ i)) := by
  conv_lhs => rw [lagrange_interpolation_eq hτ p hpdeg]
  rw [Polynomial.derivative_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add]

theorem derivative_eval_lagrange_interpolation_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ : ι → ℝ} (hτ : DistinctNodes τ)
    (p : Polynomial ℝ) (hpdeg : p.natDegree < Fintype.card ι) (x : ℝ) :
    (Polynomial.derivative p).eval x =
      Finset.univ.sum (fun i : ι =>
        p.eval (τ i) * (Polynomial.derivative (lagrangeBasis τ i)).eval x) := by
  rw [derivative_lagrange_interpolation_eq hτ p hpdeg]
  rw [Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Polynomial.eval_mul]

theorem abs_sum_mul_le_abs_sum_mul_of_abs_le_of_nonneg_terms
    {ι : Type*} (s : Finset ι) (p q w : ι → ℝ)
    (habs : ∀ i ∈ s, |p i| ≤ |q i|)
    (hterms : ∀ i ∈ s, 0 ≤ q i * w i) :
    |s.sum (fun i => p i * w i)| ≤ |s.sum (fun i => q i * w i)| := by
  calc |s.sum (fun i => p i * w i)|
      ≤ s.sum (fun i => |p i * w i|) := Finset.abs_sum_le_sum_abs _ _
    _ ≤ s.sum (fun i => |q i * w i|) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right (habs i hi) (abs_nonneg (w i))
    _ = s.sum (fun i => q i * w i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact abs_of_nonneg (hterms i hi)
    _ = |s.sum (fun i => q i * w i)| := by
        rw [abs_of_nonneg]
        exact Finset.sum_nonneg hterms

theorem abs_sum_mul_le_abs_sum_mul_of_abs_le_of_nonpos_terms
    {ι : Type*} (s : Finset ι) (p q w : ι → ℝ)
    (habs : ∀ i ∈ s, |p i| ≤ |q i|)
    (hterms : ∀ i ∈ s, q i * w i ≤ 0) :
    |s.sum (fun i => p i * w i)| ≤ |s.sum (fun i => q i * w i)| := by
  calc |s.sum (fun i => p i * w i)|
      ≤ s.sum (fun i => |p i * w i|) := Finset.abs_sum_le_sum_abs _ _
    _ ≤ s.sum (fun i => |q i * w i|) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right (habs i hi) (abs_nonneg (w i))
    _ = s.sum (fun i => -(q i * w i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact abs_of_nonpos (hterms i hi)
    _ = -(s.sum (fun i => q i * w i)) := by simp [Finset.sum_neg_distrib]
    _ = |s.sum (fun i => q i * w i)| := by
        rw [abs_of_nonpos]
        exact Finset.sum_nonpos hterms

theorem derivative_eval_le_of_lagrange_common_nonneg
    {n : ℕ} (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ) (hτ_strict : StrictMono τ)
    (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree = n)
    (hp_nodes : ∀ i : Fin (n + 1), |p.eval (τ i)| ≤ |q.eval (τ i)|)
    (x : ℝ)
    (hterms : ∀ i : Fin (n + 1),
      0 ≤ q.eval (τ i) * (Polynomial.derivative (lagrangeBasis τ i)).eval x) :
    |(Polynomial.derivative p).eval x| ≤ |(Polynomial.derivative q).eval x| := by
  have hτ_nodes : DistinctNodes τ := distinctNodes_of_strictMono hτ_strict
  have hpdeg_lt : p.natDegree < Fintype.card (Fin (n + 1)) :=
    natDegree_lt_card_fin_succ_of_le hpdeg
  have hqdeg_lt : q.natDegree < Fintype.card (Fin (n + 1)) := by
    rw [hqdeg]
    simp [Fintype.card_fin]
  rw [derivative_eval_lagrange_interpolation_eq hτ_nodes p hpdeg_lt x,
    derivative_eval_lagrange_interpolation_eq hτ_nodes q hqdeg_lt x]
  exact abs_sum_mul_le_abs_sum_mul_of_abs_le_of_nonneg_terms Finset.univ
    (fun i : Fin (n + 1) => p.eval (τ i))
    (fun i : Fin (n + 1) => q.eval (τ i))
    (fun i : Fin (n + 1) => (Polynomial.derivative (lagrangeBasis τ i)).eval x)
    (by intro i _; exact hp_nodes i)
    (by intro i _; exact hterms i)

theorem derivative_eval_le_of_lagrange_common_nonpos
    {n : ℕ} (p q : Polynomial ℝ) (τ : Fin (n + 1) → ℝ) (hτ_strict : StrictMono τ)
    (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree = n)
    (hp_nodes : ∀ i : Fin (n + 1), |p.eval (τ i)| ≤ |q.eval (τ i)|)
    (x : ℝ)
    (hterms : ∀ i : Fin (n + 1),
      q.eval (τ i) * (Polynomial.derivative (lagrangeBasis τ i)).eval x ≤ 0) :
    |(Polynomial.derivative p).eval x| ≤ |(Polynomial.derivative q).eval x| := by
  have hτ_nodes : DistinctNodes τ := distinctNodes_of_strictMono hτ_strict
  have hpdeg_lt : p.natDegree < Fintype.card (Fin (n + 1)) :=
    natDegree_lt_card_fin_succ_of_le hpdeg
  have hqdeg_lt : q.natDegree < Fintype.card (Fin (n + 1)) := by
    rw [hqdeg]
    simp [Fintype.card_fin]
  rw [derivative_eval_lagrange_interpolation_eq hτ_nodes p hpdeg_lt x,
    derivative_eval_lagrange_interpolation_eq hτ_nodes q hqdeg_lt x]
  exact abs_sum_mul_le_abs_sum_mul_of_abs_le_of_nonpos_terms Finset.univ
    (fun i : Fin (n + 1) => p.eval (τ i))
    (fun i : Fin (n + 1) => q.eval (τ i))
    (fun i : Fin (n + 1) => (Polynomial.derivative (lagrangeBasis τ i)).eval x)
    (by intro i _; exact hp_nodes i)
    (by intro i _; exact hterms i)

end OptimalConvergenceRates
