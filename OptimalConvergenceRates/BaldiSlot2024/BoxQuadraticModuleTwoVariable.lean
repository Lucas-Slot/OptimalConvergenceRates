/-
  OptimalConvergenceRates/BaldiSlot2024/BoxQuadraticModuleTwoVariable.lean

  Reusable two-variable box quadratic-module decomposition and corner estimates.
-/
import OptimalConvergenceRates.BasicNotions.SumsOfSquares
import OptimalConvergenceRates.ExamplePolynomials.BoxCorner
import OptimalConvergenceRates.Chebyshev.ChebyshevGrowth
import OptimalConvergenceRates.MarkovInequality.MarkovInequalityCorollaries
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

/-! ## Quadratic module decomposition for n = 2

If f_ε ∈ QM(B²)_r, then there exist SOS polynomials σ₀, σ₁, σ₂ with:
  f_ε = σ₀ + σ₁·(1-x²) + σ₂·(1-y²)
and degree bounds deg(σ₀) ≤ r, deg(σ_i · g_i) ≤ r.
-/

/-- Extract the QM decomposition for n = 2. -/
theorem box_qm_decomp_n2 (f : MvPolynomial (Fin 2) ℝ) (r : ℕ)
    (hf : f ∈ BoxQuadraticModule 2 r) :
    ∃ (σ₀ : MvPolynomial (Fin 2) ℝ) (σ₁ σ₂ : MvPolynomial (Fin 2) ℝ),
      IsSOS σ₀ ∧ IsSOS σ₁ ∧ IsSOS σ₂ ∧
      σ₀.totalDegree ≤ r ∧
      (σ₁ * BoxSemialgebraicGenerator 0).totalDegree ≤ r ∧
      (σ₂ * BoxSemialgebraicGenerator 1).totalDegree ≤ r ∧
      f = σ₀ + σ₁ * BoxSemialgebraicGenerator 0 + σ₂ * BoxSemialgebraicGenerator 1 := by
  obtain ⟨σ₀, σ, hsos₀, hsos, hdeg₀, hdeg, hsum⟩ := hf
  refine ⟨σ₀, σ 0, σ 1, hsos₀, hsos 0, hsos 1, hdeg₀, hdeg 0, hdeg 1, ?_⟩
  rw [hsum]
  simp only [Fin.sum_univ_two]
  ring

/-- Restrict a bivariate polynomial to y = b, yielding a univariate polynomial in x. -/
private noncomputable def restrictX1 (b : ℝ) (p : MvPolynomial (Fin 2) ℝ) : Polynomial ℝ :=
  MvPolynomial.aeval (fun i : Fin 2 => if i = 1 then Polynomial.C b else Polynomial.X) p

/-- Evaluating the y-restriction agrees with evaluating the bivariate polynomial. -/
private theorem restrictX1_eval (b : ℝ) (p : MvPolynomial (Fin 2) ℝ) (x : ℝ) :
    (restrictX1 b p).eval x = MvPolynomial.eval (![x, b]) p := by
  unfold restrictX1
  apply MvPolynomial.induction_on p
  · intro c; simp [MvPolynomial.eval_C]
  · intro p₁ p₂ ih₁ ih₂; simp only [map_add, Polynomial.eval_add]; rw [ih₁, ih₂]
  · intro p₁ i ih₁
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X,
      Polynomial.eval_mul]
    rw [ih₁]; congr 1
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The degree of σ₁ (from the QM decomposition) is bounded by r.
    Uses that deg(σ₁) ≤ deg(σ₁ · g₁) ≤ r since g₁ = 1 - x² has positive terms. -/
theorem sigma1_degree_bound (σ₁ : MvPolynomial (Fin 2) ℝ) (r : ℕ)
    (hdeg : (σ₁ * BoxSemialgebraicGenerator 0).totalDegree ≤ r) :
    σ₁.totalDegree ≤ r := by
  by_cases hσ : σ₁ = 0
  · simp [hσ]
  · have hg : (BoxSemialgebraicGenerator (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) ≠ 0 := by
      intro h
      have : MvPolynomial.eval 0 (BoxSemialgebraicGenerator (0 : Fin 2)) = 0 := by rw [h, map_zero]
      rw [BoxSemialgebraicGenerator_eval] at this
      simp at this
    have := MvPolynomial.totalDegree_mul_of_isDomain hσ hg
    linarith [this]

/-! ## Fact 1: σ₁(1,1) ≤ ε · r² / 2

From the QM decomposition f_ε = σ₀ + σ₁·g₁ + σ₂·g₂, evaluating at (1,1):
  ε = σ₀(1,1) + σ₁(1,1) · 0 + σ₂(1,1) · 0 = σ₀(1,1)
so σ₀(1,1) = ε.

Along the edge x = 1 (where g₁ = 0), the decomposition reduces to
  f_ε(1,y) = σ₀(1,y) + σ₂(1,y) · (1 - y²)
           = ε    (since f_ε(1,y) = 0 · (1-y²) + ε = ε)

This forces σ₂(1,y) · (1 - y²) = ε - σ₀(1,y) ≤ ε.
A Markov-type bound then gives σ₁(1,1) ≤ ε · r² / 2.
-/

/-- Fact 1 (Section 5, Fact 1):
    If f_ε ∈ QM(B²)_r with decomposition f_ε = σ₀ + σ₁·g₁ + σ₂·g₂,
    then σ₁(1,1) ≤ ε · r² / 2.

    The bound arises from the constraint that along the diagonal,
    g(t) = σ₁(1+t, 1-t) must satisfy g(0) = σ₁(1,1) but cannot
    grow too fast (by Markov's inequality for nonneg polynomials). -/
theorem fact1_sigma1_bound (ε : ℝ) (_hε : 0 < ε) (r : ℕ)
    (σ₀ σ₁ σ₂ : MvPolynomial (Fin 2) ℝ)
    (hsos₀ : IsSOS σ₀) (hsos₁ : IsSOS σ₁) (_hsos₂ : IsSOS σ₂)
    (_hdeg₀ : σ₀.totalDegree ≤ r)
    (hdeg₁ : (σ₁ * BoxSemialgebraicGenerator 0).totalDegree ≤ r)
    (_hdeg₂ : (σ₂ * BoxSemialgebraicGenerator 1).totalDegree ≤ r)
    (hdecomp : f_eps ε = σ₀ + σ₁ * BoxSemialgebraicGenerator 0
                            + σ₂ * BoxSemialgebraicGenerator 1) :
    MvPolynomial.eval corner_11 σ₁ ≤ ε * (r : ℝ) ^ 2 / 2 := by
  -- Restrict σ₁·g₁ to y=1: h(x) = p(x)·(1-x²) where p = σ₁(x,1).
  -- h'(1) = -2·σ₁(1,1). By Markov: |h'(1)| ≤ r²·‖h‖ ≤ r²·ε, so σ₁(1,1) ≤ ε·r²/2.
  have hσ₁_nn : 0 ≤ MvPolynomial.eval corner_11 σ₁ :=
    IsSOS_nonneg σ₁ hsos₁ corner_11 (Set.mem_univ _)
  -- Step 1: Define the univariate restrictions
  set p := restrictX1 1 σ₁ with hp_def
  set g₁_uni := restrictX1 1 (BoxSemialgebraicGenerator (0 : Fin 2)) with hg₁_uni_def
  set h := restrictX1 1 (σ₁ * BoxSemialgebraicGenerator (0 : Fin 2)) with hh_def
  -- Step 2: h = p * g₁_uni (since restrictX1 is an algebra hom)
  have hh_eq : h = p * g₁_uni := by
    simp only [hh_def, hp_def, hg₁_uni_def, restrictX1, map_mul]
  -- Step 3: g₁_uni = 1 - X² (since g₁ = 1 - X₀² and X₀ maps to X under restrictX1 1)
  have hg₁_eq : g₁_uni = 1 - Polynomial.X ^ 2 := by
    simp only [hg₁_uni_def, restrictX1, BoxSemialgebraicGenerator, map_sub, map_one, map_pow,
      MvPolynomial.aeval_X]
    simp [show (0 : Fin 2) ≠ 1 from by decide]
  -- Step 4: p(1) = σ₁(1,1) = eval corner_11 σ₁
  have hp_eval : p.eval 1 = MvPolynomial.eval corner_11 σ₁ := by
    rw [hp_def, restrictX1_eval]; congr 1
  -- Step 5: h(x) ≤ ε for x ∈ [-1,1] (from the edge evaluation at y=1)
  have hh_le_eps : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → |h.eval x| ≤ ε := by
    intro x hx1 hx2
    rw [hh_def, restrictX1_eval]
    -- h(x) = (σ₁·g₁)(x, 1) = eval ![x,1] (σ₁ * g₁)
    -- From the decomposition at (x, 1):
    -- f_ε(x,1) = σ₀(x,1) + σ₁(x,1)·g₁(x,1) + σ₂(x,1)·g₂(x,1)
    -- g₂(x,1) = 1 - 1² = 0, so:
    -- ε = σ₀(x,1) + (σ₁·g₁)(x,1)
    have hfx1 : MvPolynomial.eval (![x, 1]) (f_eps ε) = ε := by
      rw [f_eps_eval]; simp [Matrix.cons_val_one]
    have hdecomp_x1 : MvPolynomial.eval (![x, 1]) (f_eps ε) =
        MvPolynomial.eval (![x, 1]) σ₀ +
        MvPolynomial.eval (![x, 1]) (σ₁ * BoxSemialgebraicGenerator 0) +
        MvPolynomial.eval (![x, 1]) (σ₂ * BoxSemialgebraicGenerator 1) := by
      rw [hdecomp]; simp [map_add]
    have hg₂_van : MvPolynomial.eval (![x, 1]) (BoxSemialgebraicGenerator (1 : Fin 2)) = 0 := by
      rw [BoxSemialgebraicGenerator_eval]; simp [Matrix.cons_val_one]
    have hσ₂g₂_van : MvPolynomial.eval (![x, 1]) (σ₂ * BoxSemialgebraicGenerator 1) = 0 := by
      rw [MvPolynomial.eval_mul, hg₂_van, mul_zero]
    -- So ε = σ₀(x,1) + (σ₁·g₁)(x,1)
    have heq : ε = MvPolynomial.eval (![x, 1]) σ₀ +
        MvPolynomial.eval (![x, 1]) (σ₁ * BoxSemialgebraicGenerator 0) := by
      rw [← hfx1, hdecomp_x1, hσ₂g₂_van, add_zero]
    -- σ₀(x,1) ≥ 0
    have hσ₀_nn : 0 ≤ MvPolynomial.eval (![x, 1]) σ₀ :=
      IsSOS_nonneg σ₀ hsos₀ _ (Set.mem_univ _)
    -- (σ₁·g₁)(x,1) ≥ 0 (σ₁ ≥ 0 and g₁(x,1) = 1-x² ≥ 0 for x ∈ [-1,1])
    have hσ₁_nn_x : 0 ≤ MvPolynomial.eval (![x, 1]) σ₁ :=
      IsSOS_nonneg σ₁ hsos₁ _ (Set.mem_univ _)
    have hg₁_nn : 0 ≤ MvPolynomial.eval (![x, 1]) (BoxSemialgebraicGenerator (0 : Fin 2)) := by
      rw [BoxSemialgebraicGenerator_eval]; simp [Matrix.cons_val_zero]; nlinarith [sq_abs x]
    have hprod_nn : 0 ≤ MvPolynomial.eval (![x, 1]) (σ₁ * BoxSemialgebraicGenerator 0) := by
      rw [MvPolynomial.eval_mul]; exact mul_nonneg hσ₁_nn_x hg₁_nn
    -- Therefore 0 ≤ (σ₁·g₁)(x,1) ≤ ε
    have hprod_le : MvPolynomial.eval (![x, 1]) (σ₁ * BoxSemialgebraicGenerator 0) ≤ ε := by
      linarith
    rw [abs_of_nonneg hprod_nn]; exact hprod_le
  -- Step 6: polySupNormUni h ≤ ε
  have hh_sup : polySupNormUni h ≤ ε :=
    polySupNormUni_le_of_bound h ε hh_le_eps
  -- Step 7: natDegree h ≤ r
  have hh_deg : h.natDegree ≤ r := by
    rw [hh_def]
    -- restrictX1 maps each variable to degree ≤ 1, so natDegree ≤ totalDegree
    calc (restrictX1 1 (σ₁ * BoxSemialgebraicGenerator 0)).natDegree
        ≤ (σ₁ * BoxSemialgebraicGenerator 0).totalDegree := by
          unfold restrictX1
          set g := fun i : Fin 2 => if i = (1 : Fin 2) then Polynomial.C (1 : ℝ) else Polynomial.X
          -- Each g(i) has natDegree ≤ 1
          have hg_deg : ∀ i : Fin 2, (g i).natDegree ≤ 1 := by
            intro i; simp only [g]; fin_cases i <;>
              simp [Polynomial.natDegree_X]
          set f := σ₁ * BoxSemialgebraicGenerator 0
          conv_lhs => rw [f.as_sum]
          rw [map_sum]
          apply Polynomial.natDegree_sum_le_of_forall_le
          intro v hv
          rw [MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq]
          calc (Polynomial.C (MvPolynomial.coeff v f) *
                Finsupp.prod v fun i k => g i ^ k).natDegree
              ≤ (Finsupp.prod v fun i k => g i ^ k).natDegree :=
                Polynomial.natDegree_C_mul_le _ _
            _ ≤ ∑ i ∈ v.support, (g i ^ v i).natDegree :=
                Polynomial.natDegree_prod_le _ _
            _ ≤ ∑ i ∈ v.support, v i := by
                apply Finset.sum_le_sum; intro i _
                calc (g i ^ v i).natDegree ≤ v i * (g i).natDegree :=
                      Polynomial.natDegree_pow_le
                  _ ≤ v i * 1 := Nat.mul_le_mul_left _ (hg_deg i)
                  _ = v i := Nat.mul_one _
            _ = v.sum (fun _ e => e) := by simp [Finsupp.sum]
            _ ≤ f.totalDegree := Finset.le_sup (f := fun s => s.sum fun _ e => e) hv
      _ ≤ r := hdeg₁
  -- Step 8: h' at x=1 equals -2·σ₁(1,1)
  -- h = p * (1 - X²), so h' = p' * (1 - X²) + p * derivative(1 - X²)
  -- derivative(1 - X²) = -2X
  -- h'(1) = p'(1) * 0 + p(1) * (-2) = -2 * σ₁(1,1)
  have hderiv_eq : (Polynomial.derivative h).eval 1 = -2 * MvPolynomial.eval corner_11 σ₁ := by
    rw [hh_eq, Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_mul, hg₁_eq]
    -- (1 - X²) at 1 = 0
    have hg_at_1 : (1 - Polynomial.X ^ 2 : Polynomial ℝ).eval 1 = 0 := by
      simp
    rw [hg_at_1, mul_zero, zero_add]
    -- derivative(1 - X²) evaluated at 1 = -2
    have hd_eval : (Polynomial.derivative (1 - Polynomial.X ^ 2 : Polynomial ℝ)).eval 1 = -2 := by
      simp [Polynomial.derivative_sub, Polynomial.derivative_one,
        Polynomial.derivative_pow, Polynomial.derivative_X,
        Polynomial.eval_mul]
    rw [hd_eval, hp_eval]; ring
  -- Step 9: Apply univariate Markov at x=1
  have hmarkov := univariate_markov_first_derivative_inside h r hh_deg 1
    (by norm_num : |(1 : ℝ)| ≤ 1)
  -- |h'(1)| = |-2·σ₁(1,1)| = 2·σ₁(1,1) (since σ₁(1,1) ≥ 0)
  rw [hderiv_eq] at hmarkov
  have habs_eq : |-2 * MvPolynomial.eval corner_11 σ₁| =
      2 * MvPolynomial.eval corner_11 σ₁ := by
    rw [abs_mul, show |(-2 : ℝ)| = 2 from by norm_num, abs_of_nonneg hσ₁_nn]
  rw [habs_eq] at hmarkov
  -- From Markov: 2·σ₁(1,1) ≤ r²·polySupNormUni(h) ≤ r²·ε
  have h_bound : 2 * MvPolynomial.eval corner_11 σ₁ ≤ (r : ℝ) ^ 2 * ε := by
    calc 2 * MvPolynomial.eval corner_11 σ₁
        ≤ ↑r ^ 2 * polySupNormUni h := hmarkov
      _ ≤ ↑r ^ 2 * ε := mul_le_mul_of_nonneg_left hh_sup (sq_nonneg _)
  -- Conclude: σ₁(1,1) ≤ ε·r²/2
  linarith


end OptimalConvergenceRates

end
