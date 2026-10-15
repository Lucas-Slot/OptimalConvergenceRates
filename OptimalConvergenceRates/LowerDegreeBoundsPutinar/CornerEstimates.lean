/-
  OptimalConvergenceRates/LowerDegreeBoundsPutinar/CornerEstimates.lean

  Corner and outside-point estimates driving the improved Putinar lower-bound proof.
-/
import OptimalConvergenceRates.LowerDegreeBoundsPutinar.Defs
import OptimalConvergenceRates.MarkovInequality.ChebyshevEndpoint
import OptimalConvergenceRates.BaldiSlot2024.BoxQuadraticModuleTwoVariable

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

/-- Lower bound at the outside point `(1+a, 1-b)` under the quantitative
assumptions `b ≤ 1/2` and `ε / a ≤ b`. -/
theorem outside_point_sigma1_lower_bound
    (ε a b : ℝ) (ha : 0 < a) (hb0 : 0 ≤ b) (hbhalf : b ≤ 1 / 2)
    (hεa : ε / a ≤ b)
    (σ₀ σ₁ σ₂ : MvPolynomial (Fin 2) ℝ)
    (hsos₀ : IsSOS σ₀) (_hsos₁ : IsSOS σ₁) (hsos₂ : IsSOS σ₂)
    (hdecomp : f_eps ε = σ₀ + σ₁ * BoxSemialgebraicGenerator 0
                            + σ₂ * BoxSemialgebraicGenerator 1) :
    b ≤ MvPolynomial.eval (outsideCornerPoint a b) σ₁ := by
  set z := outsideCornerPoint a b
  set A := 2 * a + a ^ 2
  set B := 2 * b - b ^ 2
  have hz := congr_arg (MvPolynomial.eval z) hdecomp
  simp only [map_add, MvPolynomial.eval_mul] at hz
  have hg0 : MvPolynomial.eval z (BoxSemialgebraicGenerator (0 : Fin 2)) = -A := by
    rw [gen0_outsideCornerPoint]
  have hg1 : MvPolynomial.eval z (BoxSemialgebraicGenerator (1 : Fin 2)) = B := by
    rw [gen1_outsideCornerPoint]
  have hf : MvPolynomial.eval z (f_eps ε) = -A * B + ε := by
    rw [f_eps_outsideCornerPoint]
  have hσ0 : 0 ≤ MvPolynomial.eval z σ₀ :=
    IsSOS_nonneg σ₀ hsos₀ z (Set.mem_univ _)
  have hσ2 : 0 ≤ MvPolynomial.eval z σ₂ :=
    IsSOS_nonneg σ₂ hsos₂ z (Set.mem_univ _)
  have hB_nonneg : 0 ≤ B := by
    nlinarith [hb0, hbhalf]
  rw [hf, hg0, hg1] at hz
  have hmain : MvPolynomial.eval z σ₁ * (-A) ≤ -A * B + ε := by
    nlinarith [mul_nonneg hσ2 hB_nonneg]
  have hA_pos : 0 < A := by
    nlinarith [ha]
  have hB_lower : b + b / 2 ≤ B := by
    nlinarith [hb0, hbhalf]
  have h_eps_A : ε / A ≤ b / 2 := by
    have hA_ge : 2 * a ≤ A := by
      nlinarith [sq_nonneg a]
    have hε_le_ab : ε ≤ a * b := by
      rw [div_le_iff₀ ha] at hεa
      nlinarith
    rw [div_le_iff₀ hA_pos]
    nlinarith
  have hσ_ge : B - ε / A ≤ MvPolynomial.eval z σ₁ := by
    have h1 : A * B - ε ≤ A * MvPolynomial.eval z σ₁ := by
      nlinarith
    have hmul : A * (B - ε / A) ≤ A * MvPolynomial.eval z σ₁ := by
      nlinarith [div_mul_cancel₀ ε (ne_of_gt hA_pos)]
    nlinarith [hmul, hA_pos]
  have : b ≤ B - ε / A := by
    linarith
  exact le_trans this hσ_ge

/-! ## Upper estimate at the outside point -/
/-! ## Polynomial restrictions for the SOS square-root vector -/

private noncomputable def verticalRestriction (p : MvPolynomial (Fin 2) ℝ) : Polynomial ℝ :=
  MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then Polynomial.C 1 else 1 - Polynomial.X) p

private noncomputable def verticalDifference (p : MvPolynomial (Fin 2) ℝ) : Polynomial ℝ :=
  verticalRestriction p - Polynomial.C (MvPolynomial.eval corner_11 p)

private noncomputable def horizontalRestriction (b : ℝ) (p : MvPolynomial (Fin 2) ℝ) :
    Polynomial ℝ :=
  MvPolynomial.aeval (fun i : Fin 2 => if i = 1 then Polynomial.C (1 - b) else Polynomial.X) p

private theorem verticalRestriction_eval (p : MvPolynomial (Fin 2) ℝ) (t : ℝ) :
    (verticalRestriction p).eval t = MvPolynomial.eval (outsideCornerPoint 0 t) p := by
  unfold verticalRestriction
  apply MvPolynomial.induction_on p
  · intro c
    simp [MvPolynomial.eval_C]
  · intro p q hp hq
    simp only [map_add, Polynomial.eval_add]
    rw [hp, hq]
  · intro p i hp
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X, Polynomial.eval_mul]
    rw [hp]
    congr 1
    fin_cases i <;> simp [outsideCornerPoint, Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem verticalDifference_eval (p : MvPolynomial (Fin 2) ℝ) (t : ℝ) :
    (verticalDifference p).eval t =
      MvPolynomial.eval (outsideCornerPoint 0 t) p - MvPolynomial.eval corner_11 p := by
  simp [verticalDifference, verticalRestriction_eval]

private theorem outsideCornerPoint_zero_zero :
    outsideCornerPoint 0 0 = corner_11 := by
  ext i
  fin_cases i <;> simp [outsideCornerPoint, corner_11, Matrix.cons_val_zero,
    Matrix.cons_val_one]

private theorem verticalDifference_eval_zero (p : MvPolynomial (Fin 2) ℝ) :
    (verticalDifference p).eval 0 = 0 := by
  rw [verticalDifference_eval]
  rw [outsideCornerPoint_zero_zero]
  ring

private theorem horizontalRestriction_eval (b : ℝ) (p : MvPolynomial (Fin 2) ℝ) (x : ℝ) :
    (horizontalRestriction b p).eval x = MvPolynomial.eval (![x, 1 - b]) p := by
  unfold horizontalRestriction
  apply MvPolynomial.induction_on p
  · intro c
    simp [MvPolynomial.eval_C]
  · intro p q hp hq
    simp only [map_add, Polynomial.eval_add]
    rw [hp, hq]
  · intro p i hp
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X, Polynomial.eval_mul]
    rw [hp]
    congr 1
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem aeval_natDegree_le_totalDegree
    (p : MvPolynomial (Fin 2) ℝ) (g : Fin 2 → Polynomial ℝ)
    (hg : ∀ i : Fin 2, (g i).natDegree ≤ 1) :
    (MvPolynomial.aeval g p).natDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro v hv
  rw [MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq]
  calc (Polynomial.C (legacyMvCoeff v p) * Finsupp.prod v fun i k => g i ^ k).natDegree
      ≤ (Finsupp.prod v fun i k => g i ^ k).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
    _ ≤ ∑ i ∈ v.support, (g i ^ v i).natDegree :=
        Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i ∈ v.support, v i := by
        apply Finset.sum_le_sum
        intro i _
        calc (g i ^ v i).natDegree ≤ v i * (g i).natDegree :=
              Polynomial.natDegree_pow_le
          _ ≤ v i * 1 := Nat.mul_le_mul_left _ (hg i)
          _ = v i := Nat.mul_one _
    _ = v.sum (fun _ e => e) := by simp [Finsupp.sum]
    _ ≤ p.totalDegree := Finset.le_sup (f := fun s => s.sum fun _ e => e) hv

private theorem natDegree_one_sub_X : (1 - Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
  calc (1 - Polynomial.X : Polynomial ℝ).natDegree
      ≤ max (1 : Polynomial ℝ).natDegree (-Polynomial.X : Polynomial ℝ).natDegree := by
        simpa [sub_eq_add_neg] using Polynomial.natDegree_add_le (1 : Polynomial ℝ) (-Polynomial.X)
    _ ≤ 1 := by
        apply max_le
        · simp
        · rw [Polynomial.natDegree_neg]
          exact Polynomial.natDegree_X_le

private theorem verticalRestriction_natDegree_le_totalDegree (p : MvPolynomial (Fin 2) ℝ) :
    (verticalRestriction p).natDegree ≤ p.totalDegree := by
  unfold verticalRestriction
  apply aeval_natDegree_le_totalDegree
  intro i
  fin_cases i
  · simp
  · exact natDegree_one_sub_X

private theorem verticalDifference_natDegree_le_totalDegree (p : MvPolynomial (Fin 2) ℝ) :
    (verticalDifference p).natDegree ≤ p.totalDegree := by
  unfold verticalDifference
  calc (verticalRestriction p - Polynomial.C (MvPolynomial.eval corner_11 p)).natDegree
      ≤ max (verticalRestriction p).natDegree
          (-Polynomial.C (MvPolynomial.eval corner_11 p) : Polynomial ℝ).natDegree := by
        simpa [sub_eq_add_neg] using
          Polynomial.natDegree_add_le (verticalRestriction p)
            (-Polynomial.C (MvPolynomial.eval corner_11 p) : Polynomial ℝ)
    _ ≤ p.totalDegree := by
        apply max_le
        · exact verticalRestriction_natDegree_le_totalDegree p
        · rw [Polynomial.natDegree_neg]
          exact (Polynomial.natDegree_C _).le.trans (Nat.zero_le _)

private theorem horizontalRestriction_natDegree_le_totalDegree
    (b : ℝ) (p : MvPolynomial (Fin 2) ℝ) :
    (horizontalRestriction b p).natDegree ≤ p.totalDegree := by
  unfold horizontalRestriction
  apply aeval_natDegree_le_totalDegree
  intro i
  fin_cases i
  · exact Polynomial.natDegree_X_le
  · simp

private theorem epsilon_nonneg_of_decomp
    (ε : ℝ) (σ₀ σ₁ σ₂ : MvPolynomial (Fin 2) ℝ) (hsos₀ : IsSOS σ₀)
    (hdecomp : f_eps ε = σ₀ + σ₁ * BoxSemialgebraicGenerator 0
                            + σ₂ * BoxSemialgebraicGenerator 1) :
    0 ≤ ε := by
  have hz := congr_arg (MvPolynomial.eval corner_11) hdecomp
  simp only [map_add, MvPolynomial.eval_mul] at hz
  rw [f_eps_eval_corner] at hz
  have hg0 : MvPolynomial.eval corner_11 (BoxSemialgebraicGenerator (0 : Fin 2)) = 0 := by
    rw [BoxSemialgebraicGenerator_eval]
    simp [corner_11, Matrix.cons_val_zero]
  have hg1 : MvPolynomial.eval corner_11 (BoxSemialgebraicGenerator (1 : Fin 2)) = 0 := by
    rw [BoxSemialgebraicGenerator_eval]
    simp [corner_11, Matrix.cons_val_one]
  rw [hg0, hg1, mul_zero, mul_zero, add_zero, add_zero] at hz
  rw [hz]
  exact IsSOS_nonneg σ₀ hsos₀ corner_11 (Set.mem_univ _)

private theorem corner_vecNorm_le
    (ε : ℝ) (hε_nonneg : 0 ≤ ε) (r : ℕ)
    (σ₁ : MvPolynomial (Fin 2) ℝ)
    (N : ℕ) (P : Fin N → MvPolynomial (Fin 2) ℝ)
    (hP : σ₁ = ∑ i : Fin N, (P i) ^ 2)
    (hcorner : MvPolynomial.eval corner_11 σ₁ ≤ ε * (r : ℝ) ^ 2 / 2) :
    vecNorm (fun i => MvPolynomial.eval corner_11 (P i)) ≤
      (1 / Real.sqrt 2) * (r : ℝ) * Real.sqrt ε := by
  have hB_nonneg : 0 ≤ (1 / Real.sqrt 2) * (r : ℝ) * Real.sqrt ε := by positivity
  apply vecNorm_le_of_vecSqNorm_le hB_nonneg
  rw [← sos_eval_eq_vecSqNorm σ₁ P hP corner_11]
  calc MvPolynomial.eval corner_11 σ₁
      ≤ ε * (r : ℝ) ^ 2 / 2 := hcorner
    _ = ((1 / Real.sqrt 2) * (r : ℝ) * Real.sqrt ε) ^ 2 := by
        have hsqrt2_sq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
          rw [Real.sq_sqrt]
          norm_num
        rw [mul_pow, mul_pow, div_pow, one_pow, Real.sq_sqrt hε_nonneg, hsqrt2_sq]
        ring

private theorem f_eps_totalDegree_ge_four (ε : ℝ) : 4 ≤ (f_eps ε).totalDegree := by
  let s0 : Fin 2 →₀ ℕ := Finsupp.single (0 : Fin 2) 2
  let s1 : Fin 2 →₀ ℕ := Finsupp.single (1 : Fin 2) 2
  let s : Fin 2 →₀ ℕ := s0 + s1
  have hs_sum : s.sum (fun _ e => e) = 4 := by
    simp [s, s0, s1, Finsupp.sum_add_index]
  have hs_ne_zero : s ≠ 0 := by
    intro h
    have : s (0 : Fin 2) = 0 := by simp [h]
    simp [s, s0, s1] at this
  have hzero_ne_s : (0 : Fin 2 →₀ ℕ) ≠ s := fun h => hs_ne_zero h.symm
  rw [← hs_sum]
  apply MvPolynomial.le_totalDegree
  rw [MvPolynomial.mem_support_iff]
  have hcoeff : legacyMvCoeff s (f_eps ε) = 1 := by
    unfold f_eps
    rw [show (1 - (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2) * (1 - (X 1) ^ 2) + C ε =
        1 - (X 0)^2 - (X 1)^2 + (X 0)^2 * (X 1)^2 + C ε by ring]
    simp [s, s0, s1, hzero_ne_s, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul_monomial, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_sub,
      MvPolynomial.coeff_monomial, MvPolynomial.coeff_C, MvPolynomial.coeff_one]
  rw [hcoeff]
  norm_num

theorem two_le_of_bounded_decomp
    (ε : ℝ) (r : ℕ)
    (σ₀ σ₁ σ₂ : MvPolynomial (Fin 2) ℝ)
    (hdeg₀ : σ₀.totalDegree ≤ r)
    (hdeg₁ : (σ₁ * BoxSemialgebraicGenerator 0).totalDegree ≤ r)
    (hdeg₂ : (σ₂ * BoxSemialgebraicGenerator 1).totalDegree ≤ r)
    (hdecomp : f_eps ε = σ₀ + σ₁ * BoxSemialgebraicGenerator 0
                            + σ₂ * BoxSemialgebraicGenerator 1) :
    2 ≤ r := by
  have hf_le : (f_eps ε).totalDegree ≤ r := by
    rw [hdecomp]
    calc (σ₀ + σ₁ * BoxSemialgebraicGenerator 0 + σ₂ * BoxSemialgebraicGenerator 1).totalDegree
        ≤ max (σ₀ + σ₁ * BoxSemialgebraicGenerator 0).totalDegree
            (σ₂ * BoxSemialgebraicGenerator 1).totalDegree := MvPolynomial.totalDegree_add _ _
      _ ≤ max (max σ₀.totalDegree (σ₁ * BoxSemialgebraicGenerator 0).totalDegree)
            (σ₂ * BoxSemialgebraicGenerator 1).totalDegree := by
          exact max_le_max_right _ (MvPolynomial.totalDegree_add _ _)
      _ ≤ r := by
          exact max_le (max_le hdeg₀ hdeg₁) hdeg₂
  have h4 : 4 ≤ r := le_trans (f_eps_totalDegree_ge_four ε) hf_le
  omega

private theorem vector_markov_increment_from_sup
    {N : ℕ} (H : Fin N → Polynomial ℝ) (d : ℕ)
    (hdeg : ∀ i, (H i).natDegree ≤ d)
    (a M : ℝ) (ha : 0 < a) (_hM : 0 ≤ M)
    (hsup : ∀ x : ℝ, -1 ≤ x → x ≤ 1 + a → vecNorm (fun i => (H i).eval x) ≤ M) :
    vecNorm (fun i => (H i).eval (1 + a) - (H i).eval 1) ≤
      (2 * (d : ℝ) ^ 2 / (2 + a)) * M * a := by
  let D : Fin N → ℝ := fun i => (H i).eval (1 + a) - (H i).eval 1
  by_cases hD_zero : vecNorm D = 0
  · change vecNorm D ≤ _
    rw [hD_zero]
    positivity
  · let e : Fin N → ℝ := fun i => D i / vecNorm D
    let h : Polynomial ℝ := ∑ i : Fin N, Polynomial.C (e i) * H i
    have hdeg_h : h.natDegree ≤ d := by
      dsimp [h]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i _
      exact (Polynomial.natDegree_C_mul_le (e i) (H i)).trans (hdeg i)
    have hsup_h : ∀ x : ℝ, -1 ≤ x → x ≤ 1 + a → |h.eval x| ≤ M := by
      intro x hx1 hx2
      have hdot : h.eval x = vecDot e (fun i => (H i).eval x) := by
        dsimp [h]
        unfold vecDot
        change ((Finset.univ : Finset (Fin N)).sum (fun i => Polynomial.C (e i) * H i)).eval x =
          ∑ i : Fin N, e i * (H i).eval x
        rw [Polynomial.eval_finsetSum]
        simp only [Polynomial.eval_mul, Polynomial.eval_C]
      rw [hdot]
      exact (abs_vecDot_unit_le hD_zero (fun i => (H i).eval x)).trans (hsup x hx1 hx2)
    have hdiff_h : h.eval (1 + a) - h.eval 1 = vecNorm D := by
      have hdot1 : h.eval (1 + a) - h.eval 1 = vecDot e D := by
        dsimp [h, D]
        unfold vecDot
        change
            ((Finset.univ : Finset (Fin N)).sum
                (fun i => Polynomial.C (e i) * H i)).eval (1 + a) -
            ((Finset.univ : Finset (Fin N)).sum (fun i => Polynomial.C (e i) * H i)).eval 1 =
          ∑ i : Fin N, e i * ((H i).eval (1 + a) - (H i).eval 1)
        rw [Polynomial.eval_finsetSum, Polynomial.eval_finsetSum, ← Finset.sum_sub_distrib]
        simp only [Polynomial.eval_mul, Polynomial.eval_C]
        congr 1
        ext i
        ring
      rw [hdot1]
      exact vecDot_unit_self hD_zero
    set left : ℝ := -1
    set right : ℝ := 1 + a
    set width : ℝ := right - left
    set mid : ℝ := (left + right) / 2
    set scale : ℝ := width / 2
    have hscale_pos : 0 < scale := by dsimp [scale, width, left, right]; linarith
    set q : Polynomial ℝ := h.comp (Polynomial.C mid + Polynomial.C scale * Polynomial.X)
    have hqdeg : q.natDegree ≤ d := by
      have hlin_deg :
          (Polynomial.C mid + Polynomial.C scale * Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
        calc (Polynomial.C mid + Polynomial.C scale * Polynomial.X : Polynomial ℝ).natDegree
            ≤ max (Polynomial.C mid).natDegree (Polynomial.C scale * Polynomial.X).natDegree :=
              Polynomial.natDegree_add_le _ _
          _ ≤ max 0 1 := by
              apply max_le_max
              · exact (Polynomial.natDegree_C _).le
              · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
          _ = 1 := by simp
      calc q.natDegree
          ≤ h.natDegree *
              (Polynomial.C mid + Polynomial.C scale * Polynomial.X : Polynomial ℝ).natDegree :=
            Polynomial.natDegree_comp_le
        _ ≤ h.natDegree * 1 := Nat.mul_le_mul_left _ hlin_deg
        _ = h.natDegree := Nat.mul_one _
        _ ≤ d := hdeg_h
    have hq_sup : polySupNormUni q ≤ M := by
      apply polySupNormUni_le_of_bound
      intro y hy1 hy2
      dsimp [q]
      rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      simp only [Polynomial.eval_C]
      change |h.eval (mid + scale * y)| ≤ M
      apply hsup_h
      · dsimp [mid, scale, width, left, right]
        nlinarith [ha, hy1, hy2]
      · dsimp [mid, scale, width, left, right]
        nlinarith [ha, hy1, hy2]
    let g : Polynomial ℝ := h.comp (Polynomial.X + Polynomial.C 1)
    obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope
      (fun x => g.eval x) (fun x => (Polynomial.derivative g).eval x) ha
      g.continuous.continuousOn
      (fun x _ => g.hasDerivAt x)
    have hc_interval : c ∈ Set.Icc 0 a := Set.Ioo_subset_Icc_self hc_mem
    set x₀ : ℝ := 1 + c
    set y : ℝ := (x₀ - mid) / scale
    have hx₀_mem : -1 ≤ x₀ ∧ x₀ ≤ 1 + a := by
      dsimp [x₀]
      exact ⟨by linarith [hc_interval.1], by linarith [hc_interval.2]⟩
    have hy_abs : |y| ≤ 1 := by
      rw [abs_le]
      constructor
      · change -1 ≤ (x₀ - mid) / scale
        rw [le_div_iff₀ hscale_pos]
        dsimp [mid, scale, width, left, right]
        nlinarith [ha, hx₀_mem.1]
      · change (x₀ - mid) / scale ≤ 1
        rw [div_le_iff₀ hscale_pos]
        dsimp [mid, scale, width, left, right]
        nlinarith [ha, hx₀_mem.2]
    have hq_deriv_at :
        (Polynomial.derivative q).eval y = scale * (Polynomial.derivative h).eval x₀ := by
      dsimp [q]
      rw [Polynomial.derivative_comp]
      simp only [Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
        zero_mul, Polynomial.derivative_X, mul_one, zero_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
        mul_eq_mul_left_iff]
      have hy_eq : mid + scale * y = x₀ := by
        change mid + scale * ((x₀ - mid) / scale) = x₀
        rw [mul_div_cancel₀ _ hscale_pos.ne']
        ring_nf
      rw [hy_eq]
      ring_nf
      all_goals simp [hscale_pos.ne']
    have hg_deriv_at :
        (Polynomial.derivative g).eval c = (Polynomial.derivative h).eval x₀ := by
      dsimp [g, x₀]
      rw [Polynomial.derivative_comp]
      simp [Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.eval_comp,
        Polynomial.eval_add, Polynomial.eval_X]
      ring_nf
    have hmarkov := univariate_markov_first_derivative_inside q d hqdeg y hy_abs
    have hderiv_bound : |(Polynomial.derivative h).eval x₀| ≤ (d : ℝ) ^ 2 * M / scale := by
      rw [hq_deriv_at, abs_mul, abs_of_pos hscale_pos] at hmarkov
      have hstep : |(Polynomial.derivative h).eval x₀| * scale ≤ (d : ℝ) ^ 2 * M := by
        calc |(Polynomial.derivative h).eval x₀| * scale
            = scale * |(Polynomial.derivative h).eval x₀| := by ring
          _ ≤ (d : ℝ) ^ 2 * polySupNormUni q := by simpa using hmarkov
          _ ≤ (d : ℝ) ^ 2 * M := mul_le_mul_of_nonneg_left hq_sup (by positivity)
      rw [le_div_iff₀ hscale_pos]
      exact hstep
    have hslope : h.eval (1 + a) - h.eval 1 = (Polynomial.derivative h).eval x₀ * a := by
      have := hc_eq
      rw [hg_deriv_at] at this
      dsimp [g] at this
      simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C] at this
      rw [this]
      field_simp [ha.ne']
      ring_nf
    calc vecNorm (fun i => (H i).eval (1 + a) - (H i).eval 1)
        = vecNorm D := rfl
      _ = h.eval (1 + a) - h.eval 1 := by rw [hdiff_h]
      _ = (Polynomial.derivative h).eval x₀ * a := hslope
      _ ≤ |(Polynomial.derivative h).eval x₀| * a := by
          exact mul_le_mul_of_nonneg_right (le_abs_self _) ha.le
      _ ≤ ((d : ℝ) ^ 2 * M / scale) * a :=
          mul_le_mul_of_nonneg_right hderiv_bound ha.le
      _ = (2 * (d : ℝ) ^ 2 / (2 + a)) * M * a := by
          have h2a : 2 + a ≠ 0 := by linarith
          dsimp [scale, width, left, right]
          rw [show (1 + a - -1) / 2 = (2 + a) / 2 by ring]
          field_simp [h2a]

private theorem verticalEndpointConst_absorbs :
    Real.exp 6 * (Real.sqrt (3 * Real.exp 6) + 1) ≤ verticalEndpointConst := by
  unfold verticalEndpointConst
  have hexp6_pos : 0 < Real.exp 6 := Real.exp_pos 6
  have hexp12_pos : 0 < Real.exp 12 := Real.exp_pos 12
  have hone : (1 : ℝ) ≤ Real.exp 6 := by
    calc (1 : ℝ) ≤ Real.exp 0 := by simp
      _ ≤ Real.exp 6 := Real.exp_le_exp.mpr (by norm_num)
  have hsqrt_le : Real.sqrt (3 * Real.exp 6) ≤ 3 * Real.exp 6 := by
    calc Real.sqrt (3 * Real.exp 6) ≤ Real.sqrt ((3 * Real.exp 6) ^ 2) := by
          apply Real.sqrt_le_sqrt
          nlinarith [hexp6_pos, hone]
      _ = 3 * Real.exp 6 := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
          positivity
  have hsum : Real.sqrt (3 * Real.exp 6) + 1 ≤ 4 * Real.exp 6 := by
    linarith
  have hsq : (Real.exp 6) ^ 2 = Real.exp 12 := by
    rw [sq, ← Real.exp_add]
    norm_num
  calc Real.exp 6 * (Real.sqrt (3 * Real.exp 6) + 1)
      ≤ Real.exp 6 * (4 * Real.exp 6) := mul_le_mul_of_nonneg_left hsum hexp6_pos.le
    _ = 4 * (Real.exp 6) ^ 2 := by ring
    _ = 4 * Real.exp 12 := by rw [hsq]
    _ ≤ 100 * Real.exp 12 := by nlinarith [hexp12_pos]

private theorem chebyshev_argument_vertical_bound
    (r : ℕ) (hr2 : 2 ≤ r) (x : ℝ)
    (hx : |x| ≤ 1 + 1 / (r : ℝ) ^ 2) :
    |(|x| / Real.sqrt (1 - (r : ℝ) ^ (-2 : ℤ)))| ≤ 1 + 4 / (r : ℝ) ^ 2 := by
  have hr_pos : 0 < (r : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hr2)
  have hr_sq_pos : 0 < (r : ℝ) ^ 2 := sq_pos_of_pos hr_pos
  have hzpow_eq : (r : ℝ) ^ (-2 : ℤ) = 1 / (r : ℝ) ^ 2 := by
    rw [zpow_neg, one_div]
    rfl
  rw [hzpow_eq]
  set s : ℝ := 1 / (r : ℝ) ^ 2
  have hs_nonneg : 0 ≤ s := by dsimp [s]; positivity
  have hs_le_half : s ≤ 1 / 2 := by
    dsimp [s]
    rw [div_le_div_iff₀ hr_sq_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [show (2 : ℝ) ≤ r by exact_mod_cast hr2]
  have hs_le_one : s ≤ 1 := by linarith
  have hsqrt_pos : 0 < Real.sqrt (1 - s) := by
    apply Real.sqrt_pos.mpr
    linarith
  have hsqrt_ge : 1 - s ≤ Real.sqrt (1 - s) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg s]
  rw [abs_div, abs_of_nonneg (abs_nonneg x), abs_of_pos hsqrt_pos]
  rw [div_le_iff₀ hsqrt_pos]
  calc |x| ≤ 1 + s := by simpa [s] using hx
    _ ≤ (1 + 4 * s) * (1 - s) := by nlinarith [hs_nonneg, hs_le_half]
    _ ≤ (1 + 4 * s) * Real.sqrt (1 - s) := by
        apply mul_le_mul_of_nonneg_left hsqrt_ge
        nlinarith [hs_nonneg]
    _ = (1 + 4 / (r : ℝ) ^ 2) * Real.sqrt (1 - s) := by
        dsimp [s]
        ring

private theorem horizontal_scalar_core_bound
    (ε a b x : ℝ) (r : ℕ) (hr2 : 2 ≤ r)
    (ha0 : 0 < a) (hb0 : 0 ≤ b)
    (hxa : a ≤ 1 - x ^ 2)
    (σ₀ σ₁ σ₂ : MvPolynomial (Fin 2) ℝ)
    (hsos₀ : IsSOS σ₀) (_hsos₁ : IsSOS σ₁) (hsos₂ : IsSOS σ₂)
    (hdecomp : f_eps ε = σ₀ + σ₁ * BoxSemialgebraicGenerator 0
                            + σ₂ * BoxSemialgebraicGenerator 1)
    (hsmall : ε * (r : ℝ) ^ 4 ≤ improvedLowerBoundConst ^ 4)
    (ha_def : a = improvedLowerBoundConst / (r : ℝ) ^ 2)
    (hb_def : b = improvedLowerBoundConst / (r : ℝ) ^ 2) :
    MvPolynomial.eval (![x, 1 - b]) σ₁ ≤ 3 * b := by
  let z : Fin 2 → ℝ := ![x, 1 - b]
  have hr_pos : 0 < (r : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hr2)
  have hr_sq_pos : 0 < (r : ℝ) ^ 2 := sq_pos_of_pos hr_pos
  have hε_nonneg : 0 ≤ ε := epsilon_nonneg_of_decomp ε σ₀ σ₁ σ₂ hsos₀ hdecomp
  have hg0_pos : 0 < 1 - x ^ 2 := lt_of_lt_of_le ha0 hxa
  have hg1_nonneg : 0 ≤ MvPolynomial.eval z (BoxSemialgebraicGenerator (1 : Fin 2)) := by
    rw [BoxSemialgebraicGenerator_eval]
    have hy : 0 ≤ 1 - (1 - b) ^ 2 := by nlinarith [hb0, sq_nonneg b]
    simpa [z, Matrix.cons_val_one] using hy
  have hσ0_nonneg : 0 ≤ MvPolynomial.eval z σ₀ :=
    IsSOS_nonneg σ₀ hsos₀ z (Set.mem_univ _)
  have hσ2_nonneg : 0 ≤ MvPolynomial.eval z σ₂ :=
    IsSOS_nonneg σ₂ hsos₂ z (Set.mem_univ _)
  have hσ2g_nonneg : 0 ≤ MvPolynomial.eval z (σ₂ * BoxSemialgebraicGenerator 1) := by
    rw [MvPolynomial.eval_mul]
    exact mul_nonneg hσ2_nonneg hg1_nonneg
  have hzdecomp := congr_arg (MvPolynomial.eval z) hdecomp
  simp only [map_add, MvPolynomial.eval_mul] at hzdecomp
  have hf : MvPolynomial.eval z (f_eps ε) =
      (1 - x ^ 2) * (1 - (1 - b) ^ 2) + ε := by
    rw [f_eps_eval]
    simp [z, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hg0 : MvPolynomial.eval z (BoxSemialgebraicGenerator (0 : Fin 2)) = 1 - x ^ 2 := by
    rw [BoxSemialgebraicGenerator_eval]
    simp [z, Matrix.cons_val_zero]
  have hmain : MvPolynomial.eval z σ₁ * (1 - x ^ 2) ≤
      (1 - x ^ 2) * (1 - (1 - b) ^ 2) + ε := by
    rw [hf, hg0] at hzdecomp
    nlinarith
  have hdiv : MvPolynomial.eval z σ₁ ≤
      (1 - (1 - b) ^ 2) + ε / (1 - x ^ 2) := by
    rw [show (1 - (1 - b) ^ 2) + ε / (1 - x ^ 2) =
        ((1 - x ^ 2) * (1 - (1 - b) ^ 2) + ε) / (1 - x ^ 2) by
      field_simp [hg0_pos.ne']]
    rw [le_div_iff₀ hg0_pos]
    exact hmain
  have hyterm : 1 - (1 - b) ^ 2 ≤ 2 * b := by nlinarith [sq_nonneg b]
  have heps_div : ε / (1 - x ^ 2) ≤ b := by
    have hε_le_ab : ε ≤ a * b := by
      rw [ha_def, hb_def]
      field_simp [hr_sq_pos.ne']
      calc ε * (r : ℝ) ^ 4
          ≤ improvedLowerBoundConst ^ 4 := hsmall
        _ ≤ improvedLowerBoundConst ^ 2 := by
            have hγ0 : 0 ≤ improvedLowerBoundConst := improvedLowerBoundConst_pos.le
            have hγ2_le_one : improvedLowerBoundConst ^ 2 ≤ 1 := by
              exact pow_le_one₀ hγ0 improvedLowerBoundConst_le_one
            calc improvedLowerBoundConst ^ 4
                = improvedLowerBoundConst ^ 2 * improvedLowerBoundConst ^ 2 := by ring
              _ ≤ improvedLowerBoundConst ^ 2 * 1 :=
                  mul_le_mul_of_nonneg_left hγ2_le_one (sq_nonneg _)
              _ = improvedLowerBoundConst ^ 2 := by ring
    have hab_le : a * b ≤ b * (1 - x ^ 2) := by
      calc a * b = b * a := by ring
        _ ≤ b * (1 - x ^ 2) := mul_le_mul_of_nonneg_left hxa hb0
    rw [div_le_iff₀ hg0_pos]
    exact le_trans hε_le_ab hab_le
  linarith

private theorem chebyshev_argument_horizontal_bound
    (r : ℕ) (hr2 : 2 ≤ r) (a x : ℝ)
    (ha0 : 0 ≤ a) (ha_le : a ≤ 1 / (r : ℝ) ^ 2)
    (hx : |x| ≤ 1 + 1 / (r : ℝ) ^ 2) :
    |(|x| / Real.sqrt (1 - a))| ≤ 1 + 4 / (r : ℝ) ^ 2 := by
  have hr_pos : 0 < (r : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hr2)
  have hr_sq_pos : 0 < (r : ℝ) ^ 2 := sq_pos_of_pos hr_pos
  set s : ℝ := 1 / (r : ℝ) ^ 2
  have hs_nonneg : 0 ≤ s := by dsimp [s]; positivity
  have hs_le_half : s ≤ 1 / 2 := by
    dsimp [s]
    rw [div_le_div_iff₀ hr_sq_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [show (2 : ℝ) ≤ r by exact_mod_cast hr2]
  have hsqrt_pos : 0 < Real.sqrt (1 - a) := by
    apply Real.sqrt_pos.mpr
    linarith [ha0, ha_le, hs_le_half]
  have h_one_sub_s_le : 1 - s ≤ 1 - a := by linarith [ha_le]
  have hsqrt_ge : 1 - a ≤ Real.sqrt (1 - a) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg a]
  rw [abs_div, abs_of_nonneg (abs_nonneg x), abs_of_pos hsqrt_pos]
  rw [div_le_iff₀ hsqrt_pos]
  calc |x| ≤ 1 + s := by simpa [s] using hx
    _ ≤ (1 + 4 * s) * (1 - s) := by nlinarith [hs_nonneg, hs_le_half]
    _ ≤ (1 + 4 * s) * (1 - a) := by
        apply mul_le_mul_of_nonneg_left h_one_sub_s_le
        nlinarith [hs_nonneg]
    _ ≤ (1 + 4 * s) * Real.sqrt (1 - a) := by
        apply mul_le_mul_of_nonneg_left hsqrt_ge
        nlinarith [hs_nonneg]
    _ = (1 + 4 / (r : ℝ) ^ 2) * Real.sqrt (1 - a) := by
        dsimp [s]
        ring

private theorem vertical_scalar_core_bound
    (ε t x : ℝ) (r : ℕ) (hr2 : 2 ≤ r)
    (htρ : (r : ℝ) ^ (-2 : ℤ) ≤ t) (ht1 : t ≤ 1)
    (hxρ : (r : ℝ) ^ (-2 : ℤ) ≤ 1 - x ^ 2)
    (σ₀ σ₁ σ₂ : MvPolynomial (Fin 2) ℝ)
    (hsos₀ : IsSOS σ₀) (_hsos₁ : IsSOS σ₁) (hsos₂ : IsSOS σ₂)
    (hdecomp : f_eps ε = σ₀ + σ₁ * BoxSemialgebraicGenerator 0
                            + σ₂ * BoxSemialgebraicGenerator 1)
    (hsmall : ε * (r : ℝ) ^ 4 ≤ improvedLowerBoundConst ^ 4) :
    MvPolynomial.eval (![x, 1 - t]) σ₁ ≤ 3 * t := by
  let z : Fin 2 → ℝ := ![x, 1 - t]
  have hr_pos : 0 < (r : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hr2)
  have hr_ne : (r : ℝ) ≠ 0 := ne_of_gt hr_pos
  have hr_sq_pos : 0 < (r : ℝ) ^ 2 := sq_pos_of_pos hr_pos
  have hzpow_eq : (r : ℝ) ^ (-2 : ℤ) = 1 / (r : ℝ) ^ 2 := by
    rw [zpow_neg, one_div]
    rfl
  have hρ_pos : 0 < (r : ℝ) ^ (-2 : ℤ) := by
    rw [hzpow_eq]
    positivity
  have ht0 : 0 ≤ t := (le_of_lt hρ_pos).trans htρ
  have hε_nonneg : 0 ≤ ε := epsilon_nonneg_of_decomp ε σ₀ σ₁ σ₂ hsos₀ hdecomp
  have hg0_pos : 0 < 1 - x ^ 2 := lt_of_lt_of_le hρ_pos hxρ
  have hg1_nonneg : 0 ≤ MvPolynomial.eval z (BoxSemialgebraicGenerator (1 : Fin 2)) := by
    rw [BoxSemialgebraicGenerator_eval]
    have hy : 0 ≤ 1 - (1 - t) ^ 2 := by nlinarith [ht0, ht1]
    simpa [z, Matrix.cons_val_one] using hy
  have hσ0_nonneg : 0 ≤ MvPolynomial.eval z σ₀ :=
    IsSOS_nonneg σ₀ hsos₀ z (Set.mem_univ _)
  have hσ2_nonneg : 0 ≤ MvPolynomial.eval z σ₂ :=
    IsSOS_nonneg σ₂ hsos₂ z (Set.mem_univ _)
  have hσ2g_nonneg : 0 ≤ MvPolynomial.eval z (σ₂ * BoxSemialgebraicGenerator 1) := by
    rw [MvPolynomial.eval_mul]
    exact mul_nonneg hσ2_nonneg hg1_nonneg
  have hzdecomp := congr_arg (MvPolynomial.eval z) hdecomp
  simp only [map_add, MvPolynomial.eval_mul] at hzdecomp
  have hf : MvPolynomial.eval z (f_eps ε) =
      (1 - x ^ 2) * (1 - (1 - t) ^ 2) + ε := by
    rw [f_eps_eval]
    simp [z, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hg0 : MvPolynomial.eval z (BoxSemialgebraicGenerator (0 : Fin 2)) = 1 - x ^ 2 := by
    rw [BoxSemialgebraicGenerator_eval]
    simp [z, Matrix.cons_val_zero]
  have hmain : MvPolynomial.eval z σ₁ * (1 - x ^ 2) ≤
      (1 - x ^ 2) * (1 - (1 - t) ^ 2) + ε := by
    rw [hf, hg0] at hzdecomp
    nlinarith
  have hdiv : MvPolynomial.eval z σ₁ ≤
      (1 - (1 - t) ^ 2) + ε / (1 - x ^ 2) := by
    rw [show (1 - (1 - t) ^ 2) + ε / (1 - x ^ 2) =
        ((1 - x ^ 2) * (1 - (1 - t) ^ 2) + ε) / (1 - x ^ 2) by
      field_simp [hg0_pos.ne']]
    rw [le_div_iff₀ hg0_pos]
    exact hmain
  have hyterm : 1 - (1 - t) ^ 2 ≤ 2 * t := by nlinarith [sq_nonneg t]
  have heps_div : ε / (1 - x ^ 2) ≤ t := by
    have hden_ge : 1 / (r : ℝ) ^ 2 ≤ 1 - x ^ 2 := by rwa [← hzpow_eq]
    have hγ4_le_one : improvedLowerBoundConst ^ 4 ≤ 1 := by
      have hγ0 : 0 ≤ improvedLowerBoundConst := improvedLowerBoundConst_pos.le
      exact (pow_le_pow_left₀ hγ0 improvedLowerBoundConst_le_one 4).trans (by norm_num)
    have hsmall' : ε * (r : ℝ) ^ 4 ≤ 1 := le_trans hsmall hγ4_le_one
    have hεr2_le : ε * (r : ℝ) ^ 2 ≤ 1 / (r : ℝ) ^ 2 := by
      rw [le_div_iff₀ hr_sq_pos]
      nlinarith
    have hdiv_le : ε / (1 - x ^ 2) ≤ ε / (1 / (r : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ hg0_pos (one_div_pos.mpr hr_sq_pos)]
      nlinarith
    calc ε / (1 - x ^ 2)
        ≤ ε / (1 / (r : ℝ) ^ 2) := hdiv_le
      _ = ε * (r : ℝ) ^ 2 := by field_simp [hr_ne]
      _ ≤ 1 / (r : ℝ) ^ 2 := hεr2_le
      _ ≤ t := by rwa [← hzpow_eq]
  linarith

private theorem vertical_edge_vecNorm_bound
    (ε t : ℝ) (r : ℕ) (hr2 : 2 ≤ r)
    (htρ : (r : ℝ) ^ (-2 : ℤ) ≤ t) (ht1 : t ≤ 1)
    (σ₀ σ₁ σ₂ : MvPolynomial (Fin 2) ℝ)
    (hsos₀ : IsSOS σ₀) (hsos₁ : IsSOS σ₁) (hsos₂ : IsSOS σ₂)
    (N : ℕ) (P : Fin N → MvPolynomial (Fin 2) ℝ)
    (hP : σ₁ = ∑ i : Fin N, (P i) ^ 2)
    (hdeg₁ : (σ₁ * BoxSemialgebraicGenerator 0).totalDegree ≤ r)
    (hdecomp : f_eps ε = σ₀ + σ₁ * BoxSemialgebraicGenerator 0
                            + σ₂ * BoxSemialgebraicGenerator 1)
    (hsmall : ε * (r : ℝ) ^ 4 ≤ improvedLowerBoundConst ^ 4) :
    vecNorm (fun i => MvPolynomial.eval (outsideCornerPoint 0 t) (P i)) ≤
      Real.sqrt (3 * Real.exp 6) * Real.sqrt t := by
  have hr_pos : 0 < (r : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hr2)
  have hr_sq_pos : 0 < (r : ℝ) ^ 2 := sq_pos_of_pos hr_pos
  have hzpow_eq : (r : ℝ) ^ (-2 : ℤ) = 1 / (r : ℝ) ^ 2 := by
    rw [zpow_neg, one_div]
    rfl
  have ht0 : 0 ≤ t := by
    have hρ_pos : 0 < (r : ℝ) ^ (-2 : ℤ) := by
      rw [hzpow_eq]
      positivity
    exact (le_of_lt hρ_pos).trans htρ
  have hσdeg : σ₁.totalDegree ≤ r := sigma1_degree_bound σ₁ r hdeg₁
  let q : Polynomial ℝ := horizontalRestriction t σ₁
  have hqdeg : q.natDegree ≤ r := by
    dsimp [q]
    exact (horizontalRestriction_natDegree_le_totalDegree t σ₁).trans hσdeg
  have hs_half : (r : ℝ) ^ (-2 : ℤ) ≤ 1 / 2 := by
    rw [hzpow_eq]
    rw [div_le_div_iff₀ hr_sq_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [show (2 : ℝ) ≤ r by exact_mod_cast hr2]
  have hs_d : (r : ℝ) ^ (-2 : ℤ) ≤ 1 / (r : ℝ) ^ 2 := by
    rw [hzpow_eq]
  have hbound : ∀ x : ℝ, |x| ≤ Real.sqrt (1 - (r : ℝ) ^ (-2 : ℤ)) →
      |q.eval x| ≤ 3 * t := by
    intro x hx
    have hxρ : (r : ℝ) ^ (-2 : ℤ) ≤ 1 - x ^ 2 := by
      have hs_nonneg : 0 ≤ (r : ℝ) ^ (-2 : ℤ) := by
        rw [hzpow_eq]
        positivity
      have hsq : x ^ 2 ≤ 1 - (r : ℝ) ^ (-2 : ℤ) := by
        have hright_nonneg : 0 ≤ Real.sqrt (1 - (r : ℝ) ^ (-2 : ℤ)) :=
          Real.sqrt_nonneg _
        have habs_le : |x| ≤ |Real.sqrt (1 - (r : ℝ) ^ (-2 : ℤ))| := by
          rw [abs_of_nonneg hright_nonneg]
          exact hx
        have hsq_abs := sq_le_sq.mpr habs_le
        rw [Real.sq_sqrt] at hsq_abs
        · exact hsq_abs
        · nlinarith [hs_nonneg, hs_half]
      nlinarith
    have hcore := vertical_scalar_core_bound ε t x r hr2 htρ ht1 hxρ σ₀ σ₁ σ₂
      hsos₀ hsos₁ hsos₂ hdecomp hsmall
    have hnonneg : 0 ≤ q.eval x := by
      dsimp [q]
      rw [horizontalRestriction_eval]
      exact IsSOS_nonneg σ₁ hsos₁ (![x, 1 - t]) (Set.mem_univ _)
    rw [abs_of_nonneg hnonneg]
    dsimp [q]
    rw [horizontalRestriction_eval]
    exact hcore
  have hC_sufficient : ∀ x : ℝ, |x| ≤ 1 + 1 / (r : ℝ) ^ 2 →
      |(chebyshevT r).eval (|x| / Real.sqrt (1 - (r : ℝ) ^ (-2 : ℤ)))| ≤ Real.exp 6 := by
    intro x hx
    exact chebyshevT_abs_le_exp_six_near_one r hr2 _
      (chebyshev_argument_vertical_bound r hr2 x hx)
  have hcheb := chebyshev_extrapolate_d2_scale 1 (Real.exp 6) (3 * t)
    (by norm_num) (Real.exp_pos 6)
    (by calc (1 : ℝ) ≤ Real.exp 0 := by simp
        _ ≤ Real.exp 6 := Real.exp_le_exp.mpr (by norm_num))
    r hr2 q hqdeg ((r : ℝ) ^ (-2 : ℤ))
    (by rw [hzpow_eq]; positivity) hs_half hs_d hbound hC_sufficient
  have hq1_abs : |q.eval 1| ≤ Real.exp 6 * (3 * t) := by
    apply hcheb
    rw [abs_one]
    have hnonneg : 0 ≤ 1 / (r : ℝ) ^ 2 := by positivity
    nlinarith
  have hq1_nonneg : 0 ≤ q.eval 1 := by
    dsimp [q]
    rw [horizontalRestriction_eval]
    exact IsSOS_nonneg σ₁ hsos₁ (![1, 1 - t]) (Set.mem_univ _)
  have hq1 : q.eval 1 ≤ 3 * Real.exp 6 * t := by
    rw [abs_of_nonneg hq1_nonneg] at hq1_abs
    nlinarith
  have hσ_eval_le : MvPolynomial.eval (outsideCornerPoint 0 t) σ₁ ≤ 3 * Real.exp 6 * t := by
    dsimp [q] at hq1
    rw [horizontalRestriction_eval] at hq1
    have hpt : (![1, 1 - t] : Fin 2 → ℝ) = outsideCornerPoint 0 t := by
      ext i
      fin_cases i <;> simp [outsideCornerPoint, Matrix.cons_val_zero, Matrix.cons_val_one]
    rwa [hpt] at hq1
  have hB_nonneg : 0 ≤ Real.sqrt (3 * Real.exp 6) * Real.sqrt t := by positivity
  apply vecNorm_le_of_vecSqNorm_le hB_nonneg
  rw [← sos_eval_eq_vecSqNorm σ₁ P hP (outsideCornerPoint 0 t)]
  calc MvPolynomial.eval (outsideCornerPoint 0 t) σ₁
      ≤ 3 * Real.exp 6 * t := hσ_eval_le
    _ = (Real.sqrt (3 * Real.exp 6) * Real.sqrt t) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 3 * Real.exp 6),
          Real.sq_sqrt ht0]

private theorem vertical_endpoint_from_difference_bound
    (ε b : ℝ) (r : ℕ) (hr2 : 2 ≤ r) (hb0 : 0 ≤ b)
    (σ₁ : MvPolynomial (Fin 2) ℝ)
    (N : ℕ) (P : Fin N → MvPolynomial (Fin 2) ℝ)
    (hP : σ₁ = ∑ i : Fin N, (P i) ^ 2)
    (hPdeg : ∀ i : Fin N, (P i).totalDegree ≤ r)
    (hb_def : b = improvedLowerBoundConst / (r : ℝ) ^ 2)
    (hcorner_norm : vecNorm (fun i => MvPolynomial.eval corner_11 (P i)) ≤
      (1 / Real.sqrt 2) * (r : ℝ) * Real.sqrt ε)
    (hVbound : ∀ t : ℝ, (r : ℝ) ^ (-2 : ℤ) ≤ t → t ≤ 1 →
      vecNorm (fun i => (verticalDifference (P i)).eval t) ≤
        (Real.sqrt (3 * Real.exp 6) + 1) * Real.sqrt t) :
    Real.sqrt (MvPolynomial.eval (outsideCornerPoint 0 b) σ₁) ≤
      (1 / Real.sqrt 2) * (r : ℝ) * Real.sqrt ε +
        verticalEndpointConst * (r : ℝ) * b := by
  have hr_pos : 0 < (r : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hr2)
  have hr_ne : (r : ℝ) ≠ 0 := ne_of_gt hr_pos
  have hzpow_eq : (r : ℝ) ^ (-2 : ℤ) = 1 / (r : ℝ) ^ 2 := by
    rw [zpow_neg, one_div]
    rfl
  have hb_le : b ≤ (r : ℝ) ^ (-2 : ℤ) := by
    rw [hb_def, hzpow_eq]
    apply div_le_div_of_nonneg_right improvedLowerBoundConst_le_one (sq_nonneg _)
  let A : ℝ := Real.sqrt (3 * Real.exp 6) + 1
  let V : Fin N → Polynomial ℝ := fun i => verticalDifference (P i)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hdegV : ∀ i, (V i).natDegree ≤ r := by
    intro i
    dsimp [V]
    exact (verticalDifference_natDegree_le_totalDegree (P i)).trans (hPdeg i)
  have hV0 : ∀ i, (V i).eval 0 = 0 := by
    intro i
    dsimp [V]
    exact verticalDifference_eval_zero (P i)
  have hCpos : 0 < Real.exp 6 := Real.exp_pos 6
  have hCone : 1 ≤ Real.exp 6 := by
    calc (1 : ℝ) ≤ Real.exp 0 := by simp
      _ ≤ Real.exp 6 := Real.exp_le_exp.mpr (by norm_num)
  have hendpoint := weighted_endpoint_estimate (N := N) (d := r) V A (Real.exp 6)
    hr2 hA_nonneg hCpos hCone (chebyshevT_abs_le_exp_six_near_one r hr2)
    hdegV hV0 hVbound b hb0 hb_le
  have hendpoint' : vecNorm (fun i => (verticalDifference (P i)).eval b) ≤
      verticalEndpointConst * (r : ℝ) * b := by
    dsimp [V, A] at hendpoint
    calc vecNorm (fun i => (verticalDifference (P i)).eval b)
        ≤ Real.exp 6 * (Real.sqrt (3 * Real.exp 6) + 1) * (r : ℝ) * b := hendpoint
      _ ≤ verticalEndpointConst * (r : ℝ) * b := by
          have hr_nonneg : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
          have h1 := mul_le_mul_of_nonneg_right verticalEndpointConst_absorbs hr_nonneg
          exact mul_le_mul_of_nonneg_right h1 hb0
  have htri : vecNorm (fun i => MvPolynomial.eval (outsideCornerPoint 0 b) (P i)) ≤
      vecNorm (fun i => MvPolynomial.eval corner_11 (P i)) +
        vecNorm (fun i => (verticalDifference (P i)).eval b) := by
    have h := vecNorm_add_le (N := N)
      (fun i => MvPolynomial.eval corner_11 (P i))
      (fun i => (verticalDifference (P i)).eval b)
    convert h using 2
    ext i
    rw [verticalDifference_eval]
    ring
  rw [sos_eval_eq_vecSqNorm σ₁ P hP (outsideCornerPoint 0 b)]
  change vecNorm (fun i => MvPolynomial.eval (outsideCornerPoint 0 b) (P i)) ≤
    (1 / Real.sqrt 2) * (r : ℝ) * Real.sqrt ε +
      verticalEndpointConst * (r : ℝ) * b
  linarith

/-- Core bounded-witness form of the weighted vertical estimate near the corner. -/
theorem vertical_estimate_near_corner_bounded
    (ε b : ℝ) (r : ℕ)
    (hε : 0 < ε) (hb0 : 0 ≤ b)
    (σ₀ σ₁ σ₂ : MvPolynomial (Fin 2) ℝ)
    (hsos₀ : IsSOS σ₀) (hsos₁ : IsSOS σ₁) (hsos₂ : IsSOS σ₂)
    (N : ℕ) (P : Fin N → MvPolynomial (Fin 2) ℝ)
    (hP : σ₁ = ∑ i : Fin N, (P i) ^ 2)
    (hPdeg : ∀ i : Fin N, (P i).totalDegree ≤ r)
    (hdeg₀ : σ₀.totalDegree ≤ r)
    (hdeg₁ : (σ₁ * BoxSemialgebraicGenerator 0).totalDegree ≤ r)
    (hdeg₂ : (σ₂ * BoxSemialgebraicGenerator 1).totalDegree ≤ r)
    (hdecomp : f_eps ε = σ₀ + σ₁ * BoxSemialgebraicGenerator 0
                            + σ₂ * BoxSemialgebraicGenerator 1)
    (hsmall : ε * (r : ℝ) ^ 4 ≤ improvedLowerBoundConst ^ 4)
    (hb_def : b = improvedLowerBoundConst / (r : ℝ) ^ 2) :
    Real.sqrt (MvPolynomial.eval (outsideCornerPoint 0 b) σ₁) ≤
      (1 / Real.sqrt 2) * (r : ℝ) * Real.sqrt ε +
        verticalEndpointConst * (r : ℝ) * b := by
  have hr2 : 2 ≤ r := two_le_of_bounded_decomp ε r σ₀ σ₁ σ₂ hdeg₀ hdeg₁ hdeg₂ hdecomp
  have hr_pos : 0 < (r : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hr2)
  have hr_sq_pos : 0 < (r : ℝ) ^ 2 := sq_pos_of_pos hr_pos
  have hzpow_eq : (r : ℝ) ^ (-2 : ℤ) = 1 / (r : ℝ) ^ 2 := by
    rw [zpow_neg, one_div]
    rfl
  have hcorner := fact1_sigma1_bound ε hε r σ₀ σ₁ σ₂
    hsos₀ hsos₁ hsos₂ hdeg₀ hdeg₁ hdeg₂ hdecomp
  have hcorner_norm : vecNorm (fun i => MvPolynomial.eval corner_11 (P i)) ≤
      (1 / Real.sqrt 2) * (r : ℝ) * Real.sqrt ε :=
    corner_vecNorm_le ε hε.le r σ₁ N P hP hcorner
  have hγ4_le_one : improvedLowerBoundConst ^ 4 ≤ 1 := by
    exact pow_le_one₀ improvedLowerBoundConst_pos.le improvedLowerBoundConst_le_one
  have hεr4_le_one : ε * (r : ℝ) ^ 4 ≤ 1 := hsmall.trans hγ4_le_one
  have hVbound : ∀ t : ℝ, (r : ℝ) ^ (-2 : ℤ) ≤ t → t ≤ 1 →
      vecNorm (fun i => (verticalDifference (P i)).eval t) ≤
        (Real.sqrt (3 * Real.exp 6) + 1) * Real.sqrt t := by
    intro t htρ ht1
    have ht0 : 0 ≤ t := by
      have hρ_pos : 0 < (r : ℝ) ^ (-2 : ℤ) := by
        rw [hzpow_eq]
        positivity
      exact (le_of_lt hρ_pos).trans htρ
    have hedge := vertical_edge_vecNorm_bound ε t r hr2 htρ ht1 σ₀ σ₁ σ₂
      hsos₀ hsos₁ hsos₂ N P hP hdeg₁ hdecomp hsmall
    have hcorner_le_sqrt_t : vecNorm (fun i => MvPolynomial.eval corner_11 (P i)) ≤
        Real.sqrt t := by
      have hleft_nonneg : 0 ≤ (1 / Real.sqrt 2) * (r : ℝ) * Real.sqrt ε := by
        positivity
      have hright_nonneg : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
      have hεr2_le_t : ε * (r : ℝ) ^ 2 ≤ t := by
        have hεr2_le_ρ : ε * (r : ℝ) ^ 2 ≤ 1 / (r : ℝ) ^ 2 := by
          rw [le_div_iff₀ hr_sq_pos]
          nlinarith [hεr4_le_one]
        rw [hzpow_eq] at htρ
        exact hεr2_le_ρ.trans htρ
      have hsquares : ((1 / Real.sqrt 2) * (r : ℝ) * Real.sqrt ε) ^ 2 ≤
          (Real.sqrt t) ^ 2 := by
        have hsqrt2_ne : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
        have hsqrt2_sq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
          rw [Real.sq_sqrt]
          norm_num
        rw [mul_pow, mul_pow, div_pow, one_pow, Real.sq_sqrt hε.le,
          Real.sq_sqrt ht0, hsqrt2_sq]
        field_simp [hsqrt2_ne]
        nlinarith [hεr2_le_t]
      have habs := sq_le_sq.mp hsquares
      have hmain : (1 / Real.sqrt 2) * (r : ℝ) * Real.sqrt ε ≤ Real.sqrt t := by
        rwa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] at habs
      exact hcorner_norm.trans hmain
    have htri : vecNorm (fun i => (verticalDifference (P i)).eval t) ≤
        vecNorm (fun i => MvPolynomial.eval (outsideCornerPoint 0 t) (P i)) +
          vecNorm (fun i => MvPolynomial.eval corner_11 (P i)) := by
      have h := vecNorm_sub_le (N := N)
        (fun i => MvPolynomial.eval (outsideCornerPoint 0 t) (P i))
        (fun i => MvPolynomial.eval corner_11 (P i))
      convert h using 2
      ext i
      rw [verticalDifference_eval]
    calc vecNorm (fun i => (verticalDifference (P i)).eval t)
        ≤ vecNorm (fun i => MvPolynomial.eval (outsideCornerPoint 0 t) (P i)) +
            vecNorm (fun i => MvPolynomial.eval corner_11 (P i)) := htri
      _ ≤ Real.sqrt (3 * Real.exp 6) * Real.sqrt t + Real.sqrt t := by
          nlinarith [hedge, hcorner_le_sqrt_t]
      _ = (Real.sqrt (3 * Real.exp 6) + 1) * Real.sqrt t := by ring
  exact vertical_endpoint_from_difference_bound ε b r hr2 hb0 σ₁ N P hP hPdeg hb_def
    hcorner_norm hVbound

/-- Core bounded-witness form of the horizontal Markov control at height
`y = 1-b`. -/
theorem horizontal_control_at_height_bounded
    (ε a b : ℝ) (r : ℕ)
    (ha : 0 < a) (hb0 : 0 ≤ b)
    (σ₀ σ₁ σ₂ : MvPolynomial (Fin 2) ℝ)
    (hsos₀ : IsSOS σ₀) (hsos₁ : IsSOS σ₁) (hsos₂ : IsSOS σ₂)
    (N : ℕ) (P : Fin N → MvPolynomial (Fin 2) ℝ)
    (hP : σ₁ = ∑ i : Fin N, (P i) ^ 2)
    (hPdeg : ∀ i : Fin N, (P i).totalDegree ≤ r)
    (hdeg₀ : σ₀.totalDegree ≤ r)
    (hdeg₁ : (σ₁ * BoxSemialgebraicGenerator 0).totalDegree ≤ r)
    (hdeg₂ : (σ₂ * BoxSemialgebraicGenerator 1).totalDegree ≤ r)
    (hdecomp : f_eps ε = σ₀ + σ₁ * BoxSemialgebraicGenerator 0
                            + σ₂ * BoxSemialgebraicGenerator 1)
    (hsmall : ε * (r : ℝ) ^ 4 ≤ improvedLowerBoundConst ^ 4)
    (ha_def : a = improvedLowerBoundConst / (r : ℝ) ^ 2)
    (hb_def : b = improvedLowerBoundConst / (r : ℝ) ^ 2) :
    Real.sqrt (MvPolynomial.eval (outsideCornerPoint a b) σ₁) ≤
      Real.sqrt (MvPolynomial.eval (outsideCornerPoint 0 b) σ₁) +
        horizontalControlConst * (r : ℝ) ^ 2 * a * Real.sqrt b := by
  have hr2 : 2 ≤ r := two_le_of_bounded_decomp ε r σ₀ σ₁ σ₂ hdeg₀ hdeg₁ hdeg₂ hdecomp
  have hr_pos : 0 < (r : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hr2)
  have hr_sq_pos : 0 < (r : ℝ) ^ 2 := sq_pos_of_pos hr_pos
  have ha0 : 0 ≤ a := ha.le
  have hb_eq : b = improvedLowerBoundConst / (r : ℝ) ^ 2 := hb_def
  have ha_le_rho : a ≤ 1 / (r : ℝ) ^ 2 := by
    rw [ha_def]
    exact div_le_div_of_nonneg_right improvedLowerBoundConst_le_one (sq_nonneg _)
  have ha_half : a ≤ 1 / 2 := by
    calc a ≤ 1 / (r : ℝ) ^ 2 := ha_le_rho
      _ ≤ 1 / 2 := by
          rw [div_le_div_iff₀ hr_sq_pos (by norm_num : (0 : ℝ) < 2)]
          nlinarith [show (2 : ℝ) ≤ r by exact_mod_cast hr2]
  have hσdeg : σ₁.totalDegree ≤ r := sigma1_degree_bound σ₁ r hdeg₁
  let q : Polynomial ℝ := horizontalRestriction b σ₁
  have hqdeg : q.natDegree ≤ r := by
    dsimp [q]
    exact (horizontalRestriction_natDegree_le_totalDegree b σ₁).trans hσdeg
  have hq_bound_inside : ∀ x : ℝ, |x| ≤ Real.sqrt (1 - a) → |q.eval x| ≤ 3 * b := by
    intro x hx
    have hxa : a ≤ 1 - x ^ 2 := by
      have hright_nonneg : 0 ≤ Real.sqrt (1 - a) := Real.sqrt_nonneg _
      have habs_le : |x| ≤ |Real.sqrt (1 - a)| := by
        rw [abs_of_nonneg hright_nonneg]
        exact hx
      have hsq_abs := sq_le_sq.mpr habs_le
      rw [Real.sq_sqrt] at hsq_abs
      · nlinarith
      · linarith [ha0, ha_half]
    have hcore := horizontal_scalar_core_bound ε a b x r hr2 ha hb0 hxa σ₀ σ₁ σ₂
      hsos₀ hsos₁ hsos₂ hdecomp hsmall ha_def hb_def
    have hnonneg : 0 ≤ q.eval x := by
      dsimp [q]
      rw [horizontalRestriction_eval]
      exact IsSOS_nonneg σ₁ hsos₁ (![x, 1 - b]) (Set.mem_univ _)
    rw [abs_of_nonneg hnonneg]
    dsimp [q]
    rw [horizontalRestriction_eval]
    exact hcore
  have hC_sufficient : ∀ x : ℝ, |x| ≤ 1 + 1 / (r : ℝ) ^ 2 →
      |(chebyshevT r).eval (|x| / Real.sqrt (1 - a))| ≤ Real.exp 6 := by
    intro x hx
    exact chebyshevT_abs_le_exp_six_near_one r hr2 _
      (chebyshev_argument_horizontal_bound r hr2 a x ha0 ha_le_rho hx)
  have hcheb := chebyshev_extrapolate_d2_scale 1 (Real.exp 6) (3 * b)
    (by norm_num) (Real.exp_pos 6)
    (by calc (1 : ℝ) ≤ Real.exp 0 := by simp
        _ ≤ Real.exp 6 := Real.exp_le_exp.mpr (by norm_num))
    r hr2 q hqdeg a ha0 ha_half ha_le_rho hq_bound_inside hC_sufficient
  let H : Fin N → Polynomial ℝ := fun i => horizontalRestriction b (P i)
  have hdegH : ∀ i, (H i).natDegree ≤ r := by
    intro i
    dsimp [H]
    exact (horizontalRestriction_natDegree_le_totalDegree b (P i)).trans (hPdeg i)
  have hM_nonneg : 0 ≤ Real.sqrt (3 * Real.exp 6) * Real.sqrt b := by positivity
  have hsup : ∀ x : ℝ, -1 ≤ x → x ≤ 1 + a →
      vecNorm (fun i => (H i).eval x) ≤ Real.sqrt (3 * Real.exp 6) * Real.sqrt b := by
    intro x hx_left hx_right
    have hx_abs : |x| ≤ 1 + 1 / (r : ℝ) ^ 2 := by
      rw [abs_le]
      constructor
      · linarith [ha0, ha_le_rho]
      · calc x ≤ 1 + a := hx_right
          _ ≤ 1 + 1 / (r : ℝ) ^ 2 := by linarith
    have hq_abs : |q.eval x| ≤ Real.exp 6 * (3 * b) := hcheb x hx_abs
    have hq_nonneg : 0 ≤ q.eval x := by
      dsimp [q]
      rw [horizontalRestriction_eval]
      exact IsSOS_nonneg σ₁ hsos₁ (![x, 1 - b]) (Set.mem_univ _)
    have hσ_eval_le : MvPolynomial.eval (![x, 1 - b]) σ₁ ≤ 3 * Real.exp 6 * b := by
      rw [abs_of_nonneg hq_nonneg] at hq_abs
      dsimp [q] at hq_abs
      rw [horizontalRestriction_eval] at hq_abs
      nlinarith
    apply vecNorm_le_of_vecSqNorm_le hM_nonneg
    have hvec : vecSqNorm (fun i => (H i).eval x) =
        vecSqNorm (fun i => MvPolynomial.eval (![x, 1 - b]) (P i)) := by
      unfold vecSqNorm
      congr 1
      ext i
      dsimp [H]
      rw [horizontalRestriction_eval]
    rw [hvec, ← sos_eval_eq_vecSqNorm σ₁ P hP (![x, 1 - b])]
    calc MvPolynomial.eval (![x, 1 - b]) σ₁
        ≤ 3 * Real.exp 6 * b := hσ_eval_le
      _ = (Real.sqrt (3 * Real.exp 6) * Real.sqrt b) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 3 * Real.exp 6),
            Real.sq_sqrt hb0]
  have hmarkov := vector_markov_increment_from_sup H r hdegH a
    (Real.sqrt (3 * Real.exp 6) * Real.sqrt b) ha hM_nonneg hsup
  have hsqrt_const_le : Real.sqrt (3 * Real.exp 6) ≤ horizontalControlConst := by
    unfold horizontalControlConst
    have hexp6_pos : 0 < Real.exp 6 := Real.exp_pos 6
    have hexp12_pos : 0 < Real.exp 12 := Real.exp_pos 12
    have hone : (1 : ℝ) ≤ Real.exp 6 := by
      calc (1 : ℝ) ≤ Real.exp 0 := by simp
        _ ≤ Real.exp 6 := Real.exp_le_exp.mpr (by norm_num)
    have hsqrt_le : Real.sqrt (3 * Real.exp 6) ≤ 3 * Real.exp 6 := by
      calc Real.sqrt (3 * Real.exp 6) ≤ Real.sqrt ((3 * Real.exp 6) ^ 2) := by
            apply Real.sqrt_le_sqrt
            nlinarith [hexp6_pos, hone]
        _ = 3 * Real.exp 6 := by
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
            nlinarith [hexp6_pos]
    have hsq : (Real.exp 6) ^ 2 = Real.exp 12 := by
      rw [sq, ← Real.exp_add]
      norm_num
    calc Real.sqrt (3 * Real.exp 6) ≤ 3 * Real.exp 6 := hsqrt_le
      _ ≤ 100 * Real.exp 12 := by
          rw [← hsq]
          nlinarith [hexp6_pos, hone]
  have hinc : vecNorm (fun i => (H i).eval (1 + a) - (H i).eval 1) ≤
      horizontalControlConst * (r : ℝ) ^ 2 * a * Real.sqrt b := by
    have hfactor : 2 * (r : ℝ) ^ 2 / (2 + a) ≤ (r : ℝ) ^ 2 := by
      have hden_pos : 0 < 2 + a := by linarith
      rw [div_le_iff₀ hden_pos]
      nlinarith [sq_nonneg (r : ℝ), ha0]
    calc vecNorm (fun i => (H i).eval (1 + a) - (H i).eval 1)
        ≤ (2 * (r : ℝ) ^ 2 / (2 + a)) *
            (Real.sqrt (3 * Real.exp 6) * Real.sqrt b) * a := hmarkov
      _ ≤ (r : ℝ) ^ 2 * (horizontalControlConst * Real.sqrt b) * a := by
          apply mul_le_mul_of_nonneg_right _ ha0
          apply mul_le_mul hfactor
            (mul_le_mul_of_nonneg_right hsqrt_const_le (Real.sqrt_nonneg b))
          · positivity
          · positivity
      _ = horizontalControlConst * (r : ℝ) ^ 2 * a * Real.sqrt b := by ring
  have htri : vecNorm (fun i => MvPolynomial.eval (outsideCornerPoint a b) (P i)) ≤
      vecNorm (fun i => MvPolynomial.eval (outsideCornerPoint 0 b) (P i)) +
        vecNorm (fun i => (H i).eval (1 + a) - (H i).eval 1) := by
    have h := vecNorm_add_le (N := N)
      (fun i => MvPolynomial.eval (outsideCornerPoint 0 b) (P i))
      (fun i => (H i).eval (1 + a) - (H i).eval 1)
    convert h using 2
    ext i
    dsimp [H]
    rw [horizontalRestriction_eval, horizontalRestriction_eval]
    simp [outsideCornerPoint]
  rw [sos_eval_eq_vecSqNorm σ₁ P hP (outsideCornerPoint a b),
    sos_eval_eq_vecSqNorm σ₁ P hP (outsideCornerPoint 0 b)]
  change vecNorm (fun i => MvPolynomial.eval (outsideCornerPoint a b) (P i)) ≤
      vecNorm (fun i => MvPolynomial.eval (outsideCornerPoint 0 b) (P i)) +
        horizontalControlConst * (r : ℝ) ^ 2 * a * Real.sqrt b
  linarith

/-- Corner estimate `σ₁(1,1) ≤ ε r² / 2`, restated from
`fact1_sigma1_bound`. -/
theorem corner_sigma1_bound
    (ε : ℝ) (hε : 0 < ε) (r : ℕ)
    (σ₀ σ₁ σ₂ : MvPolynomial (Fin 2) ℝ)
    (hsos₀ : IsSOS σ₀) (hsos₁ : IsSOS σ₁) (hsos₂ : IsSOS σ₂)
    (hdeg₀ : σ₀.totalDegree ≤ r)
    (hdeg₁ : (σ₁ * BoxSemialgebraicGenerator 0).totalDegree ≤ r)
    (hdeg₂ : (σ₂ * BoxSemialgebraicGenerator 1).totalDegree ≤ r)
    (hdecomp : f_eps ε = σ₀ + σ₁ * BoxSemialgebraicGenerator 0
                            + σ₂ * BoxSemialgebraicGenerator 1) :
    MvPolynomial.eval corner_11 σ₁ ≤ ε * (r : ℝ) ^ 2 / 2 := by
  exact fact1_sigma1_bound ε hε r σ₀ σ₁ σ₂ hsos₀ hsos₁ hsos₂
    hdeg₀ hdeg₁ hdeg₂ hdecomp

/-- Weighted vertical estimate near the corner, obtained by applying the weighted
endpoint lemma to an SOS square-root vector for `σ₁`. -/
theorem vertical_estimate_near_corner
    (ε b : ℝ) (r : ℕ)
    (hε : 0 < ε) (hb0 : 0 ≤ b)
    (σ₀ σ₁ σ₂ : MvPolynomial (Fin 2) ℝ)
    (hsos₀ : IsSOS σ₀) (hsos₁ : IsSOS σ₁) (hsos₂ : IsSOS σ₂)
    (hdeg₀ : σ₀.totalDegree ≤ r)
    (hdeg₁ : (σ₁ * BoxSemialgebraicGenerator 0).totalDegree ≤ r)
    (hdeg₂ : (σ₂ * BoxSemialgebraicGenerator 1).totalDegree ≤ r)
    (hdecomp : f_eps ε = σ₀ + σ₁ * BoxSemialgebraicGenerator 0
                            + σ₂ * BoxSemialgebraicGenerator 1)
    (hsmall : ε * (r : ℝ) ^ 4 ≤ improvedLowerBoundConst ^ 4)
    (hb_def : b = improvedLowerBoundConst / (r : ℝ) ^ 2) :
    Real.sqrt (MvPolynomial.eval (outsideCornerPoint 0 b) σ₁) ≤
      (1 / Real.sqrt 2) * (r : ℝ) * Real.sqrt ε +
        verticalEndpointConst * (r : ℝ) * b := by
  have hsos₁' : IsSOS σ₁ := hsos₁
  obtain ⟨N, P, hP⟩ := hsos₁
  have hσdeg : σ₁.totalDegree ≤ r := sigma1_degree_bound σ₁ r hdeg₁
  have hσdeg2 : σ₁.totalDegree ≤ 2 * r := by
    nlinarith
  have hPdeg : ∀ i : Fin N, (P i).totalDegree ≤ r :=
    sos_summand_totalDegree_le_of_sum_sq_totalDegree hP hσdeg2
  exact vertical_estimate_near_corner_bounded ε b r hε hb0 σ₀ σ₁ σ₂
    hsos₀ hsos₁' hsos₂ N P hP hPdeg hdeg₀ hdeg₁ hdeg₂ hdecomp hsmall hb_def

/-- Horizontal Markov control at height `y = 1-b`, comparing the SOS square-root
vector at `(1,1-b)` and `(1+a,1-b)`. -/
theorem horizontal_control_at_height
    (ε a b : ℝ) (r : ℕ)
    (ha : 0 < a) (hb0 : 0 ≤ b)
    (σ₀ σ₁ σ₂ : MvPolynomial (Fin 2) ℝ)
    (hsos₀ : IsSOS σ₀) (hsos₁ : IsSOS σ₁) (hsos₂ : IsSOS σ₂)
    (hdeg₀ : σ₀.totalDegree ≤ r)
    (hdeg₁ : (σ₁ * BoxSemialgebraicGenerator 0).totalDegree ≤ r)
    (hdeg₂ : (σ₂ * BoxSemialgebraicGenerator 1).totalDegree ≤ r)
    (hdecomp : f_eps ε = σ₀ + σ₁ * BoxSemialgebraicGenerator 0
                            + σ₂ * BoxSemialgebraicGenerator 1)
    (hsmall : ε * (r : ℝ) ^ 4 ≤ improvedLowerBoundConst ^ 4)
    (ha_def : a = improvedLowerBoundConst / (r : ℝ) ^ 2)
    (hb_def : b = improvedLowerBoundConst / (r : ℝ) ^ 2) :
    Real.sqrt (MvPolynomial.eval (outsideCornerPoint a b) σ₁) ≤
      Real.sqrt (MvPolynomial.eval (outsideCornerPoint 0 b) σ₁) +
        horizontalControlConst * (r : ℝ) ^ 2 * a * Real.sqrt b := by
  have hsos₁' : IsSOS σ₁ := hsos₁
  obtain ⟨N, P, hP⟩ := hsos₁
  have hσdeg : σ₁.totalDegree ≤ r := sigma1_degree_bound σ₁ r hdeg₁
  have hσdeg2 : σ₁.totalDegree ≤ 2 * r := by
    nlinarith
  have hPdeg : ∀ i : Fin N, (P i).totalDegree ≤ r :=
    sos_summand_totalDegree_le_of_sum_sq_totalDegree hP hσdeg2
  exact horizontal_control_at_height_bounded ε a b r ha hb0 σ₀ σ₁ σ₂
    hsos₀ hsos₁' hsos₂ N P hP hPdeg hdeg₀ hdeg₁ hdeg₂ hdecomp hsmall ha_def hb_def

/-- The quantitative choice of constants turns the vertical and horizontal
estimates into `sqrt(σ₁(1+a,1-b)) ≤ sqrt b / 2`. -/
theorem outside_point_sqrt_upper_from_vertical_horizontal
    (ε a b : ℝ) (r : ℕ)
    (hε : 0 < ε) (ha : 0 < a) (hb0 : 0 ≤ b)
    (σ₀ σ₁ σ₂ : MvPolynomial (Fin 2) ℝ)
    (hsos₀ : IsSOS σ₀) (hsos₁ : IsSOS σ₁) (hsos₂ : IsSOS σ₂)
    (hdeg₀ : σ₀.totalDegree ≤ r)
    (hdeg₁ : (σ₁ * BoxSemialgebraicGenerator 0).totalDegree ≤ r)
    (hdeg₂ : (σ₂ * BoxSemialgebraicGenerator 1).totalDegree ≤ r)
    (hdecomp : f_eps ε = σ₀ + σ₁ * BoxSemialgebraicGenerator 0
                            + σ₂ * BoxSemialgebraicGenerator 1)
    (hsmall : ε * (r : ℝ) ^ 4 ≤ improvedLowerBoundConst ^ 4)
    (ha_def : a = improvedLowerBoundConst / (r : ℝ) ^ 2)
    (hb_def : b = improvedLowerBoundConst / (r : ℝ) ^ 2) :
    Real.sqrt (MvPolynomial.eval (outsideCornerPoint a b) σ₁) ≤ Real.sqrt b / 2 := by
  have hv := vertical_estimate_near_corner ε b r hε hb0
    σ₀ σ₁ σ₂ hsos₀ hsos₁ hsos₂ hdeg₀ hdeg₁ hdeg₂ hdecomp hsmall hb_def
  have hh := horizontal_control_at_height ε a b r ha hb0
    σ₀ σ₁ σ₂ hsos₀ hsos₁ hsos₂ hdeg₀ hdeg₁ hdeg₂ hdecomp hsmall ha_def hb_def
  have hr_pos : 0 < (r : ℝ) := by
    by_contra hr_nonpos
    have hr_nat : r = 0 := by
      exact Nat.cast_eq_zero.mp (le_antisymm (not_lt.mp hr_nonpos) (Nat.cast_nonneg r))
    subst r
    unfold improvedLowerBoundConst at ha_def
    norm_num at ha_def
    linarith
  have hr_sq_pos : 0 < (r : ℝ) ^ 2 := sq_pos_of_pos hr_pos
  have hb_eq : b = improvedLowerBoundConst / (r : ℝ) ^ 2 := hb_def
  have hthird : horizontalControlConst * (r : ℝ) ^ 2 * a * Real.sqrt b ≤
      Real.sqrt b / 6 := by
    rw [ha_def]
    have hsqrt_nonneg : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
    have hconst : horizontalControlConst * improvedLowerBoundConst ≤ 1 / 6 := by
      have hden_pos : 0 < 36 * horizontalControlConst ^ 2 :=
        mul_pos (by norm_num) (sq_pos_of_pos horizontalControlConst_pos)
      have hstep : horizontalControlConst * improvedLowerBoundConst ≤
          horizontalControlConst * (1 / (36 * horizontalControlConst ^ 2)) :=
        mul_le_mul_of_nonneg_left improvedLowerBoundConst_le_horizontal_sq
          horizontalControlConst_pos.le
      have hsimpl : horizontalControlConst * (1 / (36 * horizontalControlConst ^ 2)) =
          1 / (36 * horizontalControlConst) := by
        field_simp [horizontalControlConst_pos.ne']
      have hsmall' : 1 / (36 * horizontalControlConst) ≤ 1 / 6 := by
        rw [div_le_div_iff₀
          (mul_pos (by norm_num) horizontalControlConst_pos)
          (by norm_num : (0 : ℝ) < (6 : ℝ))]
        nlinarith [one_le_horizontalControlConst]
      calc horizontalControlConst * improvedLowerBoundConst
          ≤ horizontalControlConst * (1 / (36 * horizontalControlConst ^ 2)) := hstep
        _ = 1 / (36 * horizontalControlConst) := hsimpl
        _ ≤ 1 / 6 := hsmall'
    field_simp [hr_sq_pos.ne']
    nlinarith [mul_le_mul_of_nonneg_right hconst hsqrt_nonneg]
  have hsecond : verticalEndpointConst * (r : ℝ) * b ≤ Real.sqrt b / 6 := by
    have hleft_nonneg : 0 ≤ verticalEndpointConst * (r : ℝ) * b := by
      rw [hb_eq]
      exact mul_nonneg (mul_nonneg verticalEndpointConst_pos.le hr_pos.le)
        (div_nonneg improvedLowerBoundConst_pos.le hr_sq_pos.le)
    have hright_nonneg : 0 ≤ Real.sqrt b / 6 := by
      positivity
    have hgammaV : verticalEndpointConst ^ 2 * improvedLowerBoundConst ≤ 1 / 36 := by
      have hden_pos : 0 < 36 * verticalEndpointConst ^ 2 :=
        mul_pos (by norm_num) (sq_pos_of_pos verticalEndpointConst_pos)
      have h := improvedLowerBoundConst_le_vertical_sq
      rw [le_div_iff₀ hden_pos] at h
      nlinarith
    have hsquares : (verticalEndpointConst * (r : ℝ) * b) ^ 2 ≤
        (Real.sqrt b / 6) ^ 2 := by
      rw [hb_eq]
      rw [div_pow, Real.sq_sqrt]
      · field_simp [hr_sq_pos.ne']
        nlinarith [hgammaV, improvedLowerBoundConst_pos.le]
      · exact div_nonneg improvedLowerBoundConst_pos.le hr_sq_pos.le
    have habs := sq_le_sq.mp hsquares
    rwa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] at habs
  have hfirst : (1 / Real.sqrt 2) * (r : ℝ) * Real.sqrt ε ≤ Real.sqrt b / 6 := by
    by_cases hε_nonneg : 0 ≤ ε
    · have hleft_nonneg : 0 ≤ (1 / Real.sqrt 2) * (r : ℝ) * Real.sqrt ε := by
        positivity
      have hright_nonneg : 0 ≤ Real.sqrt b / 6 := by
        positivity
      have hgamma4 : improvedLowerBoundConst ^ 4 ≤ improvedLowerBoundConst / 36 := by
        have hγ0 : 0 ≤ improvedLowerBoundConst := improvedLowerBoundConst_pos.le
        have hγ1 : improvedLowerBoundConst ≤ 1 / 1000000 :=
          improvedLowerBoundConst_le_millionth
        have hγ3 : improvedLowerBoundConst ^ 3 ≤ (1 / 1000000 : ℝ) ^ 3 :=
          pow_le_pow_left₀ hγ0 hγ1 3
        have hγ3_small : improvedLowerBoundConst ^ 3 ≤ 1 / 36 := by
          calc improvedLowerBoundConst ^ 3 ≤ (1 / 1000000 : ℝ) ^ 3 := hγ3
            _ ≤ 1 / 36 := by norm_num
        calc improvedLowerBoundConst ^ 4
            = improvedLowerBoundConst * improvedLowerBoundConst ^ 3 := by ring
          _ ≤ improvedLowerBoundConst * (1 / 36) :=
              mul_le_mul_of_nonneg_left hγ3_small hγ0
          _ = improvedLowerBoundConst / 36 := by ring
      have hsquares : ((1 / Real.sqrt 2) * (r : ℝ) * Real.sqrt ε) ^ 2 ≤
          (Real.sqrt b / 6) ^ 2 := by
        rw [hb_eq]
        have hsqrt2_ne : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
        have hsqrt2_sq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
          rw [Real.sq_sqrt]
          norm_num
        rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hε_nonneg, Real.sq_sqrt]
        · field_simp [hr_sq_pos.ne', hsqrt2_ne, hsqrt2_sq]
          nlinarith [hsmall, hgamma4, improvedLowerBoundConst_pos.le]
        · exact div_nonneg improvedLowerBoundConst_pos.le hr_sq_pos.le
      have habs := sq_le_sq.mp hsquares
      rwa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] at habs
    · have hε_nonpos : ε ≤ 0 := le_of_lt (not_le.mp hε_nonneg)
      have hsqrtε : Real.sqrt ε = 0 := Real.sqrt_eq_zero_of_nonpos hε_nonpos
      rw [hsqrtε]
      nlinarith [Real.sqrt_nonneg b]
  calc
    Real.sqrt (MvPolynomial.eval (outsideCornerPoint a b) σ₁)
        ≤ Real.sqrt (MvPolynomial.eval (outsideCornerPoint 0 b) σ₁)
            + horizontalControlConst * (r : ℝ) ^ 2 * a * Real.sqrt b := hh
    _ ≤ ((1 / Real.sqrt 2) * (r : ℝ) * Real.sqrt ε
            + verticalEndpointConst * (r : ℝ) * b)
            + horizontalControlConst * (r : ℝ) ^ 2 * a * Real.sqrt b := by
        nlinarith [hv]
    _ ≤ Real.sqrt b / 2 := by
        linarith [hfirst, hsecond, hthird]

/-- Upper bound at `(1+a,1-b)` obtained from the corner, vertical, and
horizontal estimates. -/
theorem outside_point_sigma1_upper_bound
    (ε a b : ℝ) (r : ℕ)
    (hε : 0 < ε) (ha : 0 < a) (hb0 : 0 ≤ b)
    (σ₀ σ₁ σ₂ : MvPolynomial (Fin 2) ℝ)
    (hsos₀ : IsSOS σ₀) (hsos₁ : IsSOS σ₁) (hsos₂ : IsSOS σ₂)
    (hdeg₀ : σ₀.totalDegree ≤ r)
    (hdeg₁ : (σ₁ * BoxSemialgebraicGenerator 0).totalDegree ≤ r)
    (hdeg₂ : (σ₂ * BoxSemialgebraicGenerator 1).totalDegree ≤ r)
    (hdecomp : f_eps ε = σ₀ + σ₁ * BoxSemialgebraicGenerator 0
                            + σ₂ * BoxSemialgebraicGenerator 1)
    (hsmall : ε * (r : ℝ) ^ 4 ≤ improvedLowerBoundConst ^ 4)
    (ha_def : a = improvedLowerBoundConst / (r : ℝ) ^ 2)
    (hb_def : b = improvedLowerBoundConst / (r : ℝ) ^ 2) :
    MvPolynomial.eval (outsideCornerPoint a b) σ₁ ≤ b / 4 := by
  have hsqrt := outside_point_sqrt_upper_from_vertical_horizontal ε a b r hε ha hb0
    σ₀ σ₁ σ₂ hsos₀ hsos₁ hsos₂ hdeg₀ hdeg₁ hdeg₂ hdecomp hsmall ha_def hb_def
  have hσ_nn : 0 ≤ MvPolynomial.eval (outsideCornerPoint a b) σ₁ :=
    IsSOS_nonneg σ₁ hsos₁ (outsideCornerPoint a b) (Set.mem_univ _)
  have hright_nn : 0 ≤ Real.sqrt b / 2 := by positivity
  have hsq : (Real.sqrt (MvPolynomial.eval (outsideCornerPoint a b) σ₁)) ^ 2 ≤
      (Real.sqrt b / 2) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (MvPolynomial.eval (outsideCornerPoint a b) σ₁)]
  rw [Real.sq_sqrt hσ_nn] at hsq
  have hb_sq : (Real.sqrt b / 2) ^ 2 = b / 4 := by
    rw [div_pow, Real.sq_sqrt hb0]
    ring
  rwa [hb_sq] at hsq

end OptimalConvergenceRates

end

