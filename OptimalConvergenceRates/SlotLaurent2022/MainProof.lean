/-
  OptimalConvergenceRates/SlotLaurent2022/MainProof.lean

  Technical proof of the Slot-Laurent 2022 box-preordering convergence bound.
-/
import OptimalConvergenceRates.SlotLaurent2022.KernelOperator
import OptimalConvergenceRates.SlotLaurent2022.Defs
import OptimalConvergenceRates.MarkovLukacz.MarkovLukacz
import Mathlib.Analysis.Real.Pi.Bounds

open MvPolynomial Finset Real

noncomputable section

namespace OptimalConvergenceRates

variable {n : ℕ}

/-! ## Auxiliary inequalities -/

/-- Bernoulli's inequality: 1 - (1-x)^t ≤ t·x for x ∈ [0,1], t ≥ 1 -/
theorem bernoulli_ineq (x : ℝ) (t : ℕ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (ht : 1 ≤ t) :
    1 - (1 - x) ^ t ≤ t * x := by
  induction t with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn; simp
    · have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have h01 : 0 ≤ 1 - x := by linarith [hx.2]
      have h01' : 1 - x ≤ 1 := by linarith [hx.1]
      calc 1 - (1 - x) ^ (n + 1)
          = 1 - (1 - x) ^ n * (1 - x) := by ring_nf
        _ = (1 - (1 - x) ^ n) + (1 - x) ^ n * x := by ring
        _ ≤ n * x + 1 * x := by
            apply add_le_add (ih hn')
            exact mul_le_mul_of_nonneg_right (pow_le_one₀ h01 h01') hx.1
        _ = (↑(n + 1)) * x := by push_cast; ring

/-! ## Eigenvalue bounds (Lemmas 7 and 8) -/

/-- For factors in [0,1], 1 - ∏ aᵢ ≤ ∑ (1 - aᵢ) -/
private lemma one_sub_prod_le_sum_one_sub {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∏ i ∈ s, f i ≤ ∑ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    have h0' := fun j hj => h0 j (Finset.mem_insert_of_mem hj)
    have h1' := fun j hj => h1 j (Finset.mem_insert_of_mem hj)
    have hfa1 := h1 a (Finset.mem_insert_self a s)
    have hprod_nonneg := Finset.prod_nonneg h0'
    have hprod_le := Finset.prod_le_one₀ h0' h1'
    nlinarith [ih h0' h1', mul_le_mul_of_nonneg_right hfa1 (sub_nonneg.mpr hprod_le)]

/-- Lemma 7: For κ ∈ ℕ^n_d and r ≥ πd, we have |1 - λ_κ^r| ≤ nπ²d²/r² -/
theorem eigenvalue_bound {d r : ℕ} (κ : Fin n → ℕ)
    (hκ : κ ∈ multiIndices n d) (hr : Real.pi * d ≤ r) :
    |1 - jacksonCoeffMulti κ r| ≤ n * Real.pi ^ 2 * d ^ 2 / (r : ℝ) ^ 2 := by
  have hd_le_r : d ≤ r := by
    by_contra h; push Not at h
    by_cases hd0 : d = 0; · omega
    have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd0)
    have hdr : (r : ℝ) < (d : ℝ) := by exact_mod_cast h
    have : (d : ℝ) ≤ Real.pi * d :=
      le_mul_of_one_le_left hd_pos.le (by linarith [pi_gt_three])
    linarith
  have hκd := (multiIndices_mem_iff.mp hκ).2
  have hκr : ∀ i, κ i ≤ r := fun i => le_trans (hκd i) hd_le_r
  have hle1 : ∀ i : Fin n, jacksonCoeff (κ i) r ≤ 1 := fun i => jackson_coeff_le_one _ _
  have hpos : ∀ i : Fin n, 0 ≤ jacksonCoeff (κ i) r := fun i => (jackson_coeff_pos (hκr i)).le
  have hmulti_le1 : jacksonCoeffMulti κ r ≤ 1 := by
    unfold jacksonCoeffMulti; exact Finset.prod_le_one₀ (fun i _ => hpos i) (fun i _ => hle1 i)
  rw [abs_of_nonneg (sub_nonneg.mpr hmulti_le1)]
  have hprod_bound : 1 - jacksonCoeffMulti κ r ≤
      ∑ i : Fin n, (1 - jacksonCoeff (κ i) r) := by
    unfold jacksonCoeffMulti
    exact one_sub_prod_le_sum_one_sub (fun i _ => hpos i) (fun i _ => hle1 i)
  have hcoeff_bound : ∀ i : Fin n,
      1 - jacksonCoeff (κ i) r ≤ Real.pi ^ 2 * d ^ 2 / (r + 2 : ℝ) ^ 2 := fun i =>
    le_trans (le_abs_self _) (jackson_coeff_approx (hκd i) hd_le_r)
  have hsum : ∑ i : Fin n, (1 - jacksonCoeff (κ i) r) ≤
      n * (Real.pi ^ 2 * d ^ 2 / (r + 2 : ℝ) ^ 2) := by
    calc ∑ i : Fin n, (1 - jacksonCoeff (κ i) r)
        ≤ ∑ _i : Fin n, (Real.pi ^ 2 * d ^ 2 / (r + 2 : ℝ) ^ 2) :=
          Finset.sum_le_sum (fun i _ => hcoeff_bound i)
      _ = n * (Real.pi ^ 2 * d ^ 2 / (r + 2 : ℝ) ^ 2) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  by_cases hr0 : r = 0
  · have hd0 : d = 0 := Nat.eq_zero_of_le_zero (hr0 ▸ hd_le_r)
    simp [jacksonCoeffMulti, jacksonCoeff, hd0, hr0,
          show ∀ i, κ i = 0 from fun i => Nat.eq_zero_of_le_zero (hd0 ▸ hκd i)]
  · have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr0)
    have hfrac : Real.pi ^ 2 * (d : ℝ) ^ 2 / ((r : ℝ) + 2) ^ 2 ≤
        Real.pi ^ 2 * (d : ℝ) ^ 2 / (r : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hr_pos)
        (by nlinarith : (r : ℝ) ^ 2 ≤ ((r : ℝ) + 2) ^ 2)
    have hmul := mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg (α := ℝ) n)
    have hrw : ↑n * (Real.pi ^ 2 * ↑d ^ 2 / ↑r ^ 2) = ↑n * Real.pi ^ 2 * ↑d ^ 2 / ↑r ^ 2 :=
      by ring
    linarith

/-- Lemma 8: For κ ∈ ℕ^n_d and r ≥ πd√(2n), we have |1 - 1/λ_κ^r| ≤ 2nπ²d²/r² -/
theorem inverse_eigenvalue_bound {d r : ℕ} (κ : Fin n → ℕ)
    (hκ : κ ∈ multiIndices n d) (hr : Real.pi * d * Real.sqrt (2 * n) ≤ r) :
    |1 - 1 / jacksonCoeffMulti κ r| ≤ 2 * n * Real.pi ^ 2 * d ^ 2 / (r : ℝ) ^ 2 := by
  by_cases hn0 : n = 0
  · subst hn0; simp [jacksonCoeffMulti]
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  have hπd : Real.pi * d ≤ r := by
    calc Real.pi * d = Real.pi * d * 1 := (mul_one _).symm
      _ ≤ Real.pi * d * Real.sqrt (2 * n) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← Real.sqrt_one]
          exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ 2 * n by omega))
      _ ≤ r := hr
  have hev := eigenvalue_bound κ hκ hπd
  have hd_le_r : d ≤ r := by
    by_contra h; push Not at h
    by_cases hd0 : d = 0; · omega
    have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd0)
    linarith [le_mul_of_one_le_left hd_pos.le
      (show (1 : ℝ) ≤ Real.pi by linarith [pi_gt_three]),
      show (r : ℝ) < (d : ℝ) from by exact_mod_cast h]
  have hκr : ∀ i, κ i ≤ r :=
    fun i => le_trans ((multiIndices_mem_iff.mp hκ).2 i) hd_le_r
  have hmulti_pos : 0 < jacksonCoeffMulti κ r := jacksonCoeffMulti_pos hκr
  by_cases hr0 : r = 0
  · have hd0 : d = 0 := Nat.eq_zero_of_le_zero (hr0 ▸ hd_le_r)
    have hκ0 : ∀ i, κ i = 0 :=
      fun i => Nat.eq_zero_of_le_zero (hd0 ▸ (multiIndices_mem_iff.mp hκ).2 i)
    simp [jacksonCoeffMulti, jacksonCoeff, hκ0, hr0]
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr0)
  have hrsq_pos : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
  have hsq : Real.pi ^ 2 * d ^ 2 * (2 * n) ≤ (r : ℝ) ^ 2 := by
    have h1 : (Real.pi * ↑d * Real.sqrt (2 * ↑n)) ^ 2 ≤ (↑r : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hr 2
    have h2 : (Real.pi * ↑d * Real.sqrt (2 * ↑n)) ^ 2 =
        Real.pi ^ 2 * ↑d ^ 2 * (2 * ↑n) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * ↑n)]
    linarith
  have hev_half : n * Real.pi ^ 2 * d ^ 2 / (r : ℝ) ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ hrsq_pos]; nlinarith
  have habs_le_half : |1 - jacksonCoeffMulti κ r| ≤ 1 / 2 := le_trans hev hev_half
  have hcoeff_ge_half : 1 / 2 ≤ jacksonCoeffMulti κ r := by
    have := (abs_le.mp habs_le_half).2; linarith
  have hkey : |1 - 1 / jacksonCoeffMulti κ r| =
      |1 - jacksonCoeffMulti κ r| / jacksonCoeffMulti κ r := by
    rw [show 1 - 1 / jacksonCoeffMulti κ r =
        (jacksonCoeffMulti κ r - 1) / jacksonCoeffMulti κ r by field_simp,
      abs_div, abs_of_pos hmulti_pos, abs_sub_comm]
  rw [hkey]
  calc |1 - jacksonCoeffMulti κ r| / jacksonCoeffMulti κ r
      ≤ |1 - jacksonCoeffMulti κ r| / (1 / 2) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hcoeff_ge_half
    _ = 2 * |1 - jacksonCoeffMulti κ r| := by ring
    _ ≤ 2 * (n * Real.pi ^ 2 * d ^ 2 / (r : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hev (by norm_num)
    _ = 2 * n * Real.pi ^ 2 * d ^ 2 / (r : ℝ) ^ 2 := by ring

/-! ## Outline lemma (Lemma 2) -/

/-- Lemma 2 (Outline): If there exists a nonsingular operator K_r satisfying
    (P1) and (P2) with parameter ε, then f_min - f_{(r+1)n} ≤ ε · (f_max - f_min). -/
theorem outline_lemma (f : MvPolynomial (Fin n) ℝ) (r : ℕ) (ε : ℝ)
    (_hε : 0 < ε) (hd : f.totalDegree ≤ r)
    (hP1 : ∀ p : MvPolynomial (Fin n) ℝ,
      p.totalDegree ≤ r → IsNonnegOn p (Hypercube n) →
      kernelOperator n r p ∈ BoxPreordering n ((r + 1) * n))
    (hP2 : polySupNorm (kernelOperatorInv n r
      (f - MvPolynomial.C (polyMin f) +
       MvPolynomial.C (ε * (polyMax f - polyMin f))) -
      (f - MvPolynomial.C (polyMin f) +
       MvPolynomial.C (ε * (polyMax f - polyMin f)))) ≤
      ε * (polyMax f - polyMin f)) :
    ↑(polyMin f - ε * (polyMax f - polyMin f)) ≤ lasserre_bound_box_preo f ((r + 1) * n) := by
  set Ft := f - MvPolynomial.C (polyMin f) +
    MvPolynomial.C (ε * (polyMax f - polyMin f)) with hFt_def
  have hFt_eq :
      f - MvPolynomial.C (polyMin f - ε * (polyMax f - polyMin f)) = Ft := by
    simp [hFt_def, map_sub, map_mul]; ring
  have hFt_deg : Ft.totalDegree ≤ r := by
    calc Ft.totalDegree
        ≤ max (f - MvPolynomial.C (polyMin f)).totalDegree
          (MvPolynomial.C (ε * (polyMax f - polyMin f))).totalDegree :=
        MvPolynomial.totalDegree_add _ _
      _ ≤ max f.totalDegree 0 := by
        apply max_le_max
        · exact MvPolynomial.totalDegree_sub_C_le _ _
        · exact le_of_eq (MvPolynomial.totalDegree_C _)
      _ ≤ r := by simp [hd]
  have hKinv_nonneg : IsNonnegOn (kernelOperatorInv n r Ft) (Hypercube n) := by
    intro x hx
    have hFt_eval : MvPolynomial.eval x Ft =
        MvPolynomial.eval x f - polyMin f + ε * (polyMax f - polyMin f) := by
      simp [hFt_def, map_sub, map_add, MvPolynomial.eval_C]
    have hFt_bound : ε * (polyMax f - polyMin f) ≤ MvPolynomial.eval x Ft := by
      rw [hFt_eval]; linarith [polyMin_le_eval f x hx]
    have hP2_pt : |MvPolynomial.eval x (kernelOperatorInv n r Ft - Ft)| ≤
        ε * (polyMax f - polyMin f) :=
      polySupNorm_eval_le _ _ hP2 x hx
    have hdiff := abs_le.mp hP2_pt
    simp only [map_sub] at hdiff
    linarith [hdiff.1]
  have hKinv_deg : (kernelOperatorInv n r Ft).totalDegree ≤ r :=
    kernelOperatorInv_degree r Ft hFt_deg
  have hKK := hP1 (kernelOperatorInv n r Ft) hKinv_deg hKinv_nonneg
  rw [kernelOperator_inv_right r Ft hFt_deg] at hKK
  rw [← hFt_eq] at hKK
  exact lasserre_bound_box_preo_ge_feasible f ((r + 1) * n) hKK

/-- Variant of outline_lemma giving BoxPreordering membership directly. -/
theorem outline_lemma_box_preordering (f : MvPolynomial (Fin n) ℝ) (r : ℕ) (ε : ℝ)
    (_hε : 0 < ε) (hd : f.totalDegree ≤ r)
    (hP1 : ∀ p : MvPolynomial (Fin n) ℝ,
      p.totalDegree ≤ r → IsNonnegOn p (Hypercube n) →
      kernelOperator n r p ∈ BoxPreordering n ((r + 1) * n))
    (hP2 : polySupNorm (kernelOperatorInv n r
      (f - MvPolynomial.C (polyMin f) +
       MvPolynomial.C (ε * (polyMax f - polyMin f))) -
      (f - MvPolynomial.C (polyMin f) +
       MvPolynomial.C (ε * (polyMax f - polyMin f)))) ≤
      ε * (polyMax f - polyMin f)) :
    (f - MvPolynomial.C (polyMin f - ε * (polyMax f - polyMin f))) ∈
    BoxPreordering n ((r + 1) * n) := by
  set Ft := f - MvPolynomial.C (polyMin f) +
    MvPolynomial.C (ε * (polyMax f - polyMin f)) with hFt_def
  have hFt_eq :
      f - MvPolynomial.C (polyMin f - ε * (polyMax f - polyMin f)) = Ft := by
    simp [hFt_def, map_sub, map_mul]; ring
  have hFt_deg : Ft.totalDegree ≤ r := by
    calc Ft.totalDegree
        ≤ max (f - MvPolynomial.C (polyMin f)).totalDegree
          (MvPolynomial.C (ε * (polyMax f - polyMin f))).totalDegree :=
        MvPolynomial.totalDegree_add _ _
      _ ≤ max f.totalDegree 0 := by
        apply max_le_max
        · exact MvPolynomial.totalDegree_sub_C_le _ _
        · exact le_of_eq (MvPolynomial.totalDegree_C _)
      _ ≤ r := by simp [hd]
  have hKinv_nonneg : IsNonnegOn (kernelOperatorInv n r Ft) (Hypercube n) := by
    intro x hx
    have hFt_eval : MvPolynomial.eval x Ft =
        MvPolynomial.eval x f - polyMin f + ε * (polyMax f - polyMin f) := by
      simp [hFt_def, map_sub, map_add, MvPolynomial.eval_C]
    have hFt_bound : ε * (polyMax f - polyMin f) ≤ MvPolynomial.eval x Ft := by
      rw [hFt_eval]; linarith [polyMin_le_eval f x hx]
    have hP2_pt : |MvPolynomial.eval x (kernelOperatorInv n r Ft - Ft)| ≤
        ε * (polyMax f - polyMin f) :=
      polySupNorm_eval_le _ _ hP2 x hx
    have hdiff := abs_le.mp hP2_pt
    simp only [map_sub] at hdiff
    linarith [hdiff.1]
  have hKinv_deg := kernelOperatorInv_degree r Ft hFt_deg
  have hKK := hP1 (kernelOperatorInv n r Ft) hKinv_deg hKinv_nonneg
  rw [kernelOperator_inv_right r Ft hFt_deg] at hKK
  rw [← hFt_eq] at hKK
  exact hKK

/-! ## Helper lemmas for P2 verification -/

/-- Chebyshev coefficient of a constant polynomial: for κ ≠ 0,
    chebyCoeff(C(a), κ) = 0. -/
private theorem chebyCoeff_const_eq_zero (r : ℕ) (a : ℝ) (κ : Fin n → ℕ)
    (hκ : κ ≠ 0) (hκ_mem : κ ∈ multiIndices n r) :
    chebyCoeff n r (MvPolynomial.C a) κ = 0 := by
  -- C(a) = a * 1 = a * T_0, so chebyCoeff(C(a), κ) = a * δ_{0,κ} = 0 for κ ≠ 0
  have h0_mem : (0 : Fin n → ℕ) ∈ multiIndices n r :=
    multiIndices_mem_iff.mpr ⟨by simp [multiDegree], fun _ => Nat.zero_le _⟩
  have : MvPolynomial.C a = MvPolynomial.C a * chebyshevMulti (0 : Fin n → ℕ) := by
    simp [chebyshevMulti, chebyshevT_zero, embedUnivariate]
  rw [this, chebyCoeff_C_mul, chebyCoeff_chebyshev r κ 0 hκ_mem h0_mem]
  rw [ite_eq_right (Ne.symm hκ)]
  simp

/-- Adding a constant to p does not change K_r⁻¹(p) - p.
    Proof: K_r⁻¹ reproduces constants (1/λ₀ = 1), so adding C(a) to both
    K_r⁻¹(p + C(a)) and (p + C(a)) cancels. -/
private theorem kernelOperatorInv_sub_add_const (r : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (a : ℝ) (hp : p.totalDegree ≤ r) :
    kernelOperatorInv n r (p + MvPolynomial.C a) - (p + MvPolynomial.C a) =
    kernelOperatorInv n r p - p := by
  -- It suffices to show K_r⁻¹(p + C(a)) = K_r⁻¹(p) + C(a)
  suffices h : kernelOperatorInv n r (p + MvPolynomial.C a) =
      kernelOperatorInv n r p + MvPolynomial.C a by
    rw [h]; ring
  -- C(a) has degree 0 ≤ r
  have hCa_deg : (MvPolynomial.C a : MvPolynomial (Fin n) ℝ).totalDegree ≤ r := by
    rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le _
  -- p + C(a) has degree ≤ r
  have hpa_deg : (p + MvPolynomial.C a).totalDegree ≤ r := by
    calc (p + MvPolynomial.C a).totalDegree
        ≤ max p.totalDegree (MvPolynomial.C a).totalDegree :=
          MvPolynomial.totalDegree_add _ _
      _ ≤ r := by simp [MvPolynomial.totalDegree_C, hp]
  -- K_r⁻¹ is additive: unfold and use chebyCoeff_add
  simp only [kernelOperatorInv, chebyCoeff_add]
  -- Split the coefficients
  have : ∀ κ ∈ multiIndices n r,
      MvPolynomial.C ((chebyCoeff n r p κ + chebyCoeff n r (MvPolynomial.C a) κ) /
        jacksonCoeffMulti κ r) * chebyshevMulti κ =
      MvPolynomial.C (chebyCoeff n r p κ / jacksonCoeffMulti κ r) * chebyshevMulti κ +
      MvPolynomial.C (chebyCoeff n r (MvPolynomial.C a) κ / jacksonCoeffMulti κ r) *
        chebyshevMulti κ := by
    intro κ _
    rw [add_div, MvPolynomial.C_add, add_mul]
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
  -- The second sum is K_r⁻¹(C(a)) which equals C(a)
  congr 1
  -- Show K_r⁻¹(C(a)) = C(a) using left inverse property
  -- K_r(C(a)) = C(a) since C(a) = a·T_0 and λ_0 = 1
  -- Then K_r⁻¹(C(a)) = K_r⁻¹(K_r(C(a))) = C(a) by left inverse
  change kernelOperatorInv n r (MvPolynomial.C a) = MvPolynomial.C a
  -- First show K_r(C(a)) = C(a)
  have hKCa : kernelOperator n r (MvPolynomial.C a) = MvPolynomial.C a := by
    unfold kernelOperator
    -- chebyCoeff(C(a), κ) = 0 for κ ≠ 0, and = a for κ = 0
    -- So the sum collapses to λ_0 · a · T_0 = 1 · a · 1 = C(a)
    have h0_mem : (0 : Fin n → ℕ) ∈ multiIndices n r :=
      multiIndices_mem_iff.mpr ⟨by simp [multiDegree], fun _ => Nat.zero_le _⟩
    rw [Finset.sum_eq_single 0
      (fun κ hκ hκ0 => by
        rw [chebyCoeff_const_eq_zero r a κ hκ0 hκ, mul_zero, map_zero, zero_mul])
      (fun h => absurd h0_mem h)]
    -- Now: C(jacksonCoeffMulti 0 r * chebyCoeff ... 0) * chebyshevMulti 0 = C(a)
    -- chebyCoeff(C(a), 0) = a (from orthogonality)
    have hc0 : chebyCoeff n r (MvPolynomial.C a) 0 = a := by
      have : MvPolynomial.C a =
          MvPolynomial.C a * chebyshevMulti (0 : Fin n → ℕ) := by
        simp [chebyshevMulti, chebyshevT_zero, embedUnivariate]
      rw [this, chebyCoeff_C_mul, chebyCoeff_chebyshev r 0 0 h0_mem h0_mem,
          ite_eq_left rfl, mul_one]
    -- jacksonCoeffMulti 0 r = ∏ i, jacksonCoeff 0 r = ∏ i, 1 = 1
    have hj0 : jacksonCoeffMulti (0 : Fin n → ℕ) r = 1 := by
      unfold jacksonCoeffMulti
      simp [jacksonCoeff]
    -- chebyshevMulti 0 = 1
    have hT0 : chebyshevMulti (0 : Fin n → ℕ) = (1 : MvPolynomial (Fin n) ℝ) := by
      simp [chebyshevMulti, chebyshevT_zero, embedUnivariate]
    rw [hc0, hj0, one_mul, hT0, mul_one]
  -- Now use left inverse
  have hinv := kernelOperator_inv_left r (MvPolynomial.C a) hCa_deg
  rw [hKCa] at hinv
  exact hinv

/-- K_r⁻¹(p) - p only depends on the non-constant Chebyshev coefficients of p:
    K_r⁻¹(p) - p = ∑_{κ ≠ 0, κ ∈ MI(n,r)} c_κ(1/λ_κ - 1) T_κ. -/
private theorem kernelOperatorInv_sub_expansion (r : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ r) :
    kernelOperatorInv n r p - p =
    ∑ κ ∈ (multiIndices n r).filter (fun κ => κ ≠ 0),
      MvPolynomial.C (chebyCoeff n r p κ * (1 / jacksonCoeffMulti κ r - 1)) *
      chebyshevMulti κ := by
  -- Step 1: K_r⁻¹(p) - p = ∑_{all κ} c_κ(1/λ_κ - 1) T_κ
  have hfull : kernelOperatorInv n r p - p =
      ∑ κ ∈ multiIndices n r,
        MvPolynomial.C (chebyCoeff n r p κ * (1 / jacksonCoeffMulti κ r - 1)) *
        chebyshevMulti κ := by
    have hp_expand := chebyshev_expansion r p hp
    unfold kernelOperatorInv
    conv_lhs => rhs; rw [hp_expand]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro κ hκ
    rw [← sub_mul, ← map_sub]
    congr 1; congr 1
    have hjpos : (0 : ℝ) < jacksonCoeffMulti κ r :=
      jacksonCoeffMulti_pos (fun i => (multiIndices_mem_iff.mp hκ).2 i)
    field_simp
  rw [hfull]
  -- Step 2: The κ = 0 term vanishes because 1/λ_0 - 1 = 0
  -- Split the sum into κ = 0 and κ ≠ 0
  rw [← Finset.sum_filter_add_sum_filter_not (multiIndices n r) (fun κ => κ ≠ 0)]
  -- The sum over κ = 0 (i.e., not (κ ≠ 0) means κ = 0) is zero
  suffices h0 : ∑ κ ∈ (multiIndices n r).filter (fun κ => ¬κ ≠ 0),
      MvPolynomial.C (chebyCoeff n r p κ * (1 / jacksonCoeffMulti κ r - 1)) *
      chebyshevMulti κ = 0 by
    rw [h0, add_zero]
  -- The filter ¬(κ ≠ 0) contains only κ = 0
  have hfilt : (multiIndices n r).filter (fun κ => ¬κ ≠ 0) = {0} := by
    ext κ; simp only [Finset.mem_filter, not_not, Finset.mem_singleton]
    constructor
    · rintro ⟨_, rfl⟩; rfl
    · rintro rfl
      exact ⟨multiIndices_mem_iff.mpr ⟨by simp [multiDegree], fun _ => Nat.zero_le _⟩, rfl⟩
  rw [hfilt, Finset.sum_singleton]
  -- jacksonCoeffMulti 0 r = 1, so 1/1 - 1 = 0
  have hj0 : jacksonCoeffMulti (0 : Fin n → ℕ) r = 1 := by
    unfold jacksonCoeffMulti; simp [jacksonCoeff]
  rw [hj0]; norm_num

/-- The sum in kernel_property_P2, bounded using inverse_eigenvalue_bound
    and the structure of constC, gives a bound in terms of constC/r². -/
private theorem P2_sum_bound (r d : ℕ) (hr : Real.pi * d * Real.sqrt (2 * n) ≤ r) :
    ∑ κ ∈ multiIndices n d,
      (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2) *
      |1 - 1 / jacksonCoeffMulti κ r| ≤
    constC n d / (r : ℝ) ^ 2 := by
  -- Each |1 - 1/λ_κ| ≤ 2nπ²d²/r² by inverse_eigenvalue_bound
  -- Step 1: Bound each term
  have hterm : ∀ κ ∈ multiIndices n d,
      (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2) *
      |1 - 1 / jacksonCoeffMulti κ r| ≤
      (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2) *
      (2 * n * Real.pi ^ 2 * d ^ 2 / (r : ℝ) ^ 2) := by
    intro κ hκ
    apply mul_le_mul_of_nonneg_left (inverse_eigenvalue_bound κ hκ hr) (by positivity)
  -- Step 2: Sum bound
  calc ∑ κ ∈ multiIndices n d,
        (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2) *
        |1 - 1 / jacksonCoeffMulti κ r|
      ≤ ∑ κ ∈ multiIndices n d,
        (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2) *
        (2 * n * Real.pi ^ 2 * d ^ 2 / (r : ℝ) ^ 2) :=
      Finset.sum_le_sum hterm
    _ = (∑ κ ∈ multiIndices n d,
        (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2)) *
        (2 * n * Real.pi ^ 2 * d ^ 2 / (r : ℝ) ^ 2) := by
      rw [← Finset.sum_mul]
    _ ≤ ((multiIndices n d).card *
        Finset.sup' (multiIndices n d)
          ⟨0, multiIndices_mem_iff.mpr ⟨by simp [multiDegree], fun _ => Nat.zero_le _⟩⟩
          (fun κ => (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2))) *
        (2 * ↑n * Real.pi ^ 2 * ↑d ^ 2 / (↑r) ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      -- ∑ f(κ) ≤ |S| * max f(κ)
      have hne : (multiIndices n d).Nonempty :=
        ⟨0, multiIndices_mem_iff.mpr ⟨by simp [multiDegree], fun _ => Nat.zero_le _⟩⟩
      calc ∑ κ ∈ multiIndices n d,
            (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2)
          ≤ ∑ _κ ∈ multiIndices n d,
            Finset.sup' (multiIndices n d) hne
              (fun κ => (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2)) :=
          Finset.sum_le_sum (fun κ hκ =>
            Finset.le_sup' (fun κ => (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2)) hκ)
        _ = (multiIndices n d).card *
            Finset.sup' (multiIndices n d) hne
              (fun κ => (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = constC n d / (r : ℝ) ^ 2 := by
      unfold constC; ring

/-- polySupNorm of the centered polynomial g = f - C((fmin+fmax)/2) is ≤ Δ/2 -/
private theorem polySupNorm_centered_le (f : MvPolynomial (Fin n) ℝ) :
    polySupNorm (f - MvPolynomial.C ((polyMin f + polyMax f) / 2)) ≤
    (polyMax f - polyMin f) / 2 := by
  apply polySupNorm_le_of_bound
  intro x hx
  simp only [map_sub, MvPolynomial.eval_C]
  have hmin := polyMin_le_eval f x hx
  obtain ⟨_, _, hmax_eq⟩ := polyMax_mem f
  have heval_le : MvPolynomial.eval x f ≤ polyMax f := by
    exact le_csSup
      (Hypercube_compact.image (MvPolynomial.continuous_eval f)).bddAbove ⟨x, hx, rfl⟩
  rw [abs_le]
  constructor <;> linarith

/-- Generalized Chebyshev coefficient bound (without normalization):
    |chebyCoeff(p, κ)|² ≤ 2^{w(κ)} · (polySupNorm p)².
    Combines chebyCoeff_sq_le. -/
private theorem chebyCoeff_abs_le_supnorm (r : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ r) (κ : Fin n → ℕ) (hκ : κ ∈ multiIndices n r) :
    |chebyCoeff n r p κ| ≤ (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2) * polySupNorm p := by
  -- polySupNorm p ≥ 0
  have hc_nonneg : 0 ≤ polySupNorm p := by
    obtain ⟨x, hx⟩ := Hypercube_nonempty (n := n)
    exact le_csSup_of_le
      (Hypercube_compact.image
        (continuous_abs.comp (MvPolynomial.continuous_eval p))).bddAbove
      ⟨x, hx, rfl⟩ (abs_nonneg _)
  by_cases hc : polySupNorm p = 0
  · -- polySupNorm = 0: scale p by N to get ‖N·p‖ = 0 ≤ 1,
    -- chebyCoeff_bound gives |N · c_κ| ≤ 2^{w/2} for all N, so c_κ = 0
    rw [hc, mul_zero, abs_nonpos_iff]
    suffices h : ∀ ε : ℝ, 0 < ε → |chebyCoeff n r p κ| ≤ ε by
      by_contra hne
      have habs_pos : 0 < |chebyCoeff n r p κ| := by positivity
      linarith [h _ (half_pos habs_pos)]
    intro ε hε
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2) := by positivity
    -- Scale p by N = 2^{w/2}/ε, so C(N)*p has norm 0 ≤ 1
    -- chebyCoeff_bound gives N*|c_κ| ≤ 2^{w/2}, i.e., |c_κ| ≤ ε
    set N := (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2) / ε with hN_def
    have hN_pos : 0 < N := div_pos h2pos hε
    have hNp_deg : (MvPolynomial.C N * p).totalDegree ≤ r := by
      calc (MvPolynomial.C N * p).totalDegree
          ≤ (MvPolynomial.C N).totalDegree + p.totalDegree :=
            MvPolynomial.totalDegree_mul _ _
        _ = p.totalDegree := by rw [MvPolynomial.totalDegree_C, zero_add]
        _ ≤ r := hp
    have hNp_norm : polySupNorm (MvPolynomial.C N * p) ≤ 1 := by
      apply polySupNorm_le_of_bound
      intro x hx
      rw [map_mul, MvPolynomial.eval_C, abs_mul]
      have heval := polySupNorm_eval_le p 0 (by rw [hc]) x hx
      rw [abs_nonpos_iff.mp heval, abs_zero, mul_zero]
      exact zero_le_one
    have hbound := chebyCoeff_bound r _ hNp_deg hNp_norm κ hκ
    rw [chebyCoeff_C_mul, abs_mul, abs_of_pos hN_pos] at hbound
    -- N * |c_κ| ≤ 2^{w/2}, so |c_κ| ≤ 2^{w/2} / N = ε
    have hle_div : |chebyCoeff n r p κ| ≤ (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2) / N := by
      rw [le_div_iff₀ hN_pos]; linarith
    calc |chebyCoeff n r p κ|
        ≤ (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2) / N := hle_div
      _ = ε := by rw [hN_def, div_div_cancel₀ (ne_of_gt h2pos)]
  · -- polySupNorm p > 0: normalize p to q = C(1/c) * p with ‖q‖ ≤ 1
    have hc_pos : 0 < polySupNorm p := lt_of_le_of_ne hc_nonneg (Ne.symm hc)
    set c := polySupNorm p with hc_def
    set q := MvPolynomial.C (1 / c) * p with hq_def
    have hq_deg : q.totalDegree ≤ r := by
      calc q.totalDegree
          ≤ (MvPolynomial.C (1 / c)).totalDegree + p.totalDegree :=
            MvPolynomial.totalDegree_mul _ _
        _ = p.totalDegree := by rw [MvPolynomial.totalDegree_C, zero_add]
        _ ≤ r := hp
    have hq_norm : polySupNorm q ≤ 1 := by
      apply polySupNorm_le_of_bound
      intro x hx
      rw [hq_def, map_mul, MvPolynomial.eval_C, abs_mul, abs_of_pos (by positivity)]
      rw [one_div, inv_mul_le_iff₀ hc_pos, mul_one]
      exact polySupNorm_eval_le p c le_rfl x hx
    have hqc : chebyCoeff n r q κ = (1 / c) * chebyCoeff n r p κ := by
      rw [hq_def]; exact chebyCoeff_C_mul r (1 / c) p κ
    have hbound := chebyCoeff_bound r q hq_deg hq_norm κ hκ
    rw [hqc, abs_mul, abs_of_pos (by positivity)] at hbound
    calc |chebyCoeff n r p κ|
        = c * ((1 / c) * |chebyCoeff n r p κ|) := by field_simp
      _ ≤ c * (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hbound hc_pos.le
      _ = (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2) * c := mul_comm _ _

/-! ## P2 verification -/

/-- P2 verification for the outline lemma: the key estimate that connects
    the Chebyshev coefficient bound with the constC/r² bound for the shifted
    polynomial Ft.
    Key insight: K_r⁻¹(Ft) - Ft only involves non-constant Chebyshev coefficients,
    which equal those of f. Center f to g = f - C((fmin+fmax)/2) with
    ‖g‖_∞ = Δ/2. Then the bound follows from triangle inequality +
    chebyCoeff_bound applied to g + inverse_eigenvalue_bound + constC definition. -/
theorem P2_outline_verification (r d : ℕ) (f : MvPolynomial (Fin n) ℝ)
    (hd : f.totalDegree ≤ d) (hdr : d ≤ r)
    (hfr : f.totalDegree ≤ r)
    (hr : Real.pi * d * Real.sqrt (2 * n) ≤ r) :
    let ε := constC n d / (r : ℝ) ^ 2
    let Ft := f - MvPolynomial.C (polyMin f) +
      MvPolynomial.C (ε * (polyMax f - polyMin f))
    polySupNorm (kernelOperatorInv n r Ft - Ft) ≤
      ε * (polyMax f - polyMin f) := by
  -- Introduce local abbreviations
  intro ε Ft
  set Delta := polyMax f - polyMin f with hDelta_def
  -- Delta ≥ 0
  have hDelta_nonneg : 0 ≤ Delta := sub_nonneg.mpr (polyMin_le_polyMax f)
  -- Step 1: Ft has totalDegree ≤ r
  have hFt_deg : Ft.totalDegree ≤ r := by
    calc Ft.totalDegree
        ≤ max (f - MvPolynomial.C (polyMin f)).totalDegree
          (MvPolynomial.C (ε * Delta)).totalDegree :=
        MvPolynomial.totalDegree_add _ _
      _ ≤ max f.totalDegree 0 := by
        apply max_le_max
        · exact MvPolynomial.totalDegree_sub_C_le _ _
        · exact le_of_eq (MvPolynomial.totalDegree_C _)
      _ ≤ r := by simp [hfr]
  -- Step 2: The centered polynomial g = f - C((fmin+fmax)/2)
  set mid := (polyMin f + polyMax f) / 2 with hmid_def
  set g := f - MvPolynomial.C mid with hg_def
  -- g has degree ≤ d ≤ r
  have hg_deg : g.totalDegree ≤ d := by
    calc g.totalDegree ≤ f.totalDegree := MvPolynomial.totalDegree_sub_C_le _ _
      _ ≤ d := hd
  have hg_deg_r : g.totalDegree ≤ r := le_trans hg_deg hdr
  -- polySupNorm(g) ≤ Delta/2
  have hg_norm : polySupNorm g ≤ Delta / 2 := polySupNorm_centered_le f
  -- Step 3: The key bound
  -- For each κ ≠ 0 in multiIndices n d:
  --   chebyCoeff(Ft, κ) = chebyCoeff(g, κ)  (constants cancel for κ ≠ 0)
  --   |chebyCoeff(g, κ)| ≤ 2^{w(κ)/2} · polySupNorm(g) ≤ 2^{w(κ)/2} · Delta/2
  -- K_r⁻¹(Ft) - Ft = ∑_κ chebyCoeff(Ft,κ)·(1/λ_κ-1)·T_κ (κ=0 vanishes since 1/λ₀-1=0)
  -- By triangle inequality + |T_κ| ≤ 1:
  --   polySupNorm(K_r⁻¹(Ft)-Ft) ≤ ∑_{κ≠0} |chebyCoeff(g,κ)| · |1/λ_κ-1|
  --   ≤ (Delta/2) · ∑_κ 2^{w(κ)/2} · |1-1/λ_κ|
  --   ≤ (Delta/2) · constC/r²     (by P2_sum_bound)
  -- Step 3a: Apply the P2 sum bound
  have hP2_sum := P2_sum_bound r d hr
  -- Step 3b: Assemble the key bound
  -- polySupNorm g ≥ 0
  have hg_norm_nonneg : 0 ≤ polySupNorm g := by
    obtain ⟨x, hx⟩ := Hypercube_nonempty (n := n)
    exact le_csSup_of_le
      (Hypercube_compact.image
        (continuous_abs.comp (MvPolynomial.continuous_eval g))).bddAbove
      ⟨x, hx, rfl⟩ (abs_nonneg _)
  -- constC/r² ≥ 0
  have constC_div_nonneg : 0 ≤ constC n d / (r : ℝ) ^ 2 := by
    apply div_nonneg _ (sq_nonneg _)
    unfold constC
    apply mul_nonneg (mul_nonneg _ _) (by positivity)
    · exact Nat.cast_nonneg _
    · have h0_mem : (fun (_ : Fin n) => 0) ∈ multiIndices n d :=
        multiIndices_mem_iff.mpr ⟨by simp [multiDegree], fun _ => Nat.zero_le _⟩
      exact le_of_lt (lt_of_lt_of_le (by positivity : (0:ℝ) < _)
        (Finset.le_sup' (fun κ => (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2)) h0_mem))
  have key : polySupNorm (kernelOperatorInv n r Ft - Ft) ≤
      (Delta / 2) * (constC n d / (r : ℝ) ^ 2) := by
    -- Step A: Reduce to K_r⁻¹(g) - g via centering
    have hFt_eq : Ft = f + MvPolynomial.C (-polyMin f + ε * Delta) := by
      simp [Ft, Delta]; ring
    have hFt_sub : kernelOperatorInv n r Ft - Ft =
        kernelOperatorInv n r f - f := by
      rw [hFt_eq]; exact kernelOperatorInv_sub_add_const r f _ hfr
    have hf_eq : f = g + MvPolynomial.C mid := by rw [hg_def]; ring
    have hg_sub : kernelOperatorInv n r f - f =
        kernelOperatorInv n r g - g := by
      conv_lhs => rw [hf_eq]
      exact kernelOperatorInv_sub_add_const r g mid hg_deg_r
    rw [hFt_sub, hg_sub]
    -- Step B: Expand K_r⁻¹(g) - g
    have hexpand := kernelOperatorInv_sub_expansion r g hg_deg_r
    rw [hexpand]
    -- Step C: Bound pointwise
    apply polySupNorm_le_of_bound
    intro x hx
    rw [map_sum]
    -- Pointwise bound: triangle ineq + |T_κ| ≤ 1
    have hpw_bound :
        |∑ κ ∈ (multiIndices n r).filter (fun κ => κ ≠ 0),
          MvPolynomial.eval x
            (MvPolynomial.C (chebyCoeff n r g κ *
              (1 / jacksonCoeffMulti κ r - 1)) * chebyshevMulti κ)|
        ≤ ∑ κ ∈ (multiIndices n r).filter (fun κ => κ ≠ 0),
          |chebyCoeff n r g κ| * |1 - 1 / jacksonCoeffMulti κ r| := by
      calc _ ≤ ∑ κ ∈ (multiIndices n r).filter (fun κ => κ ≠ 0),
            |MvPolynomial.eval x
              (MvPolynomial.C (chebyCoeff n r g κ *
                (1 / jacksonCoeffMulti κ r - 1)) * chebyshevMulti κ)| :=
          abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum; intro κ _
          rw [map_mul, MvPolynomial.eval_C, abs_mul]
          calc |chebyCoeff n r g κ * (1 / jacksonCoeffMulti κ r - 1)| *
                  |MvPolynomial.eval x (chebyshevMulti κ)|
              ≤ |chebyCoeff n r g κ * (1 / jacksonCoeffMulti κ r - 1)| * 1 :=
                mul_le_mul_of_nonneg_left
                  (chebyshevMulti_bounded κ x hx) (abs_nonneg _)
            _ = |chebyCoeff n r g κ| * |1 - 1 / jacksonCoeffMulti κ r| := by
              rw [mul_one, abs_mul]; congr 1
              rw [show 1 / jacksonCoeffMulti κ r - 1 =
                -(1 - 1 / jacksonCoeffMulti κ r) from by ring, abs_neg]
    calc |∑ κ ∈ (multiIndices n r).filter (fun κ => κ ≠ 0),
          MvPolynomial.eval x
            (MvPolynomial.C (chebyCoeff n r g κ *
              (1 / jacksonCoeffMulti κ r - 1)) * chebyshevMulti κ)|
        ≤ ∑ κ ∈ (multiIndices n r).filter (fun κ => κ ≠ 0),
          |chebyCoeff n r g κ| * |1 - 1 / jacksonCoeffMulti κ r| :=
        hpw_bound
      -- Step D: Restrict sum to multiIndices n d (chebyCoeff = 0 for deg > d)
      _ = ∑ κ ∈ (multiIndices n d).filter (fun κ => κ ≠ 0),
          |chebyCoeff n r g κ| * |1 - 1 / jacksonCoeffMulti κ r| := by
        symm; apply Finset.sum_subset
        · intro κ hκ; rw [Finset.mem_filter] at hκ ⊢
          exact ⟨by
            rw [multiIndices_mem_iff] at hκ ⊢
            exact ⟨le_trans hκ.1.1 hdr, fun i => le_trans (hκ.1.2 i) hdr⟩, hκ.2⟩
        · intro κ hκ_r hκ_not_d
          have hκ_ne0 := (Finset.mem_filter.mp hκ_r).2
          have hκ_deg_gt : d < multiDegree κ := by
            by_contra h; push Not at h
            exact hκ_not_d (Finset.mem_filter.mpr ⟨multiDegree_le_mem h, hκ_ne0⟩)
          rw [chebyCoeff_zero_of_degree_lt r g κ (by omega), abs_zero, zero_mul]
      -- Step E: Bound |chebyCoeff(g,κ)| ≤ 2^{w/2} * polySupNorm g
      _ ≤ ∑ κ ∈ (multiIndices n d).filter (fun κ => κ ≠ 0),
          ((2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2) * polySupNorm g) *
          |1 - 1 / jacksonCoeffMulti κ r| := by
        apply Finset.sum_le_sum; intro κ hκ
        have hκ_d := (Finset.mem_filter.mp hκ).1
        have hκ_r : κ ∈ multiIndices n r := by
          rw [multiIndices_mem_iff] at hκ_d ⊢
          exact ⟨le_trans hκ_d.1 hdr, fun i => le_trans (hκ_d.2 i) hdr⟩
        exact mul_le_mul_of_nonneg_right
          (chebyCoeff_abs_le_supnorm r g hg_deg_r κ hκ_r) (abs_nonneg _)
      -- Step F: Factor out polySupNorm g, extend to full multiIndices n d
      _ = polySupNorm g *
          ∑ κ ∈ (multiIndices n d).filter (fun κ => κ ≠ 0),
            (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2) *
            |1 - 1 / jacksonCoeffMulti κ r| := by
        rw [Finset.mul_sum]; congr 1; ext κ; ring
      _ ≤ polySupNorm g *
          ∑ κ ∈ multiIndices n d,
            (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2) *
            |1 - 1 / jacksonCoeffMulti κ r| := by
        apply mul_le_mul_of_nonneg_left _ hg_norm_nonneg
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro κ _ _; exact mul_nonneg (by positivity) (abs_nonneg _)
      -- Step G: Apply P2_sum_bound
      _ ≤ polySupNorm g * (constC n d / (r : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hP2_sum hg_norm_nonneg
      _ ≤ (Delta / 2) * (constC n d / (r : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hg_norm constC_div_nonneg
  -- Step 4: (Delta/2) · constC/r² ≤ constC/r² · Delta = ε · Delta
  -- because Delta/2 ≤ Delta (since Delta ≥ 0)
  -- Step 4: (Delta/2) * constC/r² ≤ ε * Delta
  -- When r > 0: constC/r² ≥ 0 and Delta/2 * K ≤ K * Delta since Delta ≥ 0
  -- When r = 0: Lean's div by 0 gives constC/0 = 0, so both sides ≤ 0
  have constC_nonneg : 0 ≤ constC n d := by
    unfold constC
    apply mul_nonneg (mul_nonneg _ _) (by positivity)
    · exact Nat.cast_nonneg _
    · have hne : (multiIndices n d).Nonempty :=
        ⟨0, multiIndices_mem_iff.mpr ⟨by simp [multiDegree], fun _ => Nat.zero_le _⟩⟩
      have h0_mem : (fun (_ : Fin n) => 0) ∈ multiIndices n d :=
        multiIndices_mem_iff.mpr ⟨by simp [multiDegree], fun _ => Nat.zero_le _⟩
      have h0_val : (0 : ℝ) < (2 : ℝ) ^ ((hammingWeight (fun (_ : Fin n) => 0) : ℝ) / 2) :=
        by positivity
      exact le_of_lt (lt_of_lt_of_le h0_val
        (Finset.le_sup' (fun κ => (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2)) h0_mem))
  have hkey_rhs : (Delta / 2) * (constC n d / (r : ℝ) ^ 2) ≤ ε * Delta := by
    have hcr : 0 ≤ constC n d / (↑r) ^ 2 := div_nonneg constC_nonneg (sq_nonneg _)
    nlinarith [mul_comm (Delta / 2) (constC n d / (↑r) ^ 2)]
  linarith


end OptimalConvergenceRates

end
