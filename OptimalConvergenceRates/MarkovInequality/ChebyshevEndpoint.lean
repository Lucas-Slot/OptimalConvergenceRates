/-
  OptimalConvergenceRates/MarkovInequality/ChebyshevEndpoint.lean

  Endpoint and near-endpoint Chebyshev extrapolation estimates used in lower-bound proofs.
-/
import OptimalConvergenceRates.BasicNotions.SOSVector
import Mathlib.Algebra.Polynomial.Eval.Coeff
import OptimalConvergenceRates.MarkovInequality.MarkovInequalityCorollaries

open MvPolynomial Finset Polynomial

noncomputable section

namespace OptimalConvergenceRates

/-- Chebyshev extrapolation at the `d⁻²` scale, with an explicit constant parameter
`C`; applications instantiate `C` with an absolute expression depending only on `L`. -/
theorem chebyshev_extrapolate_d2_scale
    (L C M : ℝ) (_hL : 0 < L) (_hC : 0 < C) (hC_one : 1 ≤ C)
    (d : ℕ) (_hd : 2 ≤ d) (h : Polynomial ℝ) (hdeg : h.natDegree ≤ d)
    (s : ℝ) (_hs0 : 0 ≤ s) (hs_half : s ≤ 1 / 2)
    (_hs_d : s ≤ L / (d : ℝ) ^ 2)
    (hbound : ∀ x : ℝ, |x| ≤ Real.sqrt (1 - s) → |h.eval x| ≤ M)
    (hC_sufficient :
      ∀ x : ℝ, |x| ≤ 1 + L / (d : ℝ) ^ 2 →
        |(chebyshevT d).eval (|x| / Real.sqrt (1 - s))| ≤ C) :
    ∀ x : ℝ, |x| ≤ 1 + L / (d : ℝ) ^ 2 → |h.eval x| ≤ C * M := by
  intro x hx
  set A := Real.sqrt (1 - s)
  have hA_pos : 0 < A := by
    dsimp [A]
    apply Real.sqrt_pos.mpr
    linarith
  have hA_nonneg : 0 ≤ A := le_of_lt hA_pos
  have hM_nonneg : 0 ≤ M := by
    have h0 : |(0 : ℝ)| ≤ Real.sqrt (1 - s) := by
      simp
    have := hbound 0 h0
    linarith [abs_nonneg (h.eval 0)]
  by_cases hinside : |x| ≤ A
  · have hm := hbound x (by simpa [A] using hinside)
    calc |h.eval x| ≤ M := hm
      _ ≤ C * M := by
          calc M = 1 * M := by ring
            _ ≤ C * M := mul_le_mul_of_nonneg_right hC_one hM_nonneg
  · push_neg at hinside
    set y := x / A
    set q : Polynomial ℝ := h.comp (Polynomial.C A * Polynomial.X)
    have hq_eval : q.eval y = h.eval x := by
      rw [show q.eval y = h.eval (A * y) by simp [q, Polynomial.eval_comp]]
      simp [y]
      field_simp [hA_pos.ne']
    have hy_abs : |y| = |x| / A := by
      simp [y, abs_div, abs_of_pos hA_pos]
    have hy_ge : 1 ≤ |y| := by
      rw [hy_abs]
      rw [one_le_div hA_pos]
      exact le_of_lt hinside
    have hlin_deg : (Polynomial.C A * Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
      exact (Polynomial.natDegree_C_mul_le A Polynomial.X).trans Polynomial.natDegree_X_le
    have hqdeg : q.natDegree ≤ d := by
      calc q.natDegree ≤ h.natDegree * (Polynomial.C A * Polynomial.X : Polynomial ℝ).natDegree :=
            Polynomial.natDegree_comp_le
        _ ≤ h.natDegree * 1 := Nat.mul_le_mul_left _ hlin_deg
        _ = h.natDegree := Nat.mul_one _
        _ ≤ d := hdeg
    have hq_sup : polySupNormUni q ≤ M := by
      apply polySupNormUni_le_of_bound
      intro t ht1 ht2
      simp only [q, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      apply hbound
      have ht_abs : |t| ≤ 1 := abs_le.mpr ⟨ht1, ht2⟩
      have : |A * t| ≤ A := by
        rw [abs_mul, abs_of_nonneg hA_nonneg]
        calc A * |t| ≤ A * 1 := mul_le_mul_of_nonneg_left ht_abs hA_nonneg
          _ = A := by ring
      simpa [A, mul_comm] using this
    have hcheb := chebyshevT_extremal d q hqdeg y hy_ge
    rw [hq_eval] at hcheb
    have hT_nonneg : 0 ≤ (chebyshevT d).eval |y| := chebyshevT_nonneg_ge_one d |y| hy_ge
    have hT_bound : (chebyshevT d).eval |y| ≤ C := by
      have hc := hC_sufficient x hx
      have hy_abs_arg : |x| / Real.sqrt (1 - s) = |y| := by
        simp [y, A, abs_div, abs_of_pos hA_pos]
      rw [hy_abs_arg] at hc
      exact (abs_le.mp hc).2
    calc |h.eval x| ≤ polySupNormUni q * (chebyshevT d).eval |y| := hcheb
      _ ≤ M * (chebyshevT d).eval |y| :=
          mul_le_mul_of_nonneg_right hq_sup hT_nonneg
      _ ≤ M * C := mul_le_mul_of_nonneg_left hT_bound hM_nonneg
      _ = C * M := by ring

/-- Affine Chebyshev extrapolation. -/
theorem affine_chebyshev_extrapolate
    (L C M a b u : ℝ) (_hL : 0 < L) (_hC : 0 < C) (hC_one : 1 ≤ C)
    (hab : a < b) (d : ℕ) (hd : 2 ≤ d)
    (h : Polynomial ℝ) (hdeg : h.natDegree ≤ d)
    (hbound : ∀ t : ℝ, a ≤ t → t ≤ b → |h.eval t| ≤ M)
    (hC_sufficient : ∀ y : ℝ,
      (|y| ≤ 1 + 2 * L / (d : ℝ) ^ 2) → |(chebyshevT d).eval y| ≤ C)
    (hdist : u ∈ Set.Icc (a - L * (b - a) / (d : ℝ) ^ 2)
        (b + L * (b - a) / (d : ℝ) ^ 2)) :
    |h.eval u| ≤ C * M := by
  set w := b - a
  set mid := (a + b) / 2
  set scale := w / 2
  have hw_pos : 0 < w := by dsimp [w]; linarith
  have hscale_pos : 0 < scale := by dsimp [scale]; linarith
  have hdR_pos : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hd)
  have hdR_sq_pos : 0 < (d : ℝ) ^ 2 := sq_pos_of_pos hdR_pos
  have hM_nonneg : 0 ≤ M := by
    have := hbound a (le_refl a) (le_of_lt hab)
    linarith [abs_nonneg (h.eval a)]
  set y := (u - mid) / scale with hy_def
  set q : Polynomial ℝ := h.comp (Polynomial.C mid + Polynomial.C scale * Polynomial.X)
  have hq_eval : q.eval y = h.eval u := by
    rw [show q.eval y = h.eval (mid + scale * y) by simp [q, Polynomial.eval_comp]]
    rw [hy_def]
    field_simp [hscale_pos.ne']
    ring_nf
  have hlin_deg :
      (Polynomial.C mid + Polynomial.C scale * Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
    calc (Polynomial.C mid + Polynomial.C scale * Polynomial.X : Polynomial ℝ).natDegree
        ≤ max (Polynomial.C mid).natDegree
            (Polynomial.C scale * Polynomial.X).natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ max 0 1 := by
          apply max_le_max
          · exact (Polynomial.natDegree_C _).le
          · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
      _ = 1 := by simp
  have hqdeg : q.natDegree ≤ d := by
    calc q.natDegree
        ≤ h.natDegree *
            (Polynomial.C mid + Polynomial.C scale * Polynomial.X : Polynomial ℝ).natDegree :=
          Polynomial.natDegree_comp_le
      _ ≤ h.natDegree * 1 := Nat.mul_le_mul_left _ hlin_deg
      _ = h.natDegree := Nat.mul_one _
      _ ≤ d := hdeg
  have hq_sup : polySupNormUni q ≤ M := by
    apply polySupNormUni_le_of_bound
    intro t ht1 ht2
    simp only [q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    apply hbound
    · dsimp [mid, scale, w]
      nlinarith [hab, ht1]
    · dsimp [mid, scale, w]
      nlinarith [hab, ht2]
  have hy_bound : |y| ≤ 1 + 2 * L / (d : ℝ) ^ 2 := by
    set R := 1 + 2 * L / (d : ℝ) ^ 2
    have hleft : -R * scale ≤ u - mid := by
      have hl := hdist.1
      calc -R * scale
          = a - L * w / (d : ℝ) ^ 2 - mid := by
              dsimp [R, scale, mid, w]
              field_simp [hdR_sq_pos.ne']
              ring
        _ ≤ u - mid := by nlinarith
    have hright : u - mid ≤ R * scale := by
      have hr := hdist.2
      calc u - mid
          ≤ b + L * w / (d : ℝ) ^ 2 - mid := by nlinarith
        _ = R * scale := by
              dsimp [R, scale, mid, w]
              field_simp [hdR_sq_pos.ne']
              ring
    rw [abs_le]
    constructor
    · rw [hy_def]
      rw [le_div_iff₀ hscale_pos]
      exact hleft
    · rw [hy_def]
      rw [div_le_iff₀ hscale_pos]
      exact hright
  by_cases hy_inside : |y| ≤ 1
  · have ht := abs_le.mp hy_inside
    rw [← hq_eval]
    have hm : |q.eval y| ≤ M := (polySupNormUni_eval_le q y ht.1 ht.2).trans hq_sup
    calc |q.eval y| ≤ M := hm
      _ ≤ C * M := by
          calc M = 1 * M := by ring
            _ ≤ C * M := mul_le_mul_of_nonneg_right hC_one hM_nonneg
  · push_neg at hy_inside
    have hy_ge : 1 ≤ |y| := le_of_lt hy_inside
    have hcheb := chebyshev_extremal_pointwise q d hqdeg y hy_ge
    rw [hq_eval] at hcheb
    have hT := hC_sufficient y hy_bound
    calc |h.eval u| ≤ |(chebyshevT d).eval y| * polySupNormUni q := hcheb
      _ ≤ |(chebyshevT d).eval y| * M :=
          mul_le_mul_of_nonneg_left hq_sup (abs_nonneg _)
      _ ≤ C * M := mul_le_mul_of_nonneg_right hT hM_nonneg

/-- Chebyshev growth on the `4 / d^2` exterior scale used by the affine endpoint step. -/
theorem chebyshevT_abs_le_exp_six_near_one
    (d : ℕ) (hd : 2 ≤ d) (y : ℝ) (hy : |y| ≤ 1 + 4 / (d : ℝ) ^ 2) :
    |(chebyshevT d).eval y| ≤ Real.exp 6 := by
  have h_one_sided : ∀ z : ℝ, 1 ≤ z → z ≤ 1 + 4 / (d : ℝ) ^ 2 →
      (chebyshevT d).eval z ≤ Real.exp 6 := by
    intro z hz1 hz
    have hd1 : 1 ≤ d := by omega
    have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
    have hd_sq_pos : (0 : ℝ) < (d : ℝ) ^ 2 := sq_pos_of_pos hd_pos
    have hdelta_nonneg : 0 ≤ z - 1 := by linarith
    have hdelta_le : z - 1 ≤ 4 / (d : ℝ) ^ 2 := by linarith
    have hsqrt_arg : z ^ 2 - 1 ≤ (4 / (d : ℝ)) ^ 2 := by
      have hdelta_le_one : z - 1 ≤ 1 := by
        calc z - 1 ≤ 4 / (d : ℝ) ^ 2 := hdelta_le
          _ ≤ 1 := by
              rw [div_le_iff₀ hd_sq_pos]
              nlinarith [show (2 : ℝ) ≤ d by exact_mod_cast hd]
      have hz_plus : z + 1 ≤ 3 := by linarith
      have hprod : (z - 1) * (z + 1) ≤ (4 / (d : ℝ) ^ 2) * 3 := by
        apply mul_le_mul hdelta_le hz_plus
        · linarith
        · positivity
      calc z ^ 2 - 1 = (z - 1) * (z + 1) := by ring
        _ ≤ (4 / (d : ℝ) ^ 2) * 3 := hprod
        _ ≤ (4 / (d : ℝ)) ^ 2 := by
            field_simp [hd_pos.ne']
            nlinarith
    have hsqrt_le : Real.sqrt (z ^ 2 - 1) ≤ 4 / (d : ℝ) := by
      calc Real.sqrt (z ^ 2 - 1) ≤ Real.sqrt ((4 / (d : ℝ)) ^ 2) :=
            Real.sqrt_le_sqrt hsqrt_arg
        _ = 4 / (d : ℝ) := by
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
            positivity
    have hz_le' : z ≤ 1 + 2 / (d : ℝ) := by
      calc z ≤ 1 + 4 / (d : ℝ) ^ 2 := hz
        _ ≤ 1 + 2 / (d : ℝ) := by
            rw [add_le_add_iff_left]
            rw [div_le_div_iff₀ hd_sq_pos hd_pos]
            nlinarith [show (2 : ℝ) ≤ d by exact_mod_cast hd]
    have hbase : z + Real.sqrt (z ^ 2 - 1) ≤ 1 + 6 / (d : ℝ) := by
      calc z + Real.sqrt (z ^ 2 - 1)
          ≤ (1 + 2 / (d : ℝ)) + 4 / (d : ℝ) := add_le_add hz_le' hsqrt_le
        _ = 1 + 6 / (d : ℝ) := by ring
    have hbase_nonneg : 0 ≤ z + Real.sqrt (z ^ 2 - 1) := by positivity
    have hT := chebyshevT_upper_bound d z hz1 hd1
    calc (chebyshevT d).eval z
        ≤ (z + Real.sqrt (z ^ 2 - 1)) ^ d := hT
      _ ≤ (1 + 6 / (d : ℝ)) ^ d := pow_le_pow_left₀ hbase_nonneg hbase d
      _ ≤ Real.exp 6 := one_add_div_pow_le_exp 6 (by norm_num) d hd1
  by_cases hyin : |y| ≤ 1
  · have hyI := abs_le.mp hyin
    exact (chebyshevT_abs_le_one d y hyI.1 hyI.2).trans (by
      calc (1 : ℝ) ≤ Real.exp 0 := by simp
        _ ≤ Real.exp 6 := Real.exp_le_exp.mpr (by norm_num))
  · push_neg at hyin
    have hyge : 1 ≤ |y| := le_of_lt hyin
    have hdeg : (chebyshevT d).natDegree ≤ d := by rw [natDegree_chebyshevT]
    have hext := chebyshevT_extremal d (chebyshevT d) hdeg y hyge
    have hsup : polySupNormUni (chebyshevT d) ≤ 1 := by
      apply polySupNormUni_le_of_bound
      intro x hx1 hx2
      exact chebyshevT_abs_le_one d x hx1 hx2
    have hT_nonneg : 0 ≤ (chebyshevT d).eval |y| := chebyshevT_nonneg_ge_one d |y| hyge
    have hT_bound : (chebyshevT d).eval |y| ≤ Real.exp 6 := h_one_sided |y| hyge hy
    calc |(chebyshevT d).eval y|
        ≤ polySupNormUni (chebyshevT d) * (chebyshevT d).eval |y| := hext
      _ ≤ 1 * (chebyshevT d).eval |y| := mul_le_mul_of_nonneg_right hsup hT_nonneg
      _ ≤ Real.exp 6 := by linarith

/-- Weighted endpoint estimate for a polynomial vector.

The vector norm is represented by `vecNorm`. The constant `C` is an absolute
constant large enough for the affine Chebyshev extrapolation step with `L = 2`. -/
theorem weighted_endpoint_estimate
    {N d : ℕ} (V : Fin N → Polynomial ℝ) (A C : ℝ)
    (hd : 2 ≤ d) (hA : 0 ≤ A) (hC : 0 < C) (hC_one : 1 ≤ C)
    (hC_affine : ∀ y : ℝ,
      |y| ≤ 1 + 4 / (d : ℝ) ^ 2 → |(chebyshevT d).eval y| ≤ C)
    (hdeg : ∀ i, (V i).natDegree ≤ d)
    (hV0 : ∀ i, (V i).eval 0 = 0)
    (hbound : ∀ t : ℝ, (d : ℝ) ^ (-2 : ℤ) ≤ t → t ≤ 1 →
      vecNorm (fun i => (V i).eval t) ≤ A * Real.sqrt t)
    (b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ (d : ℝ) ^ (-2 : ℤ)) :
    vecNorm (fun i => (V i).eval b) ≤ C * A * (d : ℝ) * b := by
  let rho : ℝ := 1 / (d : ℝ) ^ 2
  let W : Fin N → Polynomial ℝ := fun i => Polynomial.divX (V i)
  have hdR_pos : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hd)
  have hdR_ne : (d : ℝ) ≠ 0 := ne_of_gt hdR_pos
  have hzpow_eq : (d : ℝ) ^ (-2 : ℤ) = rho := by
    dsimp [rho]
    rw [zpow_neg, one_div]
    rfl
  have hb_le_rho : b ≤ rho := by
    rwa [← hzpow_eq]
  have hrho_pos : 0 < rho := by
    dsimp [rho]
    positivity
  have hrho_nonneg : 0 ≤ rho := le_of_lt hrho_pos
  have hV_eq : ∀ i, Polynomial.X * W i = V i := by
    intro i
    dsimp [W]
    have hcoeff : (V i).coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact hV0 i
    have h := Polynomial.X_mul_divX_add (V i)
    rw [hcoeff, Polynomial.C_0, add_zero] at h
    exact h
  have h_eval : ∀ i t, (V i).eval t = t * (W i).eval t := by
    intro i t
    rw [← hV_eq i]
    simp
  have hdegW : ∀ i, (W i).natDegree ≤ d := by
    intro i
    dsimp [W]
    exact Polynomial.natDegree_divX_le.trans (hdeg i)
  have hsqrt_lower : ∀ {t : ℝ}, rho ≤ t → 1 / (d : ℝ) ≤ Real.sqrt t := by
    intro t ht
    apply Real.le_sqrt_of_sq_le
    dsimp [rho] at ht
    field_simp [hdR_ne] at ht ⊢
    nlinarith
  have hW_bound : ∀ t : ℝ, rho ≤ t → t ≤ 1 →
      vecNorm (fun i => (W i).eval t) ≤ A * (d : ℝ) := by
    intro t ht ht1
    have ht_nonneg : 0 ≤ t := le_trans hrho_nonneg ht
    have ht_pos : 0 < t := lt_of_lt_of_le hrho_pos ht
    have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
    have hV_norm : vecNorm (fun i => (V i).eval t) =
        t * vecNorm (fun i => (W i).eval t) := by
      calc
        vecNorm (fun i => (V i).eval t)
            = vecNorm (fun i => t * (W i).eval t) := by
                congr
                ext i
                exact h_eval i t
        _ = t * vecNorm (fun i => (W i).eval t) :=
            vecNorm_smul_nonneg t ht_nonneg (fun i => (W i).eval t)
    have hbase := hbound t (by rwa [hzpow_eq]) ht1
    rw [hV_norm] at hbase
    have hdiv : vecNorm (fun i => (W i).eval t) ≤ A * Real.sqrt t / t := by
      rw [le_div_iff₀ ht_pos]
      rwa [mul_comm]
    have hratio : Real.sqrt t / t ≤ (d : ℝ) := by
      have hsqrt_ge := hsqrt_lower ht
      have hsqrt_sq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht_nonneg
      calc
        Real.sqrt t / t = 1 / Real.sqrt t := by
          field_simp [hsqrt_pos.ne']
          rw [hsqrt_sq]
        _ ≤ (d : ℝ) := by
          rw [div_le_iff₀ hsqrt_pos]
          field_simp [hdR_ne] at hsqrt_ge ⊢
          nlinarith
    calc
      vecNorm (fun i => (W i).eval t) ≤ A * Real.sqrt t / t := hdiv
      _ = A * (Real.sqrt t / t) := by ring
      _ ≤ A * (d : ℝ) := mul_le_mul_of_nonneg_left hratio hA
  have hd_ge_two : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hrho_le_one : rho ≤ 1 := by
    dsimp [rho]
    have hsq_ge : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    simpa [one_div] using inv_le_one_of_one_le₀ hsq_ge
  have hrho_lt_one : rho < 1 := by
    dsimp [rho]
    field_simp [hdR_ne]
    nlinarith
  have hdist : b ∈ Set.Icc (rho - 2 * (1 - rho) / (d : ℝ) ^ 2)
      (1 + 2 * (1 - rho) / (d : ℝ) ^ 2) := by
    constructor
    · have hlower_nonpos : rho - 2 * (1 - rho) / (d : ℝ) ^ 2 ≤ 0 := by
        dsimp [rho]
        field_simp [hdR_ne]
        nlinarith
      linarith
    · have hb_le_one : b ≤ 1 := le_trans hb_le_rho hrho_le_one
      have hnonneg : 0 ≤ 2 * (1 - rho) / (d : ℝ) ^ 2 := by
        apply div_nonneg
        · nlinarith
        · positivity
      linarith
  have hVb_norm : vecNorm (fun i => (V i).eval b) =
      b * vecNorm (fun i => (W i).eval b) := by
    calc
      vecNorm (fun i => (V i).eval b)
          = vecNorm (fun i => b * (W i).eval b) := by
              congr
              ext i
              exact h_eval i b
      _ = b * vecNorm (fun i => (W i).eval b) :=
          vecNorm_smul_nonneg b hb0 (fun i => (W i).eval b)
  by_cases hWb_zero : vecNorm (fun i => (W i).eval b) = 0
  · rw [hVb_norm, hWb_zero, mul_zero]
    positivity
  · let e : Fin N → ℝ := fun i => (W i).eval b / vecNorm (fun j => (W j).eval b)
    let H : Polynomial ℝ := ∑ i : Fin N, Polynomial.C (e i) * W i
    have hH_eval : ∀ t : ℝ, H.eval t = vecDot e (fun i => (W i).eval t) := by
      intro t
      dsimp [H, vecDot]
      change (Polynomial.evalRingHom t) (∑ i : Fin N, Polynomial.C (e i) * W i) =
        ∑ i : Fin N, e i * Polynomial.eval t (W i)
      simp [Polynomial.evalRingHom, mul_comm]
    have hHdeg : H.natDegree ≤ d := by
      dsimp [H]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i _
      exact (Polynomial.natDegree_C_mul_le _ _).trans (hdegW i)
    have hHbound : ∀ t : ℝ, rho ≤ t → t ≤ 1 → |H.eval t| ≤ A * (d : ℝ) := by
      intro t ht ht1
      rw [hH_eval]
      exact (abs_vecDot_unit_le hWb_zero (fun i => (W i).eval t)).trans (hW_bound t ht ht1)
    have hC_affine' : ∀ y : ℝ,
        |y| ≤ 1 + 2 * 2 / (d : ℝ) ^ 2 → |(chebyshevT d).eval y| ≤ C := by
      intro y hy
      apply hC_affine
      nlinarith
    have hH_at_b := affine_chebyshev_extrapolate 2 C (A * (d : ℝ)) rho 1 b
      (by norm_num) hC hC_one (by linarith [hrho_lt_one]) d hd H hHdeg hHbound hC_affine' hdist
    have hH_b_eq : H.eval b = vecNorm (fun i => (W i).eval b) := by
      rw [hH_eval]
      exact vecDot_unit_self hWb_zero
    rw [hH_b_eq, abs_of_nonneg (vecNorm_nonneg _)] at hH_at_b
    calc
      vecNorm (fun i => (V i).eval b)
          = b * vecNorm (fun i => (W i).eval b) := hVb_norm
      _ ≤ b * (C * (A * (d : ℝ))) := mul_le_mul_of_nonneg_left hH_at_b hb0
      _ = C * A * (d : ℝ) * b := by ring

end OptimalConvergenceRates

end

