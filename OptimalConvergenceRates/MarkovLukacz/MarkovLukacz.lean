/-
  OptimalConvergenceRates/MarkovLukacz/MarkovLukacz.lean

  Markov-Lukacs representation of nonnegative univariate polynomials on [-1,1].
-/
import OptimalConvergenceRates.BasicNotions.SumsOfSquares
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Data.Real.Sqrt

open Polynomial Real

noncomputable section

namespace OptimalConvergenceRates

/-! ## Auxiliary: polynomial degree lemmas -/

private theorem natDegree_one_sub_X_sq_le :
    (1 - X ^ 2 : Polynomial ℝ).natDegree ≤ 2 :=
  (natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_pow_le_of_le 2 natDegree_X_le))

private theorem natDegree_one_sub_X_sq :
    (1 - X ^ 2 : Polynomial ℝ).natDegree = 2 := by
  have h1 : (1 - X ^ 2 : Polynomial ℝ) = C (-1) * X ^ 2 + C 1 := by
    simp only [map_neg, map_one]; ring
  rw [h1, natDegree_add_eq_left_of_degree_lt,
    natDegree_C_mul_X_pow _ _ (by norm_num : (-1 : ℝ) ≠ 0)]
  rw [degree_C (by norm_num : (1 : ℝ) ≠ 0), degree_C_mul_X_pow _ (by norm_num : (-1 : ℝ) ≠ 0)]
  exact WithBot.coe_lt_coe.mpr (by norm_num)

/-! ## The substitution x = cos θ -/

/-- p(cos θ) ≥ 0 for all θ when p ≥ 0 on [-1,1] -/
theorem eval_cos_nonneg (p : Polynomial ℝ)
    (hp : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → 0 ≤ p.eval x) (θ : ℝ) :
    0 ≤ p.eval (cos θ) :=
  hp _ ⟨neg_one_le_cos θ, cos_le_one θ⟩

/-! ## Core algebraic decomposition -/

/-! ### Sub-lemmas for the Lukács decomposition -/

/-- Interior roots of a polynomial nonneg on [-1,1] have even multiplicity. -/
private theorem even_rootMultiplicity_of_nonneg_interior (p : Polynomial ℝ) (a : ℝ)
    (ha : a ∈ Set.Ioo (-1 : ℝ) 1) (hpa : IsRoot p a)
    (hp : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → 0 ≤ p.eval x)
    (hp0 : p ≠ 0) : Even (p.rootMultiplicity a) := by
  set m := p.rootMultiplicity a
  obtain ⟨q, hpq, hq_not_dvd⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp0 a
  have hqa : q.eval a ≠ 0 := by
    intro hqa; exact hq_not_dvd (dvd_iff_isRoot.mpr (by rwa [IsRoot.def]))
  have hm_pos : 0 < m := (rootMultiplicity_pos hp0).mpr hpa
  by_contra h_not_even
  rw [Nat.not_even_iff_odd] at h_not_even
  -- q has constant sign near a (continuity + q(a) ≠ 0)
  have hq_cont : Continuous (fun x => q.eval x) := q.continuous
  have hqa_abs_pos : 0 < |q.eval a| := abs_pos.mpr hqa
  obtain ⟨δ, hδ_pos, hq_sign⟩ := Metric.continuousAt_iff.mp hq_cont.continuousAt
    (|q.eval a| / 2) (by linarith)
  -- Pick points left and right of a within [-1,1]
  have ha_lb : -1 < a := ha.1
  have ha_ub : a < 1 := ha.2
  -- Pick x to the left: x = a - min(δ/2, (a+1)/2)
  set ε := min (δ/2) (min ((a + 1)/2) ((1 - a)/2)) with hε_def
  have hε_pos : 0 < ε := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  -- x = a - ε is in (-1, a) and in the δ-ball of a
  have hε_le1 : ε ≤ (a + 1) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hε_le2 : ε ≤ (1 - a) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hx_left_mem : a - ε ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hx_left_dist : dist (a - ε) a < δ := by
    rw [Real.dist_eq, show a - ε - a = -ε by ring, abs_neg, abs_of_pos hε_pos]
    calc ε ≤ δ / 2 := min_le_left _ _
      _ < δ := by linarith
  -- x = a + ε is in (a, 1) and in the δ-ball of a
  have hx_right_mem : a + ε ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hx_right_dist : dist (a + ε) a < δ := by
    rw [Real.dist_eq, show a + ε - a = ε by ring, abs_of_pos hε_pos]
    calc ε ≤ δ / 2 := min_le_left _ _
      _ < δ := by linarith
  -- q(a-ε) and q(a+ε) have same sign as q(a)
  have hq_left := hq_sign hx_left_dist
  have hq_right := hq_sign hx_right_dist
  rw [Real.dist_eq] at hq_left hq_right
  -- m is odd, so (a-ε-a)^m and (a+ε-a)^m have opposite signs → one of p(a±ε) < 0
  rcases ne_iff_lt_or_gt.mp hqa with hqa_neg | hqa_pos
  · -- q(a) < 0: q(a+ε) < 0, so p(a+ε) = ε^m * q(a+ε) < 0
    have hq_right_neg : q.eval (a + ε) < 0 := by
      have h1 : q.eval (a + ε) - q.eval a ≤ |q.eval (a + ε) - q.eval a| := le_abs_self _
      linarith [abs_of_neg hqa_neg]
    have : p.eval (a + ε) < 0 := by
      rw [hpq]; simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C]
      exact mul_neg_of_pos_of_neg (pow_pos (by linarith : (0 : ℝ) < a + ε - a) m) hq_right_neg
    linarith [hp _ hx_right_mem]
  · -- q(a) > 0: p(a-ε) = (-ε)^m * q(a-ε). m odd, so (-ε)^m = -(ε^m) < 0. q(a-ε) > 0.
    have hq_left_pos : 0 < q.eval (a - ε) := by
      -- From |q(a-ε) - q(a)| < |q(a)|/2 and q(a) > 0, we get q(a-ε) > q(a)/2 > 0
      have h1 : q.eval a - q.eval (a - ε) ≤ |q.eval (a - ε) - q.eval a| := by
        calc q.eval a - q.eval (a - ε)
            = -(q.eval (a - ε) - q.eval a) := by ring
          _ ≤ |q.eval (a - ε) - q.eval a| := neg_le_abs _
      linarith [abs_of_pos hqa_pos]
    have : p.eval (a - ε) < 0 := by
      rw [hpq]; simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C]
      have h_neg_ε : a - ε - a = -ε := by ring
      rw [h_neg_ε]
      exact mul_neg_of_neg_of_pos (h_not_even.pow_neg_iff.mpr (by linarith)) hq_left_pos
    linarith [hp _ hx_left_mem]

/-- Combining interior even-multiplicity factors: if p >= 0 on [-1,1] has a root a in (-1,1),
    then p = (X - C a)^2 * q where q >= 0 on [-1,1] and deg q <= deg p - 2. -/
private theorem factor_interior_root (p : Polynomial ℝ) (a : ℝ)
    (ha : a ∈ Set.Ioo (-1 : ℝ) 1) (hpa : IsRoot p a) (hp0 : p ≠ 0)
    (hp : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → 0 ≤ p.eval x) :
    ∃ q : Polynomial ℝ, p = (X - C a) ^ 2 * q ∧
      (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → 0 ≤ q.eval x) ∧
      q.natDegree + 2 ≤ p.natDegree := by
  -- The root has even multiplicity >= 2
  have h_even := even_rootMultiplicity_of_nonneg_interior p a ha hpa hp hp0
  have hm_pos : 0 < p.rootMultiplicity a := (rootMultiplicity_pos hp0).mpr hpa
  -- So (X - C a)^2 divides p
  have h_dvd : (X - C a) ^ 2 ∣ p := by
    have : 2 ≤ p.rootMultiplicity a := by
      obtain ⟨k, hk⟩ := h_even
      omega
    exact (pow_dvd_pow _ this).trans (pow_rootMultiplicity_dvd p a)
  obtain ⟨q, hpq⟩ := h_dvd
  refine ⟨q, hpq, ?_, ?_⟩
  · -- q >= 0 on [-1,1]: at x != a, (x-a)^2 > 0 and p(x) = (x-a)^2 * q(x) >= 0, so q(x) >= 0.
    -- At x = a, q(a) >= 0 by continuity (q(x) >= 0 for x near a, x != a).
    intro x hx
    by_cases hxa : x = a
    · -- q(a) >= 0 by continuity: q(y) >= 0 for all y in [-1,1] \ {a}, and q is continuous
      rw [hxa]
      by_contra h_neg
      push_neg at h_neg
      -- q(a) < 0, so by continuity, q(y) < 0 near a, but then p(y) = (y-a)^2 * q(y) < 0
      -- for y near a, y != a. But p >= 0 on [-1,1]. Contradiction.
      have hq_cont := q.continuous
      obtain ⟨δ, hδ_pos, hq_near⟩ := Metric.continuousAt_iff.mp hq_cont.continuousAt
        (-q.eval a / 2) (by linarith)
      -- Pick y = a + min(delta/2, (1-a)/2) != a in [-1,1]
      have hε_bound : min (δ / 2) ((1 - a) / 2) ≤ (1 - a) / 2 := min_le_right _ _
      have hε_bound2 : min (δ / 2) ((1 - a) / 2) ≤ δ / 2 := min_le_left _ _
      have hε_pos : (0 : ℝ) < min (δ / 2) ((1 - a) / 2) :=
        lt_min (by linarith) (by have := ha.2; linarith)
      set y := a + min (δ / 2) ((1 - a) / 2)
      have hy_mem : y ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [ha.1], by simp [y]; linarith⟩
      have hy_ne : y ≠ a := by simp [y]; linarith
      have hy_near : dist y a < δ := by
        rw [Real.dist_eq, show y - a = min (δ / 2) ((1 - a) / 2) by simp [y],
          abs_of_pos hε_pos]; linarith
      have hq_neg : q.eval y < 0 := by
        have := hq_near hy_near
        rw [Real.dist_eq] at this
        linarith [le_abs_self (q.eval y - q.eval a)]
      have hp_neg : p.eval y < 0 := by
        rw [hpq]; simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C]
        exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (sub_ne_zero.mpr hy_ne)) hq_neg
      linarith [hp y hy_mem]
    · -- x != a: (x-a)^2 > 0, and p(x) >= 0, so q(x) = p(x)/(x-a)^2 >= 0
      have hxa_sq : 0 < (x - a) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hxa)
      have hp_x := hp x hx
      rw [hpq] at hp_x
      simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at hp_x
      exact nonneg_of_mul_nonneg_right hp_x hxa_sq
  · -- deg q + 2 = deg p (since (X-C a)^2 and q are both nonzero)
    have hq0 : q ≠ 0 := by
      intro hq0; rw [hq0, mul_zero] at hpq; exact hp0 hpq
    have h_X_sub : (X - C a) ^ 2 ≠ (0 : Polynomial ℝ) := pow_ne_zero _ (X_sub_C_ne_zero a)
    have h1 : p.natDegree = ((X - C a) ^ 2 * q).natDegree := by rw [hpq]
    have h2 : ((X - C a) ^ 2 * q).natDegree = ((X - C a) ^ 2).natDegree + q.natDegree :=
      natDegree_mul h_X_sub hq0
    have h3 : ((X - C a) ^ 2).natDegree = 2 := by rw [natDegree_pow, natDegree_X_sub_C]
    omega

/-- If p >= 0 on [-1,1] and (X - C a)^2 | p for some a in [-1,1],
    then the quotient q = p / (X - C a)^2 is also >= 0 on [-1,1].
    More general than factor_interior_root: works for boundary points too. -/
private theorem factor_sq_root (p : Polynomial ℝ) (a : ℝ)
    (ha : a ∈ Set.Icc (-1 : ℝ) 1) (hp0 : p ≠ 0)
    (hmult : 2 ≤ p.rootMultiplicity a)
    (hp : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → 0 ≤ p.eval x) :
    ∃ q : Polynomial ℝ, p = (X - C a) ^ 2 * q ∧
      (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → 0 ≤ q.eval x) ∧
      q.natDegree + 2 ≤ p.natDegree := by
  have h_dvd : (X - C a) ^ 2 ∣ p :=
    (pow_dvd_pow _ hmult).trans (pow_rootMultiplicity_dvd p a)
  obtain ⟨q, hpq⟩ := h_dvd
  refine ⟨q, hpq, ?_, ?_⟩
  · -- q >= 0 on [-1,1]
    intro x hx
    by_cases hxa : x = a
    · -- q(a) >= 0 by continuity
      rw [hxa]
      by_contra h_neg
      push_neg at h_neg
      have hq_cont := q.continuous
      obtain ⟨δ, hδ_pos, hq_near⟩ := Metric.continuousAt_iff.mp hq_cont.continuousAt
        (-q.eval a / 2) (by linarith)
      -- Pick y != a in [-1,1] within delta of a.
      -- Since a in [-1,1] and [-1,1] has more than one point, we can find such y.
      -- If a < 1, pick y = a + eps. If a = 1, pick y = a - eps.
      rcases lt_or_eq_of_le ha.2 with ha_lt_1 | ha_eq_1
      · -- a < 1: pick y > a
        set ε := min (δ / 2) ((1 - a) / 2) with hε_def
        have hε_pos : (0 : ℝ) < ε := lt_min (by linarith) (by linarith)
        set y := a + ε
        have hy_mem : y ∈ Set.Icc (-1 : ℝ) 1 :=
          ⟨by linarith [ha.1], by simp [y]; linarith [min_le_right (δ / 2) ((1 - a) / 2)]⟩
        have hy_ne : y ≠ a := by simp [y]; linarith
        have hy_near : dist y a < δ := by
          rw [Real.dist_eq, show y - a = ε by simp [y], abs_of_pos hε_pos]
          linarith [min_le_left (δ / 2) ((1 - a) / 2)]
        have hq_neg : q.eval y < 0 := by
          have := hq_near hy_near
          rw [Real.dist_eq] at this
          linarith [le_abs_self (q.eval y - q.eval a)]
        have hp_neg : p.eval y < 0 := by
          rw [hpq]; simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C]
          exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (sub_ne_zero.mpr hy_ne)) hq_neg
        linarith [hp y hy_mem]
      · -- a = 1: pick y < a
        set ε := min (δ / 2) ((a + 1) / 2) with hε_def
        have hε_pos : (0 : ℝ) < ε := lt_min (by linarith) (by rw [ha_eq_1]; norm_num)
        set y := a - ε
        have hy_mem : y ∈ Set.Icc (-1 : ℝ) 1 :=
          ⟨by linarith [min_le_right (δ / 2) ((a + 1) / 2)], by linarith⟩
        have hy_ne : y ≠ a := by simp [y]; linarith
        have hy_near : dist y a < δ := by
          rw [Real.dist_eq, show y - a = -ε by simp [y], abs_neg, abs_of_pos hε_pos]
          linarith [min_le_left (δ / 2) ((a + 1) / 2)]
        have hq_neg : q.eval y < 0 := by
          have := hq_near hy_near
          rw [Real.dist_eq] at this
          linarith [le_abs_self (q.eval y - q.eval a)]
        have hp_neg : p.eval y < 0 := by
          rw [hpq]; simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C]
          exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (sub_ne_zero.mpr hy_ne)) hq_neg
        linarith [hp y hy_mem]
    · -- x != a
      have hxa_sq : 0 < (x - a) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hxa)
      have hp_x := hp x hx
      rw [hpq] at hp_x
      simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at hp_x
      exact nonneg_of_mul_nonneg_right hp_x hxa_sq
  · -- deg q + 2 = deg p
    have hq0 : q ≠ 0 := by
      intro hq0; rw [hq0, mul_zero] at hpq; exact hp0 hpq
    have h_X_sub : (X - C a) ^ 2 ≠ (0 : Polynomial ℝ) := pow_ne_zero _ (X_sub_C_ne_zero a)
    have h1 : p.natDegree = ((X - C a) ^ 2 * q).natDegree := by rw [hpq]
    have h2 : ((X - C a) ^ 2 * q).natDegree = ((X - C a) ^ 2).natDegree + q.natDegree :=
      natDegree_mul h_X_sub hq0
    have h3 : ((X - C a) ^ 2).natDegree = 2 := by rw [natDegree_pow, natDegree_X_sub_C]
    omega


/-! ### Brahmagupta-Fibonacci: Lukacs form is closed under multiplication -/

set_option maxHeartbeats 400000 in
-- Needed for exhaustive quadratic sign/root analysis and polynomial coefficient normalization.
private theorem lukacs_deg_le_two (p : Polynomial ℝ) (_hp0 : p ≠ 0)
    (hdeg : p.natDegree ≤ 2) (r : ℕ) (hr : p.natDegree ≤ r)
    (hp_nonneg : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → 0 ≤ p.eval x) :
    ∃ (α β : Polynomial ℝ),
      p = α ^ 2 + (1 - X ^ 2) * β ^ 2 ∧
      (α ^ 2).natDegree ≤ r + 1 ∧
      ((1 - X ^ 2) * β ^ 2).natDegree ≤ r + 1 := by
  -- Handle constant polynomial case (degree 0)
  by_cases h_const : p.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero h_const]
    have hc_nn : 0 ≤ p.coeff 0 := by
      have := hp_nonneg 0 ⟨by norm_num, by norm_num⟩
      rw [eq_C_of_natDegree_eq_zero h_const] at this; simp only [eval_C] at this; exact this
    refine ⟨C (Real.sqrt (p.coeff 0)), 0, ?_, ?_, ?_⟩
    · have h1 : (C (Real.sqrt (p.coeff 0))) ^ 2 = C (p.coeff 0) := by
        rw [sq, ← C_mul, ← sq, Real.sq_sqrt hc_nn]
      rw [h1]; simp
    · have h1 : (C (Real.sqrt (p.coeff 0))) ^ 2 = C (p.coeff 0) := by
        rw [sq, ← C_mul, ← sq, Real.sq_sqrt hc_nn]
      rw [h1]; simp
    · simp
  -- Now p has degree >= 1, so r >= 1
  have hr_pos : 1 ≤ r := by omega
  -- Write p = a*X^2 + b*X + c
  set a := p.coeff 2 with ha_def
  set b := p.coeff 1 with hb_def
  set c := p.coeff 0 with hc_def
  have hp_eq : p = C a * X ^ 2 + C b * X + C c := by
    ext n; simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    rcases n with _ | n
    · simp [hc_def]
    · rcases n with _ | n
      · simp [hb_def]
      · rcases n with _ | n
        · simp [ha_def]
        · simp [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < n + 3)]
  have hc_nn : 0 ≤ c := by
    have := hp_nonneg 0 ⟨by norm_num, by norm_num⟩; rw [hp_eq] at this
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, add_zero, zero_add] at this
    exact this
  have hp1 : 0 ≤ a + b + c := by
    have := hp_nonneg 1 ⟨by norm_num, by norm_num⟩; rw [hp_eq] at this; simp at this; linarith
  have hm1 : 0 ≤ a - b + c := by
    have := hp_nonneg (-1) ⟨by norm_num, by norm_num⟩; rw [hp_eq] at this; simp at this; linarith
  have hac_nn : 0 ≤ a + c := by linarith
  have hac_ge_abs_b : |b| ≤ a + c := abs_le.mpr ⟨by linarith, by linarith⟩
  have hac_sq_ge : b ^ 2 ≤ (a + c) ^ 2 := by nlinarith [sq_abs b, sq_nonneg (a + c - |b|)]
  set D := (a + c) ^ 2 - b ^ 2 with hD_def
  have hD_nn : 0 ≤ D := by linarith
  set sqD := Real.sqrt D
  have hsqD_nn : 0 ≤ sqD := Real.sqrt_nonneg _
  have hsqD_sq : sqD ^ 2 = D := Real.sq_sqrt hD_nn
  set f_sq := (c - a + sqD) / 2 with hf_sq_def
  have hf_sq_nn : 0 ≤ f_sq := by
    apply div_nonneg _ two_pos.le
    by_cases h4ac : b ^ 2 ≤ 4 * a * c
    · have h1 : (a - c) ^ 2 ≤ D := by rw [hD_def]; nlinarith
      have h2 : |a - c| ≤ sqD := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt h1
      linarith [le_abs_self (a - c)]
    · push_neg at h4ac
      suffices h_ca : c > a by linarith
      by_contra h_not; push_neg at h_not
      by_cases ha_pos : (0 : ℝ) < a
      · have hb_le_2a : |b| ≤ 2 * a := by linarith
        have hx_star_mem : -b / (2 * a) ∈ Set.Icc (-1 : ℝ) 1 := by
          constructor
          · rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 * a)]; linarith [neg_abs_le b]
          · rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * a)]; linarith [le_abs_self b]
        have h_at_min := hp_nonneg (-b / (2 * a)) hx_star_mem
        rw [hp_eq] at h_at_min
        simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at h_at_min
        have h_val : a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c =
            c - b ^ 2 / (4 * a) := by
          field_simp; ring
        have h_nonneg : 0 ≤ c - b ^ 2 / (4 * a) := by linarith
        have h4a_pos : (0 : ℝ) < 4 * a := by linarith
        have h_mul := mul_nonneg (le_of_lt h4a_pos) h_nonneg
        rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt h4a_pos)] at h_mul; linarith
      · push_neg at ha_pos
        have ha0 : a = 0 := by linarith
        have hc0 : c = 0 := by linarith
        have hb0 : b = 0 := by
          have h := hac_ge_abs_b; rw [ha0, hc0] at h
          simp only [add_zero, abs_nonpos_iff] at h; exact h
        rw [ha0, hc0, hb0] at h4ac; simp at h4ac
  have hf_sq_le_c : f_sq ≤ c := by
    rw [hf_sq_def]
    have : sqD ≤ a + c := by
      rw [← Real.sqrt_sq hac_nn]; exact Real.sqrt_le_sqrt (by rw [hD_def]; nlinarith)
    linarith
  have hd_sq_nn : 0 ≤ a + f_sq := by rw [hf_sq_def]; linarith [hac_nn, hsqD_nn]
  set f := Real.sqrt f_sq
  have hf_sq_eq : f ^ 2 = f_sq := Real.sq_sqrt hf_sq_nn
  set d := Real.sqrt (a + f_sq)
  have hd_sq_eq : d ^ 2 = a + f_sq := Real.sq_sqrt hd_sq_nn
  have he0_nn : 0 ≤ c - f_sq := by linarith
  have h_quad : b ^ 2 = 4 * (a + f_sq) * (c - f_sq) := by
    have h1 : sqD = 2 * f_sq - c + a := by rw [hf_sq_def]; linarith
    have h2 : sqD ^ 2 = (2 * f_sq - c + a) ^ 2 := by rw [h1]
    rw [hsqD_sq, hD_def] at h2
    nlinarith
  by_cases hd_zero : d = 0
  · have ha_fsq_zero : a + f_sq = 0 := by
      have := hd_sq_eq; rw [hd_zero] at this; simp at this; linarith
    have hb_zero : b = 0 := by
      have hb_sq : b ^ 2 = 0 := by rw [h_quad, ha_fsq_zero]; ring
      exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hb_sq
    refine ⟨C (Real.sqrt (c - f_sq)), C (Real.sqrt f_sq), ?_, ?_, ?_⟩
    · have h1 : (C (Real.sqrt (c - f_sq))) ^ 2 = C (c - f_sq) := by
        rw [sq, ← C_mul, ← sq, Real.sq_sqrt he0_nn]
      have h2 : (C (Real.sqrt f_sq)) ^ 2 = C f_sq := by
        rw [sq, ← C_mul, ← sq, Real.sq_sqrt hf_sq_nn]
      rw [hp_eq, h1, h2, hb_zero]
      have ha_eq : a = -f_sq := by linarith
      rw [ha_eq]
      simp only [map_zero, zero_mul, add_zero, map_neg, map_sub]
      ring
    · have : C (Real.sqrt (c - f_sq)) ^ 2 = C (c - f_sq) := by
        rw [sq, ← C_mul, ← sq, Real.sq_sqrt he0_nn]
      rw [this]; simp
    · have : C (Real.sqrt f_sq) ^ 2 = C f_sq := by
        rw [sq, ← C_mul, ← sq, Real.sq_sqrt hf_sq_nn]
      rw [this]
      calc ((1 - X ^ 2) * C f_sq).natDegree
          ≤ (1 - X ^ 2 : Polynomial ℝ).natDegree + (C f_sq).natDegree := natDegree_mul_le
        _ ≤ 2 + 0 := Nat.add_le_add natDegree_one_sub_X_sq_le (by simp)
        _ ≤ r + 1 := by omega
  · have hd_pos : 0 < d := by
      rcases lt_or_eq_of_le (Real.sqrt_nonneg (a + f_sq)) with h | h
      · exact h
      · exact absurd h.symm hd_zero
    set e_val := b / (2 * d) with he_val_def
    have h_2de : 2 * d * e_val = b := by
      rw [he_val_def]; field_simp [ne_of_gt hd_pos]
    have h_ef_sum : e_val ^ 2 + f ^ 2 = c := by
      have h_afsq_pos : (0 : ℝ) < a + f_sq := by nlinarith [hd_sq_eq, sq_nonneg d]
      have h_e_sq : e_val ^ 2 * (4 * (a + f_sq)) = b ^ 2 := by
        rw [he_val_def, div_pow]
        have : (2 * d) ^ 2 = 4 * (a + f_sq) := by nlinarith [hd_sq_eq]
        rw [this, div_mul_cancel₀ _ (by positivity : (4 : ℝ) * (a + f_sq) ≠ 0)]
      rw [hf_sq_eq]
      nlinarith [sq_nonneg e_val, sq_nonneg f]
    have h_df_diff : d ^ 2 - f ^ 2 = a := by rw [hd_sq_eq, hf_sq_eq]; ring
    refine ⟨C d * X + C e_val, C f, ?_, ?_, ?_⟩
    · conv_lhs => rw [hp_eq, ← h_df_diff, ← h_2de, ← h_ef_sum]
      simp only [C_sub, C_add, C_mul, C_pow, map_ofNat]
      ring
    · calc ((C d * X + C e_val) ^ 2).natDegree
          ≤ 2 * (C d * X + C e_val).natDegree := natDegree_pow_le_of_le 2 le_rfl
        _ ≤ 2 * 1 := by
            apply Nat.mul_le_mul_left
            calc (C d * X + C e_val).natDegree
                ≤ max (C d * X).natDegree (C e_val).natDegree := natDegree_add_le _ _
              _ ≤ max 1 0 := max_le_max (by calc (C d * X).natDegree
                      ≤ (C d).natDegree + X.natDegree := natDegree_mul_le
                    _ = 0 + 1 := by simp
                    _ = 1 := by ring) (by simp)
              _ = 1 := by norm_num
        _ = 2 := by ring
        _ ≤ r + 1 := by omega
    · calc ((1 - X ^ 2) * (C f) ^ 2).natDegree
          ≤ (1 - X ^ 2 : Polynomial ℝ).natDegree + ((C f) ^ 2).natDegree := natDegree_mul_le
        _ ≤ 2 + 0 := Nat.add_le_add natDegree_one_sub_X_sq_le (by simp)
        _ ≤ r + 1 := by omega

/-! ### Lukacs decomposition

The proof is by strong induction on the degree of p.
- Zero polynomial: trivial.
- Interior root in (-1,1): factor out (X - C a)^2 (even multiplicity), recurse.
- Boundary root at x = 1 or x = -1 with multiplicity >= 2: factor out (X - C a)^2, recurse.
- No interior roots, boundary multiplicities <= 1: use lukacs_deg_le_two for degree <= 2,
  factor via irreducible divisor for degree >= 3.
-/

/-- If p >= 0 on [-1,1] and p has no roots in (-1,1), then p > 0 on (-1,1). -/
private theorem pos_on_interior_of_no_roots (p : Polynomial ℝ)
    (hp_nonneg : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → 0 ≤ p.eval x)
    (hp_no_roots : ∀ a : ℝ, a ∈ Set.Ioo (-1 : ℝ) 1 → ¬IsRoot p a) :
    ∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 → 0 < p.eval x := by
  intro x hx
  have h1 : 0 ≤ p.eval x := hp_nonneg x (Set.Ioo_subset_Icc_self hx)
  have h2 : p.eval x ≠ 0 := fun h => hp_no_roots x hx (by rwa [IsRoot.def])
  exact lt_of_le_of_ne h1 (Ne.symm h2)

/-- Closure: nonneg on open (-1,1) → nonneg on closed [-1,1] for polynomials (by continuity). -/
private theorem nonneg_Ioo_to_Icc (f : Polynomial ℝ)
    (hf : ∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 → 0 ≤ f.eval x) :
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → 0 ≤ f.eval x := by
  intro x hx
  by_contra h_neg; push_neg at h_neg
  obtain ⟨δ, hδ_pos, hδ_near⟩ := Metric.continuousAt_iff.mp f.continuous.continuousAt
    (-f.eval x / 2) (by linarith)
  set ε := min (δ / 2) 1 with hε_def
  have hε_pos : (0 : ℝ) < ε := lt_min (by linarith) one_pos
  have hε_le : ε ≤ δ / 2 := min_le_left _ _
  have : ∃ y : ℝ, y ∈ Set.Ioo (-1 : ℝ) 1 ∧ dist y x < δ := by
    rcases hx.1.eq_or_lt with rfl | hx_left
    · refine ⟨-1 + ε, ⟨by linarith, by linarith [min_le_right (δ/2) (1:ℝ)]⟩, ?_⟩
      rw [Real.dist_eq, show -1 + ε - -1 = ε from by ring, abs_of_pos hε_pos]; linarith
    · rcases hx.2.eq_or_lt with rfl | hx_right
      · refine ⟨1 - ε, ⟨by linarith [min_le_right (δ/2) (1:ℝ)], by linarith⟩, ?_⟩
        rw [Real.dist_eq, show 1 - ε - 1 = -ε from by ring, abs_neg, abs_of_pos hε_pos]
        linarith
      · exact ⟨x, ⟨hx_left, hx_right⟩, by simp [hδ_pos]⟩
  obtain ⟨y, hy_mem, hy_dist⟩ := this
  have h1 := hf y hy_mem
  have h2 := hδ_near hy_dist
  rw [Real.dist_eq] at h2
  linarith [le_abs_self (f.eval y - f.eval x)]

/-- Any polynomial of degree ≥ 3 over ℝ has a monic divisor of degree exactly 2.
    Proof: get a monic irreducible factor q₁. If deg q₁ = 2, done.
    If deg q₁ = 1, the quotient p/q₁ has degree ≥ 2, so it has a monic irreducible factor q₂.
    If deg q₂ = 2, use q₂. If deg q₂ = 1, use q₁*q₂ (monic, degree 2). -/
private theorem exists_monic_deg_two_factor (p : Polynomial ℝ) (hdeg : 3 ≤ p.natDegree) :
    ∃ (q : Polynomial ℝ), q.Monic ∧ q.natDegree = 2 ∧ q ∣ p := by
  have hp0 : p ≠ 0 := by intro hp0; rw [hp0, natDegree_zero] at hdeg; omega
  have hp_not_unit : ¬IsUnit p := by
    intro ⟨u, hu⟩; have := natDegree_coe_units u; rw [hu] at this; omega
  obtain ⟨q₁, hq₁_monic, hq₁_irr, hq₁_dvd⟩ := exists_monic_irreducible_factor p hp_not_unit
  have hq₁_deg_le : q₁.natDegree ≤ 2 := hq₁_irr.natDegree_le_two
  have hq₁_deg_pos : 0 < q₁.natDegree := hq₁_irr.natDegree_pos
  rcases Nat.eq_or_lt_of_le hq₁_deg_le with hq₁_eq_2 | hq₁_lt_2
  · -- q₁ has degree 2
    exact ⟨q₁, hq₁_monic, hq₁_eq_2, hq₁_dvd⟩
  · -- q₁ has degree 1
    have hq₁_deg : q₁.natDegree = 1 := by omega
    obtain ⟨s, hps⟩ := hq₁_dvd
    have hs0 : s ≠ 0 := right_ne_zero_of_mul (hps ▸ hp0)
    have hs_deg : s.natDegree ≥ 2 := by
      have : s.natDegree + q₁.natDegree = p.natDegree := by
        rw [hps, add_comm]; exact (natDegree_mul hq₁_monic.ne_zero hs0).symm
      omega
    have hs_not_unit : ¬IsUnit s := by
      intro ⟨u, hu⟩; have := natDegree_coe_units u; rw [hu] at this; omega
    obtain ⟨q₂, hq₂_monic, hq₂_irr, hq₂_dvd⟩ := exists_monic_irreducible_factor s hs_not_unit
    have hq₂_deg_le : q₂.natDegree ≤ 2 := hq₂_irr.natDegree_le_two
    have hq₂_deg_pos : 0 < q₂.natDegree := hq₂_irr.natDegree_pos
    rcases Nat.eq_or_lt_of_le hq₂_deg_le with hq₂_eq_2 | hq₂_lt_2
    · -- q₂ has degree 2: use q₂
      exact ⟨q₂, hq₂_monic, hq₂_eq_2, hq₂_dvd.trans (Dvd.intro_left q₁ hps.symm)⟩
    · -- q₂ has degree 1: use q₁ * q₂ (monic, degree 2)
      have hq₂_deg : q₂.natDegree = 1 := by omega
      refine ⟨q₁ * q₂, hq₁_monic.mul hq₂_monic, ?_, ?_⟩
      · rw [natDegree_mul hq₁_monic.ne_zero hq₂_monic.ne_zero, hq₁_deg, hq₂_deg]
      · obtain ⟨t, hst⟩ := hq₂_dvd
        rw [hps, hst, ← mul_assoc]
        exact dvd_mul_right _ _

set_option maxHeartbeats 400000 in
-- The composition proof expands the Brahmagupta-Fibonacci identity and tracks tight degree
-- bounds across the constructed Lukacs witnesses.
/-- Composition of Lukacs decompositions via Brahmagupta-Fibonacci identity with degree bounds.
    If q (deg 2) and s have Lukacs decompositions, then p = q * s has one too.
    Uses q.natDegree = 2 crucially: α₁ has deg ≤ 1 and β₁ has deg 0, giving
    tight degree bounds on the composed polynomials. -/
private theorem lukacs_compose (q s : Polynomial ℝ) (r : ℕ)
    (hr : 3 ≤ r)
    (_hq_deg : q.natDegree = 2)
    (_hs_deg_r : s.natDegree ≤ r - 2)
    (α₁ β₁ α₂ β₂ : Polynomial ℝ)
    (hq_eq : q = α₁ ^ 2 + (1 - X ^ 2) * β₁ ^ 2)
    (hα₁_deg : (α₁ ^ 2).natDegree ≤ 3)
    (hβ₁_deg : ((1 - X ^ 2) * β₁ ^ 2).natDegree ≤ 3)
    (hs_eq : s = α₂ ^ 2 + (1 - X ^ 2) * β₂ ^ 2)
    (hα₂_deg : (α₂ ^ 2).natDegree ≤ r - 1)
    (hβ₂_deg : ((1 - X ^ 2) * β₂ ^ 2).natDegree ≤ r - 1) :
    ∃ (A B : Polynomial ℝ),
      q * s = A ^ 2 + (1 - X ^ 2) * B ^ 2 ∧
      (A ^ 2).natDegree ≤ r + 1 ∧
      ((1 - X ^ 2) * B ^ 2).natDegree ≤ r + 1 := by
  refine ⟨α₁ * α₂ + (1 - X ^ 2) * (β₁ * β₂),
          α₁ * β₂ - β₁ * α₂, ?_, ?_, ?_⟩
  · -- Brahmagupta-Fibonacci identity
    rw [hq_eq, hs_eq]; ring
  · -- Degree bound for A² = (α₁*α₂ + W*β₁*β₂)²
    -- Using natDegree_pow in a domain: natDegree(f^2) = 2 * natDegree(f)
    have hα₁_nd : α₁.natDegree ≤ 1 := by
      have h := hα₁_deg; rw [natDegree_pow] at h; omega
    have hβ₁_nd : β₁.natDegree = 0 := by
      have h := hβ₁_deg
      by_cases hβ₁ : β₁ = 0; · simp [hβ₁]
      have hβ₁_sq : (β₁ ^ 2) ≠ 0 := pow_ne_zero 2 hβ₁
      have hW : (1 - X ^ 2 : Polynomial ℝ) ≠ 0 := by
        intro heq; have := congr_arg natDegree heq; simp at this
        have := natDegree_one_sub_X_sq; omega
      rw [natDegree_mul hW hβ₁_sq, natDegree_pow] at h
      have := natDegree_one_sub_X_sq; omega
    have hα₂_nd : α₂.natDegree ≤ (r - 1) / 2 := by
      have h := hα₂_deg; rw [natDegree_pow] at h; omega
    have hβ₂_nd : β₂.natDegree ≤ (r - 1) / 2 := by
      have h := hβ₂_deg
      by_cases hβ₂ : β₂ = 0; · simp [hβ₂]
      have hβ₂_sq : (β₂ ^ 2) ≠ 0 := pow_ne_zero 2 hβ₂
      have hW : (1 - X ^ 2 : Polynomial ℝ) ≠ 0 := by
        intro heq; have := congr_arg natDegree heq; simp at this
        have := natDegree_one_sub_X_sq; omega
      rw [natDegree_mul hW hβ₂_sq, natDegree_pow] at h
      have := natDegree_one_sub_X_sq; omega
    -- A = α₁*α₂ + (1-X²)*(β₁*β₂)
    -- natDegree(A) ≤ max(1 + (r-1)/2, 2 + 0 + (r-1)/2) = 2 + (r-1)/2
    -- Wait: β₁.natDegree = 0, so natDegree(β₁*β₂) ≤ 0 + (r-1)/2
    -- natDegree((1-X²)*(β₁*β₂)) ≤ 2 + (r-1)/2
    -- Key: use β₂.natDegree ≤ (r-3)/2 (from ((1-X²)*β₂²).natDegree ≤ r-1)
    -- to get both α₁*α₂ and (1-X²)*(β₁*β₂) have natDegree ≤ (r+1)/2,
    -- hence A = α₁*α₂ + (1-X²)*(β₁*β₂) has natDegree ≤ (r+1)/2 and A² ≤ r+1.
    have hβ₂_nd' : β₂.natDegree ≤ (r - 3) / 2 := by
      have h := hβ₂_deg
      by_cases hβ₂ : β₂ = 0; · simp [hβ₂]
      have hβ₂_sq : (β₂ ^ 2) ≠ 0 := pow_ne_zero 2 hβ₂
      have hW : (1 - X ^ 2 : Polynomial ℝ) ≠ 0 := by
        intro heq; have := congr_arg natDegree heq; simp at this
        have := natDegree_one_sub_X_sq; omega
      rw [natDegree_mul hW hβ₂_sq, natDegree_pow] at h
      have hW_eq := natDegree_one_sub_X_sq; omega
    -- natDegree(α₁*α₂) ≤ (r+1)/2
    have h_aa : (α₁ * α₂).natDegree ≤ (r + 1) / 2 :=
      natDegree_mul_le.trans (by omega)
    -- natDegree(β₁*β₂) ≤ (r-3)/2
    have h_bb : (β₁ * β₂).natDegree ≤ (r - 3) / 2 :=
      natDegree_mul_le.trans (by omega)
    -- natDegree((1-X²)*(β₁*β₂)) ≤ (r+1)/2
    have h_Wbb : ((1 - X ^ 2) * (β₁ * β₂)).natDegree ≤ (r + 1) / 2 :=
      natDegree_mul_le.trans (by have := natDegree_one_sub_X_sq_le; omega)
    -- natDegree(A) ≤ (r+1)/2
    have hA_nd : (α₁ * α₂ + (1 - X ^ 2) * (β₁ * β₂)).natDegree ≤ (r + 1) / 2 :=
      (natDegree_add_le _ _).trans (max_le h_aa h_Wbb)
    -- natDegree(A²) ≤ r+1
    calc ((α₁ * α₂ + (1 - X ^ 2) * (β₁ * β₂)) ^ 2).natDegree
        = 2 * (α₁ * α₂ + (1 - X ^ 2) * (β₁ * β₂)).natDegree := natDegree_pow _ _
      _ ≤ 2 * ((r + 1) / 2) := Nat.mul_le_mul_left 2 hA_nd
      _ ≤ r + 1 := by omega
  · -- Degree bound for W*B² = (1-X²)*(α₁*β₂ - β₁*α₂)²
    -- B has natDegree ≤ (r-1)/2, so (1-X²)*B² has natDegree ≤ r+1.
    have hα₁_nd : α₁.natDegree ≤ 1 := by
      have h := hα₁_deg; rw [natDegree_pow] at h; omega
    have hβ₁_nd : β₁.natDegree = 0 := by
      have h := hβ₁_deg
      by_cases hβ₁ : β₁ = 0; · simp [hβ₁]
      have hβ₁_sq : (β₁ ^ 2) ≠ 0 := pow_ne_zero 2 hβ₁
      have hW : (1 - X ^ 2 : Polynomial ℝ) ≠ 0 := by
        intro heq; have := congr_arg natDegree heq; simp at this
        have := natDegree_one_sub_X_sq; omega
      rw [natDegree_mul hW hβ₁_sq, natDegree_pow] at h
      have := natDegree_one_sub_X_sq; omega
    have hα₂_nd : α₂.natDegree ≤ (r - 1) / 2 := by
      have h := hα₂_deg; rw [natDegree_pow] at h; omega
    have hβ₂_nd' : β₂.natDegree ≤ (r - 3) / 2 := by
      have h := hβ₂_deg
      by_cases hβ₂ : β₂ = 0; · simp [hβ₂]
      have hβ₂_sq : (β₂ ^ 2) ≠ 0 := pow_ne_zero 2 hβ₂
      have hW : (1 - X ^ 2 : Polynomial ℝ) ≠ 0 := by
        intro heq; have := congr_arg natDegree heq; simp at this
        have := natDegree_one_sub_X_sq; omega
      rw [natDegree_mul hW hβ₂_sq, natDegree_pow] at h
      have hW_eq := natDegree_one_sub_X_sq; omega
    have h_ab : (α₁ * β₂).natDegree ≤ (r - 1) / 2 :=
      natDegree_mul_le.trans (by omega)
    have h_ba : (β₁ * α₂).natDegree ≤ (r - 1) / 2 :=
      natDegree_mul_le.trans (by omega)
    have hB_nd : (α₁ * β₂ - β₁ * α₂).natDegree ≤ (r - 1) / 2 :=
      (natDegree_sub_le _ _).trans (max_le h_ab h_ba)
    calc ((1 - X ^ 2) * (α₁ * β₂ - β₁ * α₂) ^ 2).natDegree
        ≤ (1 - X ^ 2 : Polynomial ℝ).natDegree +
          ((α₁ * β₂ - β₁ * α₂) ^ 2).natDegree := natDegree_mul_le
      _ = (1 - X ^ 2 : Polynomial ℝ).natDegree +
          2 * (α₁ * β₂ - β₁ * α₂).natDegree := by rw [natDegree_pow]
      _ ≤ 2 + 2 * ((r - 1) / 2) := by
          have := natDegree_one_sub_X_sq_le; omega
      _ ≤ r + 1 := by omega

private theorem lukacs_poly_decomp_aux (n : ℕ) :
    ∀ (p : Polynomial ℝ) (r : ℕ), p.natDegree ≤ r → p.natDegree ≤ n →
    (∀ θ : ℝ, 0 ≤ p.eval (cos θ)) →
    ∃ (α β : Polynomial ℝ),
      p = α ^ 2 + (1 - X ^ 2) * β ^ 2 ∧
      (α ^ 2).natDegree ≤ r + 1 ∧
      ((1 - X ^ 2) * β ^ 2).natDegree ≤ r + 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro p r hr hn hp
  -- Convert cos theta hypothesis to [-1,1] hypothesis
  have hp_Icc : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → 0 ≤ p.eval x := fun x hx => by
    rw [← cos_arccos hx.1 hx.2]; exact hp _
  -- Case 1: p = 0
  by_cases hp0 : p = 0
  · exact ⟨0, 0, by rw [hp0]; ring, by simp, by simp⟩
  -- Case 2: p has a root in (-1,1)
  by_cases h_root : ∃ a : ℝ, a ∈ Set.Ioo (-1 : ℝ) 1 ∧ IsRoot p a
  · -- Factor out (X - C a)^2
    obtain ⟨a, ha, hpa⟩ := h_root
    obtain ⟨q, hpq, hq_nonneg, hq_deg⟩ := factor_interior_root p a ha hpa hp0 hp_Icc
    -- q has smaller degree and is nonneg on [-1,1]
    have hq_cos : ∀ θ : ℝ, 0 ≤ q.eval (cos θ) := fun θ =>
      hq_nonneg _ ⟨neg_one_le_cos θ, cos_le_one θ⟩
    -- Apply induction to q (natDegree q < natDegree p <= n)
    have hq_lt_n : q.natDegree < n := by omega
    obtain ⟨α', β', hq_decomp, hα'_deg, hβ'_deg⟩ :=
      ih q.natDegree hq_lt_n q (r - 2) (by omega) le_rfl hq_cos
    -- Reconstruct: p = (X - C a)^2 * q
    -- = (X - C a)^2 * (alpha'^2 + (1-X^2)*beta'^2)
    -- = ((X - C a)*alpha')^2 + (1-X^2)*((X - C a)*beta')^2
    refine ⟨(X - C a) * α', (X - C a) * β', ?_, ?_, ?_⟩
    · rw [hpq, hq_decomp]; ring
    · have h_eq : ((X - C a) * α') ^ 2 = (X - C a) ^ 2 * α' ^ 2 := by ring
      rw [h_eq]
      have h1 : ((X - C a) ^ 2 * α' ^ 2).natDegree ≤
          ((X - C a) ^ 2).natDegree + (α' ^ 2).natDegree := natDegree_mul_le
      have h2 : ((X - C a) ^ 2).natDegree = 2 := by rw [natDegree_pow, natDegree_X_sub_C]
      omega
    · have h_eq : (1 - X ^ 2) * ((X - C a) * β') ^ 2 =
          (X - C a) ^ 2 * ((1 - X ^ 2) * β' ^ 2) := by ring
      rw [h_eq]
      have h1 : ((X - C a) ^ 2 * ((1 - X ^ 2) * β' ^ 2)).natDegree ≤
          ((X - C a) ^ 2).natDegree + ((1 - X ^ 2) * β' ^ 2).natDegree := natDegree_mul_le
      have h2 : ((X - C a) ^ 2).natDegree = 2 := by rw [natDegree_pow, natDegree_X_sub_C]
      omega
  · push_neg at h_root
    -- Case 3: No interior roots. Check boundary root multiplicities.
    -- Case 3a: Root at x = 1 with multiplicity >= 2
    by_cases h_mult1 : 2 ≤ p.rootMultiplicity 1
    · obtain ⟨q, hpq, hq_nonneg, hq_deg⟩ :=
        factor_sq_root p 1 (Set.right_mem_Icc.mpr (by norm_num)) hp0 h_mult1 hp_Icc
      have hq_cos : ∀ θ : ℝ, 0 ≤ q.eval (cos θ) := fun θ =>
        hq_nonneg _ ⟨neg_one_le_cos θ, cos_le_one θ⟩
      have hq_lt_n : q.natDegree < n := by omega
      obtain ⟨α', β', hq_decomp, hα'_deg, hβ'_deg⟩ :=
        ih q.natDegree hq_lt_n q (r - 2) (by omega) le_rfl hq_cos
      refine ⟨(X - C (1 : ℝ)) * α', (X - C (1 : ℝ)) * β', ?_, ?_, ?_⟩
      · rw [hpq, hq_decomp]; ring
      · have h_eq : ((X - C (1 : ℝ)) * α') ^ 2 = (X - C (1 : ℝ)) ^ 2 * α' ^ 2 := by ring
        rw [h_eq]
        have h1 := @natDegree_mul_le ℝ _ ((X - C (1 : ℝ)) ^ 2) (α' ^ 2)
        have h2 : ((X - C (1 : ℝ)) ^ 2).natDegree = 2 := by
          rw [natDegree_pow, natDegree_X_sub_C]
        omega
      · have h_eq : (1 - X ^ 2) * ((X - C (1 : ℝ)) * β') ^ 2 =
            (X - C (1 : ℝ)) ^ 2 * ((1 - X ^ 2) * β' ^ 2) := by ring
        rw [h_eq]
        have h1 := @natDegree_mul_le ℝ _ ((X - C (1 : ℝ)) ^ 2) ((1 - X ^ 2) * β' ^ 2)
        have h2 : ((X - C (1 : ℝ)) ^ 2).natDegree = 2 := by
          rw [natDegree_pow, natDegree_X_sub_C]
        omega
    · -- Case 3b: Root at x = -1 with multiplicity >= 2
      by_cases h_mult_neg1 : 2 ≤ p.rootMultiplicity (-1)
      · obtain ⟨q, hpq, hq_nonneg, hq_deg⟩ :=
          factor_sq_root p (-1) (Set.left_mem_Icc.mpr (by norm_num)) hp0 h_mult_neg1 hp_Icc
        have hq_cos : ∀ θ : ℝ, 0 ≤ q.eval (cos θ) := fun θ =>
          hq_nonneg _ ⟨neg_one_le_cos θ, cos_le_one θ⟩
        have hq_lt_n : q.natDegree < n := by omega
        obtain ⟨α', β', hq_decomp, hα'_deg, hβ'_deg⟩ :=
          ih q.natDegree hq_lt_n q (r - 2) (by omega) le_rfl hq_cos
        refine ⟨(X - C (-1 : ℝ)) * α', (X - C (-1 : ℝ)) * β', ?_, ?_, ?_⟩
        · rw [hpq, hq_decomp]; ring
        · have h_eq : ((X - C (-1 : ℝ)) * α') ^ 2 = (X - C (-1 : ℝ)) ^ 2 * α' ^ 2 := by ring
          rw [h_eq]
          have h1 := @natDegree_mul_le ℝ _ ((X - C (-1 : ℝ)) ^ 2) (α' ^ 2)
          have h2 : ((X - C (-1 : ℝ)) ^ 2).natDegree = 2 := by
            rw [natDegree_pow, natDegree_X_sub_C]
          omega
        · have h_eq : (1 - X ^ 2) * ((X - C (-1 : ℝ)) * β') ^ 2 =
              (X - C (-1 : ℝ)) ^ 2 * ((1 - X ^ 2) * β' ^ 2) := by ring
          rw [h_eq]
          have h1 := @natDegree_mul_le ℝ _ ((X - C (-1 : ℝ)) ^ 2) ((1 - X ^ 2) * β' ^ 2)
          have h2 : ((X - C (-1 : ℝ)) ^ 2).natDegree = 2 := by
            rw [natDegree_pow, natDegree_X_sub_C]
          omega
      · -- Case 3c: Both boundary root multiplicities <= 1.
        push_neg at h_mult1 h_mult_neg1
        -- Sub-case: p has roots at BOTH x = 1 and x = -1 (mult 1 each)
        by_cases h_root1 : IsRoot p 1
        · by_cases h_root_neg1 : IsRoot p (-1)
          · -- Both ±1 are roots (mult 1). Factor p = (X²-1)*q, so -q ≥ 0 on [-1,1].
            have h_dvd_1 : (X - C (1 : ℝ)) ∣ p := dvd_iff_isRoot.mpr h_root1
            have h_dvd_neg1 : (X - C (-1 : ℝ)) ∣ p := dvd_iff_isRoot.mpr h_root_neg1
            -- (X-1) and (X+1) are coprime, so their product divides p
            have h_coprime : IsCoprime (X - C (1 : ℝ)) (X - C (-1 : ℝ)) :=
              isCoprime_X_sub_C_of_isUnit_sub
                (sub_ne_zero_of_ne (by norm_num : (1 : ℝ) ≠ -1)).isUnit
            have h_dvd_prod : (X - C (1 : ℝ)) * (X - C (-1 : ℝ)) ∣ p :=
              h_coprime.mul_dvd h_dvd_1 h_dvd_neg1
            obtain ⟨q, hpq⟩ := h_dvd_prod
            -- p = (X-1)(X+1) * q = (X^2 - 1) * q
            -- -q >= 0 on [-1,1]
            have hq_neg_nonneg : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → 0 ≤ (-q).eval x := by
              intro x hx
              have hp_x := hp_Icc x hx
              rw [hpq] at hp_x
              simp only [eval_mul, eval_sub, eval_X, eval_C, eval_neg] at hp_x ⊢
              have h1 : x - 1 ≤ 0 := by linarith [hx.2]
              have h2 : 0 ≤ x - (-1) := by linarith [hx.1]
              rcases eq_or_lt_of_le h1 with h1_eq | h1_lt
              · -- x = 1: use continuity (q ≤ 0 on interior → q(1) ≤ 0)
                have h_at_1 : x = 1 := by linarith
                subst h_at_1
                by_contra h_neg
                push_neg at h_neg
                -- q.eval 1 > 0, so by continuity, q > 0 near 1
                have hq_cont := q.continuous
                have hq1_pos : 0 < q.eval 1 := by linarith
                obtain ⟨δ, hδ_pos, hq_near⟩ := Metric.continuousAt_iff.mp
                  hq_cont.continuousAt (q.eval 1 / 2) (by linarith)
                -- Pick y = 1 - min(delta/2, 1) in (-1, 1)
                set ε := min (δ / 2) (1 : ℝ) with hε_def
                have hε_pos : (0 : ℝ) < ε := lt_min (by linarith) one_pos
                have hε_le1 : ε ≤ 1 := min_le_right _ _
                set y := 1 - ε
                have hy_mem : y ∈ Set.Icc (-1 : ℝ) 1 :=
                  ⟨by simp [y]; linarith, by simp [y]; linarith⟩
                have hy_lt_1 : y < 1 := by simp [y]; linarith
                have hy_gt_neg1 : -1 < y := by simp [y]; linarith
                have hy_near : dist y 1 < δ := by
                  rw [Real.dist_eq, show y - 1 = -ε by simp [y], abs_neg, abs_of_pos hε_pos]
                  linarith [min_le_left (δ / 2) (1 : ℝ)]
                have hq_y_pos : 0 < q.eval y := by
                  have := hq_near hy_near
                  rw [Real.dist_eq] at this
                  linarith [neg_abs_le (q.eval y - q.eval 1)]
                -- p(y) = (y-1)(y+1)q(y) < 0, contradiction
                have hp_y := hp_Icc y hy_mem
                rw [hpq] at hp_y
                simp only [eval_mul, eval_sub, eval_X, eval_C] at hp_y
                have : (y - 1) * (y - (-1)) * q.eval y < 0 := by
                  apply mul_neg_of_neg_of_pos
                  · apply mul_neg_of_neg_of_pos <;> linarith
                  · exact hq_y_pos
                linarith
              · rcases eq_or_lt_of_le h2 with h2_eq | h2_gt
                · -- x = -1: same continuity argument
                  have h_at_neg1 : x = -1 := by linarith
                  subst h_at_neg1
                  by_contra h_neg
                  push_neg at h_neg
                  have hq_cont := q.continuous
                  have hq_neg1_pos : 0 < q.eval (-1) := by linarith
                  obtain ⟨δ, hδ_pos, hq_near⟩ := Metric.continuousAt_iff.mp
                    hq_cont.continuousAt (q.eval (-1) / 2) (by linarith)
                  set ε := min (δ / 2) (1 : ℝ)
                  have hε_pos : (0 : ℝ) < ε := lt_min (by linarith) one_pos
                  set y := -1 + ε
                  have hy_mem : y ∈ Set.Icc (-1 : ℝ) 1 :=
                    ⟨by simp [y]; linarith, by simp [y]; linarith [min_le_right (δ / 2) (1 : ℝ)]⟩
                  have hy_near : dist y (-1) < δ := by
                    rw [Real.dist_eq, show y - (-1) = ε by simp [y], abs_of_pos hε_pos]
                    linarith [min_le_left (δ / 2) (1 : ℝ)]
                  have hq_y_pos : 0 < q.eval y := by
                    have := hq_near hy_near
                    rw [Real.dist_eq] at this
                    linarith [neg_abs_le (q.eval y - q.eval (-1))]
                  have hp_y := hp_Icc y hy_mem
                  rw [hpq] at hp_y
                  simp only [eval_mul, eval_sub, eval_X, eval_C] at hp_y
                  have : (y - 1) * (y - (-1)) * q.eval y < 0 := by
                    apply mul_neg_of_neg_of_pos
                    · apply mul_neg_of_neg_of_pos
                      · linarith [min_le_right (δ / 2) (1 : ℝ)]
                      · linarith
                    · exact hq_y_pos
                  linarith
                · -- Interior: (x-1)(x+1) < 0, product ≥ 0, so q(x) ≤ 0
                  have h_prod_neg : (x - 1) * (x - (-1)) < 0 :=
                    mul_neg_of_neg_of_pos h1_lt h2_gt
                  by_contra h_neg
                  push_neg at h_neg
                  have : (x - 1) * (x - (-1)) * q.eval x < 0 :=
                    mul_neg_of_neg_of_pos h_prod_neg (by linarith)
                  linarith
            have hq0 : q ≠ 0 := by
              intro hq0; rw [hq0, mul_zero] at hpq; exact hp0 hpq
            have hnq0 : -q ≠ 0 := neg_ne_zero.mpr hq0
            -- Degree of q
            have hq_deg : q.natDegree + 2 ≤ p.natDegree := by
              have h_prod_ne : (X - C (1 : ℝ)) * (X - C (-1 : ℝ)) ≠ 0 :=
                mul_ne_zero (X_sub_C_ne_zero 1) (X_sub_C_ne_zero (-1))
              have h1 : p.natDegree = ((X - C (1 : ℝ)) * (X - C (-1 : ℝ)) * q).natDegree := by
                rw [hpq]
              have h2 : ((X - C (1 : ℝ)) * (X - C (-1 : ℝ)) * q).natDegree =
                  ((X - C (1 : ℝ)) * (X - C (-1 : ℝ))).natDegree + q.natDegree :=
                natDegree_mul h_prod_ne hq0
              have h3 : ((X - C (1 : ℝ)) * (X - C (-1 : ℝ))).natDegree = 2 := by
                rw [natDegree_mul (X_sub_C_ne_zero 1) (X_sub_C_ne_zero (-1)),
                    natDegree_X_sub_C, natDegree_X_sub_C]
              omega
            -- Apply induction to -q (which is nonneg on [-1,1])
            have hnq_cos : ∀ θ : ℝ, 0 ≤ (-q).eval (cos θ) := fun θ =>
              hq_neg_nonneg _ ⟨neg_one_le_cos θ, cos_le_one θ⟩
            have hnq_deg_r : (-q).natDegree ≤ r - 2 := by
              rw [natDegree_neg]; omega
            have hnq_lt_n : (-q).natDegree < n := by rw [natDegree_neg]; omega
            obtain ⟨A, B, h_decomp, hA_deg, hB_deg⟩ :=
              ih (-q).natDegree hnq_lt_n (-q) (r - 2) hnq_deg_r le_rfl hnq_cos
            -- p = (1-X²)·(-q) = ((1-X²)B)² + (1-X²)A²
            refine ⟨(1 - (X : Polynomial ℝ) ^ 2) * B, A, ?_, ?_, ?_⟩
            · -- p = ((1-X^2)*B)^2 + (1-X^2)*A^2
              have : -q = A ^ 2 + (1 - X ^ 2) * B ^ 2 := h_decomp
              have h_prod_eq : (X - C (1 : ℝ)) * (X - C (-1 : ℝ)) = X ^ 2 - 1 := by
                simp [C_1, C_neg]; ring
              calc p = (X - C (1 : ℝ)) * (X - C (-1 : ℝ)) * q := hpq
                _ = (X ^ 2 - 1) * q := by rw [h_prod_eq]
                _ = -(1 - X ^ 2) * q := by ring
                _ = (1 - X ^ 2) * (-q) := by ring
                _ = (1 - X ^ 2) * (A ^ 2 + (1 - X ^ 2) * B ^ 2) := by rw [this]
                _ = ((1 - X ^ 2) * B) ^ 2 + (1 - X ^ 2) * A ^ 2 := by ring
            · -- degree bound for ((1-X^2)*B)^2
              -- ((1-X^2)*B)^2 = (1-X^2) * ((1-X^2)*B^2)
              have h_eq : ((1 - X ^ 2) * B) ^ 2 = (1 - X ^ 2) * ((1 - X ^ 2) * B ^ 2) := by
                ring
              rw [h_eq]
              have h1 := @natDegree_mul_le ℝ _
                (1 - (X : Polynomial ℝ) ^ 2) ((1 - X ^ 2) * B ^ 2)
              have h2 := natDegree_one_sub_X_sq_le
              omega
            · -- degree bound for (1-X^2)*A^2
              have h1 := @natDegree_mul_le ℝ _
                (1 - (X : Polynomial ℝ) ^ 2) (A ^ 2)
              have h2 := natDegree_one_sub_X_sq_le
              omega
          · -- Root at x = 1 only (no root at -1)
            -- Same factorization approach: find degree-2 monic factor, IVT, compose
            by_cases hdeg : p.natDegree ≤ 2
            · exact lukacs_deg_le_two p hp0 hdeg r hr hp_Icc
            · push_neg at hdeg
              obtain ⟨q, hq_monic, hq_deg2, hq_dvd⟩ :=
                exists_monic_deg_two_factor p (by omega)
              have hq0 : q ≠ 0 := hq_monic.ne_zero
              obtain ⟨s, hps⟩ := hq_dvd
              have hs0 : s ≠ 0 := right_ne_zero_of_mul (hps ▸ hp0)
              have hs_deg : s.natDegree + q.natDegree = p.natDegree := by
                rw [hps, add_comm]; exact (natDegree_mul hq0 hs0).symm
              have hs_deg_lt : s.natDegree < p.natDegree := by omega
              have hq_no_interior : ∀ a : ℝ, a ∈ Set.Ioo (-1 : ℝ) 1 → ¬IsRoot q a := by
                intro a ha hqa
                have : IsRoot (q * s) a := by
                  rw [IsRoot.def, eval_mul, mul_eq_zero]; left; exact hqa
                exact h_root a ha (hps ▸ this)
              have hp_pos_interior := pos_on_interior_of_no_roots p hp_Icc h_root
              have hq_const_sign : (∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 → 0 < q.eval x) ∨
                  (∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 → q.eval x < 0) := by
                have h0_mem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
                have hq0_ne : q.eval 0 ≠ 0 := fun h =>
                  hq_no_interior 0 h0_mem (by rwa [IsRoot.def])
                -- IVT: any sign change between two points in (-1,1) gives a root
                have ivt_sign_change : ∀ a b : ℝ, a ∈ Set.Ioo (-1 : ℝ) 1 →
                    b ∈ Set.Ioo (-1 : ℝ) 1 → q.eval a < 0 → 0 < q.eval b → False := by
                  intro a b ha hb hqa_neg hqb_pos
                  have h_cont : ContinuousOn q.eval (Set.uIcc a b) :=
                    q.continuous.continuousOn
                  have h0_mem : (0 : ℝ) ∈ Set.uIcc (q.eval a) (q.eval b) :=
                    Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)
                  obtain ⟨c, hc_mem, hc_eq⟩ := intermediate_value_uIcc h_cont h0_mem
                  have hc_Ioo : c ∈ Set.Ioo (-1 : ℝ) 1 := by
                    constructor
                    · calc (-1 : ℝ) < a ⊓ b := lt_min ha.1 hb.1
                        _ ≤ c := hc_mem.1
                    · calc c ≤ a ⊔ b := hc_mem.2
                        _ < 1 := sup_lt_iff.mpr ⟨ha.2, hb.2⟩
                  exact hq_no_interior c hc_Ioo (by rwa [IsRoot.def])
                rcases lt_or_gt_of_ne hq0_ne with hq0_neg | hq0_pos
                · right; intro x hx
                  by_contra h; push_neg at h
                  rcases eq_or_lt_of_le h with heq | hlt
                  · exact hq_no_interior x hx (by rw [IsRoot.def]; linarith)
                  · exact ivt_sign_change 0 x h0_mem hx hq0_neg hlt
                · left; intro x hx
                  by_contra h; push_neg at h
                  rcases eq_or_lt_of_le h with heq | hlt
                  · exact hq_no_interior x hx (by rw [IsRoot.def]; linarith)
                  · exact ivt_sign_change x 0 hx h0_mem hlt hq0_pos
              have ⟨q', s', hps', hq'0, hs'0, hq'_deg, hs'_deg, hq'_nonneg, hs'_nonneg⟩ :
                  ∃ q' s' : Polynomial ℝ, p = q' * s' ∧ q' ≠ 0 ∧ s' ≠ 0 ∧
                    q'.natDegree = 2 ∧ s'.natDegree = s.natDegree ∧
                    (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → 0 ≤ q'.eval x) ∧
                    (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → 0 ≤ s'.eval x) := by
                rcases hq_const_sign with hq_pos | hq_neg
                · refine ⟨q, s, hps, hq0, hs0, hq_deg2, rfl,
                    nonneg_Ioo_to_Icc q (fun x hx => le_of_lt (hq_pos x hx)),
                    nonneg_Ioo_to_Icc s (fun x hx => ?_)⟩
                  have hpx := hp_pos_interior x hx
                  have hqx := hq_pos x hx
                  have : p.eval x = q.eval x * s.eval x := by rw [hps]; simp [eval_mul]
                  nlinarith [mul_pos_iff.mp (this ▸ hpx)]
                · refine ⟨-q, -s, ?_, neg_ne_zero.mpr hq0, neg_ne_zero.mpr hs0,
                    by rw [natDegree_neg]; exact hq_deg2,
                    by rw [natDegree_neg],
                    nonneg_Ioo_to_Icc (-q) (fun x hx => by simp; linarith [hq_neg x hx]),
                    nonneg_Ioo_to_Icc (-s) (fun x hx => by
                      simp only [eval_neg, Left.nonneg_neg_iff]
                      have hpx := hp_pos_interior x hx
                      have hqx := hq_neg x hx
                      have : p.eval x = q.eval x * s.eval x := by rw [hps]; simp [eval_mul]
                      nlinarith [mul_pos_iff.mp (this ▸ hpx)])⟩
                  rw [hps]; ring
              have hq'_deg_le2 : q'.natDegree ≤ 2 := le_of_eq hq'_deg
              obtain ⟨α₁, β₁, hq'_eq, hα₁_deg, hβ₁_deg⟩ :=
                lukacs_deg_le_two q' hq'0 hq'_deg_le2 q'.natDegree le_rfl hq'_nonneg
              have hs'_cos : ∀ θ : ℝ, 0 ≤ s'.eval (cos θ) := fun θ =>
                hs'_nonneg _ ⟨neg_one_le_cos θ, cos_le_one θ⟩
              have hs'_lt_n : s'.natDegree < n := by omega
              obtain ⟨α₂, β₂, hs'_eq, hα₂_deg, hβ₂_deg⟩ :=
                ih s'.natDegree hs'_lt_n s' (r - 2) (by omega) le_rfl hs'_cos
              obtain ⟨A, B, hprod_eq, hA_deg, hB_deg⟩ := lukacs_compose q' s' r
                (by omega) hq'_deg (by omega : s'.natDegree ≤ r - 2)
                α₁ β₁ α₂ β₂ hq'_eq
                (by omega)
                (by omega)
                hs'_eq (by omega) (by omega)
              exact ⟨A, B, by rw [hps']; exact hprod_eq, hA_deg, hB_deg⟩
        · -- No root at x = 1, no interior roots, boundary mults <= 1
          -- Same logic as above branch
          by_cases hdeg : p.natDegree ≤ 2
          · exact lukacs_deg_le_two p hp0 hdeg r hr hp_Icc
          · push_neg at hdeg
            obtain ⟨q, hq_monic, hq_deg2, hq_dvd⟩ :=
              exists_monic_deg_two_factor p (by omega)
            have hq0 : q ≠ 0 := hq_monic.ne_zero
            obtain ⟨s, hps⟩ := hq_dvd
            have hs0 : s ≠ 0 := right_ne_zero_of_mul (hps ▸ hp0)
            have hs_deg : s.natDegree + q.natDegree = p.natDegree := by
              rw [hps, add_comm]; exact (natDegree_mul hq0 hs0).symm
            have hs_deg_lt : s.natDegree < p.natDegree := by omega
            have hq_no_interior : ∀ a : ℝ, a ∈ Set.Ioo (-1 : ℝ) 1 → ¬IsRoot q a := by
              intro a ha hqa
              have : IsRoot (q * s) a := by
                rw [IsRoot.def, eval_mul, mul_eq_zero]; left; exact hqa
              exact h_root a ha (hps ▸ this)
            have hp_pos_interior := pos_on_interior_of_no_roots p hp_Icc h_root
            have hq_const_sign : (∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 → 0 < q.eval x) ∨
                (∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 → q.eval x < 0) := by
              have h0_mem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
              have hq0_ne : q.eval 0 ≠ 0 := fun h =>
                hq_no_interior 0 h0_mem (by rwa [IsRoot.def])
              -- IVT: any sign change between two points in (-1,1) gives a root
              have ivt_sign_change : ∀ a b : ℝ, a ∈ Set.Ioo (-1 : ℝ) 1 →
                  b ∈ Set.Ioo (-1 : ℝ) 1 → q.eval a < 0 → 0 < q.eval b → False := by
                intro a b ha hb hqa_neg hqb_pos
                have h_cont : ContinuousOn q.eval (Set.uIcc a b) :=
                  q.continuous.continuousOn
                have h0_mem : (0 : ℝ) ∈ Set.uIcc (q.eval a) (q.eval b) :=
                  Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)
                obtain ⟨c, hc_mem, hc_eq⟩ := intermediate_value_uIcc h_cont h0_mem
                have hc_Ioo : c ∈ Set.Ioo (-1 : ℝ) 1 := by
                  constructor
                  · calc (-1 : ℝ) < a ⊓ b := lt_min ha.1 hb.1
                      _ ≤ c := hc_mem.1
                  · calc c ≤ a ⊔ b := hc_mem.2
                      _ < 1 := sup_lt_iff.mpr ⟨ha.2, hb.2⟩
                exact hq_no_interior c hc_Ioo (by rwa [IsRoot.def])
              rcases lt_or_gt_of_ne hq0_ne with hq0_neg | hq0_pos
              · right; intro x hx
                by_contra h; push_neg at h
                rcases eq_or_lt_of_le h with heq | hlt
                · exact hq_no_interior x hx (by rw [IsRoot.def]; linarith)
                · exact ivt_sign_change 0 x h0_mem hx hq0_neg hlt
              · left; intro x hx
                by_contra h; push_neg at h
                rcases eq_or_lt_of_le h with heq | hlt
                · exact hq_no_interior x hx (by rw [IsRoot.def]; linarith)
                · exact ivt_sign_change x 0 hx h0_mem hlt hq0_pos
            have ⟨q', s', hps', hq'0, hs'0, hq'_deg, hs'_deg, hq'_nonneg, hs'_nonneg⟩ :
                ∃ q' s' : Polynomial ℝ, p = q' * s' ∧ q' ≠ 0 ∧ s' ≠ 0 ∧
                  q'.natDegree = 2 ∧ s'.natDegree = s.natDegree ∧
                  (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → 0 ≤ q'.eval x) ∧
                  (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → 0 ≤ s'.eval x) := by
              rcases hq_const_sign with hq_pos | hq_neg
              · refine ⟨q, s, hps, hq0, hs0, hq_deg2, rfl,
                  nonneg_Ioo_to_Icc q (fun x hx => le_of_lt (hq_pos x hx)),
                  nonneg_Ioo_to_Icc s (fun x hx => ?_)⟩
                have hpx := hp_pos_interior x hx
                have hqx := hq_pos x hx
                have : p.eval x = q.eval x * s.eval x := by rw [hps]; simp [eval_mul]
                nlinarith [mul_pos_iff.mp (this ▸ hpx)]
              · refine ⟨-q, -s, ?_, neg_ne_zero.mpr hq0, neg_ne_zero.mpr hs0,
                  by rw [natDegree_neg]; exact hq_deg2,
                  by rw [natDegree_neg],
                  nonneg_Ioo_to_Icc (-q) (fun x hx => by simp; linarith [hq_neg x hx]),
                  nonneg_Ioo_to_Icc (-s) (fun x hx => by
                    simp only [eval_neg, Left.nonneg_neg_iff]
                    have hpx := hp_pos_interior x hx
                    have hqx := hq_neg x hx
                    have : p.eval x = q.eval x * s.eval x := by rw [hps]; simp [eval_mul]
                    nlinarith [mul_pos_iff.mp (this ▸ hpx)])⟩
                rw [hps]; ring
            have hq'_deg_le2 : q'.natDegree ≤ 2 := le_of_eq hq'_deg
            obtain ⟨α₁, β₁, hq'_eq, hα₁_deg, hβ₁_deg⟩ :=
              lukacs_deg_le_two q' hq'0 hq'_deg_le2 q'.natDegree le_rfl hq'_nonneg
            have hs'_cos : ∀ θ : ℝ, 0 ≤ s'.eval (cos θ) := fun θ =>
              hs'_nonneg _ ⟨neg_one_le_cos θ, cos_le_one θ⟩
            have hs'_lt_n : s'.natDegree < n := by omega
            obtain ⟨α₂, β₂, hs'_eq, hα₂_deg, hβ₂_deg⟩ :=
              ih s'.natDegree hs'_lt_n s' (r - 2) (by omega) le_rfl hs'_cos
            obtain ⟨A, B, hprod_eq, hA_deg, hB_deg⟩ := lukacs_compose q' s' r
              (by omega) hq'_deg (hs'_deg ▸ (by omega : s.natDegree ≤ r - 2))
              α₁ β₁ α₂ β₂ hq'_eq
              (by omega)
              (by omega)
              hs'_eq (by omega) (by omega)
            exact ⟨A, B, by rw [hps']; exact hprod_eq, hA_deg, hB_deg⟩

private theorem lukacs_poly_decomp (p : Polynomial ℝ) (r : ℕ) (hr : p.natDegree ≤ r)
    (hp : ∀ θ : ℝ, 0 ≤ p.eval (cos θ)) :
    ∃ (α β : Polynomial ℝ),
      p = α ^ 2 + (1 - X ^ 2) * β ^ 2 ∧
      (α ^ 2).natDegree ≤ r + 1 ∧
      ((1 - X ^ 2) * β ^ 2).natDegree ≤ r + 1 :=
  lukacs_poly_decomp_aux p.natDegree p r hr le_rfl hp

/-- Fejér-Riesz: p(cos θ) ≥ 0 ⟹ p(cos θ) = α(cos θ)² + sin²θ · β(cos θ)²
    with deg(α²) ≤ r+1 and deg((1-x²)·β²) ≤ r+1. -/
theorem fejer_riesz_cos_decomp (p : Polynomial ℝ) (r : ℕ) (hr : p.natDegree ≤ r)
    (hp : ∀ θ : ℝ, 0 ≤ p.eval (cos θ)) :
    ∃ (α β : Polynomial ℝ),
      (∀ θ : ℝ, p.eval (cos θ) =
        (α.eval (cos θ)) ^ 2 + (sin θ) ^ 2 * (β.eval (cos θ)) ^ 2) ∧
      (α ^ 2).natDegree ≤ r + 1 ∧
      ((1 - X ^ 2) * β ^ 2).natDegree ≤ r + 1 := by
  obtain ⟨α, β, heq, hα, hβ⟩ := lukacs_poly_decomp p r hr hp
  refine ⟨α, β, ?_, hα, hβ⟩
  intro θ
  have := congr_arg (fun q => q.eval (cos θ)) heq
  simp only [eval_add, eval_mul, eval_sub, eval_one, eval_pow, eval_X] at this
  nlinarith [sin_sq_add_cos_sq θ]

/-! ## Polynomial identity from pointwise identity -/

/-- Trig identity → polynomial identity via density of cos(θ) in [-1,1]. -/
theorem trig_identity_to_poly (p α β : Polynomial ℝ)
    (h : ∀ θ : ℝ, p.eval (cos θ) =
      (α.eval (cos θ)) ^ 2 + (sin θ) ^ 2 * (β.eval (cos θ)) ^ 2) :
    p = α ^ 2 + (1 - X ^ 2) * β ^ 2 := by
  set q := p - (α ^ 2 + (1 - X ^ 2) * β ^ 2) with hq_def
  suffices h_eq : q = 0 by
    have : p = q + (α ^ 2 + (1 - X ^ 2) * β ^ 2) := by rw [hq_def]; ring
    rw [h_eq, zero_add] at this; exact this
  have hq_eval : ∀ θ : ℝ, q.eval (cos θ) = 0 := by
    intro θ
    have h1 := h θ
    simp only [hq_def, eval_sub, eval_add, eval_mul, eval_sub, eval_one, eval_pow, eval_X]
    rw [h1]; ring_nf; rw [sin_sq]; ring
  have hq_root : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → IsRoot q x := by
    intro x ⟨hx1, hx2⟩
    rw [IsRoot.def, ← cos_arccos hx1 hx2]
    exact hq_eval (arccos x)
  apply eq_zero_of_infinite_isRoot
  apply Set.Infinite.mono (s := Set.Icc (-1 : ℝ) 1)
  · intro x hx; exact hq_root x hx
  · exact Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)

/-! ## Lukács decomposition -/

/-- Lukács decomposition:
    If p is nonneg on [-1,1] with natDegree ≤ r, then there exist polynomials α, β
    such that p = α² + (1-X²)·β², with deg(α²) ≤ r+1 and deg((1-X²)·β²) ≤ r+1. -/
theorem lukacs_decomposition_raw (p : Polynomial ℝ) (r : ℕ) (hr : p.natDegree ≤ r)
    (hp : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → 0 ≤ p.eval x) :
    ∃ (α β : Polynomial ℝ),
      p = α ^ 2 + (1 - X ^ 2) * β ^ 2 ∧
      (α ^ 2).natDegree ≤ r + 1 ∧
      ((1 - X ^ 2) * β ^ 2).natDegree ≤ r + 1 := by
  have hp_cos : ∀ θ : ℝ, 0 ≤ p.eval (cos θ) := eval_cos_nonneg p hp
  obtain ⟨α, β, h_eq, h_deg_α, h_deg_β⟩ := fejer_riesz_cos_decomp p r hr hp_cos
  exact ⟨α, β, trig_identity_to_poly p α β h_eq, h_deg_α, h_deg_β⟩

/-! ## Markov-Lukacz theorem (Theorem 7) -/

/-- Markov-Lukacz (Theorem 7): p nonneg on [-1,1] with deg ≤ r ⟹ p ∈ Q([-1,1])_{r+1}.
    Proved via Lukács: p = α² + (1-x²)β², taking σ₀ = α², σ₁ = β². -/
theorem markov_lukacz (p : Polynomial ℝ) (hr : p.natDegree ≤ r)
    (hp : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → 0 ≤ p.eval x) :
    p ∈ BoxUniPreordering (r + 1) := by
  obtain ⟨α, β, hdecomp, hdeg_α, hdeg_β⟩ := lukacs_decomposition_raw p r hr hp
  refine ⟨α ^ 2, β ^ 2, IsSOSUni_sq α, IsSOSUni_sq β, hdeg_α, ?_, ?_⟩
  · rw [mul_comm]
    exact hdeg_β
  · rw [hdecomp, mul_comm (1 - X ^ 2) (β ^ 2)]

end OptimalConvergenceRates

end
